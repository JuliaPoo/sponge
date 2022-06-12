open Proofview

let constants = ref ([] : EConstr.t list)

(* This is a pattern to collect terms from the Coq memory of valid terms
  and proofs.  This pattern extends all the way to the definition of function
 c_U *)
let collect_constants () =
  if (!constants = []) then
    let open EConstr in
    let open UnivGen in
    let find_reference = Coqlib.find_reference [@ocaml.warning "-3"] in
    let gr_H = find_reference "egg" ["egg"; "Data"] "pack" in
    let gr_M = find_reference "egg" ["egg"; "Data"] "packer" in
    let gr_R = find_reference "egg" ["Coq"; "Init"; "Datatypes"] "pair" in
    let gr_P = find_reference "egg" ["Coq"; "Init"; "Datatypes"] "prod" in
    let gr_U = find_reference "egg" ["egg"; "Data"] "uncover" in
    constants := List.map (fun x -> of_constr (constr_of_monomorphic_global (Global.env ()) x))
      [gr_H; gr_M; gr_R; gr_P; gr_U];
    !constants
  else
    !constants

let c_H () =
  match collect_constants () with
    it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of pack"

let c_M () =
  match collect_constants () with
    _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of pack_marker"

let c_R () =
  match collect_constants () with
    _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of pair"

let c_P () =
  match collect_constants () with
    _ :: _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of prod"

let c_U () =
  match collect_constants () with
    _ :: _ :: _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of prod"

(* The following tactic is meant to pack an hypothesis when no other
   data is already packed.

   The main difficulty in defining this tactic is to understand how to
   construct the input expected by apply_in. *)
let package i = Goal.enter begin fun gl ->
  Tactics.apply_in true false i
   [(* this means that the applied theorem is not to be cleared. *)
    None, (CAst.make (c_M (),
           (* we don't specialize the theorem with extra values. *)
           Tactypes.NoBindings))]
     (* we don't destruct the result according to any intro_pattern *)
    None
  end

(* This function is meant to observe a type of shape (f a)
   and return the value a.  *)

(* Remark by Maxime: look for destApp combinator. *)
let unpack_type sigma term =
  let report () =
    CErrors.user_err (Pp.str "expecting a packed type") in
  match EConstr.kind sigma term with
  | Constr.App (_, [| ty |]) -> ty
  | _ -> report ()

(* This function is meant to observe a type of shape
   A -> pack B -> C and return A, B, C
  but it is not used in the current version of our tactic.
  It is kept as an example. *)
let two_lambda_pattern sigma term =
  let report () =
    CErrors.user_err (Pp.str "expecting two nested implications") in
(* Note that pattern-matching is always done through the EConstr.kind function,
   which only provides one-level deep patterns. *)
  match EConstr.kind sigma term with
  (* Here we recognize the outer implication *)
  | Constr.Prod (_, ty1, l1) ->
      (* Here we recognize the inner implication *)
      (match EConstr.kind sigma l1 with
      | Constr.Prod (n2, packed_ty2, deep_conclusion) ->
        (* Here we recognized that the second type is an application *)
        ty1, unpack_type sigma packed_ty2, deep_conclusion
      | _ -> report ())
  | _ -> report ()

(* In the environment of the goal, we can get the type of an assumption
  directly by a lookup.  The other solution is to call a low-cost retyping
  function like *)
let get_type_of_hyp env id =
  match EConstr.lookup_named id env with
  | Context.Named.Declaration.LocalAssum (_, ty) -> ty
  | _ -> CErrors.user_err (let open Pp in
                             str (Names.Id.to_string id) ++
                             str " is not a plain hypothesis")

let repackage i h_hyps_id = Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Tacmach.project gl in
    let concl = Tacmach.pf_concl gl in
    let (ty1 : EConstr.t) = get_type_of_hyp env i in
    let (packed_ty2 : EConstr.t) = get_type_of_hyp env h_hyps_id in
    let ty2 = unpack_type sigma packed_ty2 in
    let new_packed_type = EConstr.mkApp (c_P (), [| ty1; ty2 |]) in
    let open EConstr in
    let new_packed_value =
        mkApp (c_R (), [| ty1; ty2; mkVar i;
          mkApp (c_U (), [| ty2; mkVar h_hyps_id|]) |]) in
    Refine.refine ~typecheck:true begin fun sigma ->
      let sigma, new_goal = Evarutil.new_evar env sigma
          (mkArrowR (mkApp(c_H (), [| new_packed_type |]))
             (Vars.lift 1 concl))
      in
      sigma, mkApp (new_goal,
                  [|mkApp(c_M (), [|new_packed_type; new_packed_value |]) |])
      end
    end

let pack_tactic i =
  let h_hyps_id = (Names.Id.of_string "packed_hyps") in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Environ.named_context_val (Proofview.Goal.env gl) in
    if not (Termops.mem_named_context_val i hyps) then
      (CErrors.user_err
          (Pp.str ("no hypothesis named" ^ (Names.Id.to_string i))))
    else
      if Termops.mem_named_context_val h_hyps_id hyps then
          tclTHEN (repackage i h_hyps_id)
            (tclTHEN (Tactics.clear [h_hyps_id; i])
               (Tactics.introduction h_hyps_id))
      else
        tclTHEN (package i)
          (tclTHEN (Tactics.rename_hyp [i, h_hyps_id])
             (Tactics.move_hyp h_hyps_id Logic.MoveLast))
    end

let binder_name_to_string b =
  let open Context in
  Pp.string_of_ppcmds (Names.Name.print b.binder_name)

exception NotACoqNumber

let positive_to_int sigma e =
  let open Names in
  let xI = Coqlib.lib_ref "num.pos.xI" in
  let xO = Coqlib.lib_ref "num.pos.xO" in
  let xH = Coqlib.lib_ref "num.pos.xH" in
  let rec recf p =
    match EConstr.kind sigma p with
    | Constr.Construct (ctor, univs) ->
       if GlobRef.equal (GlobRef.ConstructRef ctor) xH then 1 else raise NotACoqNumber
    | Constr.App (f, args) ->
       let digit = match EConstr.kind sigma f with
         | Constr.Construct (ctor, univs) ->
            if GlobRef.equal (GlobRef.ConstructRef ctor) xI then 1 else
              if GlobRef.equal (GlobRef.ConstructRef ctor) xO then 0 else
                raise NotACoqNumber
         | _ -> raise NotACoqNumber in
       let rest = match args with
         | [| a |] -> recf a
         | _ -> raise NotACoqNumber in
       rest * 2 + digit (* TODO this might overflow, use bigints or fail? *)
    | _ -> raise NotACoqNumber in
  recf e

let z_to_int sigma e =
  let open Names in
  let z0 = Coqlib.lib_ref "num.Z.Z0" in
  let zpos = Coqlib.lib_ref "num.Z.Zpos" in
  let zneg = Coqlib.lib_ref "num.Z.Zneg" in
  match EConstr.kind sigma e with
  | Constr.Construct (ctor, univs) ->
     if GlobRef.equal (GlobRef.ConstructRef ctor) z0 then 0 else raise NotACoqNumber
  | Constr.App (f, args) -> begin
     let sign = match EConstr.kind sigma f with
       | Constr.Construct (ctor, univs) ->
          if GlobRef.equal (GlobRef.ConstructRef ctor) zpos then 1 else
            if GlobRef.equal (GlobRef.ConstructRef ctor) zneg then -1 else
              raise NotACoqNumber
       | _ -> raise NotACoqNumber in
     match args with
     | [| a |] -> sign * positive_to_int sigma a
     | _ -> raise NotACoqNumber
    end
  | _ -> raise NotACoqNumber

exception Unsupported

let lookup_name nameEnv index =
  List.nth nameEnv (index - 1)

let make_rust_valid s =
  Str.global_replace (Str.regexp "@") "AT" (Str.global_replace (Str.regexp "\\.") "DOT" s)

let print_lang arities chan =
  Printf.fprintf chan "define_language! {\n";
  Printf.fprintf chan "  pub enum CoqSimpleLanguage {\n";
  Printf.fprintf chan "    Num(i32),\n";
  Hashtbl.iter
    (fun f n -> Printf.fprintf chan "    \"%s\" = %s([Id; %d]),\n" f (make_rust_valid f) n)
    arities;
  Printf.fprintf chan "    Symbol(Symbol),\n";
  Printf.fprintf chan "  }\n";
  Printf.fprintf chan "}\n\n"

let register_arity arities f n =
  match Hashtbl.find_opt arities f with
  | Some m -> if n == m then () else failwith (f ^ " appears with different arities")
  | None -> Hashtbl.add arities f n

let has_implicit_args gref =
  let open Impargs in
  let impargs = select_stronger_impargs (implicits_of_global gref) in
  let impargs = List.map is_status_implicit impargs in
  (*Printf.printf "%s\n" (String.concat " "
                          (List.map (fun b -> if b then "I" else "E") impargs)); *)
  List.exists (fun b -> b) impargs

let rec process_expr env sigma arities nameEnv e =
  let ind_to_str i =
    let r = Names.GlobRef.IndRef i in
    let a = if has_implicit_args r then "@" else "" in
    a ^ Pp.string_of_ppcmds (Printer.pr_inductive env i) in
  let const_to_str c =
    let r = Names.GlobRef.ConstRef c in
    let a = if has_implicit_args r then "@" else "" in
    a ^ Pp.string_of_ppcmds (Printer.pr_constant env c) in
  let ctor_to_str c =
    let r = Names.GlobRef.ConstructRef c in
    let a = if has_implicit_args r then "@" else "" in
    a ^ Pp.string_of_ppcmds (Printer.pr_constructor env c) in
  let sort_to_str s = Pp.string_of_ppcmds
                        (Printer.pr_sort sigma (EConstr.ESorts.kind sigma s)) in
  try Stdlib.string_of_int (z_to_int sigma e)
  with NotACoqNumber ->
        match EConstr.kind sigma e with
        | Constr.App (f, args) -> begin
            (let arity = Array.length args in
             match EConstr.kind sigma f with
             | Constr.Ind (i, univs) ->
                (*let r = Names.GlobRef.IndRef i in
                Printf.printf "%s :::" s;
                let _ = has_implicit_args r in*)
                let s = ind_to_str i in
                register_arity arities s arity
             | Constr.Const (c, univs) ->
                (*let r = Names.GlobRef.ConstRef c in
                Printf.printf "%s :::" s;
                let _ = has_implicit_args r in*)
                let s = const_to_str c in
                register_arity arities s arity
             | Constr.Var id -> register_arity arities (Names.Id.to_string id) arity
             | _ -> ());
            "(" ^ process_expr env sigma arities nameEnv f ^ " " ^
              String.concat " " (List.map (process_expr env sigma arities nameEnv)
                                   (Array.to_list args)) ^ ")"
          end
        | Constr.Rel i -> "?" ^ lookup_name nameEnv i
        | Constr.Var id -> Names.Id.to_string id
        | Constr.Ind (i, univs) -> ind_to_str i
        | Constr.Const (c, univs) -> const_to_str c
        | Constr.Construct (ctor, univs) -> ctor_to_str ctor
        | Constr.Sort s -> sort_to_str s
        | _ -> raise Unsupported

let eggify_thm env sigma arities term =
  let process_equality nameEnv t =
    match EConstr.kind sigma t with
    | Constr.App (e, args) -> begin
       match args with
       | [| tp; lhs; rhs |] -> begin
           match EConstr.kind sigma e with
           | Constr.Ind (i, univs) ->
              let open Names in
              let open Coqlib in
              if GlobRef.equal (Coqlib.build_coq_eq_data ()).eq (GlobRef.IndRef i)
              then
                (*let op = if List.length nameEnv == 0 then " <=> " else " => " in*)
                let op = " => " in
                let l = process_expr env sigma arities nameEnv lhs in
                let r = process_expr env sigma arities nameEnv rhs in
                "\"" ^ l ^ "\"" ^ op ^ "\"" ^ r ^ "\""
              else raise Unsupported
           | _ -> raise Unsupported
         end
       | _ -> raise Unsupported
      end
    | _ -> raise Unsupported in

  let rec process_impls nameEnv t =
    match EConstr.kind sigma t with
    | Constr.Prod (name, tp, body) ->
       if EConstr.Vars.noccurn sigma 1 body then
         process_equality nameEnv tp ^ "--->" ^ process_impls ("" :: nameEnv) body
       else raise Unsupported (* foralls after impls are not supported *)
    | _ -> process_equality nameEnv t in

  let rec process_foralls nameEnv t =
    match EConstr.kind sigma t with
    | Constr.Prod (b, tp, body) ->
       if EConstr.Vars.noccurn sigma 1 body then
         process_impls nameEnv t
       else
         process_foralls (binder_name_to_string b :: nameEnv) body
    | _ -> process_equality nameEnv t in

  process_foralls [] term

let egg_simpl_goal () =
  Goal.enter begin fun gl ->
    let open Context in
    let open Named.Declaration in
    let sigma = Tacmach.project gl in
    let hyps = Environ.named_context (Goal.env gl) in
    Printf.printf "\n#![allow(missing_docs,non_camel_case_types)]\n";
    Printf.printf "use crate ::*;\n";
    let arities = Hashtbl.create 20 in
    let rules_str = ref "" in
    List.iter (function
        | LocalAssum (id, t) -> begin
           let name = Names.Id.to_string id.binder_name in
           try
             let stmt = eggify_thm (Goal.env gl) sigma arities (EConstr.of_constr t) in
             rules_str := !rules_str ^ "    rewrite!(\"" ^ name ^ "\"; " ^ stmt ^ "),\n";
           with
             Unsupported -> ()
          end
        | LocalDef (id, c, t) -> ())
      (List.rev hyps);

    let g = process_expr (Goal.env gl) sigma arities [] (Goal.concl gl) in

    print_lang arities stdout;

    Printf.printf "pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {\n";
    Printf.printf "  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![\n";
    Printf.printf "%s" !rules_str;
    Printf.printf "  ];\n";
    Printf.printf "  v\n";
    Printf.printf "}\n\n";

    Printf.printf "pub fn run_simplifier(f : fn(&str) -> ()) {\n";
    Printf.printf "  let st : &str = \"%s\";\n" g;
    Printf.printf "  f(&st);\n";
    Printf.printf "}\n\n";

    Proofview.tclUNIT ()
    end
