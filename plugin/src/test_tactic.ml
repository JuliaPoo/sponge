open Sexplib (* opam install sexplib *)
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

let equals_glob_ref glref c =
  let open Names in GlobRef.equal (Coqlib.lib_ref glref) c

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
             | Constr.Ind (i, univs) -> register_arity arities (ind_to_str i) arity
             | Constr.Construct (c, univs) -> register_arity arities (ctor_to_str c) arity
             | Constr.Const (c, univs) -> register_arity arities (const_to_str c) arity
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

let destruct_eq sigma t =
  match EConstr.kind sigma t with
  | Constr.App (e, args) ->
     (match args with
      | [| tp; lhs; rhs |] ->
         (match EConstr.kind sigma e with
          | Constr.Ind (i, univs) ->
             let open Names in
             let open Coqlib in
             if GlobRef.equal (Coqlib.build_coq_eq_data ()).eq (GlobRef.IndRef i)
             then Some (tp, lhs, rhs)
             else None
          | _ -> None)
      | _ -> None)
  | _ -> None

let rec convert_dyn_list sigma t =
  match EConstr.kind sigma t with
  | Constr.App (h, args) ->
     (match EConstr.kind sigma h with
      | Constr.Construct (c, univs) ->
         if equals_glob_ref "egg.dyn_cons" (Names.GlobRef.ConstructRef c) then
           (match args with
            | [| _tp; head; tail |] -> head :: convert_dyn_list sigma tail
            | _ -> failwith "not a well-typed dyn_list")
         else failwith "Constr.App is not a dyn_list"
      | _ -> failwith "expected dyn_list, but got app whose head is not a constructor")
  | Constr.Construct (c, univs) ->
     if equals_glob_ref "egg.dyn_nil" (Names.GlobRef.ConstructRef c) then []
     else failwith "expected dyn_list, but got constructor which is not dyn_nil"
  | _ -> failwith "not a dyn_list"

let destruct_trigger sigma t =
  match EConstr.kind sigma t with
  | Constr.App (trg, args) ->
     (match args with
      | [| triggers; x |] ->
         (match EConstr.kind sigma trg with
          | Constr.Const (c, univs) ->
             if equals_glob_ref "egg.with_trigger" (Names.GlobRef.ConstRef c)
             then Some (convert_dyn_list sigma triggers, x)
             else None
          | _ -> None)
      | _ -> None)
  | _ -> None

let rec count_leading_empty_strs l =
  match l with
  | "" :: t -> 1 + count_leading_empty_strs t
  | _ -> 0

(* arities:  maps function symbols to the number of arguments they take
   qnames:   maps lemma names to their list of quantifier names, "" for hypotheses
   is_eq:    maps lemma names to booleans indicating whether their conclusion is an equality
   exprs:    set (represented as Hashtbl with unit values) of extra expressions
             to add to the egraph
   name:     name of thm
   hyp:      Context.Named.Declaration (LocalAssum or LocalDef) *)
let eggify_hyp env sigma arities qnames is_eq exprs hyp =
  let register_expr e = Hashtbl.replace exprs e () in

  let to_equality nameEnv t =
    let e1, e2 = match destruct_eq sigma t with
      | Some (_, lhs, rhs) ->
         (process_expr env sigma arities nameEnv lhs,
          process_expr env sigma arities nameEnv rhs)
      | None ->
         ("True", process_expr env sigma arities nameEnv t) in
    if List.length nameEnv == count_leading_empty_strs nameEnv
    then (register_expr e1; register_expr e2) else ();
    (e1, e2) in

  let stringify_equality_without_sideconds name nameEnv lhs rhs =
    Hashtbl.replace qnames name (List.rev nameEnv);
    Hashtbl.replace is_eq name (lhs != "True");
    if List.length nameEnv == 0 then
      "    rewrite!(\"" ^ name ^ "\"; \"" ^ lhs ^ "\" => \"" ^ rhs ^ "\"),\n" ^
      "    rewrite!(\"" ^ name ^ "-rev\"; \"" ^ rhs ^ "\" => \"" ^ lhs ^ "\"),\n"
    else
      "    rewrite!(\"" ^ name ^ "\"; \"" ^ lhs ^ "\" => \"" ^ rhs ^ "\"),\n" in

  let rec process_impls name nameEnv manual_triggers t =
    let i = count_leading_empty_strs nameEnv in
    let prefix = if i == 0 then "    coq_rewrite!(\"" ^ name ^ "\"; \"" else "" in
    match destruct_trigger sigma t with
    | Some (trigger_exprs, body) ->
       let trigger_strs = List.map (process_expr env sigma arities nameEnv) trigger_exprs in
       process_impls name nameEnv
         (List.append trigger_strs manual_triggers) body
    | None ->
      match EConstr.kind sigma t with
      | Constr.Prod (b, tp, body) ->
         if EConstr.Vars.noccurn sigma 1 body then
           let (lhs, rhs) = to_equality nameEnv tp in
           (* including $ to avoid clashes with Coq variable names *)
           prefix ^"?hyp$" ^ (Stdlib.string_of_int i) ^ " = " ^ lhs ^ " = " ^ rhs ^ ", " ^
             process_impls name ("" :: nameEnv) manual_triggers body
         else raise Unsupported (* foralls after impls are not supported *)
      | _ ->
         if i == 0 && List.length manual_triggers == 0 then
           let (lhs, rhs) = to_equality nameEnv t in
           stringify_equality_without_sideconds name nameEnv lhs rhs
         else begin
           let (lhs, rhs) = to_equality nameEnv t in
           Hashtbl.replace qnames name (List.rev nameEnv);
           Hashtbl.replace is_eq name (lhs != "True");
           let t = String.concat "" (List.mapi
                     (fun i e -> "?trigger$" ^ (Stdlib.string_of_int i) ^ " = " ^ e ^ ", ")
                     manual_triggers) in
           prefix ^ t ^ "?lhs$ = " ^ lhs ^ "\" => \"" ^ rhs ^ "\"),\n"
           end in

  let rec process_foralls name nameEnv t =
    match EConstr.kind sigma t with
    | Constr.Prod (b, tp, body) ->
       if EConstr.Vars.noccurn sigma 1 body then
         process_impls name nameEnv [] t
       else
         process_foralls name (binder_name_to_string b :: nameEnv) body
    | _ -> process_impls name nameEnv [] t in

  let open Context in
  let open Named.Declaration in
  match hyp with
  | LocalAssum (id, t) -> begin
      let sigma, tp = Typing.type_of env sigma (EConstr.of_constr t) in
      if Termops.is_Prop sigma tp then
        let name = Names.Id.to_string id.binder_name in
        process_foralls name [] (EConstr.of_constr t)
      else raise Unsupported
    end
  | LocalDef (id, t, _tp) -> begin
     let name = Names.Id.to_string id.binder_name in
     let rhs = process_expr env sigma arities [] (EConstr.of_constr t) in
     register_expr name;
     register_expr rhs;
     stringify_equality_without_sideconds (name ^ "$def") [] name rhs
    end

let egg_simpl_goal proof_file_path =
  Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Goal.env gl in
    let hyps = Environ.named_context (Goal.env gl) in

    let arities = Hashtbl.create 20 in
    let qnames = Hashtbl.create 20 in
    let is_eq = Hashtbl.create 20 in
    let exprs = Hashtbl.create 20 in
    let rules_str = ref "" in

    List.iter (fun hyp ->
        try
          let rule = eggify_hyp env sigma arities qnames is_eq exprs hyp in
          rules_str := !rules_str ^ rule;
        with
          Unsupported -> ())
      (List.rev hyps);

    let g = process_expr env sigma arities [] (Goal.concl gl) in

    let egg_repo_path = "/home/sam/git/clones/egg" (* adapt as needed *) in
    let rust_rules_path = egg_repo_path ^ "/src/rw_rules.rs" in
    let oc = open_out rust_rules_path in

    Printf.fprintf oc "\n#![allow(missing_docs,non_camel_case_types)]\n";
    Printf.fprintf oc "use crate ::*;\n";
    Printf.fprintf oc "pub fn get_proof_file_path() -> &'static str {\n";
    Printf.fprintf oc "  \"%s\"\n" proof_file_path;
    Printf.fprintf oc "}\n";

    print_lang arities oc;

    Printf.fprintf oc "pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {\n";
    Printf.fprintf oc "  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![\n";
    Printf.fprintf oc "%s" !rules_str;
    Printf.fprintf oc "  ];\n";
    Printf.fprintf oc "  v\n";
    Printf.fprintf oc "}\n\n";

    Printf.fprintf oc "pub fn get_lemma_arity(name: &str) -> Option<usize> {\n";
    Printf.fprintf oc "  let v = vec![\n";
    Hashtbl.iter (fun l ns -> Printf.fprintf oc "    (\"%s\", %d),\n" l (List.length ns))
      qnames;
    Printf.fprintf oc "  ];\n";
    Printf.fprintf oc "  let o = v.iter().find(|t| t.0 == name);\n";
    Printf.fprintf oc "  match o {\n";
    Printf.fprintf oc "    Some((_, n)) => { return Some(*n); }\n";
    Printf.fprintf oc "    None => { return None; }\n";
    Printf.fprintf oc "  }\n";
    Printf.fprintf oc "}\n\n";

    Printf.fprintf oc "pub fn is_eq(name: &str) -> Option<bool> {\n";
    Printf.fprintf oc "  let v = vec![\n";
    Hashtbl.iter (fun l b -> Printf.fprintf oc "    (\"%s\", %b),\n" l b) is_eq;
    Printf.fprintf oc "  ];\n";
    Printf.fprintf oc "  let o = v.iter().find(|t| t.0 == name);\n";
    Printf.fprintf oc "  match o {\n";
    Printf.fprintf oc "    Some((_, n)) => { return Some(*n); }\n";
    Printf.fprintf oc "    None => { return None; }\n";
    Printf.fprintf oc "  }\n";
    Printf.fprintf oc "}\n\n";

    Printf.fprintf oc "#[allow(unused_variables)]\n";
    Printf.fprintf oc "pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {\n";
    Printf.fprintf oc "  let st : &str = \"%s\";\n" g;
    Printf.fprintf oc "  let es = vec![\n";
    Hashtbl.iter (fun e _ -> Printf.fprintf oc "    \"%s\",\n" e) exprs;
    Printf.fprintf oc "  ];\n";
    Printf.fprintf oc "  f_simplify(st, es);\n";
    Printf.fprintf oc "}\n\n";

    close_out oc;
    Printf.printf "Wrote Rust code to %s\n" rust_rules_path;
    flush stdout;

    let cargo_command = "cd \"" ^ egg_repo_path ^ "\" && cargo run coq" in
    let status = Sys.command cargo_command in
    Printf.printf "Command '%s' returned exit status %d\n" cargo_command status;
    if status != 0 then
      Tacticals.tclZEROMSG (Pp.str "invoking rust failed")
    else begin
        let exp1 = Sexp.(List [
                             Atom "This";
                             List [Atom "is"; Atom "an"];
                             List [Atom "s"; Atom "expression"]
                   ]) in
        (* Serialize an Sexp object into a string *)
        print_endline (Sexp.to_string exp1);
        (* Parse a string and produce a Sexp object  *)
        let exp2 = Sexp.of_string "(This (is an) (s expression to be parsed))" in
        print_endline (Sexp.to_string_hum exp2);
        Proofview.tclUNIT ()
      end;
    end
