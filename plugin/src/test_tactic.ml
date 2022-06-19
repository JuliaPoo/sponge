open Sexplib (* opam install sexplib *)
open Proofview


type assertion =
  | AEq of Sexp.t * Sexp.t
  | AProp of Sexp.t

let assertion_to_equality a =
  match a with
  | AEq (lhs, rhs) -> (lhs, rhs)
  | AProp e -> (Sexp.Atom "True", e)

type rule =
  { rulename: string;
    quantifiers: string list;
    sideconditions: assertion list;
    conclusion: assertion;
    triggers: Sexp.t list }

type query_accumulator =
  { declarations: (string, int) Hashtbl.t; (* arity of each function symbol *)
    rules: rule Queue.t;
    initial_exprs: Sexp.t Queue.t }

let empty_query_accumulator () =
  { declarations = Hashtbl.create 20;
    rules = Queue.create ();
    initial_exprs = Queue.create () }

let make_rust_valid s =
  Str.global_replace (Str.regexp "@") "AT" (Str.global_replace (Str.regexp "\\.") "DOT" s)

let proof_file_to_reversed_list filepath f =
  let res = ref [] in
  let chan = open_in filepath in
  let _discard_unshelve = input_line chan in
  let line = ref (input_line chan) in
  (try
     while not (String.starts_with ~prefix:"idtac" !line); do
       if String.starts_with ~prefix:"eapply " !line &&
            String.ends_with ~suffix:";" !line
       then
         let c = String.sub !line 7 (String.length !line - 8) in
         res := f c :: !res;
         line := input_line chan
       else
         failwith ("expected 'eapply (...)', but got '" ^ !line ^ "'")
     done
   with End_of_file -> ());
  close_in chan;
  !res

let proof_file_path = "/tmp/egg_proof.txt"

module type BACKEND =
  sig
    type t
    val create: unit -> t
    val declare_fun: t -> string -> int -> unit
    val declare_rule: t -> rule -> unit
    val declare_initial_expr: t -> Sexp.t -> unit
    val minimize: t -> Sexp.t -> string list
    val prove_equal: t -> Sexp.t -> Sexp.t -> string list option
    val reset: t -> unit
    val close: t -> unit
  end

(* Once created, supports interactions satisfying the following regex:
( declare_fun+; declare_rule+; declare_initial_expr+; ( minimize | prove_equal ); reset )
and the close at the end is optional a no-op. *)
module RecompilationBackend : BACKEND = struct
  let needs_multipattern r =
    (match r.sideconditions with
     | _ :: _ -> true
     | [] -> match r.triggers with
             | _ :: _ -> true
             | [] -> false)

  let rule_to_macro buf r =
    if needs_multipattern r then (
      Buffer.add_string buf {|    coq_rewrite!("|};
      Buffer.add_string buf r.rulename;
      Buffer.add_string buf {|", "|};
      List.iteri (fun i sc ->
          Buffer.add_string buf "$hyp";
          Buffer.add_string buf (string_of_int i);
          Buffer.add_string buf " = ";
          (match sc with
           | AEq (lhs, rhs) ->
              Sexp.to_buffer ~buf lhs;
              Buffer.add_string buf " = ";
              Sexp.to_buffer ~buf rhs;
           | AProp e ->
              Sexp.to_buffer ~buf e);
          Buffer.add_string buf ", ";
        ) r.sideconditions;
      List.iteri (fun i tr ->
          Buffer.add_string buf "$trigger";
          Buffer.add_string buf (string_of_int i);
          Buffer.add_string buf " = ";
          Sexp.to_buffer ~buf tr;
          Buffer.add_string buf ", "
        ) r.triggers;
      let (lhs, rhs) = assertion_to_equality r.conclusion in
      Buffer.add_string buf "$lhs = ";
      Sexp.to_buffer ~buf lhs;
      Buffer.add_string buf {|" => "|};
      Sexp.to_buffer ~buf rhs;
      Buffer.add_string buf "\");\n"
    ) else (
      Buffer.add_string buf {|    rewrite!("|};
      Buffer.add_string buf r.rulename;
      Buffer.add_string buf {|", "|};
      let (lhs, rhs) = assertion_to_equality r.conclusion in
      Sexp.to_buffer ~buf lhs;
      Buffer.add_string buf {|" => "|};
      Sexp.to_buffer ~buf rhs;
      Buffer.add_string buf "\");\n"
    )

  type state =
    | SDeclaringFuns
    | SDeclaringRules
    | SDeclaringInitialExprs
    | SDone

  type t = {
      buf: Buffer.t;
      lemma_arity_buf: Buffer.t;
      is_eq_buf: Buffer.t;
      mutable state: state }

  let create () =
    let buf = Buffer.create 10000 in
begin
Buffer.add_string buf {|
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
pub fn get_proof_file_path() -> &'static str {
  "|};
Buffer.add_string buf proof_file_path;
Buffer.add_string buf {|"
}
define_language! {
  pub enum CoqSimpleLanguage {
    Num(i32),
|}
end;
    let lemma_arity_buf = Buffer.create 1000 in
    let is_eq_buf = Buffer.create 1000 in
    { buf; lemma_arity_buf; is_eq_buf; state = SDeclaringFuns }

  let declare_fun t fname arity =
    match t.state with
    | SDeclaringFuns ->
       Buffer.add_string t.buf
         (Printf.sprintf {|    "%s" = %s([Id; %d]),\n|} fname (make_rust_valid fname) arity)
    | _ -> failwith "invalid state machine transition"

  let declare_rule t rule =
    (match t.state with
     | SDeclaringFuns ->
        t.state <- SDeclaringRules;
begin
Buffer.add_string t.buf
{|    Symbol(Symbol),
  }
}

pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {
  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![
|}
end
     | SDeclaringRules -> ()
     | _ -> failwith "invalid state machine transition");
    rule_to_macro t.buf rule;
    Buffer.add_string t.is_eq_buf {|    ("|};
    Buffer.add_string t.is_eq_buf rule.rulename;
    Buffer.add_string t.is_eq_buf
      (match rule.conclusion with
       | AEq (_, _) -> "\", true),\n"
       | AProp _ -> "\", false),\n");
    Buffer.add_string t.lemma_arity_buf {|    ("|};
    Buffer.add_string t.lemma_arity_buf rule.rulename;
    Buffer.add_string t.lemma_arity_buf ", ";
    Buffer.add_string t.lemma_arity_buf (string_of_int (List.length rule.quantifiers));
    Buffer.add_string t.lemma_arity_buf "),\n"

  let declare_initial_expr t e =
    (match t.state with
     | SDeclaringRules ->
        t.state <- SDeclaringInitialExprs;
begin
Buffer.add_string t.buf {|  ];
  v
}

pub fn get_lemma_arity(name: &str) -> Option<usize> {
  let v = vec![
|};
Buffer.add_buffer t.buf t.lemma_arity_buf;
Buffer.add_string t.buf {|  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

pub fn is_eq(name: &str) -> Option<bool> {
  let v = vec![
|};
Buffer.add_buffer t.buf t.is_eq_buf;
Buffer.add_string t.buf {|
#[allow(unused_variables)]
pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {
  let es = vec![
|}
end
     | SDeclaringInitialExprs -> ()
     | _ -> failwith "invalid state machine transition");
    Buffer.add_string t.buf {|    "|};
    Sexp.to_buffer ~buf:t.buf e;
    Buffer.add_string t.buf "\",\n"

  let minimize t e =
    (match t.state with
     | SDeclaringInitialExprs -> ()
     | _ -> failwith "invalid state machine transition");
    Buffer.add_string t.buf "  ];\n";
    Buffer.add_string t.buf "  let st : &str = \"";
    Sexp.to_buffer ~buf:t.buf e;
    Buffer.add_string t.buf {|";
  f_simplify(st, es);
}
|};
    let egg_repo_path = "/home/sam/git/clones/egg" (* adapt as needed *) in
    let rust_rules_path = egg_repo_path ^ "/src/rw_rules.rs" in
    let oc = open_out rust_rules_path in
    Buffer.output_buffer oc t.buf;
    close_out oc;
    Printf.printf "Wrote Rust code to %s\n" rust_rules_path;
    flush stdout;
    let cargo_command = "cd \"" ^ egg_repo_path ^ "\" && cargo run coq" in
    let status = Sys.command cargo_command in
    Printf.printf "Command '%s' returned exit status %d\n" cargo_command status;
    if status != 0 then failwith "invoking rust failed"
    else t.state <- SDone;
    let reversed_pf = proof_file_to_reversed_list proof_file_path (fun l -> l) in
    List.rev reversed_pf

  let prove_equal t lhs rhs = failwith "not supported yet"

  let reset t =
    t.state <- SDeclaringFuns;
    Buffer.clear t.buf;
    Buffer.clear t.lemma_arity_buf;
    Buffer.clear t.is_eq_buf

  let close t = ()

end

(* can be switched to another backend *)
module Backend = RecompilationBackend

let parse_constr_expr s =
  Pcoq.parse_string Pcoq.Constr.constr s

let print_constr_expr env sigma e =
  Pp.string_of_ppcmds (Ppconstr.pr_constr_expr env sigma e)

let mkCApp f args =
  Constrexpr_ops.mkAppC (f, args)

let cHole = CAst.make (Constrexpr.CHole (None, Namegen.IntroAnonymous, None))

let compose_constr_expr_proofs revlist =
  let rec f revlist acc =
    match revlist with
    | [] -> acc
    | h :: t -> f t (mkCApp h [acc]) in
  f revlist cHole

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

let egg_simpl_goal () =
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

        let reversed_pf = proof_file_to_reversed_list proof_file_path parse_constr_expr in
        let composed_pf = compose_constr_expr_proofs reversed_pf in
        print_endline "Composed proof:";
        print_endline (print_constr_expr env sigma composed_pf);
        Refine.refine ~typecheck:true (fun sigma ->
          let (sigma, constr_pf) = Constrintern.interp_constr_evars env sigma composed_pf in
          Feedback.msg_notice
            Pp.(str"Proof: " ++ Printer.pr_econstr_env env sigma constr_pf);
          (sigma, constr_pf))

        (*
        print_endline "Proof as constr_exprs:";
        List.iter (fun e -> print_endline (print_constr_expr env sigma e)) pf;
        print_endline "";
         *)

      end;
    end

let kind_to_str sigma c =
  match EConstr.kind sigma c with
  | Constr.Rel i -> "Rel"
  | Constr.Var x -> "Var"
  | Constr.Meta m -> "Meta"
  | Constr.Evar ex -> "Evar"
  | Constr.Sort s -> "Sort"
  | Constr.Cast (c, k, t) -> "Cast"
  | Constr.Prod (b, t, body) -> "Prod"
  | Constr.Lambda (b, t, body) -> "Lambda"
  | Constr.LetIn (b, rhs, t, body) -> "LetIn"
  | Constr.App (f, args) -> "App"
  | Constr.Const (c, u) -> "Const"
  | Constr.Ind (i, u) -> "Ind"
  | Constr.Construct (c, u) -> "Construct"
  | Constr.Case (c, u, b, r, d, x, y) -> "Case"
  | Constr.Fix f -> "Fix"
  | Constr.CoFix f -> "CoFix"
  | Constr.Proj (p, c) -> "Proj"
  | Constr.Int i -> "Int"
  | Constr.Float f -> "Float"
  | Constr.Array (u, a, b, c) -> "Array"

let inspect c =
  Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    (match EConstr.kind sigma c with
     | Constr.App (f, args) ->
        (match args with
         | [| tp; arg |] -> Printf.printf "It's a %s\n" (kind_to_str sigma arg)
         | _ -> Printf.printf "unexpected")
     | _ -> Printf.printf "unexpected");
    Proofview.tclUNIT ()
    end
