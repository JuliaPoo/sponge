open Sexplib (* opam install sexplib *)
open Proofview


type assertion =
  | AEq of Sexp.t * Sexp.t
  | AProp of Sexp.t

let assertion_to_equality a =
  match a with
  | AEq (lhs, rhs) -> (lhs, rhs)
  | AProp e -> (Sexp.Atom "&True", e)

type rule =
  { rulename: string;
    quantifiers: string list;
    sideconditions: assertion list;
    conclusion: assertion;
    triggers: Sexp.t list }

type query_accumulator =
  { declarations: (string, int) Hashtbl.t; (* arity of each function symbol *)
    rules: rule Queue.t;
    initial_exprs: (Sexp.t, unit) Hashtbl.t }

let empty_query_accumulator () =
  let ds = Hashtbl.create 20 in
  (* always-present constants (even if they don't appear in any expression) *)
  Hashtbl.replace ds "&True" 0;
  Hashtbl.replace ds "&False" 0;
  { declarations = ds;
    rules = Queue.create ();
    initial_exprs = Hashtbl.create 20 }

(* only needed to create valid Rust enum names, not needed to translate back *)
let make_rust_valid s =
  Str.global_replace (Str.regexp "@") "AT"
    (Str.global_replace (Str.regexp "\\.") "DOT"
       (Str.global_replace (Str.regexp "&") "ID" s))

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

let assertion_to_smtlib a =
  match a with
  | AEq (lhs, rhs) -> Sexp.List [Sexp.Atom "="; lhs; rhs]
  | AProp e -> (* e is of type U, but we need to convert it to `Bool`: *)
     Sexp.List [Sexp.Atom "="; Sexp.Atom "&True"; e]

(* (! body tag value) *)
let smtlib_annot body tag value =
  Sexp.List [Sexp.Atom "!"; body; Sexp.Atom tag; value]

(* (assert (! body :named name)) *)
let smtlib_assert_named name body =
  Sexp.List [Sexp.Atom "assert"; smtlib_annot body ":named" (Sexp.Atom name)]

(* (forall ((x1 U) .. (xN U)) body) *)
let smtlib_forall varnames body =
  match varnames with
  | _ :: _ ->
     let qs = List.map (fun x -> Sexp.List [Sexp.Atom ("?" ^ x); Sexp.Atom "$U"]) varnames in
     Sexp.List [Sexp.Atom "forall"; Sexp.List qs; body]
  | [] -> body

(* (! body :pattern (tr1 .. trN)) *)
let smtlib_pattern triggers body =
  match triggers with
  | _ :: _ -> smtlib_annot body ":pattern" (Sexp.List triggers)
  | [] -> body

(* (=> hyp1 .. hypN concl) *)
let smtlib_impls hyps concl =
  match hyps with
  | _ :: _ -> Sexp.List (Sexp.Atom "=>" :: List.append hyps [concl])
  | [] -> concl

let smtlib_rule r =
  smtlib_assert_named r.rulename
    (smtlib_forall r.quantifiers
       (smtlib_pattern r.triggers
          (smtlib_impls (List.map assertion_to_smtlib r.sideconditions)
             (assertion_to_smtlib r.conclusion))))

let smtlib_initial_expr e =
  Sexp.List [Sexp.Atom "assert"; (Sexp.List [Sexp.Atom "$initial"; e])]

module type BACKEND =
  sig
    type t
    val create: unit -> t
    val declare_fun: t -> string -> int -> unit
    val declare_rule: t -> rule -> unit
    val declare_initial_expr: t -> Sexp.t -> unit
    val minimize: t -> Sexp.t -> string list
    val prove: t -> assertion -> string list option
    val reset: t -> unit
    val close: t -> unit
  end

module FileBasedSmtBackend : BACKEND = struct
  type t = out_channel option ref

  let smt_file_path = "/tmp/egraph_query.smt2"

  let new_output_file () =
    let oc = open_out smt_file_path in
    Printf.fprintf oc "(set-logic UF)\n";
    Printf.fprintf oc "(set-option :produce-proofs true)\n";
    (* U stands for "Universe", the only sort *)
    Printf.fprintf oc "(declare-sort $U 0)\n";
    (* to mark initial expressions to be used for saturation *)
    Printf.fprintf oc "(declare-fun $initial ($U) Bool)\n";
    (* Note: in smtlib, there's already a constant `true` of sort `Bool`, but
       we need our own `True` of sort `U` to make sure it's comparable
       to what our untyped functions return *)
    oc

  let create () = ref (Some (new_output_file ()))

  let declare_fun t fname arity =
    let oc = Option.get !t in
    let args = String.concat " " (List.init arity (fun _ -> "$U")) in
    Printf.fprintf oc "(declare-fun %s (%s) $U)\n" fname args

  let declare_rule t r =
    let oc = Option.get !t in
    Sexp.output oc (smtlib_rule r);
    Printf.fprintf oc "\n"

  let declare_initial_expr t e =
    let oc = Option.get !t in
    Sexp.output oc (smtlib_initial_expr e);
    Printf.fprintf oc "\n"

  let minimize t e =
    failwith "not supported"

  let prove t a =
    let oc = Option.get !t in
    Sexp.output oc (Sexp.List [Sexp.Atom "assert";
                               Sexp.List [Sexp.Atom "not"; (assertion_to_smtlib a)]]);
    Printf.fprintf oc "\n";
    Printf.fprintf oc "(check-sat)\n";
    (*Printf.fprintf oc "(get-proof)\n"; (* quite verbose *) *)
    close_out oc;
    t := None;
    Printf.printf "Wrote %s\n" smt_file_path;
    flush stdout;
    let command = "time cvc5 --tlimit=1000 " ^ smt_file_path in
    let status = Sys.command command in
    Printf.printf "Command '%s' returned exit status %d\n" command status;
    None

  let reset t =
    (match !t with
     | Some oc -> close_out oc
     | None -> ());
    t := Some (new_output_file ())

  let close t =
    match !t with
    | Some oc -> close_out oc
    | None -> ()

end

let apply_query_accumulator qa (type bt) (module B : BACKEND with type t = bt) =
  let m = B.create () in
  Hashtbl.iter (B.declare_fun m) qa.declarations;
  Queue.iter (B.declare_rule m) qa.rules;
  Hashtbl.iter (fun e () -> B.declare_initial_expr m e) qa.initial_exprs;
  m

(* Once created, supports interactions satisfying the following regex:
( declare_fun+; declare_rule+; declare_initial_expr+; ( minimize | prove ); reset )
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
      Buffer.add_string buf {|"; "|};
      List.iteri (fun i sc ->
          Buffer.add_string buf "?$hyp";
          Buffer.add_string buf (string_of_int i);
          Buffer.add_string buf " = ";
          let (lhs, rhs) = assertion_to_equality sc in
          Sexp.to_buffer ~buf lhs;
          Buffer.add_string buf " = ";
          Sexp.to_buffer ~buf rhs;
          Buffer.add_string buf ", ";
        ) r.sideconditions;
      List.iteri (fun i tr ->
          Buffer.add_string buf "?$trigger";
          Buffer.add_string buf (string_of_int i);
          Buffer.add_string buf " = ";
          Sexp.to_buffer ~buf tr;
          Buffer.add_string buf ", "
        ) r.triggers;
      let (lhs, rhs) = assertion_to_equality r.conclusion in
      Buffer.add_string buf "?$lhs = ";
      Sexp.to_buffer ~buf lhs;
      Buffer.add_string buf {|" => "|};
      Sexp.to_buffer ~buf rhs;
      Buffer.add_string buf "\"),\n"
    ) else (
      Buffer.add_string buf {|    rewrite!("|};
      Buffer.add_string buf r.rulename;
      Buffer.add_string buf {|"; "|};
      let (lhs, rhs) = assertion_to_equality r.conclusion in
      Sexp.to_buffer ~buf lhs;
      Buffer.add_string buf {|" => "|};
      Sexp.to_buffer ~buf rhs;
      Buffer.add_string buf "\"),\n"
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
|}
end;
    let lemma_arity_buf = Buffer.create 1000 in
    let is_eq_buf = Buffer.create 1000 in
    { buf; lemma_arity_buf; is_eq_buf; state = SDeclaringFuns }

  let declare_fun t fname arity =
    match t.state with
    | SDeclaringFuns ->
       Buffer.add_string t.buf
         (Printf.sprintf "    \"%s\" = %s([Id; %d]),\n" fname (make_rust_valid fname) arity)
    | _ -> failwith "invalid state machine transition"

  let declare_rule t rule =
    (match t.state with
     | SDeclaringFuns ->
        t.state <- SDeclaringRules;
begin
Buffer.add_string t.buf {|  }
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
    Buffer.add_string t.lemma_arity_buf "\", ";
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
Buffer.add_string t.buf {|  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

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
    let egg_repo_path = "/home/bthom/git/fjfj2/coq/Coquetier/egg" (* adapt as needed *) in
    let rust_rules_path = egg_repo_path ^ "/src/rw_rules.rs" in
    let oc = open_out rust_rules_path in
    Buffer.output_buffer oc t.buf;
    close_out oc;
    Printf.printf "Wrote Rust code to %s\n" rust_rules_path;
    flush stdout;
    let cargo_command = "cd \"" ^ egg_repo_path ^ "\" && cargo run --bin coq" in
    let status = Sys.command cargo_command in
    Printf.printf "Command '%s' returned exit status %d\n" cargo_command status;
    if status != 0 then failwith "invoking rust failed"
    else t.state <- SDone;
    let reversed_pf = proof_file_to_reversed_list proof_file_path (fun l -> l) in
    List.rev reversed_pf

  let prove t a = failwith "not supported yet"

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
  Pcoq.parse_string Pcoq.Constr.constr
    (* to avoid clashes of our names with SMT-defined names (eg and, not, true,
       we prefix them with &, and need to undo that here *)
    (Str.global_replace (Str.regexp "&") "" s)

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

(* we use % instead of @ because leading @ is reserved in smtlib *)
let implicits_prefix r =
  if has_implicit_args r then "@" else ""

let rec process_expr env sigma arities nameEnv e =
  let ind_to_str i =
    let r = Names.GlobRef.IndRef i in
    implicits_prefix r ^ Pp.string_of_ppcmds (Printer.pr_inductive env i) in
  let const_to_str c =
    let r = Names.GlobRef.ConstRef c in
    implicits_prefix r ^ Pp.string_of_ppcmds (Printer.pr_constant env c) in
  let ctor_to_str c =
    let r = Names.GlobRef.ConstructRef c in
    implicits_prefix r ^ Pp.string_of_ppcmds (Printer.pr_constructor env c) in
  let sort_to_str s = Pp.string_of_ppcmds
                        (Printer.pr_sort sigma (EConstr.ESorts.kind sigma s)) in
  (* Note: arity is determined by usage, not by type, because some function (eg sep)
     might always be used partially applied (we require the same arity at all usages) *)
  let process_atom e arity =
    let name = match EConstr.kind sigma e with
      | Constr.Rel i -> "?" ^ lookup_name nameEnv i
      | Constr.Var id -> Names.Id.to_string id
      | Constr.Ind (i, univs) -> ind_to_str i
      | Constr.Const (c, univs) -> const_to_str c
      | Constr.Construct (ctor, univs) -> ctor_to_str ctor
      | Constr.Sort s -> sort_to_str s
      | _ -> raise Unsupported in
    if String.starts_with ~prefix:"?" name then
      Sexp.Atom name
    else (
      let n = "&" ^ name in (* to avoid clashes with predefined names from smtlib *)
      register_arity arities n arity;
      Sexp.Atom n) in
  try
    (* treat Z literals as uninterpreted, so that they can have the same smtlib type U
       as everything else *)
    let z = "&" ^ Stdlib.string_of_int (z_to_int sigma e) in
    register_arity arities z 0;
    Sexp.Atom z
  with NotACoqNumber ->
        match EConstr.kind sigma e with
        | Constr.App (f, args) ->
           Sexp.List (process_atom f (Array.length args) ::
                        List.map (process_expr env sigma arities nameEnv)
                          (Array.to_list args))
        | _ -> process_atom e 0

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

(* hyp:      Context.Named.Declaration (LocalAssum or LocalDef) *)
let eggify_hyp env sigma (qa: query_accumulator) hyp =
  let register_expr e = Hashtbl.replace qa.initial_exprs e () in

  let to_assertion nameEnv t =
    let e1, e2, res = match destruct_eq sigma t with
      | Some (_, lhs, rhs) ->
         let lhs' = process_expr env sigma qa.declarations nameEnv lhs in
         let rhs' = process_expr env sigma qa.declarations nameEnv rhs in
         (lhs', rhs', AEq (lhs', rhs'))
      | None ->
         let lhs' = Sexp.Atom "&True" in
         let rhs' = process_expr env sigma qa.declarations nameEnv t in
         (lhs', rhs', AProp rhs') in
    if List.length nameEnv == count_leading_empty_strs nameEnv
    then (register_expr e1; register_expr e2) else ();
    res in

  let rec process_impls name nameEnv sideconditions manual_triggers t =
    match destruct_trigger sigma t with
    | Some (tr_exprs, body) ->
       let tr_sexprs = List.map (process_expr env sigma qa.declarations nameEnv) tr_exprs in
       process_impls name nameEnv sideconditions (List.append manual_triggers tr_sexprs) body
    | None ->
      match EConstr.kind sigma t with
      | Constr.Prod (b, tp, body) ->
         if EConstr.Vars.noccurn sigma 1 body then
           let side = to_assertion nameEnv tp in
           process_impls name ("" :: nameEnv) (side :: sideconditions) manual_triggers body
         else raise Unsupported (* foralls after impls are not supported *)
      | _ -> Queue.push {
                 rulename = name;
                 quantifiers = List.rev nameEnv;
                 sideconditions = List.rev sideconditions;
                 conclusion = to_assertion nameEnv t;
                 triggers = manual_triggers;
               } qa.rules in

  let rec process_foralls name nameEnv t =
    match EConstr.kind sigma t with
    | Constr.Prod (b, tp, body) ->
       if EConstr.Vars.noccurn sigma 1 body then
         process_impls name nameEnv [] [] t
       else
         process_foralls name (binder_name_to_string b :: nameEnv) body
    | _ -> process_impls name nameEnv [] [] t in

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
      let rawname = Names.Id.to_string id.binder_name in
      let name = "&" ^ rawname in
      register_arity qa.declarations name 0;
      let lhs = Sexp.Atom name in
      let rhs = process_expr env sigma qa.declarations [] (EConstr.of_constr t) in
      register_expr lhs;
      register_expr rhs;
      Queue.push { rulename = rawname ^ "$def";
                   quantifiers = [];
                   sideconditions = [];
                   conclusion = AEq (lhs, rhs);
                   triggers = [] } qa.rules
    end

let egg_simpl_goal () =
  Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Goal.env gl in
    let hyps = Environ.named_context (Goal.env gl) in

    let qa = empty_query_accumulator () in

    List.iter (fun hyp ->
        try eggify_hyp env sigma qa hyp
        with Unsupported -> ())
      (List.rev hyps);

    let g = process_expr env sigma qa.declarations [] (Goal.concl gl) in

    let b_smt = apply_query_accumulator qa (module FileBasedSmtBackend) in
    let _ = FileBasedSmtBackend.prove b_smt (AProp g) in

    let b = apply_query_accumulator qa (module Backend) in
    let reversed_pf = List.rev (Backend.minimize b g) in
    let composed_pf = compose_constr_expr_proofs (List.map parse_constr_expr reversed_pf) in
    print_endline "Composed proof:";
    print_endline (print_constr_expr env sigma composed_pf);
    Refine.refine ~typecheck:true (fun sigma ->
        let (sigma, constr_pf) = Constrintern.interp_constr_evars env sigma composed_pf in
        Feedback.msg_notice
          Pp.(str"Proof: " ++ Printer.pr_econstr_env env sigma constr_pf);
        (sigma, constr_pf))
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
