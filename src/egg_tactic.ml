open Sexplib (* opam install sexplib *)
open Proofview

let egg_repo_path = "/opt/link_to_egg" (* adapt as needed *)
let rust_rules_path = egg_repo_path ^ "/src/rw_rules.rs"
let recompilation_proof_file_path = "/tmp/egg_proof.txt"
let _coquetier_input_path = egg_repo_path ^ "/coquetier_input.smt2"
let _coquetier_proof_file_path = egg_repo_path ^ "/coquetier_proof_output.txt"

type assertion =
  | AEq of Sexp.t * Sexp.t
  | AProp of Sexp.t

  type proof =
  | PSteps of string list
  | PContradiction of string * string list

exception Unsupported
let true_typed = 
  Sexp.List [Sexp.Atom "annot"; Sexp.Atom "&True"; Sexp.Atom "&Prop"; Sexp.Atom "0"]

let assertion_to_equality a =
  match a with
  | AEq (lhs, rhs) -> (lhs, rhs)
  | AProp e -> (true_typed, e)

type rule =
  { rulename: string;
    quantifiers: string list;
    sideconditions: assertion list;
    conclusion: assertion;
    triggers: Sexp.t list }

type fn_metadata =
  { arity : int;
    is_nonprop_ctor : bool }

type query_accumulator =
  { declarations: (string, fn_metadata) Hashtbl.t; (* arity of each function symbol, and is it a non-propositional constructor *)
    rules: rule Queue.t;
    evar_constraints: (Sexp.t, unit) Hashtbl.t;
    initial_exprs: (Sexp.t, unit) Hashtbl.t }

let get_backend_name: unit -> string =
  Goptions.declare_string_option_and_ref
    ~depr:false
    ~key:["Egg"; "Backend"]
    ~value:"FileBasedEggBackend"

let log_ignored_hyps: unit -> bool =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Egg";"Log";"Ignored";"Hypotheses"]
    ~value:false

let log_proofs: unit -> bool =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Egg";"Log";"Proofs"]
    ~value:false

let log_misc_tracing: unit -> bool =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Egg";"Misc";"Tracing"]
    ~value:false
let empty_query_accumulator () =
  let ds = Hashtbl.create 20 in
  (* always-present constants (even if they don't appear in any expression) *)
  Hashtbl.replace ds "annot" { arity = 3; is_nonprop_ctor = false;};
  Hashtbl.replace ds "&True" { arity = 0; is_nonprop_ctor = false;};
  Hashtbl.replace ds "&False" { arity = 0; is_nonprop_ctor = false;};
  { declarations = ds;
    rules = Queue.create ();
    evar_constraints =  Hashtbl.create 20;
    initial_exprs = Hashtbl.create 20 }

(* only needed to create valid Rust enum names, not needed to translate back *)
let make_rust_valid s =
  Str.global_replace (Str.regexp "!") "BANG"
    (Str.global_replace (Str.regexp "@") "AT"
      (Str.global_replace (Str.regexp "\\.") "DOT"
         (Str.global_replace (Str.regexp "&") "ID"
            (Str.global_replace (Str.regexp "'") "PRIME" s))))

let strip_pre_suff s prefix suffix =
  if String.starts_with ~prefix:prefix s && String.ends_with ~suffix:suffix s
  then
    String.sub s (String.length prefix) (String.length s - (String.length suffix + String.length prefix))
  else
    failwith ("expected '" ^ prefix ^ "..." ^ suffix ^"', but got '" ^ s ^ "'")

let proof_file_to_proof filepath =
  let res = ref [] in
  let chan = open_in filepath in
  let contradiction = ref None in
  let fst_line = input_line chan in
  (if String.starts_with ~prefix:"(* CONTRADICTION *)" fst_line
   then
      let line = input_line chan in
      let prefix = "assert " in
      let suffix = " as ABSURDCASE." in
      let middle = strip_pre_suff line prefix suffix in
      contradiction:= Some(middle)
    else
     ());
  ignore(input_line chan);
  (try
    let line = ref (input_line chan) in
    while not (String.starts_with ~prefix:"idtac" !line) do
      let prefix = "eapply " in
      let suffix = ";" in
      let middle = strip_pre_suff !line prefix suffix in
      res := middle :: !res;
      line := input_line chan
    done
  with End_of_file -> ());
  close_in chan;
  match !contradiction with
  | Some(c) -> PContradiction(c, List.rev !res)
  | None -> PSteps (List.rev !res)


let evar_instantiate_from_file filepath =
  if log_misc_tracing () then Printf.printf "Read file \n" else ();
  (* Produce a list of instantiation datastructure *)
  let res = ref [] in
  let current_subst = ref [] in
  let current_var = ref 0 in
  let chan = open_in filepath in
  (try
    let line = ref (input_line chan) in
    while true do
      flush stdout;
      if log_misc_tracing() then Printf.printf "Read one line \n" else ();
      let current_line = !line in 
      if current_line = "(* Substitution suggested *)" then 
        ((if !current_subst != [] then 
          res := !current_subst :: !res else ());
        current_subst := []; 
        line := input_line chan)
      else 
        begin
          let suffix = "" in
          (if String.starts_with ~prefix:"var" current_line then 
            let prefix = "var ?X" in
            let middle = strip_pre_suff current_line prefix suffix in
            if log_misc_tracing () then Printf.printf "Parsed var %s\n" middle else ();
            current_var := int_of_string middle
          else (if String.starts_with ~prefix:"val" current_line then 
            let prefix = "val " in
            let middle = strip_pre_suff current_line prefix suffix in
            current_subst := (!current_var, middle):: !current_subst;
            if log_misc_tracing() then Printf.printf "Parsed val %s\n" middle else ();
          else raise Unsupported));
          line := input_line chan
        end
    done
  with End_of_file -> ());
  (if !current_subst != [] then 
          res := !current_subst :: !res else ());
  close_in chan;
  !res


let assertion_to_smtlib a =
  match a with
  | AEq (lhs, rhs) -> Sexp.List [Sexp.Atom "="; lhs; rhs]
  | AProp e -> (* e is of type U, but we need to convert it to `Bool`: *)
     Sexp.List [Sexp.Atom "="; true_typed ; e]

(* (! body tag value) *)
let smtlib_annot body tag value =
  Sexp.List [Sexp.Atom "!"; body; Sexp.Atom tag; value]
let smtlib_highcost r = 
  Sexp.List [Sexp.Atom "avoid"; Sexp.Atom r]

let smtlib_requires_term t = 
  Sexp.List [Sexp.Atom "require"; t]
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
    val declare_fun: t -> string -> fn_metadata -> unit
    val declare_rule: t -> rule -> unit
    val declare_highcost: t -> string -> unit
    val declare_requires_term: t -> Sexp.t -> unit
    val declare_initial_expr: t -> Sexp.t -> unit
    (* val declare_evar_constraint : t -> Sexp.t -> unit *)
    val minimize: t -> Sexp.t -> int -> proof
    val search_evars : t -> Sexp.t -> int -> ((int * string) list) list 
    val prove: t -> assertion -> string list option
    val reset: t -> unit
    val close: t -> unit
  end

module FileBasedSmtBackend : BACKEND = struct
  type t =
    { oc: out_channel;
      smt_file_path: string }

  let declare_highcost t r =
    assert false
  let declare_requires_term t r =
    assert false
  let new_output_file smt_file_path =
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

  let create () =
    let smt_file_path = "/tmp/egraph_query.smt2" in
    let oc = new_output_file smt_file_path in
    { oc; smt_file_path }

  let declare_fun t fname fn_m =
    let args = String.concat " " (List.init fn_m.arity (fun _ -> "$U")) in
    Printf.fprintf t.oc "(declare-fun %s (%s) $U)\n" fname args

  let declare_rule t r =
    Sexp.output t.oc (smtlib_rule r);
    Printf.fprintf t.oc "\n"

  let declare_initial_expr t e =
    Sexp.output t.oc (smtlib_initial_expr e);
    Printf.fprintf t.oc "\n"
  
  (* let declare_evar_constraint t e = assert false *)

  let minimize t e ffn_limit =
    failwith "not supported"

  let search_evars t e ffn_limit = assert false

  let prove t a =
    Sexp.output t.oc (Sexp.List [Sexp.Atom "assert";
                               Sexp.List [Sexp.Atom "not"; (assertion_to_smtlib a)]]);
    Printf.fprintf t.oc "\n";
    Printf.fprintf t.oc "(check-sat)\n";
    (*Printf.fprintf t.oc "(get-proof)\n"; (* quite verbose *) *)
    close_out t.oc;
    if log_misc_tracing() then Printf.printf "Wrote %s\n" t.smt_file_path else ();
    flush stdout;
    let command = "time cvc5 --tlimit=1000 " ^ t.smt_file_path in
    let status = Sys.command command in
    if log_misc_tracing() then  Printf.printf "Command '%s' returned exit status %d\n" command status else ();
    None

  let reset t =
    failwith "not supported"

  let close t =
    try close_out t.oc with _ -> ()

end


module FileBasedEggBackend : BACKEND = struct
  type t =
    { oc: out_channel;
      query_file_path: string;
      response_file_path: string }

  let create () =
    (* Generate a new file name *)
    let open Filename in 
    let query_file_path = temp_file ~temp_dir:egg_repo_path "coquetier_" ".in" in
    (* let query_file_path = coquetier_input_path in *)
    let oc = open_out query_file_path in
    (* let response_file_path = coquetier_proof_file_path in *)
    let response_file_path = temp_file ~temp_dir:egg_repo_path "coquetier_" ".out" in
    { oc; query_file_path; response_file_path }

  let declare_fun t fname fn_m = () (* no need to declare functions *)
  let declare_highcost t r =
    Sexp.output t.oc (smtlib_highcost r);
    Printf.fprintf t.oc "\n"
    
  let declare_requires_term t r = 
    Sexp.output t.oc (smtlib_requires_term r);
    Printf.fprintf t.oc "\n"

  let declare_rule t r =
    Sexp.output t.oc (smtlib_rule r);
    Printf.fprintf t.oc "\n"

  let declare_initial_expr t e =
    Sexp.output t.oc (smtlib_initial_expr e);
    Printf.fprintf t.oc "\n"

  (* let declare_evar_constraint t e = assert false *)

  let minimize t e ffn_limit =
    Sexp.output t.oc (Sexp.List [Sexp.Atom "minimize";
                                 e; Sexp.Atom (string_of_int ffn_limit)]);
    Printf.fprintf t.oc "\n";
    close_out t.oc;
    if log_misc_tracing() then Printf.printf "Wrote %s\n" t.query_file_path else ();
    flush stdout;
    (* let command = "cd \"" ^ egg_repo_path ^ "\" && time ./target/release/coquetier" in *)
    let command = "cd \"" ^ egg_repo_path ^ "\" && ./target/release/coquetier " ^t.query_file_path ^ " " ^ t.response_file_path in
    (* Printf.printf "%s\n" command; *)
    (* flush stdout; *)
    let status = Sys.command command in
    if log_misc_tracing() then Printf.printf "Command '%s' returned exit status %d\n" command status else ();
    if not (log_misc_tracing()) then 
      let open Sys in 
      remove t.query_file_path
    else ();
    let res = proof_file_to_proof t.response_file_path in
    if not (log_misc_tracing()) then 
      let open Sys in 
      remove t.response_file_path
    else ();
    res

  let search_evars t e ffn_limit =
    Sexp.output t.oc (Sexp.List [Sexp.Atom "search";
                                 e; Sexp.Atom (string_of_int ffn_limit)]);
    Printf.fprintf t.oc "\n";
    close_out t.oc;
    if log_misc_tracing() then Printf.printf "\n Wrote evarsearch %s\n" t.query_file_path else ();
    flush stdout;
    let command = "cd \"" ^ egg_repo_path ^ "\" && ./target/release/coquetier " ^t.query_file_path ^ " " ^ t.response_file_path in
    (* Printf.printf "%s\n" command; *)
    (* flush stdout; *)
    let _status = Sys.command command in
    if log_misc_tracing() then Printf.printf "Command for evar '%s' returned exit status %d\n" command _status else ();
    flush stdout;
    if not (log_misc_tracing()) then 
      let open Sys in 
      remove t.query_file_path
    else ();
    let res = evar_instantiate_from_file  t.response_file_path in
    if not (log_misc_tracing()) then 
      let open Sys in 
      remove t.response_file_path
    else ();
    res


  let prove t a =
    failwith "not supported"

  let reset t =
    failwith "not supported"

  let close t =
    (* TODO: This seem to never be called? Ask about the intention *)
    try 
      close_out t.oc;
      if not (log_misc_tracing()) then 
        let open Sys in 
        remove t.query_file_path;
        remove t.response_file_path
      else ();
    with _ -> ()

end

let apply_query_accumulator qa (type bt) (module B : BACKEND with type t = bt) (m: bt) =
  Hashtbl.iter (B.declare_fun m) qa.declarations;
  Queue.iter (B.declare_rule m) qa.rules;
  (* Hashtbl.iter (fun e () -> B.declare_evar_constraint m e) qa.evar_constraints; *)
  Hashtbl.iter (fun e () -> B.declare_initial_expr m e) qa.initial_exprs

(* Once created, supports interactions satisfying the following regex:
( declare_fun+; declare_rule+; declare_initial_expr+; ( minimize | prove ); reset )
and the close at the end is optional a no-op. *)
module RecompilationBackend : BACKEND = struct

  let declare_highcost t r =
    assert false
  let declare_requires_term t r =
    assert false
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
      ctor_buf : Buffer.t;
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
Buffer.add_string buf recompilation_proof_file_path;
Buffer.add_string buf {|"
}

define_language! {
  pub enum CoqSimpleLanguage {
|}
end;
    let lemma_arity_buf = Buffer.create 1000 in
    let is_eq_buf = Buffer.create 1000 in
    let ctor_buf = Buffer.create 1000 in
    { buf; ctor_buf; lemma_arity_buf; is_eq_buf; state = SDeclaringFuns; }

  let declare_fun t fname fn_m=
    match t.state with
    | SDeclaringFuns ->
       Buffer.add_string t.buf
          (Printf.sprintf "    \"%s\" = %s([Id; %d]),\n" fname (make_rust_valid fname) fn_m.arity);
       Buffer.add_string t.ctor_buf
          (Printf.sprintf "    (\"%s\", (%n,%b)),\n" fname fn_m.arity fn_m.is_nonprop_ctor)
    | _ -> failwith "invalid state machine transition"

  let declare_rule t rule =
    (match t.state with
     | SDeclaringFuns ->
        t.state <- SDeclaringRules;
begin
Buffer.add_string t.buf {|  }
}

pub fn symbol_metadata(name : &str) -> Option<(usize,bool)> {
  let v = vec![
|};
Buffer.add_buffer t.buf t.ctor_buf;
Buffer.add_string t.buf {|  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
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
    Buffer.add_string t.lemma_arity_buf "\", ";
    let arity = List.length rule.quantifiers + List.length rule.sideconditions in
    Buffer.add_string t.lemma_arity_buf (string_of_int arity);
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
pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>, Ffn) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {
  let es = vec![
|}
end
     | SDeclaringInitialExprs -> ()
     | _ -> failwith "invalid state machine transition");
    Buffer.add_string t.buf {|    "|};
    Sexp.to_buffer ~buf:t.buf e;
    Buffer.add_string t.buf "\",\n"

  (* let declare_evar_constraint t e = assert false *)

  let minimize t e ffn_limit =
    (match t.state with
     | SDeclaringInitialExprs -> ()
     | _ -> failwith "invalid state machine transition");
    Buffer.add_string t.buf "  ];\n";
    Buffer.add_string t.buf "  let st : &str = \"";
    Sexp.to_buffer ~buf:t.buf e;
    Buffer.add_string t.buf "\";\n";
    Buffer.add_string t.buf "  f_simplify(st, es, ";
    Buffer.add_string t.buf (string_of_int ffn_limit);
    Buffer.add_string t.buf ");\n";
    Buffer.add_string t.buf "}\n";
    let oc = open_out rust_rules_path in
    Buffer.output_buffer oc t.buf;
    close_out oc;
    if log_misc_tracing() then Printf.printf "Wrote Rust code to %s\n" rust_rules_path else ();
    flush stdout;
    let cargo_command = "cd \"" ^ egg_repo_path ^ "\" && time cargo run --release --bin coq" in
    let status = Sys.command cargo_command in
    if log_misc_tracing() then Printf.printf "Command '%s' returned exit status %d\n" cargo_command status else ();
    if status != 0 then failwith "invoking rust failed"
    else t.state <- SDone;
    let pf = proof_file_to_proof recompilation_proof_file_path in
    pf

  let search_evars t e ffn_limit = assert false

  let prove t a = failwith "not supported yet"

  let reset t =
    t.state <- SDeclaringFuns;
    Buffer.clear t.buf;
    Buffer.clear t.lemma_arity_buf;
    Buffer.clear t.is_eq_buf

  let close t = ()

end


let get_backend () : (module BACKEND) =
  let name = get_backend_name () in
  match name with
  | "FileBasedEggBackend" -> (module FileBasedEggBackend)
  | "FileBasedSmtBackend" -> (module FileBasedSmtBackend)
  | "RecompilationBackend" -> (module RecompilationBackend)
  | _ -> failwith ("no backend named " ^ name)

let parse_constr_expr s =
  Pcoq.parse_string Pcoq.Constr.constr
    (* to avoid clashes of our names with SMT-defined names (eg and, not, true,
       we prefix them with &, and need to undo that here *)
    (Str.global_replace (Str.regexp "!") "" (Str.global_replace (Str.regexp "&") "" s))

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



let register_metadata metadata f n =
  match Hashtbl.find_opt metadata f with
  | Some m -> if n = m then () else failwith (f ^ " appears with different arities or different nature of being a constructor")
  | None -> Hashtbl.add metadata f n

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
let ind_to_str env i =
    let r = Names.GlobRef.IndRef i in
    implicits_prefix r ^ Pp.string_of_ppcmds (Printer.pr_inductive env i)

let const_to_str env c =
  let r = Names.GlobRef.ConstRef c in
  implicits_prefix r ^ Pp.string_of_ppcmds (Printer.pr_constant env c)

let ctor_to_str env c =
  let r = Names.GlobRef.ConstructRef c in
  implicits_prefix r ^ Pp.string_of_ppcmds (Printer.pr_constructor env c)

let rec process_expr  (handle_evar : bool) (is_type : bool) env sigma fn_metadatas e = 
  let ind_to_str i =
    ind_to_str env i in
  let const_to_str c =
    const_to_str env c in
  let ctor_to_str c =
    ctor_to_str env c in
  
  let sort_to_str s = Pp.string_of_ppcmds
                        (Printer.pr_sort sigma (EConstr.ESorts.kind sigma s)) in
  let evar_to_str i =
    let r = Evar.repr i in
    "?X" ^string_of_int r in
  (* Note: arity is determined by usage, not by type, because some function (eg sep)
     might always be used partially applied (we require the same arity at all usages) *)
  let process_atom show_types e arity =
    let name, is_nonprop_ctor = match EConstr.kind sigma e with
      | Constr.Rel i -> 
          let rel_decl = Environ.lookup_rel i env in 
          let n = (match rel_decl with 
              | Context.Rel.Declaration.LocalAssum(n, t) -> 
                  binder_name_to_string n
              | Context.Rel.Declaration.LocalDef(_,_,_) -> assert false) in
          ("?" ^ n, false)
      | Constr.Var id -> (Names.Id.to_string id, false)
      | Constr.Ind (i, univs) -> (ind_to_str i, false)
      | Constr.Const (c, univs) -> (const_to_str c, false)
      | Constr.Construct (ctor, univs) ->
        (* TODO thread sigma properly *)
        (* This is false, likely *)
         let sigma, tp = Typing.type_of env sigma e in
         (ctor_to_str ctor, not (Termops.is_Prop sigma tp))
      | Constr.Sort s -> (sort_to_str s, false)
      | Constr.Evar (key, _evar_cstrs) -> 
        if handle_evar then 
          (evar_to_str key, false)
        else raise Unsupported
      | _ -> 
        (*  *)
        let unk = Pp.string_of_ppcmds (Printer.pr_econstr_env env  sigma e) in 
        if log_misc_tracing() then Printf.printf "Unsupported Atom %s\n" unk else ();
        flush stdout;
        raise Unsupported in
    if String.starts_with ~prefix:"?" name then
      (
      let sigma, tp = Typing.type_of env sigma e in
      if not show_types || Termops.is_Set sigma tp || Termops.is_Type sigma tp then 
        Sexp.Atom name
      else
        let sigma, tp = Typing.type_of env sigma e in
        Sexp.List [Sexp.Atom "annot"; Sexp.Atom name; 
                  process_expr handle_evar true env sigma fn_metadatas tp;
                  Sexp.Atom "0"]) (* TODO replace by appropriate ffn? *)
    else (
      let n = (if is_nonprop_ctor then "!" else "&") ^ name in (* to avoid clashes with predefined names from smtlib *)
      register_metadata fn_metadatas n {arity; is_nonprop_ctor};
      let sigma, tp = Typing.type_of env sigma e in
      if show_types && arity = 0 && not (Termops.is_Set sigma tp) && not (Termops.is_Type sigma tp) then 
        Sexp.List [ Sexp.Atom "annot"; Sexp.Atom n; process_expr handle_evar true env sigma fn_metadatas tp;
                    Sexp.Atom "0"] (* TODO *)
       else
            Sexp.Atom n) 
                                    in
      (* Sexp.Atom "annot" (Sexp.List [Sexp.Atom n; type_to_sexp tp]) in *)
  try
    (* treat Z literals as uninterpreted, so that they can have the same smtlib type U
       as everything else *)
    let sigma, tp = Typing.type_of env sigma e in
    let z = "!" ^ Stdlib.string_of_int (z_to_int sigma e) in
    register_metadata fn_metadatas z { arity=0; is_nonprop_ctor = true};
    (if is_type then 
      Sexp.Atom z
      else
         Sexp.List ([Sexp.Atom "annot"; Sexp.Atom z; 
                    process_expr handle_evar true env sigma fn_metadatas tp;
                    Sexp.Atom "0"])) (* TODO *)
  with NotACoqNumber ->
        let sigma, tp = Typing.type_of env sigma e in
        match EConstr.kind sigma e with
        | Constr.App (f, args) ->
            if is_type || Termops.is_Set sigma tp || Termops.is_Type sigma tp  then 
            Sexp.List (process_atom false f (Array.length args) ::
                        List.map (process_expr handle_evar is_type env sigma fn_metadatas)
                          (Array.to_list args))
            else  
             Sexp.List ([Sexp.Atom "annot"; Sexp.List (process_atom false f (Array.length args) ::
                        List.map (process_expr handle_evar is_type env sigma fn_metadatas )
                          (Array.to_list args)); 
                          (* No evar in types? *)
                        process_expr handle_evar true env sigma fn_metadatas tp;
                        Sexp.Atom "0"]) (* TODO *)
        | Constr.Prod (b, tp, body) ->
          if EConstr.Vars.noccurn sigma 1 body then
            Sexp.List ([Sexp.Atom "arrow"; 
            process_expr handle_evar true env sigma fn_metadatas tp;
            let env = EConstr.push_rel 
                      (Context.Rel.Declaration.LocalAssum (Context.make_annot Names.Anonymous Sorts.Relevant, tp))
                      env in
            process_expr handle_evar true env sigma fn_metadatas body;
            ])
         else raise Unsupported (* dependent types are not accepted for now *)
        | _ -> 
            if is_type then 
                process_atom false e 0
          else process_atom true e 0
        

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

let register_expr qa e = Hashtbl.replace qa.initial_exprs e () 

let rec biggest_closed_subexprs' (e : Sexp.t) : Sexp.t list option =
      (* None means that the current entire e is closed *)
      (* Some l means that the term is not closed, but has the closed subterms contained in the list *)
      match e with
      | Sexp.Atom(s) ->
        if (String.starts_with ~prefix:"?" s) then Some([]) else None
      | Sexp.List(l)->
           let r = List.map biggest_closed_subexprs' l in
           let is_none = List.for_all (fun x -> x = None) r in
           if is_none then
            None
           else
            Some (List.fold_left
                    (fun acc (el, maybe_subterms) ->
                      match maybe_subterms with
                      | None -> acc
                      | Some(subterms) -> acc @ subterms)
                    []
                    (List.combine l r))
let biggest_closed_subexprs (e : Sexp.t) : Sexp.t list =
      match biggest_closed_subexprs' e with
      | Some(l) -> l
      | None -> [e] 
(* hyp:      Context.Named.Declaration (LocalAssum or LocalDef) *)
let eggify_hyp env sigma (qa: query_accumulator) hyp =

  let to_assertion env t =
    let e1, e2, res = match destruct_eq sigma t with
      | Some (_, lhs, rhs) ->
         let lhs' = process_expr false false env sigma qa.declarations lhs in
         let rhs' = process_expr false false env sigma qa.declarations rhs in
         (lhs', rhs', AEq (lhs', rhs'))
      | None ->
         let lhs' = true_typed in
         let rhs' = process_expr false false env sigma qa.declarations t in
         (lhs', rhs', AProp rhs') in
  (* Register all the quantifier frees subexprs of e1 and e2 *)
    (*List.iter (fun s -> Printf.printf "Closedsubexpr %s\n" (Sexp.to_string_hum s)) (biggest_closed_subexprs e1);*)
    List.iter (register_expr qa) (biggest_closed_subexprs e1);
    List.iter (register_expr qa) (biggest_closed_subexprs e2);
    res in

  let rec process_impls name env sideconditions manual_triggers t =
    match destruct_trigger sigma t with
    | Some (tr_exprs, body) ->
       let tr_sexprs = List.map (process_expr false false env sigma qa.declarations) tr_exprs in
       process_impls name env sideconditions (List.append manual_triggers tr_sexprs) body
    | None ->
      match EConstr.kind sigma t with
      | Constr.Prod (b, tp, body) ->
         if log_misc_tracing() then Printf.printf "Pass below impl\n" else ();
         if EConstr.Vars.noccurn sigma 1 body then
           let side = to_assertion env tp in
           let env = EConstr.push_rel 
                        (* Maybe we can just push the binder b directly, instead of
                        making an anonymous binder? *) 
                        (Context.Rel.Declaration.LocalAssum (Context.make_annot Names.Anonymous Sorts.Relevant, tp))
                        env in
           process_impls name env (side :: sideconditions) manual_triggers body
         else raise Unsupported (* foralls after impls are not supported *)
      | _ -> 
        let quant_names = Environ.fold_rel_context 
              (fun _ rel_decl acc -> match rel_decl with 
                                     | Context.Rel.Declaration.LocalAssum(n, t) -> 
                                        (match Context.binder_name n with 
                                        | Names.Anonymous -> acc
                                        | Names.Name(t) -> (binder_name_to_string n)::acc)
                                     | Context.Rel.Declaration.LocalDef(_,_,_) -> acc)
              env ~init:([]) in
        if log_misc_tracing() then Printf.printf "Add rule" else ();
        Queue.push {
                 rulename = name;
                 quantifiers = List.rev quant_names;
                 sideconditions = List.rev sideconditions;
                 conclusion = to_assertion env t;
                 triggers = manual_triggers;
               } qa.rules in

  let rec process_foralls name env t =
    match EConstr.kind sigma t with
    | Constr.Prod (b, tp, body) ->
       if EConstr.Vars.noccurn sigma 1 body then
         ( if log_misc_tracing() then Printf.printf "Pass below false forall\n" else ();
         process_impls name env [] [] t)
       else
         (if log_misc_tracing() then Printf.printf "Pass below forall\n" else ();
         let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (b, tp)) env in
         process_foralls name env body)
    | _ -> process_impls name env [] [] t in

  let open Context in
  let open Named.Declaration in
  match hyp with
  | LocalAssum (id, t) ->
    begin
      let name = Names.Id.to_string id.binder_name in
      (*Printf.printf "Start processing %s\n" name;*)
      try
        let sigma, tp = Typing.type_of env sigma (EConstr.of_constr t) in
        if Termops.is_Prop sigma tp then
          process_foralls name env (EConstr.of_constr t)
        else raise Unsupported
      with
        Unsupported -> if log_ignored_hyps () then 
          Printf.printf "Dropped %s\n" name
    end
  | LocalDef (id, t, _tp) -> begin
      let rawname = Names.Id.to_string id.binder_name in
      try
        let name = "&" ^ rawname in
        register_metadata qa.declarations name {arity = 0; is_nonprop_ctor= false};
        let lhs = Sexp.Atom name in
        let rhs = process_expr false false env sigma qa.declarations (EConstr.of_constr t) in
        register_expr qa lhs;
        register_expr qa rhs;
        Queue.push { rulename = rawname ^ "$def";
                     quantifiers = [];
                     sideconditions = [];
                     conclusion = AEq (lhs, rhs);
                     triggers = [] } qa.rules

      with
        Unsupported -> if log_ignored_hyps () then 
          Printf.printf "Dropped %s\n" rawname
    end


(* does not reconstruct the proof at the moment *)
let egg_cvc5 () =
  Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Goal.env gl in
    let hyps = Environ.named_context (Goal.env gl) in
    let qa = empty_query_accumulator () in
    List.iter (fun hyp -> eggify_hyp env sigma qa hyp) (List.rev hyps);
    let g = process_expr false false env sigma qa.declarations (Goal.concl gl) in
    let b = FileBasedSmtBackend.create () in
    apply_query_accumulator qa (module FileBasedSmtBackend) b;
    let _pf = FileBasedSmtBackend.prove b (AProp g) in
    tclUNIT ()
    end

let egg_simpl_goal ffn_limit (id_simpl : Names.GlobRef.t option) terms =
  Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Goal.env gl in
    let hyps = Environ.named_context (Goal.env gl) in

    let qa = empty_query_accumulator () in
    
    List.iter (fun hyp -> eggify_hyp env sigma qa hyp) (List.rev hyps);
    if log_misc_tracing() then print_endline("Went through hypothesis") else ();
    flush stdout;
    let g = process_expr false false env sigma qa.declarations (Goal.concl gl) in
    if log_misc_tracing() then print_endline("Processed goal") else ();
    flush stdout;
    let (module B) = get_backend () in
    
    (* File created here *)
    let b = B.create () in
    begin 
      let open Names.GlobRef in
      match id_simpl with 
      | Some (VarRef id) ->
        let s = "&" ^ Pp.string_of_ppcmds (Names.Id.print id) in
        B.declare_highcost b s
      | Some (IndRef ind) ->
        B.declare_highcost b ( "&" ^ ind_to_str env ind)
      | Some (ConstructRef ctr) ->
        B.declare_highcost b ( "!" ^ ctor_to_str env ctr )
      | Some (ConstRef cst) ->
        B.declare_highcost b ( "&" ^const_to_str env cst )
      | None -> ()
    end;
    begin
      let rec aux l = match l with 
            | h::t -> 
                let sexp = process_expr false false env sigma qa.declarations h in
                B.declare_requires_term b sexp; aux t
            | [] -> () in
      aux terms
    end;
    if log_misc_tracing() then print_endline("So far so good") else ();
    flush stdout;
    apply_query_accumulator qa (module B) b;
    let pf = B.minimize b g ffn_limit in

    (match pf with
    | PSteps(pf_steps) ->
      let reversed_pf = List.rev pf_steps in
      let composed_pf = compose_constr_expr_proofs (List.map parse_constr_expr reversed_pf) in
      if log_proofs () then (
        print_endline "Composed proof:";
        print_endline (print_constr_expr env sigma composed_pf);
      ) else ();
      Refine.refine ~typecheck:true (fun sigma ->
          let (sigma, constr_pf) = Constrintern.interp_constr_evars env sigma composed_pf in
          if log_proofs () then (
            Feedback.msg_notice
              Pp.(str"Proof: " ++ Printer.pr_econstr_env env sigma constr_pf);
          ) else ();
          (sigma, constr_pf))
    | PContradiction(ctr, pf_steps) ->
       let reversed_pf = List.rev pf_steps in
       let composed_pf = compose_constr_expr_proofs (List.map parse_constr_expr reversed_pf) in
       let ctr_coq = parse_constr_expr ctr in
       if log_proofs () then (
         print_endline "Contradiction proof:";
         print_endline ctr;
         print_endline "Composed proof of contradiction:";
         print_endline (print_constr_expr env sigma composed_pf);
       ) else ();
       let tac_proof_equal = Refine.refine ~typecheck:true (fun sigma ->
          let (sigma, constr_pf) = Constrintern.interp_constr_evars env sigma composed_pf in
          if log_proofs () then (
            Feedback.msg_notice
              Pp.(str"Proof: " ++ Printer.pr_econstr_env env sigma constr_pf);
          ) else ();
          (sigma, constr_pf)) in
       let (_sigma, t_ctr) = (Constrintern.interp_constr_evars env sigma ctr_coq) in
       tclBIND (Tacticals.pf_constr_of_global (Coqlib.(lib_ref "core.False.type")))
         (fun coqfalse ->
           Tacticals.tclTHENLIST
             [ Tactics.elim_type coqfalse;
               Tacticals.tclTHENFIRST
                 (Tactics.assert_as true None None t_ctr) tac_proof_equal ]))
    end

(* Borrowed from ltac/evar_tactics.ml because it was not public *)

let goal_subexpr env sigma qa t =
    let e1, e2= match destruct_eq sigma t with
      | Some (_, lhs, rhs) ->
         let lhs' = process_expr true false env sigma qa.declarations lhs in
         let rhs' = process_expr true false env sigma qa.declarations rhs in
         (lhs', rhs')
      | None ->
         let lhs' = true_typed in
         let rhs' = process_expr true false env sigma qa.declarations t in
         (lhs', rhs') in
  (* Register all the quantifier frees subexprs of e1 and e2 *)

    List.iter (register_expr qa) (biggest_closed_subexprs e1);
    List.iter (register_expr qa) (biggest_closed_subexprs e2)


let egg_search_evars ffn_limit =
  Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Goal.env gl in
    let hyps = Environ.named_context (Goal.env gl) in

    let qa = empty_query_accumulator () in
    (* Queue.push { rulename = "rm_annot";
                quantifiers = ["a"; "t"];
                sideconditions = [];
                conclusion = AEq (Sexp.List [Sexp.Atom "annot"; Sexp.Atom "?a"; Sexp.Atom "?t"], Sexp.Atom "?a");
                triggers = [] } qa.rules; *)
    (* We hope that there is nohypothesis with evars, otherwise we are in trouble *)

    if log_misc_tracing() then print_endline("Start hyps for evar query") else ();
    flush stdout;
    List.iter (fun hyp -> eggify_hyp env sigma qa hyp) (List.rev hyps);
    if log_misc_tracing() then print_endline("Start goal for evar") else ();
    flush stdout;
    let g = process_expr true false env sigma qa.declarations (Goal.concl gl) in
    goal_subexpr env sigma qa (Goal.concl gl);
    if log_misc_tracing() then print_endline("goal processed, added to init expr") else ();
    flush stdout;


    (* For now we don't have hypothesis that contains evars, to avoid compiler complaining about unused evar_constraints,
       we put something dummy there. This will be removed replaced by code that handle hypothesis with evars. *)
    Hashtbl.replace qa.evar_constraints g ();

    let (module B) = get_backend () in

    let b = B.create () in

    apply_query_accumulator qa (module B) b;

    if log_misc_tracing() then print_endline("Search evar") else ();
    flush stdout;
    List.iter (fun hyp -> eggify_hyp env sigma qa hyp) (List.rev hyps);
    let pf = B.search_evars b g ffn_limit in
    (if pf = [] then failwith "No evar found or instantiated" 
    else ());
    let evar_proposition_to_str = List.map (fun (key, c_string) -> string_of_int key ^ " := " ^ c_string ) in 
    let spf = String.concat "\nAlternative:\n" (List.map (String.concat "\n") (List.map evar_proposition_to_str pf)) in 
      (* there is more than one, so just return them to the user *)
     Feedback.msg_notice
      Pp.(str"Possibilities (First one hardselected): \n" ++ str spf);
    (* Pf is a list of lists *)
    match pf with 
    | subst::_q -> 
        let constrify = List.map (fun (evk, c_string) -> (evk, parse_constr_expr c_string)) subst in 
        let newsigma = List.fold_left (fun sigma (evk,c_string) -> 
            let (sigma, ecstr) = Constrintern.interp_constr_evars env sigma c_string  in
            Evd.define (Evar.unsafe_of_int evk) ecstr sigma) sigma constrify in 
        Proofview.Unsafe.tclEVARS newsigma 
      (* There is a single possible instantiation of the evar present, we are good to do it *)
    | _ -> 
     Proofview.tclUNIT ()
   
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
