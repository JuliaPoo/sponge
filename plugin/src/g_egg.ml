let __coq_plugin_name = "egg_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/g_egg.mlg"
 

open Ltac_plugin

open Construction_game

(* This one is necessary, to avoid message about missing wit_string *)
open Stdarg



let () = Vernacextend.vernac_extend ~command:"ShowTypeConstruction" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Test3_1", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 16 "src/g_egg.mlg"
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, s = Evd.new_sort_variable Evd.univ_rigid sigma in
    let new_type_2 = EConstr.mkSort s in
    let sigma, _ =
      Typing.type_of (Global.env()) (Evd.from_env (Global.env())) new_type_2 in
    Feedback.msg_notice
      (Printer.pr_econstr_env env sigma new_type_2) 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ShowOneConstruction" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Test3_2", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 27 "src/g_egg.mlg"
                     example_sort_app_lambda () 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "collapse_hyps" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("pack", Tacentries.TyIdent ("hypothesis", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyNil))), 
           (fun i ist -> 
# 32 "src/g_egg.mlg"
    Test_tactic.pack_tactic i 
           )))]

let () = Vernacextend.vernac_extend ~command:"TriggerClasses" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Test3_3", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_int), 
                                     Vernacextend.TyNil)), (let coqpp_body n
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 39 "src/g_egg.mlg"
                            example_classes n 
                                                                ) in fun n
                                                           ?loc ~atts ()
                                                           -> coqpp_body n
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"TriggerCanonical" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Test3_4", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_int), 
                                     Vernacextend.TyNil)), (let coqpp_body n
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 44 "src/g_egg.mlg"
                            example_canonical n 
                                                                ) in fun n
                                                           ?loc ~atts ()
                                                           -> coqpp_body n
                                                           (Attributes.unsupported_attributes atts)), None))]

