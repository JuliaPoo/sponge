val egg_simpl_goal : int(* far-fetched-ness limit *) -> unit Proofview.tactic
val egg_search_evars : int(* far-fetched-ness limit *) -> unit Proofview.tactic

val egg_cvc5 : unit -> unit Proofview.tactic

(* uconstr = Ltac_pretype.closed_glob_constr with holes = CHole,
   open_constr = EConstr.t with holes being evars *)
val inspect : EConstr.t -> unit Proofview.tactic
