val egg_simpl_goal : string -> unit Proofview.tactic

(* uconstr = Ltac_pretype.closed_glob_constr with holes = CHole,
   open_constr = EConstr.t with holes being evars *)
val inspect : EConstr.t -> unit Proofview.tactic
