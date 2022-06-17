val two_lambda_pattern :
    Evd.evar_map -> EConstr.t -> EConstr.t * EConstr.t * EConstr.t
val pack_tactic : Names.Id.t -> unit Proofview.tactic
val egg_simpl_goal : string -> unit Proofview.tactic
