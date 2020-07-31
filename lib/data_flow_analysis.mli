
include module type of struct
  include Data_flow_analysis_intf.S
end

(** Functor to build a solver for a data-flow problem. *)
module Make_solver (P: Problem) : sig
  val solve : P.t -> (P.S.t * P.S.t) P.Node.Map.t
end

(** Functor to build a solver for a kill-gen problem. *)
module Make_kill_gen_solver (P: KillGenProblem) : sig
  val solve : P.t -> (P.K.S.t * P.K.S.t) P.Node.Map.t
end

(** Functor to build a forward solver on the cfg. *)
module Make_forward_cfg_solver (P: CfgKillGenProblem) : sig
  val solve : P.t -> (P.K.S.t * P.K.S.t) Inst_id.Map.t
end

(** Functor to build a backward solver on the cfg. *)
module Make_backward_cfg_solver (P: CfgKillGenProblem) : sig
  val solve : P.t -> (P.K.S.t * P.K.S.t) Inst_id.Map.t
end

(** Functor to build a backward solver on the cfg. *)
module Make_backward_cfg_inst_solver (P: CfgKillGenInstProblem) : sig
  val solve : P.t -> (P.K.S.t * P.K.S.t) Inst_id.Map.t
end
