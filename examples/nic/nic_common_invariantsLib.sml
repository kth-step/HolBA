structure nic_common_invariantsLib :> nic_common_invariantsLib =
struct

  open HolKernel Parse boolLib bossLib;
  open bslSyntax;
  open pretty_exnLib;
  open nic_helpersLib nic_stateLib;

  val ERR = mk_HOL_ERR "nic_common_invariantsLib";
  val wrap_exn = Feedback.wrap_exn "nic_common_invariantsLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("nic_common_invariantsLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "nic_common_invariantsLib" level_log;

  (* End of prelude
   ****************************************************************************)

  (*****************************************************************************
   *
   *)

  val invariant_nic_not_dead = beq ((bden o bvarimm1) "nic_dead", bfalse)


end (* nic_common_invariantsLib *)
