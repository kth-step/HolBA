structure nic_stateLib :> nic_stateLib =
struct

  open HolKernel Parse boolLib bossLib;
  open bslSyntax;
  open pretty_exnLib;
  open nic_helpersLib;

  val ERR = mk_HOL_ERR "nic_stateLib";
  val wrap_exn = Feedback.wrap_exn "nic_stateLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("nic_stateLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "nic_stateLib" level_log;

  (* End of prelude
   ****************************************************************************)

  val init_state = gen_state_helpers "init" [
      ("it_power_on",           (1, false)),
      ("it_reset",              (2, true)),
      ("it_initialize_hdp_cp",  (3, false)),
      ("it_initialized",        (4, false))
    ]

  val tx_state = gen_state_helpers "tx" [
      ("tx1_idle",                            (1, false)),
      ("tx2_fetch_next_bd",                   (2, true)),
      ("tx3_issue_next_memory_read_request",  (3, true)),
      ("tx4_process_memory_read_reply",       (4, false)),
      ("tx5_post_process",                    (5, true)),
      ("tx6_clear_owner_and_hdp",             (6, true)),
      ("tx7_write_cp",                        (7, true))
    ]

  val td_state = gen_state_helpers "td" [
      ("td_idle",                 (1, false)),
      ("td_set_eoq",              (2, false)),
      ("td_set_td",               (3, false)),
      ("td_clear_owner_and_hdp",  (4, false)),
      ("td_write_cp",             (5, false))
    ]

end (* nic_stateLib *)
