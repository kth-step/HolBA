structure tx_automatonLib :> tx_automatonLib =
struct

  open HolKernel Parse boolLib bossLib;
  open bslSyntax;
  open pretty_exnLib;
  open nic_helpersLib nic_stateLib;
  open nic_common_invariantsLib;

  val ERR = mk_HOL_ERR "tx_automatonLib";
  val wrap_exn = Feedback.wrap_exn "tx_automatonLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("tx_automatonLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "tx_automatonLib" level_log;

  (* End of prelude
   ****************************************************************************)

  (*****************************************************************************
   * Transmission automaton
   *)

  val bstateval_init = #bstateval init_state
  val bstateval_tx = #bstateval tx_state
  val bstateval_td = #bstateval td_state

  val tx_blocks =
    ([bjmp_block ("tx_entry", "tx_try_s1")]

    (* Autonomous transition jump *)
    @ bstate_cases ("nic_tx_state", "tx_unknown_state", bstateval_tx) [
      ("tx_try_s1", "tx1_idle",                           "tx_no_autonomous_step_state"),
      ("tx_try_s2", "tx2_fetch_next_bd",                  "tx_s2_entry"),
      ("tx_try_s3", "tx3_issue_next_memory_read_request", "tx_s3_entry"),
      ("tx_try_s4", "tx4_process_memory_read_reply",      "tx_no_autonomous_step_state"),
      ("tx_try_s5", "tx5_post_process",                   "tx_s5_entry"),
      ("tx_try_s6", "tx6_clear_owner_and_hdp",            "tx_s6_entry"),
      ("tx_try_s7", "tx7_write_cp",                       "tx_s7_entry")
    ]

    @ [
      bjmp_block ("tx_s2_entry", "tx_s2_epilogue"),
      bjmp_block ("tx_s2_epilogue", "tx_s2_end"),
      bjmp_block ("tx_s2_end", "tx_epilogue")
    ]

    @ [
      bjmp_block ("tx_s3_entry", "tx_s3_epilogue"),
      bjmp_block ("tx_s3_epilogue", "tx_s3_end"),
      bjmp_block ("tx_s3_end", "tx_epilogue")
    ]

    @ [

      bjmp_block ("tx_s5_entry", "tx_s5_epilogue"),
      bjmp_block ("tx_s5_epilogue", "tx_s5_end"),
      bjmp_block ("tx_s5_end", "tx_epilogue")
    ]

    (* TX-6: Writes the physical address of the current buffer descriptor to
     * the TX0_CP register.
     *)
    @ [
      bjmp_block ("tx_s6_entry", "tx_s6_set_nic_regs_TX0_CP"),
      (blabel_str "tx_s6_set_nic_regs_TX0_CP", [
        bassign (bvarimm32 "nic_regs_TX0_CP", (bden o bvarimm32) "nic_tx_eop_bd_pa")

      ], bjmplabel_str "tx_s6_set_nic_interrupt"),
      (blabel_str "tx_s6_set_nic_interrupt", [
        bassign (bvarimm1 "nic_interrupt", bite ((bden o bvarimm1) "env_tx_assert_interrupt",
                                                 btrue, (bden o bvarimm1) "nic_interrupt"))
      ], bjmplabel_str "tx_s6_set_nic_tx_interrupt"),
      (blabel_str "tx_s6_set_nic_tx_interrupt", [
        bassign (bvarimm1 "nic_tx_interrupt", bite ((bden o bvarimm1) "env_tx_assert_interrupt",
                                                    btrue, (bden o bvarimm1) "nic_tx_interrupt"))
      ], bjmplabel_str "tx_s6_set_nic_tx_state"),
      (blabel_str "tx_s6_set_nic_tx_state", [
        bassign (bvarstate "nic_tx_state", bite (
          borl [
            beq ((bden o bvarimm32) "nic_tx_current_bd_pa", bconst32 0),
            beq ((bden o bvarimm32) "nic_init_state", bstateval_init "it_reset"),
            bneq ((bden o bvarimm32) "nic_td_state", bstateval_td "td_set_eoq")
          ],
          bstateval_tx "tx1_idle", bstateval_tx "tx2_fetch_next_bd"))
      ], bjmplabel_str "tx_s6_epilogue"),
      bjmp_block ("tx_s6_epilogue", "tx_s6_end"),
      bjmp_block ("tx_s6_end", "tx_epilogue")
    ]

    @ [
      bjmp_block ("tx_s7_entry", "tx_s7_epilogue"),
      bjmp_block ("tx_s7_epilogue", "tx_s7_end"),
      bjmp_block ("tx_s7_end", "tx_epilogue")
    ]

    @ [
      block_nic_die ("tx_no_autonomous_step_state", "tx_epilogue"),
      block_nic_die ("tx_unknown_state", "tx_epilogue"),
      bjmp_block ("tx_epilogue", "tx_end"),
      bjmp_block ("tx_end", "end")
    ])
      handle e => raise pp_exn e;
    val tx_program = bprog_list alpha tx_blocks;

end (* tx_automatonLib *)
