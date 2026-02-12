structure init_automatonLib :> init_automatonLib =
struct

  open HolKernel Parse boolLib bossLib;
  open bslSyntax;
  open pretty_exnLib;
  open nic_helpersLib nic_stateLib;

  val ERR = mk_HOL_ERR "init_automatonLib";
  val wrap_exn = Feedback.wrap_exn "init_automatonLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("init_automatonLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "init_automatonLib" level_log;

  (* End of prelude
   ****************************************************************************)

  (*****************************************************************************
   * Lemma generators
   *)

(*  fun gen_NIC_DELTA_PRESERVES_IT_def =*)
(*    bandl [*)
(*      beq ((bden o bvarimm1) "nic_dead_0", (bden o bvarimm1) "nic_dead")*)
(*    ]*)

(*  val NIC_DELTA_PRESERVES_IT_def = Define `*)
(*    NIC_DELTA_PRESERVES_IT (nic_delta : nic_delta_type) =*)
(*    !nic. (nic_delta nic).it = nic.it`;*)

  (*****************************************************************************
   * Initialisation automaton
   *)

  val bstateval = #bstateval init_state

  val init_blocks =
    ([bjmp_block ("init_entry", "init_try_s1")]

    (* Autonomous transition jump *)
  @ bstate_cases ("nic_init_state", "init_unknown_state", bstateval) [
    ("init_try_s1", "it_power_on",          "init_no_autonomous_step_state"),
    ("init_try_s2", "it_reset",             "init_s2_entry"),
    ("init_try_s3", "it_initialize_hdp_cp", "init_no_autonomous_step_state"),
    ("init_try_s4", "it_initialized",       "init_no_autonomous_step_state")
  ]

  @ [
    bjmp_block ("init_s2_entry", "init_s2_set_regs"),
    (blabel_str "init_s2_set_regs", [
      bassign (bvarimm1 "nic_regs_CPDMA_SOFT_RESET", bfalse),
      bassign (bvarstate "nic_init_state", (bstateval) "it_initialize_hdp_cp")
    ], bjmplabel_str "init_s2_epilogue"),
    bjmp_block ("init_s2_epilogue", "init_s2_end"),
    bjmp_block ("init_s2_end", "init_epilogue")
  ]

  @ [
    block_nic_die ("init_no_autonomous_step_state", "init_epilogue"),
    block_nic_die ("init_unknown_state", "init_epilogue"),
    bjmp_block ("init_epilogue", "init_end"),
    bjmp_block ("init_end", "end")
  ])
    handle e => raise pp_exn e;
  val init_program = bprog_list alpha init_blocks;

end (* init_automatonLib *)
