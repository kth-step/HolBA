open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_auxTheory;

open bin_motor_funcTheory;

(*
val _ = print_term (concl bin_motor_func_thm);
*)

val bprog = List.nth((snd o strip_comb o concl) bin_motor_func_thm, 3);
val bprog_def = Define `
    bprog = ^(bprog)
`;
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb08w))``;
val birs_stop_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb46w))``;
val birs_stop_lbl = ``<|bpc_label := BL_Address (Imm32 0xb08w); bpc_index := 1|>``;

(* TODO: *)
val birenvtyl_def = Define `
    birenvtyl = [("R7", BType_Imm Bit32); ("SP_process", BType_Imm Bit32); ("countw", BType_Imm Bit64)]
`;

val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_Const (Imm1 1w)
|>``;
(* ........................... *)

val birs_rule_STEP_thm = birs_rule_STEP_prog_fun bprog_tm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_fun_spec = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm;
(* ........................... *)


val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
(* ........................... *)

(*
val step_A_thm = single_step_A_thm;
val STEP_fun_spec = birs_rule_STEP_fun_spec;
val stop_lbl = birs_stop_lbl;
*)
fun exec_until step_A_thm STEP_fun_spec stop_lbl =
  (* TODO: stop condition check *)
  let
    val (_, _, Pi_A_tm) = (symb_sound_struct_get_sysLPi_fun o concl) step_A_thm;

    (* continue with a second step *)
    val birs_states_mid = symb_sound_struct_Pi_to_birstatelist_fun Pi_A_tm;
    val birs_state_mid = List.nth(birs_states_mid,0);
    (* ........................... *)

    (* TODO: *)
    (*
    (* now the composition *)
    val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
    (* ........................... *)

    (* compose together *)
    val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
    val bprog_composed_thm = birs_rule_SEQ_fun_spec single_step_A_thm single_step_B_thm;
    *)
  in
    (* TODO: recursion *)
    step_A_thm
  end;
(* ........................... *)


val result = exec_until single_step_A_thm birs_rule_STEP_fun_spec birs_stop_lbl;
