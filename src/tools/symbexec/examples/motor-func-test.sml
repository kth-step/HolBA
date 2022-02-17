open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_auxTheory;

open bin_motor_funcTheory;

(*
val _ = print_term (concl bin_motor_func_thm);
*)

val bprog = List.nth((snd o strip_comb o concl) bin_motor_func_thm, 3);
(*
(hd o fst o listSyntax.dest_list o snd o dest_comb) bprog
*)
val bprog_def = Define `
    bprog = ^(bprog)
`;
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb08w))``;
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb46w))``];
(*
val birs_stop_lbls = [``<|bpc_label := BL_Address (Imm32 0xb08w); bpc_index := 7|>``];
*)


(* ---------------------------------------------------------------------------------------------------------------- *)
(* TODO: the following is copied from transfer-test script (MODIFIED FOR TEMP VARS) *)
(* ---------------------------------------------------------------------------------------------------------------- *)
val m0_mod_vars_def = Define `
    m0_mod_vars = APPEND (bmr_vars (m0_mod_bmr (T,T))) (bmr_temp_vars (m0_mod_bmr (T,T)))
`;

val m0_mod_vars_thm = store_thm(
   "m0_mod_vars_thm", ``
!ef sel.
  m0_mod_vars = APPEND (bmr_vars (m0_mod_bmr (ef,sel))) (bmr_temp_vars (m0_mod_bmr (ef,sel)))
``,
  METIS_TAC [m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL, bir_lifting_machinesTheory.m0_mod_bmr_temp_vars_EVAL]
);

val birenvtyl_def = Define `
    birenvtyl = MAP BVarToPair m0_mod_vars
`;
(*    birenvtyl = [("R7", BType_Imm Bit32); ("SP_process", BType_Imm Bit32); ("countw", BType_Imm Bit64)]*)
(*
bir_lifting_machinesTheory.m0_mod_REGS_lifted_imms_LIST_def
m0_mod_REGS_lifted_imms_LIST
m0_mod_lifted_mem
bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL
*)
val birenvtyl_EVAL_thm = save_thm(
   "birenvtyl_EVAL_thm",
  (REWRITE_CONV [birenvtyl_def, m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL, bir_lifting_machinesTheory.m0_mod_bmr_temp_vars_EVAL] THENC EVAL) ``birenvtyl``
);
(* ---------------------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------------------- *)


(* TODO: add a sanity check here that all the variables of the program are included in birenvtyl! *)


val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
|>``;
(* ........................... *)

val birs_rule_STEP_thm = birs_rule_STEP_prog_fun bprog_tm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_fun_spec = birs_rule_STEP_tryassert_fun birs_rule_STEP_thm bprog_tm;
(* now the composition *)
val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
(* ........................... *)


val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
(* ........................... *)

(*
val tm = ``<|bsst_pc := a;
             bsst_environ :=b;
             bsst_status := BST_AssertionViolated;
             bsst_pcond := c|>``;
val tm = ``<|bsst_pc := a;
             bsst_environ :=b;
             bsst_status := BST_Running;
             bsst_pcond := c|>``;
*)
fun birs_get_pc tm =
  ((snd o dest_eq o concl o EVAL) ``(^tm).bsst_pc``);
fun birs_is_running tm =
  identical ((snd o dest_eq o concl o EVAL) ``(^tm).bsst_status``) ``BST_Running``;

(*
val STEP_fun_spec = birs_rule_STEP_fun_spec;
val SEQ_fun_spec = birs_rule_SEQ_fun_spec;

val symbex_A_thm = single_step_A_thm;
val stop_lbls = birs_stop_lbls;
*)
fun exec_until (STEP_fun_spec, SEQ_fun_spec) symbex_A_thm stop_lbls =
  let
    val _ = print ("\n");
    val (_, _, Pi_A_tm) = (symb_sound_struct_get_sysLPi_fun o concl) symbex_A_thm;

    fun is_executable st =
      birs_is_running st andalso (not (List.exists (identical (birs_get_pc st)) stop_lbls));

    val birs_states_mid = symb_sound_struct_Pi_to_birstatelist_fun Pi_A_tm;
    val birs_states_mid_running = List.filter birs_is_running birs_states_mid;
    val birs_states_mid_executable = List.filter is_executable birs_states_mid;
    val _ = print ("- have " ^ (Int.toString (length birs_states_mid)) ^ " states\n");
    val _ = print ("    (" ^ (Int.toString (length birs_states_mid_running)) ^ " running)\n");
    val _ = print ("    (" ^ (Int.toString (length birs_states_mid_executable)) ^ " executable)\n");
  in
    (* stop condition (no more running states, or reached the stop_lbls) *)
    if List.length birs_states_mid_executable = 0 then
      (print "no executable states left, terminating";
       symbex_A_thm)
    else
      (* continue with a second step and then recursive call *)
      let
        (* select one state that did not reach the end yet *)
        val birs_state_mid = hd birs_states_mid_executable;
        val _ = print ("Executing one more step @(" ^ (term_to_string (birs_get_pc birs_state_mid)) ^ ")\n");
        val single_step_B_thm = STEP_fun_spec birs_state_mid;

        (* compose together *)
        val bprog_composed_thm = SEQ_fun_spec symbex_A_thm single_step_B_thm;
      in
        (* recursion *)
        exec_until (STEP_fun_spec, SEQ_fun_spec) bprog_composed_thm stop_lbls
      end
  end;
(* ........................... *)


val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;

val _ = (print_term o concl) result;
