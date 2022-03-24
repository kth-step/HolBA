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
(hd o tl o fst o listSyntax.dest_list o snd o dest_comb) bprog

List.nth ((fst o listSyntax.dest_list o snd o dest_comb) bprog, 13)
*)
val bprog_def = Define `
    bprog = ^(bprog)
`;
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb08w))``;
(*
val birs_stop_lbls = [``<|bpc_label := BL_Address (Imm32 0xb08w); bpc_index := 7|>``];
*)
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb12w))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb20w))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb22w))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb2ew))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb46w))``];


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
val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
val birs_rule_STEP_fun_spec = (birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm o birs_rule_STEP_tryassert_fun birs_rule_STEP_thm bprog_tm);
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

datatype symbexec_tree_t =
  Symb_Node of (thm  * (symbexec_tree_t list));

fun reduce_tree SEQ_fun_spec (Symb_Node (symbex_A_thm, [])) = symbex_A_thm
  | reduce_tree SEQ_fun_spec (Symb_Node (symbex_A_thm, (symbex_B_subtree::symbex_B_subtrees))) =
      let
        val symbex_B_thm = reduce_tree SEQ_fun_spec symbex_B_subtree;
        val symbex_A_thm_new = SEQ_fun_spec symbex_A_thm symbex_B_thm NONE;
      in
        reduce_tree SEQ_fun_spec (Symb_Node (symbex_A_thm_new, symbex_B_subtrees))
      end;

(*
val STEP_fun_spec = birs_rule_STEP_fun_spec;
val SEQ_fun_spec = birs_rule_SEQ_fun_spec;

val symbex_A_thm = single_step_A_thm;
val stop_lbls = birs_stop_lbls;
*)
fun build_tree (STEP_fun_spec, SEQ_fun_spec) symbex_A_thm stop_lbls =
  let
    val _ = print ("\n");
    val (_, _, Pi_A_tm) = (symb_sound_struct_get_sysLPi_fun o concl) symbex_A_thm;

    fun is_executable st =
      birs_is_running st andalso (not (List.exists (identical (birs_get_pc st)) stop_lbls));

    val birs_states_mid = symb_sound_struct_Pi_to_birstatelist_fun Pi_A_tm;
(*
    val birs_states_mid_running = List.filter birs_is_running birs_states_mid;
*)
    val birs_states_mid_executable = List.filter is_executable birs_states_mid;
(*
    val _ = print ("- have " ^ (Int.toString (length birs_states_mid)) ^ " states\n");
    val _ = print ("    (" ^ (Int.toString (length birs_states_mid_running)) ^ " running)\n");
    val _ = print ("    (" ^ (Int.toString (length birs_states_mid_executable)) ^ " executable)\n");
*)

    fun take_step birs_state_mid =
      let
        val _ = print ("Executing one more step @(" ^ (term_to_string (birs_get_pc birs_state_mid)) ^ ")\n");
        val single_step_B_thm = STEP_fun_spec birs_state_mid;
      in
        single_step_B_thm
      end;
  in
    (* stop condition (no more running states, or reached the stop_lbls) *)
    if List.length birs_states_mid_executable = 0 then
      (print "no executable states left, terminating here\n";
       (Symb_Node (symbex_A_thm,[])))
    else
      (* safety check *)
      if List.length birs_states_mid < 1 then
        raise Fail "build_tree_until_branch::this can't happen"
      (* carry out a sequential composition with singleton mid_state set *)
      else if List.length birs_states_mid = 1 then
        let

          val _ = print ("sequential composition with singleton mid_state set\n");

          val birs_state_mid = hd birs_states_mid;
    val timer_exec_step_P1 = bir_miscLib.timer_start 0;
          val single_step_B_thm = take_step birs_state_mid;
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>> executed a whole step in " ^ delta_s ^ "\n")) timer_exec_step_P1;
    val timer_exec_step_P2 = bir_miscLib.timer_start 0;
          (* TODO: derive freesymbols EMPTY from birs *)
          val (sys_B_tm, _, Pi_B_tm) = (symb_sound_struct_get_sysLPi_fun o concl) single_step_B_thm;
          val freesymbols_B_thm = prove (T, cheat);
          (*val freesymbols_B_thm = prove (
            ``(symb_symbols_set (bir_symb_rec_sbir ^bprog_tm) ^Pi_B_tm DIFF
                 symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_B_tm)
               = EMPTY
            ``, cheat);*)
          (* compose together *)
          val bprog_composed_thm = SEQ_fun_spec symbex_A_thm single_step_B_thm (SOME freesymbols_B_thm);
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>> sequentially composed a step in " ^ delta_s ^ "\n")) timer_exec_step_P2;

        in
          build_tree (STEP_fun_spec, SEQ_fun_spec) bprog_composed_thm stop_lbls
        end
      (* continue with executing one step on each branch point... *)
      else
        let
          val _ = print ("continuing only with the executable states\n");
          (*
          val birs_state_mid = hd birs_states_mid_executable;
          *)
          fun buildsubtree birs_state_mid =
            let
              val _ = print ("starting a branch\n");
              val single_step_B_thm = take_step birs_state_mid;
            in
              build_tree (STEP_fun_spec, SEQ_fun_spec) single_step_B_thm stop_lbls
            end
        in
          Symb_Node (symbex_A_thm, List.map buildsubtree birs_states_mid_executable)
        end
  end;

fun exec_until (STEP_fun_spec, SEQ_fun_spec) symbex_A_thm stop_lbls =
  let
    val tree = build_tree (STEP_fun_spec, SEQ_fun_spec) symbex_A_thm stop_lbls;
  in
    reduce_tree SEQ_fun_spec tree
  end;
(* ........................... *)

val tree = build_tree (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
val _ = print "done building the tree\n";

val _ = print "now reducing it to one sound structure\n";
val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;

val _ = (print_term o concl) result;
