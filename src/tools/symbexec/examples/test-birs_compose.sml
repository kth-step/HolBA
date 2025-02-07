
open HolKernel Parse boolLib bossLib;

open birsSyntax;
open birs_execLib;
open birs_stepLib;
open birs_composeLib;

(* testing *)
val bprog = ``
BirProgram [
           <|bb_label := BL_Address_HC (Imm32 2826w) "B084 (sub sp, #16)";
             bb_statements :=
               [BStmt_Assert
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)));
                BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                  (BExp_BinExp BIExp_Minus
                     (BExp_Align Bit32 2
                        (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
                     (BExp_Const (Imm32 16w)));
                BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>;
           <|bb_label := BL_Address_HC (Imm32 2828w) "AF00 (add r7, sp, #0)";
             bb_statements :=
               [BStmt_Assert
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)));
                BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32)));
                BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2830w)))|>
] : 'obs_type bir_program_t
``;

val bprog_test_def = Define `
    bprog_test =
BirProgram [
           <|bb_label := BL_Address (Imm32 2826w);
             bb_statements :=
               [BStmt_Assert
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)));
                BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>
] : 'obs_type bir_program_t
`;
val bprog = (fst o dest_eq o concl) bprog_test_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 2826w))``;
val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := birs_gen_env
                   [("R7", BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
                    ("SP_process", BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
                    ("countw", BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))];
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_Const (Imm1 1w)
|>``;
val birs_state_init_2 = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := birs_gen_env
                   [("R7", BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
                    ("SP_process", BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
                    ("countw", BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))];
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w))
|>``;
(* ........................... *)


(*
val birs_state_init_tm = birs_state_init_2;
val bprog_tm = bprog;
*)
fun execute_two_steps bprog_tm birs_state_init_tm =
 let
  val (birs_rule_STEP_thms, _) =
    birs_rule_STEP_prog_fun (birs_auxLib.get_prog_no_halt_thm bprog_tm);
  
  fun birs_post_step_fun (t, _) = (
    birs_rule_tryjustassert_fun false
  ) t;
  val birs_rule_STEP_fun_spec = birs_post_step_fun o birs_rule_STEP_fun birs_rule_STEP_thms;
  (* ........................... *)

  (* first step *)
  val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init_tm;

  (* continue with a second step *)
  val birs_states_mid = (get_birs_Pi_list o concl) single_step_A_thm;
  (* it would be better to find the running one, oh well *)
  val birs_state_mid = List.nth(birs_states_mid,0);

  (* second step *)
  val single_step_B_thm = birs_rule_STEP_fun_spec birs_state_mid;
  (* ........................... *)

  (* now the composition *)
  val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
  (* ........................... *)

  (* compose together *)
  val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
  val bprog_composed_thm = birs_rule_SEQ_fun_spec single_step_A_thm single_step_B_thm;

  (*
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
  val tm = (concl) bprog_composed_thm;

  val bprog_composed_thm_ = (snd o dest_eq o concl o (SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) [])) tm;

  val bprog_composed_thm_ = (snd o dest_eq o concl o (SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++birs_state_ss) [bir_symbTheory.birs_symb_to_symbst_EQ_thm, pred_setTheory.INSERT_UNION])) tm;
  *)

  val _ = print_term (concl bprog_composed_thm);
 in
   ()
 end;


val _ = execute_two_steps bprog birs_state_init;

val _ = execute_two_steps bprog birs_state_init_2;
