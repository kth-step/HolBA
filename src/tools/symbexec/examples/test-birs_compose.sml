
open HolKernel Parse boolLib bossLib;

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
  bsst_environ  := ("R7"         =+ (SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))))
                   (("SP_process" =+ (SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                      (("countw"     =+ (SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))))
                       (K NONE)
                   ));
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_Const (Imm1 1w)
|>``;
(* ........................... *)

val bprog_tm = bprog;
val birs_rule_STEP_thm = birs_rule_STEP_prog_fun bprog_tm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_fun_spec = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm;
(* ........................... *)

(* first step *)
val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
val (_, _, Pi_A_tm) = (symb_sound_struct_get_sysLPi_fun o concl) single_step_A_thm;

(* continue with a second step *)
val birs_states_mid = symb_sound_struct_Pi_to_birstatelist_fun Pi_A_tm;
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

