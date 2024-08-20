(* ------------------------------------------------------------------------- *)
(*  Tests and sanity checks for the repository                               *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory bir_binexpTheory bir_evalTheory ;
open bir_binpredTheory ;
open bir_envTheory ;
open bir_cv_basicLib;
open bir_cv_envLib;
open bir_cv_programLib ;

(* ------------------------------------------------- *)
(* ------------------- Utilities ------------------- *)
(* ------------------------------------------------- *)

(* Checks that the RHS on the output theorem is output *)
fun print_and_check_thm name thm t_concl =
  let
    val _ = print (name ^ ":\n");
    val _ = print "===============================\n";
    val _ = (Hol_pp.print_thm thm; print "\n");
    val _ = if identical (concl thm) t_concl then () else
            raise Fail "print_and_check_thm::conclusion is not as expected"
    val _ = print "\n\n";
  in
    ()
  end;

fun print_and_check_conv name conv input t_concl =
  let 
    val _ = print (name ^ ":\n");
    val _ = print "===============================\n";
    val thm = conv input;
    val _ = (Hol_pp.print_thm thm; print "\n");
    val _ = if identical (rand (rhs (concl thm))) t_concl andalso 
               identical (lhs (concl thm)) input then () else
            raise Fail "print_and_check_thm::conclusion is not as expected"
    val _ = print "\n\n";
  in 
    ()
  end;

(* ------------------------------------------------- *)
(* -------------------- bir_eval ------------------- *)
(* ------------------------------------------------- *)

val _ = prove(``
  !imm. bir_eval_exp bir_empty_env (BExp_Const imm) (BVal_Imm imm)``,

  rw [Once bir_eval_exp_cases]) ;

val _ = prove(``
  !imm. bir_eval_exp bir_empty_env (BExp_Const imm) (BVal_Imm imm)``,

  rw [Once bir_eval_exp_cases]) ;

val _ = prove (``
  !env var vimm. bir_eval_exp (bir_env_update env var vimm) (BExp_Den var) vimm``, 

  Cases_on `var` >> Cases_on `env` >>
  rw [Once bir_eval_exp_cases, bir_env_update_def, bir_env_lookup_rel_def]) ;

val _ = prove (``
  !imm1 imm2. bir_eval_exp bir_empty_env 
    (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 imm1)) (BExp_Const (Imm64 imm2)))
    (BVal_Imm (Imm64 (imm1 + imm2)))``,

  rw [Ntimes bir_eval_exp_cases 3, bir_eval_binexp_def, bir_eval_binexp_imm_cases, bir_binexp_get_oper_def] >>
  rw [Once bir_eval_exp_cases, bir_eval_binexp_def, bir_eval_binexp_imm_cases, bir_binexp_get_oper_def]) ;


(* ------------------------------------------------- *)
(* ------------------ bir_binpred ------------------ *)
(* ------------------------------------------------- *)

(* Equal predicate is reflexive *)
val _ = prove (``
  !env v. bir_eval_binpred BIExp_Equal (BVal_Imm v) (BVal_Imm v) birT``, 

  Cases_on `v` >>
    rw [Once bir_eval_binpred_cases, bir_eval_binpred_imm_cases, bir_binpred_get_oper_def] >>
    rw [bool2b_T_eq_birT, bool2b_F_eq_birF]) ;


(* ------------------------------------------------- *)
(* ---------------- bir_cv_basicLib ---------------- *)
(* ------------------------------------------------- *)

val _ = print_and_check_conv
  "bir_val_conv BVal_Imm" 
  bir_val_conv ``BVal_Imm (Imm64 1w)``
  ``BCVVal_Imm (Imm64 1w)``;

val _ = print_and_check_conv
  "bir_val_conv BVal_Mem" 
  bir_val_conv ``BVal_Mem Bit64 Bit32 (FEMPTY |+ (1,2) |+ (3,4))``
  ``BCVVal_Mem Bit64 Bit32 [(3,4); (1,2)]``;


val _ = print_and_check_conv
  "bir_val_option_conv NONE" 
  bir_val_option_conv ``NONE:bir_val_t option``
  ``NONE:bir_cv_val_t option``;

val _ = print_and_check_conv
  "bir_val_option_conv BVal_Imm" 
  bir_val_option_conv ``SOME (BVal_Imm (Imm64 1w))``
  ``SOME (BCVVal_Imm (Imm64 1w))``;

val _ = print_and_check_conv
  "bir_val_option_conv BVal_Mem" 
  bir_val_option_conv ``SOME (BVal_Mem Bit64 Bit32 (FEMPTY |+ (1,2) |+ (3,4)))``
  ``SOME (BCVVal_Mem Bit64 Bit32 [(3,4); (1,2)])``;


val _ = print_and_check_conv
  "fmap_to_alist_conv"
  fmap_to_alist_conv ``FEMPTY |+ (1,2) |+ (3,4)``
  ``[(3,4); (1,2)]``;


val _ = print_and_check_conv
  "bir_exp_conv BExp_Const"
  bir_exp_conv ``BExp_Const (Imm64 1w)``
  ``BCVExp_Const (Imm64 1w)``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_MemConst"
  bir_exp_conv ``BExp_MemConst Bit64 Bit32 (FEMPTY |+ (1,2) |+ (3,4))``
  ``BCVExp_MemConst Bit64 Bit32 [(3,4); (1,2)]``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_Den"
  bir_exp_conv ``BExp_Den (BVar "var")``
  ``BCVExp_Den (BVar "var")``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_BinExp"
  bir_exp_conv ``BExp_BinExp BIExp_Plus (BExp_Const (Imm64 1w)) (BExp_Const (Imm64 2w))``
  ``BCVExp_BinExp BIExp_Plus (BCVExp_Const (Imm64 1w)) (BCVExp_Const (Imm64 2w))``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_UnaryExp"
  bir_exp_conv ``BExp_UnaryExp BIExp_Not (BExp_Const (Imm64 1w))``
  ``BCVExp_UnaryExp BIExp_Not (BCVExp_Const (Imm64 1w))``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_BinPred"
  bir_exp_conv ``BExp_BinPred BIExp_Equal (BExp_Const (Imm64 1w)) (BExp_Const (Imm64 2w))``
  ``BCVExp_BinPred BIExp_Equal (BCVExp_Const (Imm64 1w)) (BCVExp_Const (Imm64 2w))``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_IfThenElse"
  bir_exp_conv ``BExp_IfThenElse (BExp_Const (Imm64 0w)) (BExp_Const (Imm64 1w)) (BExp_Const (Imm64 2w))``
  ``BCVExp_IfThenElse (BCVExp_Const (Imm64 0w)) (BCVExp_Const (Imm64 1w)) (BCVExp_Const (Imm64 2w))``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_Load"
  bir_exp_conv ``BExp_Load (BExp_MemConst Bit64 Bit32 (FEMPTY |+ (1,2))) (BExp_Const (Imm64 1w)) BEnd_BigEndian Bit32``
  ``BCVExp_Load (BCVExp_MemConst Bit64 Bit32 [(1,2)]) (BCVExp_Const (Imm64 1w)) BEnd_BigEndian Bit32``;

val _ = print_and_check_conv
  "bir_exp_conv BExp_Store"
  bir_exp_conv ``BExp_Store (BExp_MemConst Bit64 Bit32 (FEMPTY |+ (1,2))) (BExp_Const (Imm64 1w)) BEnd_BigEndian (BExp_Const (Imm32 2w))``
  ``BCVExp_Store (BCVExp_MemConst Bit64 Bit32 [(1,2)]) (BCVExp_Const (Imm64 1w)) BEnd_BigEndian (BCVExp_Const (Imm32 2w))``;



(* ------------------------------------------------- *)
(* ----------------- bir_cv_envLib ----------------- *)
(* ------------------------------------------------- *)

val _ = print_and_check_conv
  "env_to_cv_env_conv"
  env_to_cv_env_conv ``BEnv (("r0" =+ (SOME (BVal_Imm (Imm64 1w)))) (\x. NONE))``
  ``BCVEnv [("r0", BCVVal_Imm (Imm64 1w))]``;



(* ------------------------------------------------- *)
(* --------------- bir_cv_programLib --------------- *)
(* ------------------------------------------------- *)

val _ = print_and_check_conv
  "bir_label_exp_conv BLE_Label"
  bir_label_exp_conv ``BLE_Label (BL_Label "label")``
  ``BCVLE_Label (BL_Label "label")``;

val _ = print_and_check_conv
  "bir_label_exp_conv BLE_Exp"
  bir_label_exp_conv ``BLE_Exp (BExp_Const (Imm64 1w))``
  ``BCVLE_Exp (BCVExp_Const (Imm64 1w))``;


val _ = print_and_check_conv
  "bir_stmt_basic_conv BStmt_Assign"
  bir_stmt_basic_conv ``BStmt_Assign (BVar "var") (BExp_Const (Imm64 1w))``
  ``BCVStmt_Assign (BVar "var") (BCVExp_Const (Imm64 1w))``;


val _ = print_and_check_conv
  "bir_stmt_end_conv BStmt_Jmp"
  bir_stmt_end_conv ``BStmt_Jmp (BLE_Label (BL_Label "label"))``
  ``BCVStmt_Jmp (BCVLE_Label (BL_Label "label"))``;

val _ = print_and_check_conv
  "bir_stmt_end_conv BStmt_CJmp"
  bir_stmt_end_conv ``BStmt_CJmp (BExp_Const (Imm64 0w)) (BLE_Label (BL_Label "label1")) (BLE_Label (BL_Label "label2"))``
  ``BCVStmt_CJmp (BCVExp_Const (Imm64 0w)) (BCVLE_Label (BL_Label "label1")) (BCVLE_Label (BL_Label "label2"))``;

val _ = print_and_check_conv
  "bir_block_conv"
  bir_block_conv ``<|bb_label := (BL_Label "label") ; bb_statements := [BStmt_Assign (BVar "var") (BExp_Const (Imm64 1w))] ;
      bb_last_statement := (BStmt_Jmp (BLE_Label (BL_Label "label")))|>``
  ``BCVBlock (BL_Label "label") [BCVStmt_Assign (BVar "var") (BCVExp_Const (Imm64 1w))] (BCVStmt_Jmp (BCVLE_Label (BL_Label "label")))``;

val _ = print_and_check_conv
  "bir_program_conv"
  bir_program_conv ``BirProgram []``
  ``BirCVProgram []``;

val _ = print_and_check_conv
  "bir_state_conv"
  bir_state_conv ``<|bst_pc := <|bpc_label := (BL_Label "label"); bpc_index := 0|>; bst_environ := BEnv (\x.NONE); bst_status := BST_Running|>``
  ``BCVState (BCVProgramCounter (BL_Label "label") 0) (BCVEnv []) BST_Running``;





