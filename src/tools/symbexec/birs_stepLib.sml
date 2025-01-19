structure birs_stepLib =
struct

local

open HolKernel Parse boolLib bossLib;
open computeLib;

open birsSyntax;

open bir_exp_substitutionsTheory;
open bir_expTheory;

open bir_symbTheory;
open birs_auxTheory;

open birs_auxLib;
open birs_utilsLib;

open bir_exp_typecheckLib;

  (* error handling *)
  val libname = "bir_symbLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname



(*

val test_term_birs_eval_exp = ``
          birs_eval_exp
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
            (K NONE)⦇
              "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
              "SP_process" ↦
                SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
              "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            ⦈
``;


val test_term_birs_eval_exp_subst = ``
          birs_eval_exp_subst
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
            (K NONE)⦇
              "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
              "SP_process" ↦
                SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
              "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            ⦈
``;


val test_term_birs_senv_typecheck = ``
          birs_senv_typecheck
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
            (K NONE)⦇
              "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
              "SP_process" ↦
                SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
              "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            ⦈
``;


*)

(*
birs_senv_typecheck_CONV test_term_birs_senv_typecheck
*)

(*
val test_term_birs_eval_exp = ``
birs_eval_exp
            (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 1w)))
            (birs_gen_env
               [("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
                ("SP_process",
                 BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
                ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))])
``;

birs_eval_exp_CONV test_term_birs_eval_exp
*)

(*
val test_term = ``
birs_exec_step bprog_test
      <|bsst_pc := <|bpc_label := BL_Address (Imm32 2826w); bpc_index := 1|>;
        bsst_environ :=
          birs_gen_env
            [("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))];
        bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))|>
``;

val bstate_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm64 0x10w); bpc_index := 1|>;
    bsst_environ :=
      birs_gen_env
        [("x2",BExp_Den (BVar "sy_x2" (BType_Imm Bit64)));
         ("x1",BExp_Const (Imm64 0x14w))];
    bsst_status := BST_Running;
    bsst_pcond := (BExp_Const (Imm1 1w))|>
``;
val bprog_tm = ``
  BirProgram [
          <|bb_label := BL_Address (Imm64 0x10w);
             bb_statements :=
               [BStmt_Assert
                  (BExp_UnaryExp BIExp_Not
                     (BExp_LSB
                        (BExp_BinExp BIExp_And
                           (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
                           (BExp_Den (BVar "x1" (BType_Imm Bit64))))))];
             bb_last_statement :=
               BStmt_Jmp
                 (BLE_Exp
                    (BExp_BinExp BIExp_And
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
                       (BExp_Den (BVar "x1" (BType_Imm Bit64)))))|>;
          <|bb_label :=
               BL_Address (Imm64 0x14w);
             bb_statements :=
               [BStmt_Assign (BVar "x2" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "x2" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 32w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x18w)))|>]
``;
val test_term = ``birs_exec_step ^bprog_tm ^bstate_tm``;
birs_exec_step_CONV test_term;

val test_eval_label_term = ``
birs_eval_label_exp
          (BLE_Exp
             (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
                (BExp_Den (BVar "x1" (BType_Imm Bit64)))))
          (birs_gen_env
             [("x2",BExp_Den (BVar "sy_x2" (BType_Imm Bit64)));
              ("x1",BExp_Const (Imm64 20w))]) (BExp_Const (Imm1 1w))
``;
val test_eval_label_term = ``
birs_eval_label_exp
  (BLE_Exp
     (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
        (BExp_Den (BVar "x1" (BType_Imm Bit64)))))
  (birs_gen_env
     [("x2",
       BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
         (BExp_Const (Imm64 32w)));
      ("x8",
       BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
         (BExp_Const (Imm64 0w)));
      ("x10",
       BExp_Cast BIExp_SignedCast
         (BExp_Cast BIExp_LowCast
            (BExp_BinExp BIExp_Plus
               (BExp_Cast BIExp_SignedCast
                  (BExp_Cast BIExp_LowCast
                     (BExp_Load
                        (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_Const (Imm64 256w)) BEnd_LittleEndian Bit64)
                     Bit32) Bit64) (BExp_Const (Imm64 10w))) Bit32) Bit64);
      ("x15",
       BExp_Cast BIExp_SignedCast
         (BExp_Cast BIExp_LowCast
            (BExp_BinExp BIExp_Plus
               (BExp_Cast BIExp_SignedCast
                  (BExp_Cast BIExp_LowCast
                     (BExp_Load
                        (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_Const (Imm64 256w)) BEnd_LittleEndian Bit64)
                     Bit32) Bit64) (BExp_Const (Imm64 10w))) Bit32) Bit64);
      ("x14",BExp_Const (Imm64 10w));
      ("MEM8",
       BExp_Store
         (BExp_Store
            (BExp_Store
               (BExp_Store
                  (BExp_Store
                     (BExp_Store
                        (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                        (BExp_Den (BVar "sy_x1" (BType_Imm Bit64))))
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 16w))) BEnd_LittleEndian
                     (BExp_Den (BVar "sy_x8" (BType_Imm Bit64))))
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                  (BExp_Cast BIExp_LowCast (BExp_Const (Imm64 1w)) Bit32))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 40w))) BEnd_LittleEndian
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 0w))))
            (BExp_BinExp BIExp_Minus
               (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
            (BExp_Const (Imm64 3w)))
         (BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
            (BExp_Const (Imm64 60w))) BEnd_LittleEndian
         (BExp_Cast BIExp_LowCast (BExp_Const (Imm64 7w)) Bit32));
      ("x1",BExp_Const (Imm64 1692w)); ("x11",BExp_Const (Imm64 7w))])
  (BExp_BinExp BIExp_And
     (BExp_BinPred BIExp_Equal (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
        (BExp_Const (Imm64 pre_x2)))
     (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_Equal
           (BExp_BinExp BIExp_And (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
              (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)))
        (BExp_BinExp BIExp_And
           (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 8192w))
              (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
           (BExp_BinPred BIExp_LessThan
              (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
              (BExp_Const (Imm64 0x100000000w))))))
``;
birs_eval_label_exp_CONV test_eval_label_term;
*)

(*
val tm = ``birs_symbval_concretizations
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                (BExp_Const (Imm64 pre_x2)))
             (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_Equal
                   (BExp_BinExp BIExp_And
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)))
                (BExp_BinExp BIExp_And
                   (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 8192w))
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
                   (BExp_BinPred BIExp_LessThan
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 0x100000000w))))))
          (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
             (BExp_Const (Imm64 1692w)))``;
val tm = ``birs_symbval_concretizations
                (BExp_BinExp BIExp_And
                   (BExp_BinPred BIExp_LessThan
		      (BExp_Const (Imm64 0x20w))
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
                   (BExp_BinPred BIExp_LessThan
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 0x20w))))
          (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFw))
             (BExp_Const (Imm64 1692w)))``;
birs_symbval_concretizations_oracle_CONV tm;
*)

(*
val test_term = (snd o dest_eq o snd o strip_forall o concl) bir_symbTheory.birs_exec_step_def;
((fn (_,x,_) => x) o TypeBase.dest_case o (fn (_,_,x) => x) o dest_cond) test_term
(rand o rator o rator o rand) test_term

val test_term = (fst o dest_eq o snd o strip_forall o concl) bir_symbTheory.birs_exec_step_def;
(rand) test_term
*)

(*
val test_term = ``ABC (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 0w))
                            (BExp_BinExp BIExp_LeftShift
                               (BExp_Cast BIExp_SignedCast
                                  (BExp_BinExp BIExp_RightShift
                                     (BExp_Cast BIExp_LowCast
                                        (BExp_BinExp BIExp_Xor
                                           (BExp_Cast BIExp_SignedCast
                                              (BExp_Load
                                                 (BExp_Den
                                                    (BVar "sy_MEM8"
                                                       (BType_Mem Bit64 Bit8)))
                                                 (BExp_BinExp BIExp_Plus
                                                    (BExp_Den
                                                       (BVar "sy_x12"
                                                          (BType_Imm Bit64)))
                                                    (BExp_Const (Imm64 4w)))
                                                 BEnd_LittleEndian Bit32)
                                              Bit64)
                                           (BExp_Cast BIExp_SignedCast
                                              (BExp_Load
                                                 (BExp_Den
                                                    (BVar "sy_MEM8"
                                                       (BType_Mem Bit64 Bit8)))
                                                 (BExp_BinExp BIExp_Plus
                                                    (BExp_Den
                                                       (BVar "sy_x10"
                                                          (BType_Imm Bit64)))
                                                    (BExp_Const (Imm64 4w)))
                                                 BEnd_LittleEndian Bit32)
                                              Bit64)) Bit32)
                                     (BExp_Const (Imm32 24w))) Bit64)
                               (BExp_Const (Imm64 2w)))) (DEF:num) = 0w:word64``;
val test_thm = prove(test_term, cheat);

val subs_tm = (rand o rator o fst o dest_eq o concl) test_thm;
val abc_tm = ``(abc:bir_exp_t)``;
val eq_tm = ``^abc_tm = ^subs_tm``

val B_tm = ``(B:bir_exp_t)``;
val pat_tm = ``ABC ^B_tm (DEF:num) = 0w:word64``;

SUBST [B_tm |-> GSYM (ASSUME eq_tm)] pat_tm test_thm

val changed_thm = REWRITE_RULE [GSYM (ASSUME eq_tm)] test_thm;

(*
val changed_back_thm = SIMP_RULE std_ss [] (DISCH_ALL changed_thm);

val changed_back_thm = REWRITE_RULE [] (CONV_RULE (RATOR_CONV EVAL) (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)));
*)

val changed_back_thm = BETA_RULE (CONV_RULE (RATOR_CONV EVAL) (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)));

val changed_back_thm = MP (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)) (REFL subs_tm);

val changed_back_thm = MP (DISCH_ALL (INST [abc_tm |-> subs_tm] (changed_thm))) (REFL subs_tm);

val changed_back_thm = REWRITE_RULE [gen_rev_thm] (DISCH_ALL (INST [abc_tm |-> subs_tm] (changed_thm)));

prove(``
  ^test_term
``,
  METIS_TAC [changed_back_thm]
);

*)

(*
val bstate_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm32 2826w); bpc_index := 1|>;
    bsst_environ :=
      birs_gen_env
        [("SP_process",
          BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
            (BExp_Const (Imm32 8w)));
         ("MEM",
          BExp_Store
            (BExp_Store (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 8w))) BEnd_LittleEndian
               (BExp_Den (BVar "sy_R7" (BType_Imm Bit32))))
            (BExp_BinExp BIExp_Minus
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
            (BExp_Den (BVar "sy_LR" (BType_Imm Bit32))));
         ("countw",
          BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 3w)));
         ("tmp_SP_process",
          BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
            (BExp_Const (Imm32 8w)));
         ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
         ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
         ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
         ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
         ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
         ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
         ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
         ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
         ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
         ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
         ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
         ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
         ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
         ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
         ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
         ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
         ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
         ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
         ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
         ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
         ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
         ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
         ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
         ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
         ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
         ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
         ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
         ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
         ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
         ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
         ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
         ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
         ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
         ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
         ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
         ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
         ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
         ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
         ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
         ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
         ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
         ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
         ("tmp_ModeHandler",
          BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
    bsst_status := BST_Running;
    bsst_pcond :=
      BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_And
           (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
              (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                 (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
        (BExp_BinPred BIExp_LessOrEqual
           (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
           (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>
``;
*)
(*
val bstate_tm = birs_state_init;
val bstate_tm = birs_state_mid;

val bstate_tm = birs_state_init_tm;
val bprog_tm = bprog_tm;

val tm = ``ABCD (birs_exec_step ^bprog_tm ^bstate_tm)``;
val tm = ``birs_exec_step ^bprog_tm ^bstate_tm``;
birs_exec_step_CONV_fun tm
*)


(* ----------------------------------------------------------------- *)
fun count_term is_tm_fun count_tm_fun tm =
    if is_tm_fun tm then
      count_tm_fun tm
    else if is_comb tm then
      let
        val (rator,rand) = dest_comb tm;
      in
        (count_term is_tm_fun count_tm_fun rator) +
        (count_term is_tm_fun count_tm_fun rand)
      end
    else if is_abs tm then
      count_term is_tm_fun count_tm_fun ((snd o dest_abs) tm)
    else
      0
    ;

fun get_birs_state_size t =
  let
    val (_, env, _, pcond) = dest_birs_state t;
    val n_pcond = bir_exp_size pcond;
    val n_env = count_term is_bir_exp bir_exp_size env;
  in
    n_pcond + n_env
  end;


val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

(* ---------------------------------------------------------------------------- *)

(*
val t = ``[("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))]``;
val t = ``[("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
                ("SP_process",
                 BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
                ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))]``;
val i = 0;
val acc = [] : thm list;
fun consf thm = thm:thm;
*)
fun gen_abbr_var i = mk_var ("temp_envl_abbr_" ^ (Int.toString i), bir_expSyntax.bir_exp_t_ty);
fun abbr_birs_gen_env i acc consf t =
  if not (listSyntax.is_cons t) then (consf (REFL t), acc) else
  let
    val (h,tl) = listSyntax.dest_cons t;
    val (_, e_tm) = pairSyntax.dest_pair h;
    val e_abbr_tm = gen_abbr_var i;
    val eq_thm = ASSUME (mk_eq (e_abbr_tm, e_tm));
    val thm0 = LAND_CONV (REWRITE_CONV [GSYM eq_thm]) t;
    fun consf_ thm = consf (CONV_RULE (RAND_CONV (RAND_CONV (K thm))) thm0);
  in
    abbr_birs_gen_env (i+1) (eq_thm::acc) consf_ tl
  end
  handle _ => raise ERR "abbr_birs_gen_env" "abbreviation failed";
(*
val (thm, eq_thms) = abbr_birs_gen_env 0 [] I t;
*)
val mk_gen_subst = (fn (abbr,x) => (abbr |-> x)) o dest_eq;
fun rev_birs_gen_env (thm, eq_thms) =
  let
    val eq_tms = map (concl) eq_thms;
  in
    foldl (fn (x,acc) =>  MP ((INST [mk_gen_subst x] o DISCH x) acc) ((REFL o snd o dest_eq) x)) thm eq_tms
  end;

local
  val env_abbr_tm = ``temp_env_abbr : string -> bir_exp_t option``;
  val pcond_abbr_tm = ``temp_pcond_abbr : bir_exp_t``;
in
 fun abbr_app (t, env_tm, pcond_tm) =
  let
     val env_eq_tm = mk_eq (env_abbr_tm, env_tm);
     val pcond_eq_tm = mk_eq (pcond_abbr_tm, pcond_tm);
     val env_eq_thm = ASSUME (env_eq_tm);
     val pcond_eq_thm = ASSUME (pcond_eq_tm);
     (*val abbr_thm = REWRITE_CONV [GSYM (env_eq_thm), GSYM (pcond_eq_thm)] t;*)
  in
    (*abbr_thm, [env_eq_thm, pcond_eq_thm]*)
    (env_eq_thm, pcond_eq_thm)
  end;
 fun abbr_rev (res, env_tm, pcond_tm) =
  MP (MP ((INST [env_abbr_tm |-> env_tm, pcond_abbr_tm |-> pcond_tm] o DISCH_ALL) res) (REFL env_tm)) (REFL pcond_tm);
end;

fun deabbr_CONV eq_thms tm =
  let
    (* find thm for tm on lhs in eq_thms, return that theorem *)
    val thms = List.filter (fn t => identical tm ((lhs o concl) t)) eq_thms;
    val thm =
      case length thms of
          1 => hd thms
        | 0 => raise UNCHANGED
        | _ => raise ERR "deabbr_CONV" "more than one theorem with same lhs in eq_thms";
  in
    thm
  end;

  val state_access_conv =
    REWRITE_CONV [bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM];
  fun unabbrev_conv eq_thms =
    state_access_conv THENC deabbr_CONV eq_thms;

(* ---------------------------------------------------------------------------- *)

fun birs_gen_env_exp_CONV eq_thms =
  REPEATC (
    REWR_CONV birs_gen_env_GET_thm THENC
    CHANGED_CONV
      (ITE_CONV aux_setLib.bir_varname_EQ_CONV)
  ) THENC
  TRY_CONV (REWR_CONV birs_gen_env_GET_NULL_thm) THENC
  RAND_CONV (deabbr_CONV eq_thms);
val option_bind_def_1 = List.nth(CONJUNCTS optionTheory.OPTION_BIND_def, 1);
val option_bind_def_0 = List.nth(CONJUNCTS optionTheory.OPTION_BIND_def, 0);
val OPTION_BIND_CONV =
  (*REWRITE_CONV [optionTheory.OPTION_BIND_def]*)
  (IFC
    (TRY_CONV (REWR_CONV (option_bind_def_1)))
    (ALL_CONV)
    (TRY_CONV (REWR_CONV (option_bind_def_0)))
  );
val includes_vs_EMPTY_thm = prove(``bir_envty_includes_vs envty EMPTY = T``, fs[bir_symbTheory.bir_envty_includes_vs_EMPTY]);
fun bir_envty_includes_vs_CONV eq_thms tm = (
  if (pred_setSyntax.is_insert o rand) tm then
    REWR_CONV bir_envTheory.bir_envty_includes_vs_INSERT THENC
    CONJL_CONV
      (REWR_CONV bir_envty_includes_v_senv_gen_env_thm THENC
        LHS_CONV (
          LAND_CONV (
            RAND_CONV (REWR_CONV bir_envTheory.bir_var_name_def) THENC
            birs_gen_env_exp_CONV eq_thms
          ) THENC
          OPTION_BIND_CONV THENC
          type_of_bir_exp_CONV
        ) THENC
        RHS_CONV (RAND_CONV (REWR_CONV bir_envTheory.bir_var_type_def)) THENC
        REWRITE_CONV [optionTheory.SOME_11, optionTheory.NOT_SOME_NONE, GSYM optionTheory.NOT_SOME_NONE] THENC
        aux_setLib.bir_type_EQ_CONV)
      (bir_envty_includes_vs_CONV eq_thms)
  else
    REWR_CONV includes_vs_EMPTY_thm
  ) tm;

fun birs_senv_typecheck_CONV eq_thms = (
  (* TODO: this can be optimized: reuse vars_of_exp, and
       construct EnvTy (maybe good as list as with gen_env, maybe can even reuse gen_env?),
       then use bir_symbTheory.birs_senv_typecheck_thm and
       go through the symbol set one by one with bir_envTheory.bir_envty_includes_vs_INSERT, bir_symbTheory.bir_envty_includes_vs_EMPTY
       for each use bir_envty_includes_v_senv_gen_env_thm
       also: use deabbr_CONV *)
  (*(fn x => (print "\n\n"; print_term x; print "\n\n"; REFL x)) THENC*)
  REWR_CONV bir_symbTheory.birs_senv_typecheck_thm THENC
  RAND_CONV (bir_vars_ofLib.bir_vars_of_exp_DIRECT_CONV) THENC
  bir_envty_includes_vs_CONV eq_thms
  (*
  RESTR_EVAL_CONV [bir_typing_expSyntax.type_of_bir_exp_tm] THENC
  REWRITE_CONV eq_thms THENC
  type_of_bir_exp_CONV THENC
  EVAL
  *)
);
val birs_senv_typecheck_CONV = fn x => Profile.profile "senv_typecheck_CONV" (birs_senv_typecheck_CONV x);


fun birs_eval_exp_CONV_p1 t =
   let
     val tm = (dest_birs_gen_env o snd o dest_birs_eval_exp) t;
     val (thm, eq_thms) = abbr_birs_gen_env 0 [] I tm;
   in
     (* rewrite the environment list *)
     (RAND_CONV (RAND_CONV (K thm)) t, eq_thms)
   end
   handle e => (print_term t; raise wrap_exn "birs_eval_exp_CONV_p1" e);

fun birs_eval_exp_CONV_p2 eq_thms =
  REWR_CONV birs_eval_exp_def THENC
  type_of_bir_exp_CONV THENC
  GEN_match_conv (is_birs_senv_typecheck) (birs_senv_typecheck_CONV eq_thms);

(* TODO: can possibly improve this,
     for example by only taking the environment into the expressions where there are symbol lookups,
     could even work with a cache of lookup theorems for the present symbols
fun birs_eval_exp_subst_CONV eq_thms =
  (fn x => (print "\nAAAAAAAAAAAAAAA:\n"; print_term x; print "\n\n"; REFL x)) THENC
  EVAL THENC
  REWRITE_CONV eq_thms THENC
  EVAL THENC
  (fn x => (print "\nBBBBBBBBBBBBBBB:\n"; print_term x; print "\n\n"; REFL x));
   *)

val birs_eval_exp_subst_var_CONV =
  let
    val birs_gen_env_GET_REWR_thms = [birs_auxTheory.birs_gen_env_GET_thm, birs_auxTheory.birs_gen_env_GET_NULL_thm];
    val option_case_def_thms = CONJUNCTS optionTheory.option_case_def;
  in
    fn eq_thms =>
      REWR_CONV bir_symbTheory.birs_eval_exp_subst_var_def THENC
      PATH_CONV "llr" (
        RAND_CONV (REWR_CONV bir_envTheory.bir_var_name_def) THENC
        REPEATC (CHANGED_CONV (
          TRY_LIST_REWR_CONV birs_gen_env_GET_REWR_thms THENC
          TRY_CONV (ITE_CONV aux_setLib.bir_varname_EQ_CONV)
        )) THENC
        TRY_CONV (RAND_CONV (deabbr_CONV eq_thms))
      ) THENC
      TRY_LIST_REWR_CONV option_case_def_thms THENC
      REWR_CONV combinTheory.I_THM
  end;

val birs_eval_exp_subst_def_thms = CONJUNCTS bir_symbTheory.birs_eval_exp_subst_def;

fun birs_eval_exp_subst_CONV eq_thms tm =
(
  TRY_LIST_REWR_CONV birs_eval_exp_subst_def_thms THENC
  GEN_match_conv is_birs_eval_exp_subst_var (birs_eval_exp_subst_var_CONV eq_thms) THENC
  GEN_match_conv is_birs_eval_exp_subst (birs_eval_exp_subst_CONV eq_thms)
) tm;

val birs_eval_exp_CONV_p4 =
  let
    val thm_T = (GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
    val thm_is_some_def = CONJUNCT1 optionTheory.IS_SOME_DEF;
  in
    fn eq_thms =>
      REWR_CONV LET_THM THENC
      LIST_BETA_CONV THENC
      ITE_CONV (REWR_CONV thm_T THENC REWR_CONV thm_is_some_def) THENC
      TRY_CONV (REWR_CONV LET_THM) THENC
      LIST_BETA_CONV THENC
      LIST_BETA_CONV THENC
      RAND_CONV (LAND_CONV (birs_eval_exp_subst_CONV eq_thms))
  end;

fun birs_eval_exp_CONV t = (
  let
    val (thm_p1, eq_thms) = Profile.profile "eval_exp_CONV_p1" birs_eval_exp_CONV_p1 t;
    (*val _ = print_thm thm_p1;*)
    val thm_p2 = Profile.profile "eval_exp_CONV_p2" (CONV_RULE (RAND_CONV (birs_eval_exp_CONV_p2 eq_thms))) thm_p1;
    val thm_p4 = Profile.profile "eval_exp_CONV_p4" (CONV_RULE (RAND_CONV (birs_eval_exp_CONV_p4 eq_thms))) thm_p2;
    val thm_p4rev = Profile.profile "eval_exp_CONV_p5" rev_birs_gen_env (thm_p4, eq_thms);
  in
    thm_p4rev
  end
);
val birs_eval_exp_CONV = Profile.profile "eval_exp_CONV" birs_eval_exp_CONV;


(*
is_plain_jumptarget_set ``{BL_Address (Imm64 20w)}``
is_plain_jumptarget_set ``{BL_Address iv | Imm64 20w = iv}``
*)
fun is_plain_jumptarget_set tm =
  let
    open bir_programSyntax;
    val l = pred_setSyntax.strip_set tm;
  in
    List.all (fn e_tm =>
      is_BL_Address e_tm andalso
      bir_immSyntax.gen_is_Imm (dest_BL_Address e_tm)) l
  end handle _ => false;

val birs_symbval_concretizations_oracle_ext_CONV = ref ((K NONE):term -> thm option);

val birs_symbval_concretizations_oracle_CONV =
  (fn tm => if is_birs_symbval_concretizations tm then REFL tm else
   (print_term tm;
    raise ERR "birs_symbval_concretizations_oracle_CONV" "something is not right here, expect a birs_symbval_concretizations")) THENC
  IFC
    (fn tm =>
    let
      val vaex_tm = (rand) tm;
      val pcond_tm = (rand o rator) tm;
      val (pcond_is_sat, pcond_sat_thm) = check_pcond_sat pcond_tm;
      val res_thm =
        if not pcond_is_sat then
          SIMP_RULE (std_ss) [pcond_sat_thm] (SPECL [pcond_tm, vaex_tm] birs_rulesTheory.birs_jumptarget_empty_thm)
        else
          let
            val vaex_thm = EVAL ``birs_interpret_fun i ^vaex_tm``;
            val concr_thm = SIMP_RULE (std_ss++HolBACoreSimps.holBACore_ss) [vaex_thm, pcond_sat_thm] (SPECL [pcond_tm, vaex_tm] birs_rulesTheory.birs_jumptarget_singletonconst_thm);
          in
            concr_thm
          end;
    in
      if
        identical tm ((fst o dest_eq o concl) res_thm)
        handle _ => (print_thm res_thm; print "\n\n"; print_term tm; print "\n\n"; raise ERR "birs_symbval_concretizations_oracle_CONV" "failed to resolve single jump target, not an equality theorem")
      then res_thm else
      raise ERR "birs_symbval_concretizations_oracle_CONV" "failed to resolve single jump target"
    end)
    ALL_CONV
    (fn tm =>
      let
        val t_o = (!birs_symbval_concretizations_oracle_ext_CONV) tm;
      in
        if isSome t_o then valOf t_o else
        raise ERR "birs_symbval_concretizations_oracle_CONV" "birs_symbval_concretizations_oracle_ext_CONV couldn't fix the concretization"
      end);

val birs_eval_label_exp_def_Label = CONJUNCT1 birs_eval_label_exp_def;
val birs_eval_label_exp_def_Exp = CONJUNCT2 birs_eval_label_exp_def;
val case_to_concretizations =
  REWRITE_CONV [optionTheory.option_case_def, pairTheory.pair_CASE_def, optionTheory.THE_DEF] THENC
  LIST_BETA_CONV THENC
  LIST_BETA_CONV THENC
  LIST_BETA_CONV THENC
  REWRITE_CONV [bir_valuesTheory.bir_type_t_case_def] THENC
  LIST_BETA_CONV;
fun birs_eval_label_exp_CONV tm =
  if (not o is_birs_eval_label_exp) tm then
    raise (print_term tm; ERR "birs_eval_label_exp_CONV" "something is not right here, expect a birs_eval_label_exp")
  else if (bir_programSyntax.is_BLE_Label o (fn (x,_,_) => x) o dest_birs_eval_label_exp) tm then
    REWR_CONV birs_eval_label_exp_def_Label tm
  else (
    REWR_CONV birs_eval_label_exp_def_Exp THENC
    GEN_match_conv is_birs_eval_exp (birs_eval_exp_CONV) THENC
    case_to_concretizations THENC

    (* here we should have either NONE or SOME and a set that is either trivially singleton of a constant or we have to resolve it into a set of constants *)
    (fn tm_ =>
      if optionSyntax.is_none tm_ then ALL_CONV tm_ else
      if optionSyntax.is_some tm_ then RAND_CONV (
        (fn tm => if is_birs_symbval_concretizations tm then birs_symbval_concretizations_oracle_CONV tm else ALL_CONV tm) THENC
        (* here we should have a simple set of constants *)
        (fn tm => if is_plain_jumptarget_set tm then ALL_CONV tm else
          (print_term tm;
          raise ERR "birs_eval_label_exp_CONV" "could not resolve the jump targets"))
      ) tm_ else
      raise (print_term tm; print_term tm_; ERR "birs_eval_label_exp_CONV" "something is not right here, should be NONE or SOME"))
  ) tm;


fun birs_exec_step_CONV_pre t =
let
  val bprog_tm = (rand o rator) t;
  (*val _ = print_term bprog_tm;*)
  val pc = (dest_birs_state_pc o rand) t;
  val pc_string = aux_moveawayLib.pc_to_string pc;
  val state_size = (get_birs_state_size o rand) t;
  val _ = print ("symb state exp sizes = " ^ (Int.toString state_size) ^ "\n");
  (*val _ = print ("symb state term size = " ^ ((Int.toString o term_size) t) ^ "\n");*)
  val _ = print ("pc = " ^ pc_string ^ "\n");
  val _ = if is_const bprog_tm then () else
          raise ERR "birs_exec_step_CONV" "program term is not a constant";
in
  bprog_tm
end;

val birs_state_env_CONV =
  PATH_CONV "rlrr";
val birs_state_pcond_CONV =
  PATH_CONV "rrrlrr";
fun birs_exec_step_CONV_p1 (bprog_tm, t) = (* get the statement *)
  let
    val st_tm = (rand) t;
    val (pc_tm,env_tm,_,pcond_tm) = (dest_birs_state) st_tm;
    val pc_lookup_thm = birs_auxLib.pc_lookup_fun (bprog_tm, pc_tm);
    (*val _ = print_thm pc_lookup_thm;*)

    val (*abbr_thm, eq_thms*) (env_eq_thm, pcond_eq_thm) = abbr_app (t, env_tm, pcond_tm);
    val eq_thms = [env_eq_thm, pcond_eq_thm];
    val abbr_thm =
      RAND_CONV (
        birs_state_env_CONV (K (GSYM env_eq_thm)) THENC
        birs_state_pcond_CONV (K (GSYM pcond_eq_thm))
      ) t;
    (*val _ = print_thm abbr_thm;*)
    val conv = (
      REWR_CONV birs_exec_step_def THENC
      REWRITE_CONV [
        bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM, pc_lookup_thm] THENC
      ITE_CONV (REWR_CONV birs_state_is_terminated_def THENC REWRITE_CONV [
        bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM]) THENC
      TRY_CONV (REWRITE_CONV [optionTheory.option_case_def] THENC LIST_BETA_CONV)
      );
    val res = (CONV_RULE (RHS_CONV conv)) abbr_thm;
    (*
    val res = abbr_rev (res, env_tm, pcond_tm);
    *)
    (*
    val _ = print_thm abbr_thm;
    val _ = print_thm res;
    val _ = raise ERR "" "";
    *)
  in
    (res, env_tm, pcond_tm, eq_thms)
  end;

fun continue_eq_rule c = CONV_RULE (RHS_CONV c);
fun restr_conv_eq_rule consts c th =
  let
    val fix_th = continue_eq_rule (RESTR_EVAL_CONV consts) th;
  in
    continue_eq_rule c fix_th
  end;

(*
val test_term =
``birs_update_env
        ("MEM8",
         BExp_Store (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
           (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))) BEnd_LittleEndian
           (BExp_Load (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64))
        (birs_update_env
           ("x14",
            BExp_Load (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64)
           (birs_update_env
              ("x15",
               BExp_Load (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "sy_x10" (BType_Imm Bit64)))
                 BEnd_LittleEndian Bit64)
              (birs_gen_env
                 [("x14",BExp_Den (BVar "sy_x14" (BType_Imm Bit64)));
                  ("MEM8",BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)));
                  ("x11",BExp_Den (BVar "sy_x11" (BType_Imm Bit64)));
                  ("x15",BExp_Den (BVar "sy_x15" (BType_Imm Bit64)));
                  ("x10",BExp_Den (BVar "sy_x10" (BType_Imm Bit64)));
                  ("x1",BExp_Den (BVar "sy_x1" (BType_Imm Bit64)))])))``;
is_birs_update_env test_term;
*)

val firstcase_pre =
  REWRITE_CONV [birs_exec_stmtB_def, birs_exec_stmt_assign_def, birs_exec_stmt_assert_def, birs_exec_stmt_assume_def, birs_exec_stmt_observe_def];
val firstcase =
  REWRITE_CONV [optionTheory.option_case_def, pairTheory.pair_CASE_def, birs_state_set_typeerror_def] THENC
  LIST_BETA_CONV THENC
  LIST_BETA_CONV THENC
  LIST_BETA_CONV THENC
  REWRITE_CONV [pairTheory.SND, optionTheory.THE_DEF, bir_valuesTheory.bir_type_t_case_def] THENC
  LIST_BETA_CONV THENC
  REWRITE_CONV [bir_immTheory.bir_immtype_t_case_def];
fun birs_gen_env_CONV eq_thms =
  RATOR_CONV (deabbr_CONV eq_thms) THENC
  REPEATC (
    REWR_CONV birs_gen_env_GET_thm THENC
    CHANGED_CONV
      (ITE_CONV aux_setLib.bir_varname_EQ_CONV)
  ) THENC
  TRY_CONV (REWR_CONV birs_gen_env_GET_NULL_thm);

val birs_update_env_P_CONV =
  BETA_CONV THENC
  NEG_CONV (
    LHS_CONV (
      REWR_CONV pairTheory.FST
    ) THENC
    aux_setLib.bir_varname_EQ_CONV
  );

val birs_update_env_CONV =
  REWR_CONV birs_update_env_thm THENC
  RAND_CONV (RAND_CONV (aux_setLib.FILTER_CONV birs_update_env_P_CONV));

fun birs_exec_stmtB_CONV eq_thms tm =
let
  (* evaluate to symbolic expression *)
  val res_b_eval_exp = (* restr_conv_eq_rule *)
    (firstcase_pre THENC
      GEN_match_conv is_birs_eval_exp (RAND_CONV (unabbrev_conv eq_thms) THENC birs_eval_exp_CONV) THENC
      firstcase
    ) tm
  ;
in
 if (can pred_setSyntax.strip_set o rhs o concl) res_b_eval_exp then res_b_eval_exp else
 let
  (* lookup type of previous symbolic expression, if is assignment statement *)
  val res_b_option_bind =
    CONV_RULE (RHS_CONV (
      ITE_CONV (
        RAND_CONV (LHS_CONV (
          LAND_CONV (RATOR_CONV (unabbrev_conv eq_thms)) THENC
          RATOR_CONV (RAND_CONV (
            RAND_CONV (REWR_CONV bir_envTheory.bir_var_name_def) THENC
            birs_gen_env_CONV eq_thms
          )) THENC
          OPTION_BIND_CONV THENC
          type_of_bir_exp_CONV
        )) THENC
        EVAL
      )
    )) res_b_eval_exp;

  (* update symbolic environment, if is assignment statement *)
  val res_b_update_env =
    CONV_RULE (RHS_CONV
    (*
   restr_conv_eq_rule
    [birs_update_env_tm]*)
    ( GEN_match_conv is_birs_update_env (
      LAND_CONV (LAND_CONV (REWR_CONV bir_envTheory.bir_var_name_def)) THENC
      RAND_CONV (unabbrev_conv eq_thms) THENC
      birs_update_env_CONV
    )))
    res_b_option_bind;

(*
  val _ = print "\neval expression\n";
  val _ = (print_term o concl) res_b_eval_exp;
  val _ = print "\neval option_bind\n";
  val _ = (print_term o concl) res_b_option_bind;
  val _ = print "\neval update env\n";
  val _ = (print_term o concl) res_b_update_env;
  val _ = print "\nresult\n";
  val _ = (print_term o concl) res;
  val _ = raise ERR "" "";
*)

in
  res_b_update_env
end end;

(*
val birs_state_pc_update_thm = prove(“
  !pc env status pcond f.
  <|bsst_pc := pc;
    bsst_environ := env; bsst_status := status;
    bsst_pcond := pcond|> with bsst_pc updated_by f =
  <|bsst_pc := f pc;
    bsst_environ := env; bsst_status := status;
    bsst_pcond := pcond|>
”, rpt GEN_TAC >> EVAL_TAC);

val birs_state_pcond_update_thm = prove(“
  !pc env status pcond f.
  <|bsst_pc := pc;
    bsst_environ := env; bsst_status := status;
    bsst_pcond := pcond|> with bsst_pcond updated_by f =
  <|bsst_pc := pc;
    bsst_environ := env; bsst_status := status;
    bsst_pcond := f pcond|>
”, rpt GEN_TAC >> EVAL_TAC);

val K_o_thm = prove(“
  !x y.
  (K x) o (K y) = K x
”,
  REWRITE_TAC [Once boolTheory.FUN_EQ_THM] >>
  rpt GEN_TAC >>
  EVAL_TAC
);
*)

val bir_pc_index_update_thm = prove(“
  !l i f.
  <|bpc_label := l; bpc_index := i|> with bpc_index updated_by f =
  <|bpc_label := l; bpc_index := f i|>
”, rpt GEN_TAC >> EVAL_TAC);

val birs_state_thms = type_rws ``:birs_state_t``;
val birs_state_thms_filtd1 = List.take(birs_state_thms, 7);
val birs_state_thms_filtd = (hd birs_state_thms_filtd1)::(List.drop(birs_state_thms_filtd1, 3));
val birs_state_thms_filtd1 = List.take(birs_state_thms, 7);
val birs_state_thms_filtd2 = (hd birs_state_thms_filtd1)::(List.drop(birs_state_thms_filtd1, 3));
val birs_state_thms_filtd3 = (List.take(birs_state_thms_filtd2, 2))@(List.drop(birs_state_thms_filtd2, 4));
val birs_state_thms_filtd = [hd birs_state_thms_filtd3, (last) birs_state_thms_filtd3];
val birs_state_thms_filtd = birs_state_thms_filtd3;

val rewrite_conv_state =
  REWRITE_CONV ((*[(*bir_symbTheory.birs_state_t_accfupds, *)
(*birs_state_pc_update_thm, birs_state_pcond_update_thm,*) ](@*)birs_state_thms_filtd);
val rewrite_conv_pc =
  REWRITE_CONV [bir_programTheory.bir_pc_next_def, bir_pc_index_update_thm];
val K_o_THM_conj2 =
  CONJUNCT2 combinTheory.K_o_THM

fun REWR_MATCH_REC_CONV is_f t tm =
  GEN_match_conv is_f (
    REWR_CONV t THENC
    REWR_MATCH_REC_CONV is_f t
  ) tm;

(*  RESTR_EVAL_CONV [birs_eval_exp_tm, birs_update_env_tm] *)
fun birs_exec_step_CONV_B eq_thms =
  REWRITE_CONV [birs_exec_stmt_def] THENC
  RAND_CONV (birs_exec_stmtB_CONV eq_thms) THENC
  REWR_CONV LET_THM THENC
  LIST_BETA_CONV THENC
  pred_setLib.IMAGE_CONV
    (
      LIST_BETA_CONV THENC
      ITE_CONV (REWR_CONV birs_state_is_terminated_def THENC REWRITE_CONV [
        bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM] THENC EVAL) THENC
(* cleanup state record assignments *)
(rewrite_conv_state) THENC
(*fix pc_next*)
GEN_match_conv (combinSyntax.is_o) (
  REWR_CONV K_o_THM_conj2 THENC
  rewrite_conv_pc) THENC
GEN_match_conv (numSyntax.is_suc) (numLib.REDUCE_CONV) THENC
(* other stuff *)
(*combinSyntax.is_K “K 1 3”*)
REWR_MATCH_REC_CONV combinSyntax.is_K combinTheory.K_THM
(*THENC
(SIMP_CONV (pure_ss++birs_state_ss) [K_o_thm])
*)
(*
(fn x => (print "\nbefore simp:\n"; print_term x; print "\n\n"; REFL x)) THENC
REWRITE_CONV ([(*bir_symbTheory.birs_state_t_accfupds, *)combinTheory.K_THM, bir_programTheory.bir_pc_next_def,
(*birs_state_pc_update_thm, birs_state_pcond_update_thm,*) bir_pc_index_update_thm]@birs_state_thms) THENC
GEN_match_conv (numSyntax.is_suc) (numLib.REDUCE_CONV) THENC
Profile.profile "exec_step_CONV_B_p0_state_simp" (SIMP_CONV (pure_ss++birs_state_ss) [K_o_thm])) THENC
(fn x => (print "\nafter simp:\n"; print_term x; print "\n\n"; REFL x))
*)
      (*REWRITE_CONV eq_thms THENC*)
      (*Profile.profile "exec_step_CONV_B_p0_eval1" (SIMP_CONV (pure_ss++birs_state_ss) [combinTheory.K_THM, bir_programTheory.bir_pc_next_def]) THENC*)
      (*(fn x => (print_term x; print "\n\n"; REFL x))*)
      (*Profile.profile "exec_step_CONV_B_p0_eval2" (RESTR_EVAL_CONV [birs_gen_env_tm])*)
    )
    (aux_setLib.birs_state_EQ_CONV);
val birs_exec_step_CONV_B = fn x => Profile.profile "exec_step_CONV_B" (birs_exec_step_CONV_B x);

local
  val MEM_tm = ``MEM : bir_label_t -> bir_label_t list -> bool``;

  val birs_exec_stmt_cjmp_tm = ``birs_exec_stmt_cjmp``; (* TODO: type here! *)
  val birs_exec_stmt_cjmp_str = "birs_exec_stmt_cjmp";
  fun is_birs_exec_stmt_cjmp tm =
    is_comb tm andalso
    (is_const o fst o strip_comb) tm andalso
    ((fst o dest_const o fst o strip_comb) tm) = birs_exec_stmt_cjmp_str;

  val birs_exec_stmt_jmp_to_label_CONV =
    REWR_CONV birs_exec_stmt_jmp_to_label_def THENC
    ITE_CONV (fn t => birs_auxLib.MEM_proglabels_fun (t)) THENC
    EVAL (* TODO: bir_block_pc_def, "with bsst_status" update *);

  val birs_exec_stmt_jmp_CONV =
    let
      val case_conv =
        REWRITE_CONV [optionTheory.option_case_def, birs_state_set_typeerror_def];
    in
     fn eq_thms =>
      REWR_CONV birs_exec_stmt_jmp_def THENC
      (GEN_match_conv is_birs_eval_label_exp (
        LAND_CONV (unabbrev_conv eq_thms) THENC
        RAND_CONV (unabbrev_conv eq_thms) THENC
        (birs_eval_label_exp_CONV)
      )) THENC
      case_conv THENC
      TRY_CONV (
        LIST_BETA_CONV THENC
        pred_setLib.IMAGE_CONV
          (birs_exec_stmt_jmp_to_label_CONV)
          (aux_setLib.birs_state_EQ_CONV))
    end;

(*
val exec_jmp_stmt = “birs_exec_stmt_jmp bir_balrob_prog
  (BLE_Label (BL_Address (Imm32 0x100013B6w)))
  <|bsst_pc :=
      <|bpc_label := BL_Address (Imm32 0x100013B4w); bpc_index := 5|>;
    bsst_environ := temp_env_abbr; bsst_status := BST_Running;
    bsst_pcond := temp_pcond_abbr|>”;
birs_exec_stmt_jmp_CONV [] exec_jmp_stmt
*)

  val birs_exec_stmt_cjmp_CONV =
    let
      val case_to_union =
        REWRITE_CONV [optionTheory.option_case_def, pairTheory.pair_CASE_def, birs_state_set_typeerror_def] THENC
        LIST_BETA_CONV THENC
        LIST_BETA_CONV THENC
        LIST_BETA_CONV THENC
        REWRITE_CONV [pairTheory.SND, optionTheory.THE_DEF, bir_valuesTheory.bir_type_t_case_def] THENC
        LIST_BETA_CONV THENC
        REWRITE_CONV [bir_immTheory.bir_immtype_t_case_def];
    in
     fn eq_thms =>
      REWR_CONV birs_exec_stmt_cjmp_def THENC      
      (GEN_match_conv is_birs_eval_exp (
        RAND_CONV (unabbrev_conv eq_thms) THENC
        birs_eval_exp_CONV
      )) THENC
      case_to_union THENC
      (LAND_CONV (birs_exec_stmt_jmp_CONV eq_thms) THENC
      RAND_CONV (birs_exec_stmt_jmp_CONV eq_thms) THENC
      pred_setLib.UNION_CONV (aux_setLib.birs_state_EQ_CONV))
    end;

(*
val exec_cjmp_stmt = “birs_exec_stmt_cjmp bir_balrob_prog
  (BExp_Den (BVar "PSR_C" (BType_Imm Bit1)))
  (BLE_Label (BL_Address (Imm32 0x100013BEw)))
  (BLE_Label (BL_Address (Imm32 0x100013C2w)))
  <|bsst_pc :=
      <|bpc_label := BL_Address (Imm32 0x100013BCw); bpc_index := 2|>;
    bsst_environ := temp_env_abbr; bsst_status := BST_Running;
    bsst_pcond := temp_pcond_abbr|>”;

val eq_thms = [ASSUME “temp_env_abbr = birs_gen_env
               [("PSR_C",BExp_Const (Imm1 0x1w))]”];

birs_exec_stmt_cjmp_CONV eq_thms exec_cjmp_stmt;
*)

in
  fun birs_exec_step_CONV_E eq_thms =
    REWRITE_CONV [birs_exec_stmt_def, birs_exec_stmtE_def] THENC
    (fn tm =>
      if is_birs_exec_stmt_cjmp tm then
        birs_exec_stmt_cjmp_CONV eq_thms tm
      else
        birs_exec_stmt_jmp_CONV eq_thms tm
    );
(*
val tm_step_e_thm = ASSUME “A =birs_exec_stmt bir_balrob_prog
  (BStmtE (BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x100013B6w)))))
  <|bsst_pc :=
      <|bpc_label := BL_Address (Imm32 0x100013B4w); bpc_index := 5|>;
    bsst_environ := temp_env_abbr; bsst_status := BST_Running;
    bsst_pcond := temp_pcond_abbr|>”;

birs_exec_step_CONV_E (T, (tm_step_e_thm, []));
*)
    (*
    let
      val =
      val res_e_eval_exp = restr_conv_eq_rule
        [bprog_tm, birs_exec_stmt_jmp_tm, birs_eval_exp_tm]
        (GEN_match_conv is_birs_eval_exp (REWRITE_CONV eq_thms THENC birs_eval_exp_CONV))
        res_p1;

      val res_e_eval_label = restr_conv_eq_rule
        [bprog_tm, birs_eval_label_exp_tm]
        (GEN_match_conv is_birs_eval_label_exp (REWRITE_CONV eq_thms THENC birs_eval_label_exp_CONV))
        res_e_eval_exp;
      
      val res_e_mem_proglabels = restr_conv_eq_rule
        [bprog_tm, MEM_tm]
        (GEN_match_conv listSyntax.is_mem )
        res_e_eval_label;

      val res_e_finish = continue_eq_rule
        EVAL
        res_e_mem_proglabels;

      (*
      val _ = print_thm res_e_eval_label;
      val _ = raise ERR "" "";
      *)
    in
      res_e_finish
    end;
    *)
  val birs_exec_step_CONV_E = fn x => Profile.profile "exec_step_CONV_E" (birs_exec_step_CONV_E x);
end;

fun birs_exec_step_CONV t =
  let
    open bir_programSyntax;
    val bprog_tm = birs_exec_step_CONV_pre t;
    val (res_p1, env_tm, pcond_tm, eq_thms) = birs_exec_step_CONV_p1 (bprog_tm, t);
    (*val _ = (print "P1: GET STATEMENT\n"; print_thm res_p1);*)
    val stmt_tm = (rand o rator o rhs o concl) res_p1;
    (*val _ = print_term stmt_tm;
      val stmt_type_tm = (rator) stmt_tm;
      val _ = print_term stmt_type_tm;*)
    val res =
      if is_BStmtB stmt_tm then
        CONV_RULE (RHS_CONV (birs_exec_step_CONV_B eq_thms)) res_p1
      else if is_BStmtE stmt_tm then
        CONV_RULE (RHS_CONV (birs_exec_step_CONV_E eq_thms)) res_p1
      else
        raise ERR "birs_exec_step_CONV" "something is wrong, should be BStmtB or BStmtE here";
    val res_unabbr = abbr_rev (res, env_tm, pcond_tm);
  in
    res_unabbr
  end;
val birs_exec_step_CONV = Profile.profile "exec_step_CONV" birs_exec_step_CONV;



in

val birs_eval_exp_CONV = birs_eval_exp_CONV;


(* bir symbolic execution steps *)
(* ----------------------------------------------- *)
fun birs_exec_step_CONV_fun tm =
  let
    val last_pc = ref T;
    val last_stmt = ref T;
    val birs_step_thm =
      GEN_match_conv
      (is_birs_exec_step)
      (fn exec_tm => (
        RAND_CONV (check_CONV birs_state_is_norm ("birs_exec_step_CONV_fun", "the state is not as expected")) THENC

        (fn tm_i =>
          let
            val (bprog_tm, st_i) = dest_birs_exec_step tm_i;
            val (pc, _, _, _) = dest_birs_state st_i;
            val _ = last_pc := pc;
            val _ = last_stmt := (snd o dest_eq o concl o birs_auxLib.pc_lookup_fun) (bprog_tm, pc); (* TODO: avoid pc_lookup_fun twice *)
            val timer_exec_step = holba_miscLib.timer_start 0;
            (* TODO: optimize *)
            val birs_exec_thm = birs_exec_step_CONV tm_i;
            val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> executed step in " ^ delta_s ^ "\n")) timer_exec_step;
          in
            birs_exec_thm
          end) THENC

        (check_CONV birs_states_is_norm ("birs_exec_step_CONV_fun", "the produced theorem is not evaluated enough")
          handle e => (print "\n[[[[\n"; print_term exec_tm; print "\n]]]]\n"; raise e))
        ) exec_tm)
      tm;
  in
    (birs_step_thm, (!last_pc, !last_stmt))
  end;

val birs_symbval_concretizations_oracle_ext_CONV = birs_symbval_concretizations_oracle_ext_CONV;

val birs_update_env_CONV = birs_update_env_CONV;

end (* local *)

end (* struct *)
