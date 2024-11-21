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
(snd o dest_comb o fst o dest_comb o fst o dest_comb o snd o dest_comb) test_term

val test_term = (fst o dest_eq o snd o strip_forall o concl) bir_symbTheory.birs_exec_step_def;
(snd o dest_comb) test_term
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

val subs_tm = (snd o dest_comb o fst o dest_comb o fst o dest_eq o concl) test_thm;
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

local
  open bir_expSyntax;
in
 fun is_bir_exp t =
  type_of t = bir_exp_t_ty;

 fun bir_exp_size t =
  if is_BExp_Const t then
     1
  else if is_BExp_MemConst t then
     1
  else if is_BExp_Den t then
     1
  else if is_BExp_Cast t then
   let
     val (_,x,_) = dest_BExp_Cast t;
   in
     1 + bir_exp_size x
   end
  else if is_BExp_UnaryExp t then
   let
     val (_,x) = dest_BExp_UnaryExp t;
   in
     1 + bir_exp_size x
   end
  else if is_BExp_BinExp t then
   let
     val (_,x1,x2) = dest_BExp_BinExp t;
   in
     1 + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_BinPred t then
   let
     val (_,x1,x2) = dest_BExp_BinPred t;
   in
     1 + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_MemEq t then
   let
     val (x1,x2) = dest_BExp_MemEq t;
   in
     1 + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_IfThenElse t then
   let
     val (c,x1,x2) = dest_BExp_IfThenElse t;
   in
     1 + bir_exp_size c + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_Load t then
   let
     val (mem_e,a_e,_,_) = dest_BExp_Load t;
   in
     1 + bir_exp_size mem_e + bir_exp_size a_e
   end
  else if is_BExp_Store t then
   let
     val (mem_e,a_e,_,v_e) = dest_BExp_Store t;
   in
     1 + bir_exp_size mem_e + bir_exp_size a_e + bir_exp_size v_e
   end
  else if is_BExp_IntervalPred t then
   let
     val (ref_e, lim_tm) = dest_BExp_IntervalPred t;
     val (l_e, h_e) = pairSyntax.dest_pair lim_tm;
   in
     1 + bir_exp_size ref_e + bir_exp_size l_e + bir_exp_size h_e
   end
(*
  else if is_... t then
   let
     val (_,x1,...) = dest_... t;
   in
     1 + bir_exp_size x1 + ...
   end
*)
  else raise ERR "bir_exp_size" ("unknown BIR expression " ^ (term_to_string t));
end

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

fun birs_senv_typecheck_CONV eq_thms = (
  RESTR_EVAL_CONV [bir_typing_expSyntax.type_of_bir_exp_tm] THENC
  REWRITE_CONV eq_thms THENC
  type_of_bir_exp_CONV THENC
  EVAL
);
val birs_senv_typecheck_CONV = fn x => Profile.profile "senv_typecheck_CONV" (birs_senv_typecheck_CONV x);


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


fun birs_eval_exp_CONV_p1 t =
   let
     val tm = (dest_birs_gen_env o snd o dest_birs_eval_exp) t;
     val (thm, eq_thms) = abbr_birs_gen_env 0 [] I tm;
   in
     (* rewrite the environment list *)
     (RAND_CONV (RAND_CONV (K thm)) t, eq_thms)
   end
   handle e => (print_term t; raise wrap_exn "birs_eval_exp_CONV_p1" e);

val birs_eval_exp_CONV_p2 =
  REWRITE_CONV [birs_eval_exp_def] THENC
  type_of_bir_exp_CONV;

fun birs_eval_exp_CONV_p3 eq_thms =
  GEN_match_conv (is_birs_senv_typecheck) (birs_senv_typecheck_CONV eq_thms);

(* TODO: can possibly improve this,
     for example by only taking the environment into the expressions where there are symbol lookups,
     could even work with a cache of lookup theorems for the present symbols *)
fun birs_eval_exp_CONV_p4 eq_thms =
  EVAL THENC
  REWRITE_CONV eq_thms THENC
  EVAL;

fun birs_eval_exp_CONV t = (
  let
    val (thm_p1, eq_thms) = birs_eval_exp_CONV_p1 t;
    (*val _ = print_thm thm_p1;*)
    val thm_p2 = CONV_RULE (RAND_CONV (birs_eval_exp_CONV_p2)) thm_p1;
    val thm_p3 = CONV_RULE (RAND_CONV (birs_eval_exp_CONV_p3 eq_thms)) thm_p2;
    val thm_p4 = CONV_RULE (RAND_CONV (birs_eval_exp_CONV_p4 eq_thms)) thm_p3;
    val thm_p4rev = rev_birs_gen_env (thm_p4, eq_thms);
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
    val l = pred_setSyntax.strip_set tm;
  in
    List.all (fn e_tm =>
      bir_programSyntax.is_BL_Address e_tm andalso
      bir_immSyntax.gen_is_Imm (bir_programSyntax.dest_BL_Address e_tm)) l
  end handle _ => false;

val birs_symbval_concretizations_oracle_CONV =
  (fn tm => if is_birs_symbval_concretizations tm then REFL tm else
   (print_term tm;
    raise ERR "birs_symbval_concretizations_oracle_CONV" "something is not right here, expect a birs_symbval_concretizations")) THENC
  (fn tm => let
    val vaex_tm = (snd o dest_comb) tm;
    val pcond_tm = (snd o dest_comb o fst o dest_comb) tm;
    val pcond_is_sat = bir_smtLib.bir_smt_check_sat false pcond_tm;
    val pcond_sat_thm =
     if pcond_is_sat then
       mk_oracle_thm "BIRS_SIMP_LIB_Z3" ([], ``?i. birs_interpret_fun i ^pcond_tm = SOME bir_val_true``)
     else
       mk_oracle_thm "BIRS_SIMP_LIB_Z3" ([], ``!i. birs_interpret_fun i ^pcond_tm = SOME bir_val_false``);
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
   end);

val birs_eval_label_exp_CONV = (
  (fn tm => if is_birs_eval_label_exp tm then REFL tm else
   raise ERR "birs_eval_label_exp_CONV" "something is not right here, expect a birs_eval_label_exp") THENC
  RESTR_EVAL_CONV [birs_eval_exp_tm, birs_gen_env_tm, birs_symbval_concretizations_tm] THENC
  GEN_match_conv is_birs_eval_exp (birs_eval_exp_CONV) THENC
  RESTR_EVAL_CONV [birs_symbval_concretizations_tm] THENC

(* here we should have either NONE or SOME and a set that is either trivially singleton of a constant or we have to resolve it into a set of constants *)
  (fn tm =>
    if optionSyntax.is_none tm then REFL tm else
    if optionSyntax.is_some tm then RAND_CONV (
      (fn tm => if is_birs_symbval_concretizations tm then birs_symbval_concretizations_oracle_CONV tm else REFL tm) THENC
      (* here we should have a simple set of constants *)
      (fn tm => if is_plain_jumptarget_set tm then REFL tm else
        (print_term tm;
         raise ERR "birs_eval_label_exp_CONV" "could not resolve the jump targets"))
    ) tm else
    raise ERR "birs_eval_label_exp_CONV" "something is not right here, should be NONE or SOME")
);


fun birs_exec_step_CONV_pre t =
let
  val bprog_tm = (snd o dest_comb o fst o dest_comb) t;
  (*val _ = print_term bprog_tm;*)
  val pc = (dest_birs_state_pc o snd o dest_comb) t;
  val pc_string = aux_moveawayLib.pc_to_string pc;
  val state_size = (get_birs_state_size o snd o dest_comb) t;
  val _ = print ("symb state exp sizes = " ^ (Int.toString state_size) ^ "\n");
  (*val _ = print ("symb state term size = " ^ ((Int.toString o term_size) t) ^ "\n");*)
  val _ = print ("pc = " ^ pc_string ^ "\n");
  val _ = if is_const bprog_tm then () else
          raise ERR "birs_exec_step_CONV" "program term is not a constant";
in
  bprog_tm
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
     val abbr_thm = REWRITE_CONV [GSYM (env_eq_thm), GSYM (pcond_eq_thm)] t;
  in
    (abbr_thm, [env_eq_thm, pcond_eq_thm])
  end;
 fun abbr_rev (res, env_tm, pcond_tm) =
  MP (MP ((INST [env_abbr_tm |-> env_tm, pcond_abbr_tm |-> pcond_tm] o DISCH_ALL) res) (REFL env_tm)) (REFL pcond_tm);
end;

(*
https://github.com/kth-step/HolBA/blob/master/src/tools/exec/bir_exec_blockLib.sml
https://github.com/kth-step/HolBA/blob/dev_symbnoproof_next/src/tools/symbexec/examples/binaries/binariesLib.sml
*)
fun pc_lookup_fallback_fun pc_lookup_t =
  let
     val _ = print "falling back to evaluation to get current statement";
     val pc_lookup_thm = EVAL pc_lookup_t;
  in
    pc_lookup_thm
  end;
fun pc_lookup_fun (bprog_tm, pc_tm) =
  let
     val pc_lookup_t = mk_bir_get_current_statement (bprog_tm, pc_tm);
  in
 case (!cur_stmt_lookup_fun) pc_tm of
     NONE =>  pc_lookup_fallback_fun pc_lookup_t
   | SOME x => if (identical pc_lookup_t o fst o dest_eq o concl) x then x else pc_lookup_fallback_fun pc_lookup_t
  end;

fun birs_exec_step_CONV_p1 (bprog_tm, t) = (* get the statement *)
  let
    val st_tm = (snd o dest_comb) t;
    val (pc_tm,env_tm,_,pcond_tm) = (dest_birs_state) st_tm;
    val pc_lookup_thm = pc_lookup_fun (bprog_tm, pc_tm);
    (*val _ = print_thm pc_lookup_thm;*)

    val (abbr_thm, eq_thms) = abbr_app (t, env_tm, pcond_tm);

    val rhs_tm = (snd o dest_eq o concl) abbr_thm;
    val res = (
            REWRITE_CONV [birs_exec_step_def, bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM, pc_lookup_thm]
      THENC RESTR_EVAL_CONV ([bprog_tm, birs_exec_stmt_tm])
      ) rhs_tm;
    val res = TRANS abbr_thm res;
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
val birs_exec_step_CONV_p1 = Profile.profile "exec_step_CONV_p1" birs_exec_step_CONV_p1;

(*
val birs_exec_step_CONV_p2 =
  GEN_match_conv is_birs_eval_label_exp birs_eval_label_exp_CONV;
val birs_exec_step_CONV_p2 = Profile.profile "exec_step_CONV_p2" birs_exec_step_CONV_p2;

val birs_exec_step_CONV_p4 =
  GEN_match_conv is_birs_eval_exp (birs_eval_exp_CONV) THENC
   REWRITE_CONV [birs_gen_env_GET_thm, birs_gen_env_GET_NULL_thm] THENC
   RESTR_EVAL_CONV [birs_update_env_tm, birs_gen_env_tm, bir_typing_expSyntax.type_of_bir_exp_tm] THENC
   type_of_bir_exp_CONV THENC
   RESTR_EVAL_CONV [birs_update_env_tm, birs_gen_env_tm];
val birs_exec_step_CONV_p4 = Profile.profile "exec_step_CONV_p4" birs_exec_step_CONV_p4;

val birs_exec_step_CONV_p5 =
  (* TODO: here better only convert the subexpression birs_update_env *)
   REWRITE_CONV [birs_update_env_thm] THENC
   RESTR_EVAL_CONV [birs_gen_env_tm];
val birs_exec_step_CONV_p5 = Profile.profile "exec_step_CONV_p5" birs_exec_step_CONV_p5;
*)

fun continue_eq_rule c = CONV_RULE (RAND_CONV c);
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

(*  RESTR_EVAL_CONV [birs_eval_exp_tm, birs_update_env_tm] *)
fun birs_exec_step_CONV_B (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms)) =
let
  (* evaluate to symbolic expression *)
  val res_b_eval_exp = (* restr_conv_eq_rule *)
   continue_eq_rule
    (GEN_match_conv is_birs_eval_exp (REWRITE_CONV eq_thms THENC birs_eval_exp_CONV))
    (continue_eq_rule
      (SIMP_CONV (pure_ss++birs_state_ss) [birs_exec_stmt_def, birs_exec_stmtB_def, birs_exec_stmt_assign_def, birs_exec_stmt_assert_def, birs_exec_stmt_assume_def, birs_exec_stmt_observe_def, combinTheory.K_THM])
      res_p1)
  ;

  (* lookup type of previous symbolic expression, if is assignment statement *)
  val res_b_option_bind =
    continue_eq_rule
      (GEN_match_conv is_OPTION_BIND (
        RATOR_CONV (RAND_CONV (
          RAND_CONV (REWR_CONV bir_envTheory.bir_var_name_def) THENC
          RATOR_CONV (REWR_CONV (hd eq_thms)) THENC
          REPEATC (
            REWR_CONV birs_gen_env_GET_thm THENC
            CHANGED_CONV
              (aux_setLib.ITE_CONV aux_setLib.bir_varname_EQ_CONV)
          ) THENC
          TRY_CONV (REWR_CONV birs_gen_env_GET_NULL_thm)
        )) THENC
        (*REWRITE_CONV [optionTheory.OPTION_BIND_def]*)
        (IFC
          (TRY_CONV (REWR_CONV (List.nth(CONJUNCTS optionTheory.OPTION_BIND_def, 1))))
          (ALL_CONV)
          (TRY_CONV (REWR_CONV (List.nth(CONJUNCTS optionTheory.OPTION_BIND_def, 0))))
        ) THENC
        type_of_bir_exp_CONV
      ))
      res_b_eval_exp;

  val birs_update_env_P_CONV =
    BETA_CONV THENC
    RAND_CONV (
      LHS_CONV (
        REWR_CONV pairTheory.FST
      ) THENC
      aux_setLib.bir_varname_EQ_CONV
    ) THENC
    REWRITE_CONV [boolTheory.NOT_CLAUSES];

  val birs_update_env_CONV =
    REWR_CONV birs_update_env_thm THENC
    RAND_CONV (RAND_CONV (listLib.FILTER_CONV birs_update_env_P_CONV));
    
  (* update symbolic environment, if is assignment statement *)
  val res_b_update_env =
   restr_conv_eq_rule
    [birs_update_env_tm]
    (GEN_match_conv is_birs_update_env (
      (*(fn t => (print "UPDATE ENV HERE\n"; print_term t; REFL t)) THENC*)
      RAND_CONV (REWR_CONV (hd eq_thms)) THENC
      birs_update_env_CONV
    ))
    res_b_option_bind;


  val res = (abbr_rev (res_b_update_env, env_tm, pcond_tm));

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
  res
end;
val birs_exec_step_CONV_B = Profile.profile "exec_step_CONV_B" birs_exec_step_CONV_B;

local
 val spec_conv_thm = (GSYM o GEN_ALL) (List.nth((CONJUNCTS o Q.SPEC `t`) boolTheory.EQ_CLAUSES,1));
in
 fun MEM_proglabels_fun (t, eq_thms) =
  let
    val l_tm = (snd o dest_comb o fst o dest_comb) t;
    val mem_thm_o = !cur_l_mem_lookup_fun l_tm;
  fun fallback_fun t =
    (print "falling back to evaluating membership of prog labels"; EVAL t);
  in
    case mem_thm_o of
     NONE =>  fallback_fun t
   | SOME x => if (identical t o concl) x then EQ_MP (SPEC t spec_conv_thm) x else fallback_fun t
  end;
end;

local
 val MEM_tm = ``MEM : bir_label_t -> bir_label_t list -> bool``;
in
 fun birs_exec_step_CONV_E (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms)) =
 let
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
    (GEN_match_conv listSyntax.is_mem (fn t => MEM_proglabels_fun (t, eq_thms)))
    res_e_eval_label;

  val res_e_finish = continue_eq_rule
    EVAL
    res_e_mem_proglabels;

  (*
  val _ = print_thm res_e_eval_label;
  val _ = raise ERR "" "";
  *)

  val res = (abbr_rev (res_e_finish, env_tm, pcond_tm));
 in
  res
 end;
end;

val birs_exec_step_CONV_E = Profile.profile "exec_step_CONV_E" birs_exec_step_CONV_E;

fun birs_exec_step_CONV t =
  let
    val bprog_tm = birs_exec_step_CONV_pre t;
    val (res_p1, env_tm, pcond_tm, eq_thms) = birs_exec_step_CONV_p1 (bprog_tm, t);
  (*val _ = (print "P1: GET STATEMENT\n"; print_thm res_p1);*)
    val stmt_tm = (snd o dest_comb o fst o dest_comb o snd o dest_eq o concl) res_p1;
  (*val _ = print_term stmt_tm;
    val stmt_type_tm = (fst o dest_comb) stmt_tm;
    val _ = print_term stmt_type_tm;*)
  in
  (
       if bir_programSyntax.is_BStmtB stmt_tm then
         birs_exec_step_CONV_B (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms))
       else if bir_programSyntax.is_BStmtE stmt_tm then
         birs_exec_step_CONV_E (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms))
       else
         raise ERR "birs_exec_step_CONV" "something is wrong, should be BStmtB or BStmtE here"
  )
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
            val _ = last_stmt := (snd o dest_eq o concl o pc_lookup_fun) (bprog_tm, pc); (* TODO: avoid pc_lookup_fun twice *)
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


end (* local *)

end (* struct *)
