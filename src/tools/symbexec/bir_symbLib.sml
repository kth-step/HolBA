structure bir_symbLib =
struct

local

open HolKernel Parse boolLib bossLib;
open computeLib;

open bir_exp_substitutionsTheory;
open bir_expTheory;

open bir_symbTheory;

  (* error handling *)
  val libname = "bir_symbLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

(* TODO: we really have to put this in a central place... *)
 fun type_of_bir_exp_CONV term =
    (* Manual test
    val term = ``
      BExp_BinExp BIExp_Plus
        (BExp_Const (Imm32 20w))
        (BExp_Const (Imm32 22w))
    ``;
    val thm = type_of_bir_exp_CONV ``type_of_bir_exp ^term``;
    *)
    let
      open bir_immTheory
      open bir_valuesTheory
      open bir_envTheory
      open bir_exp_memTheory
      open bir_bool_expTheory
      open bir_extra_expsTheory
      open bir_nzcv_expTheory
      open bir_interval_expTheory;
      open bir_typing_expTheory;
      val type_of_bir_exp_thms = [
        type_of_bir_exp_def,
        bir_var_type_def,
        bir_type_is_Imm_def,
        type_of_bir_imm_def,
        BExp_Aligned_type_of,
        BExp_unchanged_mem_interval_distinct_type_of,
        bir_number_of_mem_splits_REWRS,
        BType_Bool_def,
        bir_exp_true_def,
        bir_exp_false_def,
        BExp_MSB_type_of,
        BExp_nzcv_ADD_DEFS,
        BExp_nzcv_SUB_DEFS,
        n2bs_def,
        BExp_word_bit_def,
        BExp_Align_type_of,
        BExp_ror_type_of,
        BExp_LSB_type_of,
        BExp_word_bit_exp_type_of,
        BExp_ADD_WITH_CARRY_type_of,
        BExp_word_reverse_type_of,
        BExp_ror_exp_type_of,
        bir_immtype_of_size_def
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end
      handle _ => raise ERR "type_of_bir_exp_CONV" "conversion failed";

(*
val bexp_term = ``type_of_bir_exp (BExp_BinPred BIExp_LessOrEqual
          (BExp_Den (BVar "countw" (BType_Imm Bit64)))
          (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))``;
type_of_bir_exp_DIRECT_CONV bexp_term
*)
 fun type_of_bir_exp_DIRECT_CONV term =
   let
     open optionSyntax;
     open bir_valuesSyntax;
     open bir_typing_expSyntax;

     val _ = if is_type_of_bir_exp term then () else
               raise ERR "type_of_bir_exp_DIRECT_CONV" "cannot handle term";

     val thm = type_of_bir_exp_CONV term;

     val result = (snd o dest_eq o concl) thm;
     val _ = if is_none result orelse
                (is_some result andalso
                 ((fn x => is_BType_Imm x orelse is_BType_Mem x) o dest_some) result) then () else
               raise ERR "type_of_bir_exp_DIRECT_CONV" "didn't reach the result";
   in thm end
   handle _ => raise ERR "type_of_bir_exp_DIRECT_CONV" ("ill-typed term: " ^ Parse.term_to_string term);


(* TODO: this is stolen from exec tool *)
  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;

in

(*
birs_senv_typecheck_CONV test_term_birs_senv_typecheck
*)
val is_birs_senv_typecheck =
  ((fn x => (identical ``birs_senv_typecheck`` o fst) x andalso ((fn l => l = 2) o length o snd) x) o strip_comb);
val birs_senv_typecheck_CONV = (
  RESTR_EVAL_CONV [``type_of_bir_exp``] THENC
  GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
  EVAL
);

(*
CBV_CONV (new_compset [
  birs_eval_exp_subst_def,
  bir_exp_subst_def,
  bir_exp_subst_var_def,
  bir_typing_expTheory.bir_vars_of_exp_def,
  finite_mapTheory.FLOOKUP_DEF
]) test_term_birs_eval_exp_subst
*)

(*
birs_eval_exp_CONV test_term_birs_eval_exp
*)
val birs_eval_exp_CONV = (
  CBV_CONV (new_compset [birs_eval_exp_def]) THENC
  GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
  GEN_match_conv (is_birs_senv_typecheck) (birs_senv_typecheck_CONV) THENC
  EVAL
);

(*
val restr_consts = [``birs_eval_exp``, ``LET``];
RESTR_EVAL_CONV restr_consts test_term
*)


(*
birs_exec_step_CONV test_term
*)
(* TODO: add purging of stale environment mappings *)
val birs_exec_step_CONV = (
  RESTR_EVAL_CONV [``birs_eval_exp``] THENC
  GEN_match_conv (identical ``birs_eval_exp`` o fst o strip_comb) (birs_eval_exp_CONV) THENC
  EVAL
);


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

val bprog1 = ``
BirProgram [
           <|bb_label := BL_Address_HC (Imm32 2826w) "B084 (sub sp, #16)";
             bb_statements :=
               [BStmt_Assert
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>
] : 'obs_type bir_program_t
``;

val bprog2 = ``
BirProgram [
           <|bb_label := BL_Address_HC (Imm32 2826w) "B084 (sub sp, #16)";
             bb_statements :=
               [BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>
] : 'obs_type bir_program_t
``;

val birs_state_init = ``<|
  bsst_pc       := bir_block_pc (BL_Address (Imm32 2826w));
  bsst_environ  := ("R7"         =+ (SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))))
                   (("SP_process" =+ (SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                      (("countw"     =+ (SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))))
                       (K NONE)
                   ));
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_Const (Imm1 1w)
|>``;

val test_term_1 = ``birs_exec_step ^bprog1 ^birs_state_init``;
val test_term_2 = ``birs_exec_step ^bprog2 ^birs_state_init``;

val _ = (print_term o concl) (birs_exec_step_CONV test_term_1);
val _ = (print_term o concl) (birs_exec_step_CONV test_term_2);

end (* local *)

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

end (* struct *)
