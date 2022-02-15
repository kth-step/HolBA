structure birs_stepLib =
struct

local

open HolKernel Parse boolLib bossLib;
open computeLib;

open bir_exp_substitutionsTheory;
open bir_expTheory;

open bir_symbTheory;
open birs_auxTheory;

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
val birs_eval_exp_CONV = (
  CBV_CONV (new_compset [birs_eval_exp_def, birs_gen_env_thm, birs_gen_env_NULL_thm]) THENC
  GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
  GEN_match_conv (is_birs_senv_typecheck) (birs_senv_typecheck_CONV) THENC
  EVAL
);

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

birs_exec_step_CONV test_term
*)
val birs_exec_step_CONV = (
  RESTR_EVAL_CONV [``birs_eval_exp``, ``birs_update_env``, ``birs_gen_env``] THENC

  (* TODO: remove this patch later *)
  REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm] THENC

  GEN_match_conv (identical ``birs_eval_exp`` o fst o strip_comb) (birs_eval_exp_CONV) THENC
  REWRITE_CONV [birs_gen_env_GET_thm, birs_gen_env_GET_NULL_thm] THENC
  RESTR_EVAL_CONV [``birs_update_env``, ``birs_gen_env``] THENC

  (* TODO: here better only convert the subexpression birs_update_env *)
  REWRITE_CONV [birs_update_env_thm] THENC
  RESTR_EVAL_CONV [``birs_gen_env``]
);


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

in

val birs_eval_exp_CONV = birs_eval_exp_CONV;

(* bir symbolic execution steps *)
(* ----------------------------------------------- *)
(*
val bstate_tm = birs_state_init;
val bstate_tm = birs_state_mid;
*)
fun birs_exec_step_fun bprog_tm bstate_tm =
  let
    (* execution of steps *)
    val test_term = ``birs_exec_step ^bprog_tm ^bstate_tm``;
    (*
    val _ = (print_term o concl) (birs_exec_step_CONV test_term);
    *)
    val birs_exec_thm = birs_exec_step_CONV test_term;
  in
    birs_exec_thm
  end;


(* halt free programs *)
(* ----------------------------------------------- *)
(*
val bprog_tm = bprog;
*)
fun bir_prog_has_no_halt_fun bprog_tm =
  let
    (* prep step rule to be used *)
    (*
    val bir_prog_has_no_halt_prog_thm = store_thm(
       "bir_prog_has_no_halt_prog_thm", *)
    val bir_prog_has_no_halt_prog_thm = prove(``
      bir_prog_has_no_halt ^bprog_tm
    ``,
      EVAL_TAC
    );
  in
    bir_prog_has_no_halt_prog_thm
  end;

(*
val bprog_tm = bprog;
val no_halt_thm = (bir_prog_has_no_halt_fun bprog_tm)
*)
fun birs_rule_STEP_prog_fun bprog_tm no_halt_thm =
  let
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    val step_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_step_sound_thm;
    val birs_symb_step_sound_prog_thm =
      MP
        (SPEC (bprog_tm) (step_sound_thm))
        no_halt_thm;
    val birs_rule_STEP_thm =
      SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss) []
      (REWRITE_RULE [Once bir_symbTheory.bir_symb_rec_sbir_def]
         (MATCH_MP symb_rulesTheory.symb_rule_STEP_thm birs_symb_step_sound_prog_thm));
  in
    birs_rule_STEP_thm
  end;


(* plugging in the execution of steps to obtain sound structure *)
(* ----------------------------------------------- *)
local
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
  open birs_auxTheory;
in
fun birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm bstate_tm =
  let

    val birs_exec_thm = birs_exec_step_fun bprog_tm bstate_tm;
    val symb_state = ``birs_symb_to_symbst ^bstate_tm``;
    val lbl = (snd o dest_eq o concl o EVAL) ``(^bstate_tm).bsst_pc``;
    val lbls = ``{^lbl}``;

    val single_step_prog_thm =
      SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss++HolBACoreSimps.holBACore_ss)
        [birs_symb_symbst_pc_thm, pred_setTheory.IN_SING]
        (REWRITE_RULE [bir_symbTheory.birs_symb_to_from_symbst_thm, birs_exec_thm]
           (SPECL [symb_state, lbls] birs_rule_STEP_thm));
  in
    single_step_prog_thm
  end;
end;


(* extract information from a sound structure *)
(* ----------------------------------------------- *)
fun symb_sound_struct_get_sysLPi_fun tm =
  let
    val sysLPi_tm =
      case (strip_comb) tm of
         (_,[_,tm]) => tm
       | _ => raise Fail "symb_sound_struct_get_sysLPi_fun::unexpected term1";
    val res =
      case pairSyntax.strip_pair sysLPi_tm of
         [sys_tm, L_tm, Pi_tm] => (sys_tm, L_tm, Pi_tm)
       | _ => raise Fail "symb_sound_struct_get_sysLPi_fun::unexpected term2";
  in
    res
  end;

(*
val Pi_tm = Pi_A_tm;
*)
fun symb_sound_struct_Pi_to_birstatelist_fun Pi_tm =
  (pred_setSyntax.strip_set o snd o dest_comb) Pi_tm;


(* TODO: justify the second branch of assert is infeasible (need precondition for this) *)
(* TODO: simplify path condition in poststate to get rid of the implied and not accumulate it *)
(* TODO: clean up environment after assignment to not accumulate useless mappings *)
(* TODO: maybe have a specialized assert/assignment step function? (optimization to detect this situation directly, maybe better as separate function?) *)

end (* local *)

end (* struct *)
