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
  RESTR_EVAL_CONV [``birs_update_env``, ``birs_gen_env``, ``type_of_bir_exp``] THENC
  GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
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


(* helpers to check if sound structure terms (and subterms) are in normalform *)
(* ----------------------------------------------- *)
  local

    fun is_bsst_pc_fupd tm =
      is_comb tm andalso
      (identical ``bsst_pc_fupd`` o fst o dest_comb) tm;
    fun is_bsst_environ_fupd tm =
      is_comb tm andalso
      (identical ``bsst_environ_fupd`` o fst o dest_comb) tm;
    fun is_bsst_status_fupd tm =
      is_comb tm andalso
      (identical ``bsst_status_fupd`` o fst o dest_comb) tm;
    fun is_bsst_pcond_fupd tm =
      is_comb tm andalso
      (identical ``bsst_pcond_fupd`` o fst o dest_comb) tm;

  in

    fun birs_state_is_normform tm =
      is_comb tm andalso
      ((is_bsst_pc_fupd o fst o dest_comb) tm orelse
       (is_bsst_environ_fupd o fst o dest_comb) tm orelse
       (is_bsst_status_fupd o fst o dest_comb) tm orelse
       (is_bsst_pcond_fupd o fst o dest_comb) tm);

    fun is_a_normform_set tm =
      (pred_setSyntax.strip_set tm; true)
      handle _ => false;

    fun birs_states_are_normform tm =
      is_a_normform_set tm andalso
      (List.all birs_state_is_normform o pred_setSyntax.strip_set) tm;

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

(* check if sound structure term is in normalform *)
(* ----------------------------------------------- *)
fun symb_sound_struct_is_normform tm =
  let
    val (sys, L, Pi) = symb_sound_struct_get_sysLPi_fun tm
                       handle _ => raise Fail "symb_sound_struct_is_normform::unexpected term1";

    (*
    val bir_state_init = ``<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>;
      bsst_environ := bir_senv_GEN_list birenvtyl;
      bsst_status := BST_Running;
      bsst_pcond :=
        BExp_BinExp BIExp_And
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0xFFFFFFw))
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
             (BExp_Aligned Bit32 2
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
          (BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>``;
    is_bsst_pc_fupd bir_state_init
    birs_state_is_ok bir_state_init
    *)

    val sys_ok =
      is_comb sys andalso
      (identical ``birs_symb_to_symbst`` o fst o dest_comb) sys andalso
      (birs_state_is_normform o snd o dest_comb) sys;

    val L_ok = is_a_normform_set L;

    val Pi_ok =
      is_comb Pi andalso
      (identical ``IMAGE birs_symb_to_symbst`` o fst o dest_comb) Pi andalso
      (birs_states_are_normform o snd o dest_comb) Pi;
  in
    sys_ok andalso L_ok andalso Pi_ok
  end;


(* bir symbolic execution steps *)
(* ----------------------------------------------- *)
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
*)
fun birs_exec_step_fun bprog_tm bstate_tm =
  let
    val _ = if (birs_state_is_normform) bstate_tm then () else
            (print_term bstate_tm;
             raise ERR "birs_exec_step_fun" "something is not right, the input state is not as expected");

    (* execution of steps *)
    val test_term = ``birs_exec_step ^bprog_tm ^bstate_tm``;
    (*
    val _ = (print_term o concl) (birs_exec_step_CONV test_term);
    *)
    val birs_exec_thm = birs_exec_step_CONV test_term;

    val _ = if (birs_states_are_normform o snd o dest_eq o concl) birs_exec_thm then () else
            (print_term (concl birs_exec_thm);
             raise ERR "birs_exec_step_fun" "something is not right, the produced theorem is not evaluated enough");
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

    val _ = if symb_sound_struct_is_normform (concl single_step_prog_thm) then () else
            (print_term (concl single_step_prog_thm);
             raise ERR "birs_rule_STEP_fun" "something is not right, the produced theorem is not evaluated enough");
  in
    single_step_prog_thm
  end;
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

(*
val pcond_tm = ``
               BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
                 (BExp_UnaryExp BIExp_Not
                    (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))))
``;
*)

(* stepping a sound structure, try to justify assert *)
(* ----------------------------------------------- *)
(*
val bstate_tm = birs_state_init_tm;
*)
local
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
  open birs_auxTheory;

  val assert_spec_thm = prove(``
!bprog sys L lbl1 env1 status pre cond lbl2 env2.
  (symb_hl_step_in_L_sound (bir_symb_rec_sbir bprog)
    (sys, L, IMAGE birs_symb_to_symbst {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>;
      <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := BST_AssertionViolated;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>})) ==>
  (IS_BIR_CONTRADICTION (BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond))) ==>
  (symb_hl_step_in_L_sound (bir_symb_rec_sbir bprog)
    (sys, L, IMAGE birs_symb_to_symbst {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := pre|>}))
``, cheat);


(* ======================================= *)
val debug_z3_taut_on = false;
fun holsmt_is_taut wtm =
  let val wtm_fixed = subst [mk_var ("MEM", ``:word64|->word8``) |-> Term`MEMV:word64|->word8`] wtm; in
    ((HolSmtLib.Z3_ORACLE_PROVE wtm_fixed; true)
    handle HOL_ERR e => (
      if not debug_z3_taut_on then () else
      let
        val _ = print "--- not a tautology:\n";
        val _ = print_term wtm_fixed;
        val _ = print ">>> generating a model\n";
        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL (mk_neg wtm_fixed);
        (*val _ = PolyML.print model;*)
        val _ = print "<<< done generating a model\n";
      in () end;
        false))
  end;

fun holsmt_bir_check_unsat bexp =
  let
    (* little amounts of output *)
    val _ = Library.trace := 1;
    val pcond_bexp = (snd o dest_eq o concl o EVAL) bexp;
    val wtm = bir_exp_to_wordsLib.bir2bool pcond_bexp;
  in
    holsmt_is_taut (mk_neg wtm)
  end;

open bir_smtLib;

fun birsmt_check_unsat bexp =
  let
    val vars_empty = Redblackset.empty smtlib_vars_compare;
    val (_, vars, query) = bexp_to_smtlib [] vars_empty bexp;

    (* little amounts of output *)
(*
    val _ = (print o fst) query;
*)
    val result = querysmt bir_smtLib_z3_prelude vars [query];

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "bir_smt_check_unsat" "smt solver couldn't determine satisfiability"
  in
    result = BirSmtUnsat
  end;

val vars_empty = Redblackset.empty smtlib_vars_compare;

(* ======================================= *)

fun bir_check_unsat use_holsmt =
  if use_holsmt then
    holsmt_bir_check_unsat
  else
    birsmt_check_unsat;

in
fun birs_rule_STEP_tryassert_fun birs_rule_STEP_thm bprog_tm bstate_tm =
  let
    val single_step_prog_thm = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm bstate_tm;
    val continue_thm_o =
      SOME (MATCH_MP assert_spec_thm single_step_prog_thm)
      handle _ => NONE;
  in
    (* val SOME continue_thm = continue_thm_o; *)
    case continue_thm_o of
       SOME continue_thm =>
        let
          val pcond_tm = (snd o dest_comb o snd o dest_comb o fst o dest_comb o concl) continue_thm;
          (*val _ = print_term pcond_tm;*)
          val pcond_is_contr = bir_check_unsat false pcond_tm;
          val pcond_thm_o =
            if pcond_is_contr then
              SOME (prove(``(IS_BIR_CONTRADICTION ^pcond_tm):bool``, cheat))
            else
              NONE;
        in
          (* val SOME pcond_thm = pcond_thm_o; *)
          case pcond_thm_o of
             SOME pcond_thm => MP continue_thm pcond_thm
           | _ => single_step_prog_thm
        end
     | _ => single_step_prog_thm
  end;
end;


(* stepping a sound structure, try to simplify after assignment *)
(* ----------------------------------------------- *)
val symb_rule_SUBST_SING_thm = prove(``
!sr.
!sys L sys2 var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, {sys2})) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>

  (symb_simplification sr sys2 symbexp symbexp') ==>

  (symb_hl_step_in_L_sound sr (sys, L, {symb_symbst_store_update var symbexp' sys2}))
``,
  REPEAT STRIP_TAC >>

  `({sys2} DIFF {sys2}) UNION {symb_symbst_store_update var symbexp' sys2} = {symb_symbst_store_update var symbexp' sys2}` by (
    METIS_TAC [pred_setTheory.DIFF_EQ_EMPTY, pred_setTheory.UNION_EMPTY]
  ) >>

  METIS_TAC [symb_rulesTheory.symb_rule_SUBST_thm]
);

(*
val birs_symb_rule_SUBST_SING_thm = prove(``
``,
);
*)


(* first prepare the SUBST rule for prog *)
fun birs_rule_SUBST_prog_fun bprog_tm =
  let
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    val symbols_f_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_symbols_f_sound_thm;
    val birs_symb_symbols_f_sound_prog_thm =
      (SPEC (bprog_tm) symbols_f_sound_thm);
    val ARB_val_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_ARB_val_sound_thm;
    val birs_symb_ARB_val_sound_prog_thm =
      (SPEC (bprog_tm) ARB_val_sound_thm);

    val prep_thm =
      MATCH_MP
        (MATCH_MP symb_rule_SUBST_SING_thm birs_symb_symbols_f_sound_prog_thm)
        birs_symb_ARB_val_sound_prog_thm;

    val inst_thm = prove(``
         !sys L lbl envl status pcond vn symbexp symbexp'.
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>}) ==>
           symb_simplification (bir_symb_rec_sbir ^bprog_tm) (birs_symb_to_symbst 
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) symbexp symbexp' ==>
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>})
      ``,
        cheat (* TODO: connect this with prep_thm from above *)
      );
  in
    inst_thm
  end;

val const_add_subst_thms = [

  prove(``!bprog sys be w1 w2. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm64 (w1 + w2))))``, cheat),
  prove(``!bprog sys be w1 w2. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm64 (w1 - w2))))``, cheat),

(*
  prove(``!bprog sys be w1. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_BinExp BIExp_And
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm32 w1)))
      (BExp_Const (Imm32 0xFFFFFFFCw)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm32 w1)))``, cheat (* TODO: but this has to do with how the path condition constrains bvar (in this case by alignment) and the value of w1, needs to be taken into account *)),
*)

  prove(``!bprog sys be w1 w2. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_Minus
          be
          (BExp_Const (Imm32 w1)))
        (BExp_Const (Imm32 0xFFFFFFFCw)))
      (BExp_Const (Imm32 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm32 (w1 + w2))))``, cheat (* TODO: but this has to do with how the path condition constrains bvar (in this case by alignment) and the value of w1, needs to be taken into account *)
     (* TODO: this is just a bad fix, need to make this better *)),

  prove(``!bprog sys be w1 w2. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm64 (w1 + w2))))``, cheat),
  prove(``!bprog sys be w1 w2. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm64 (w1 - w2))))``, cheat),

  prove(``!bprog sys be_m be_sa be_v be_la. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_Load
      (BExp_Store
        be_m
        be_sa
        BEnd_LittleEndian
        be_v)
      be_la
      BEnd_LittleEndian
      Bit32)
    (if be_sa = be_la then
       be_v
     else
       (BExp_Load
         be_m
         be_la
         BEnd_LittleEndian
         Bit32))``, cheat (* TODO: this is not quite right, it's just an experiment *)),

  prove(``!bprog sys be_m be_sa be_v be_la sz. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_Load
      (BExp_Store
        be_m
        be_sa
        BEnd_LittleEndian
        be_v)
      be_la
      BEnd_LittleEndian
      sz)
    (if be_sa = be_la then
       be_v
     else
       (BExp_Load
         be_m
         be_la
         BEnd_LittleEndian
         sz))``, cheat (* TODO: this is not quite right, it's just an experiment *)),

  prove(``!bprog sys be_m be_sa be_v be_la sz. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_Cast BIExp_UnsignedCast (BExp_Load
      (BExp_Store
        be_m
        be_sa
        BEnd_LittleEndian
        be_v)
      be_la
      BEnd_LittleEndian
      sz) Bit32)
    (BExp_Cast BIExp_UnsignedCast (if be_sa = be_la then
       be_v
     else
       (BExp_Load
         be_m
         be_la
         BEnd_LittleEndian
         sz)) Bit32)``, cheat (* TODO: this is not quite right, it's just an experiment *)),

  prove(``!bprog sys be. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_Cast BIExp_UnsignedCast
      (BExp_Cast BIExp_LowCast
        (BExp_Cast BIExp_UnsignedCast
          (BExp_Cast BIExp_LowCast be Bit8) Bit32) Bit8) Bit32)
    (BExp_Cast BIExp_UnsignedCast
      (BExp_Cast BIExp_LowCast be Bit8) Bit32)``, cheat),

  prove(``!bprog sys be be_v. symb_simplification (bir_symb_rec_sbir bprog) sys
    (BExp_IfThenElse be
              (BExp_BinExp BIExp_Plus
                 (BExp_BinExp BIExp_Plus (BExp_Den (BVar "countw" (BType_Imm Bit64))) be_v)
                 (BExp_Const (Imm64 3w)))
              (BExp_BinExp BIExp_Plus
                 (BExp_BinExp BIExp_Plus (BExp_Den (BVar "countw" (BType_Imm Bit64))) be_v)
                 (BExp_Const (Imm64 1w))))
    (
              (BExp_BinExp BIExp_Plus
                 (BExp_BinExp BIExp_Plus (BExp_Den (BVar "countw" (BType_Imm Bit64))) be_v)
                 (BExp_Const (Imm64 3w)))
    )``, cheat (* TODO: this is not quite right, it's just an experiment *))

];
(*symb_rulesTheory.symb_simplification_def*)

(*
val single_step_prog_thm = result;
*)
fun birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm single_step_prog_thm =
  let
    (*
    val t = hd const_add_subst_thms;
    val simp_thm = MATCH_MP birs_rule_SUBST_thm single_step_prog_thm;
    *)
    fun try_inst t simp_thm =
      let
        val t_ = SPEC_ALL t;
        val bir_simp_tm = (fst o dest_comb o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl) t_;
        val bir_simp_inst_tm = (fst o dest_comb o fst o dest_imp o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl o Q.SPEC `symbexp'`) simp_thm;

        val tm_subst = match_term bir_simp_tm bir_simp_inst_tm;
        val final_thm = INST_TY_TERM tm_subst t_;
      in
        CONV_RULE (TRY_CONV (RAND_CONV EVAL) THENC REFL) final_thm
      end;


    fun try_fold_match simp_thm (t, thm_o) =
      if isSome thm_o then
        thm_o
      else
        SOME (MATCH_MP simp_thm (try_inst t simp_thm))
        handle _ => NONE;

    fun repeat_fold step_thm =
      let
        val assignment_thm = MATCH_MP birs_rule_SUBST_thm step_thm;
        val thm_o = List.foldr (try_fold_match assignment_thm) NONE const_add_subst_thms;
      in
        if isSome thm_o then
          repeat_fold (valOf thm_o)
        else
          step_thm
      end;

  in
    repeat_fold single_step_prog_thm
    handle _ => single_step_prog_thm
  end;


end (* local *)

end (* struct *)
