structure birs_stepLib =
struct

local

open HolKernel Parse boolLib bossLib;
open computeLib;

open bir_exp_substitutionsTheory;
open bir_expTheory;

open bir_symbTheory;
open birs_auxTheory;

open bir_exp_typecheckLib;

  (* error handling *)
  val libname = "bir_symbLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname


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


    fun birs_state_is_normform_CONV sfun bstate_tm =
      (if (birs_state_is_normform) bstate_tm then () else
            (print_term bstate_tm;
             raise ERR (sfun^"::birs_state_is_normform_CONV") "something is not right, the input state is not as expected");
       REFL bstate_tm);

    fun birs_states_are_normform_CONV sfun bstates_tm =
      (if (birs_states_are_normform) bstates_tm then () else
            (print_term bstates_tm;
             raise ERR (sfun^"::birs_states_are_normform_CONV") "something is not right, the produced theorem is not evaluated enough");
       REFL bstates_tm);

    fun birs_states_are_normform_CONV_with_start sfun bstate_tm bstates_tm =
        birs_states_are_normform_CONV sfun bstates_tm
	handle e => (print "\n[[[[\n"; print_term bstate_tm; print "\n]]]]\n"; raise e);

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

val bstate_tm = birs_state_init_tm;
val bprog_tm = bprog_tm;

val tm = ``ABCD (birs_exec_step ^bprog_tm ^bstate_tm)``;
val tm = ``birs_exec_step ^bprog_tm ^bstate_tm``;
*)
val birs_exec_step_tm = ``birs_exec_step``;
fun is_birs_exec_step tm =
  is_comb tm andalso
  (is_comb o fst o dest_comb) tm andalso
  (same_const birs_exec_step_tm o fst o dest_comb o fst o dest_comb) tm;
fun birs_exec_step_CONV_fun tm =
  GEN_match_conv
(is_birs_exec_step)
(fn bstate_tm => (
  RAND_CONV (birs_state_is_normform_CONV "birs_exec_step_CONV_fun") THENC

  (fn tm_i =>
    let
      val timer_exec_step = bir_miscLib.timer_start 0;
      (* TODO: optimize *)
      val birs_exec_thm = birs_exec_step_CONV tm_i;
      val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> executed step in " ^ delta_s ^ "\n")) timer_exec_step;
    in
      birs_exec_thm
    end) THENC

  birs_states_are_normform_CONV_with_start "birs_exec_step_CONV_fun" bstate_tm
  ) bstate_tm
)
tm;


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
fun birs_rule_STEP_prog_fun no_halt_thm =
  let
    val prep_thm = 
      MATCH_MP birs_rulesTheory.birs_rule_STEP_gen2_thm no_halt_thm;
(*
    val _ = (print_term o concl) prep_thm;
*)
  in
    prep_thm
  end;


(* plugging in the execution of steps to obtain sound structure *)
(* ----------------------------------------------- *)
local
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
  open birs_auxTheory;
in
fun birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm bstate_tm =
  let

    val birs_exec_thm = CONV_RULE birs_exec_step_CONV_fun (SPEC bstate_tm birs_rule_STEP_thm);

    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
    (* TODO: optimize *)
    val single_step_prog_thm =
      REWRITE_RULE
        [bir_symbTheory.recordtype_birs_state_t_seldef_bsst_pc_def,
         bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM]
        birs_exec_thm;

    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> STEP in " ^ delta_s ^ "\n")) timer_exec_step_p3;

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

  open birs_rulesTheory;

  open birs_smtLib;

  fun justify_assumption_EVAL t =
    if (not o is_imp o concl) t then
      raise ERR "justify_assumption_EVAL" "not an implication"
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
        val assmpt_thm = (EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "justify_assumption_EVAL" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "justify_assumption_EVAL" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        (REWRITE_RULE [assmpt_thm] t)
      end;

  val birs_pcondinf_tm = ``birs_pcondinf``;
in
fun birs_rule_tryjustassert_fun force_assert_justify single_step_prog_thm =
  let
    (*
    val single_step_prog_thm = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm bstate_tm;
    *)
    val continue_thm_o_1 =
      SOME (MATCH_MP assert_spec_thm single_step_prog_thm)
      handle _ => NONE;
    val continue_thm_o_2 =
      Option.map (justify_assumption_EVAL) continue_thm_o_1
      handle _ => NONE;
  in
    (* val SOME continue_thm = continue_thm_o; *)
    case continue_thm_o_2 of
       SOME continue_thm =>
        let
    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
          val pcond_tm = (snd o dest_comb o snd o dest_comb o fst o dest_comb o concl) continue_thm;
          (*val _ = print_term pcond_tm;*)
          val pcond_is_contr = bir_check_unsat false pcond_tm;
          val _ = if (not force_assert_justify) orelse pcond_is_contr then () else
            (print "\n\n\n<<<<<<<<<<<< ASSERTION MAY FAIL <<<<<<<<<<<< \n";
             print_term (concl single_step_prog_thm);
             print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n";
             raise ERR "birs_rule_tryjustassert_fun" "can't prove assertion to hold");
          val pcond_thm_o =
            if pcond_is_contr then
              SOME (mk_oracle_thm "BIRS_CONTR_Z3" ([], mk_comb (birs_pcondinf_tm, pcond_tm)))
            else
              NONE;
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> tryassert in " ^ delta_s ^ "\n")) timer_exec_step_p3;
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
(* first prepare the SUBST rule for prog *)
fun birs_rule_SUBST_prog_fun bprog_tm =
  let
    open birs_rulesTheory;
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    (*
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
           birs_simplification pcond symbexp symbexp' ==>
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>})
      ``,
        cheat (* TODO: connect this with prep_thm from above *)
      );*)
    val inst_thm = SIMP_RULE std_ss [] ((SPEC bprog_tm o INST_TYPE [Type.alpha |-> prog_type]) birs_rule_SUBST_spec_thm);
    (*val _ = (print_term o concl) inst_thm;*)
  in
    inst_thm
  end;


(*
val single_step_prog_thm = result;
*)
fun birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm single_step_prog_thm =
  let
    val assignment_thm_o =
      SOME (MATCH_MP birs_rule_SUBST_thm single_step_prog_thm)
      handle _ => NONE;

    val simp_t_o = Option.mapPartial (fn assignment_thm =>
      let
        val simp_tm = (fst o dest_imp o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl o Q.SPEC `symbexp'`) assignment_thm;

    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
        val simp_t = birs_simpLib.birs_simp_repeat simp_tm;
        (* TODO: need to remove the following line later and enable the simp function above *)
        (*val simp_t_o = NONE;*)
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> SUBST in " ^ delta_s ^ "\n")) timer_exec_step_p3;
      in
        SOME (simp_t, assignment_thm)
      end) assignment_thm_o;
  in
    case simp_t_o of
       SOME (simp_t, assignment_thm) => MATCH_MP assignment_thm simp_t
     | NONE => single_step_prog_thm
  end;


end (* local *)

end (* struct *)
