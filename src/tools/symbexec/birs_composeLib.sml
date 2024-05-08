structure birs_composeLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_composeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

(*
open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;
*)
  open birs_stepLib;
  open birs_auxTheory;
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in

(* TODO: *)
val betterTheorem = prove(``
!sr.
!sys_A L_A Pi_A sys_B L_B Pi_B.
  (symb_symbols_f_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys_A, L_A, Pi_A)) ==>
  (symb_hl_step_in_L_sound sr (sys_B, L_B, Pi_B)) ==>

  (* can't reintroduce symbols in fragment B that have been lost in A *)
  (((symb_symbols sr sys_A) (* DIFF (symb_symbols sr sys_B) *))
       INTER ((symb_symbols_set sr Pi_B) DIFF (symb_symbols sr sys_B))
   = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys_A, L_A UNION L_B, (Pi_A DIFF {sys_B}) UNION Pi_B))
``,
  METIS_TAC[symb_rulesTheory.symb_rule_SEQ_thm]
);

(* first prepare the SEQ rule for prog *)
fun birs_rule_SEQ_prog_fun bprog_tm =
  let
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    val symbols_f_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_symbols_f_sound_thm;
    val birs_symb_symbols_f_sound_prog_thm =
      (SPEC (bprog_tm) symbols_f_sound_thm);
  in
    (MATCH_MP betterTheorem birs_symb_symbols_f_sound_prog_thm)
  end;

(* symbol freedom helper function *)
fun birs_rule_SEQ_free_symbols_fun freesymbols_tm freesymbols_B_thm_o =
  let

fun freevarset_CONV tm =
(
  REWRITE_CONV [Once (prove(``
!s t g.
g INTER (s DIFF t) =
s INTER (g DIFF t)
``,
(*REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER*)
METIS_TAC [pred_setTheory.INTER_COMM, pred_setTheory.DIFF_INTER]
))] THENC

  (* DIFF first *)
(*
  RATOR_CONV (RAND_CONV (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY])) THENC
*)
 (* RATOR_CONV (RAND_CONV (INTER_INSERT_CONV)) THENC*)
  (RAND_CONV (
(*
   (fn tm => prove (``^tm = EMPTY``, cheat))
*)
   aux_setLib.DIFF_INSERT_CONV
)) THENC
(*
(fn tm => (if false then print ".\n" else print_term tm; print "aa\n\n"; REFL tm)) THENC
*)

  

  (* then INTER *)
  aux_setLib.INTER_INSERT_CONV
) tm;

(* EVAL tm *)

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

    val superspeedcheat = false;

    val freesymbols_thm = prove(freesymbols_tm,
      (if superspeedcheat then cheat else ALL_TAC) >> 
      (case freesymbols_B_thm_o of
          NONE => ALL_TAC
        | SOME freesymbols_B_thm => REWRITE_TAC [freesymbols_B_thm, pred_setTheory.INTER_EMPTY]) >>

      FULL_SIMP_TAC (std_ss) [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm, birs_symb_symbols_set_EQ_thm] >>

      (* TODO *)
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``, ``$BIGUNION``]) >>



      CONV_TAC (aux_setLib.birs_symb_symbols_MATCH_CONV) >>
(*
      CONV_TAC (
  SIMP_CONV (std_ss++birs_state_ss) [birs_symb_symbols_thm] THENC


  GEN_match_conv is_birs_exps_of_senv birs_exps_of_senv_CONV THENC
(*
  REWRITE_CONV [birs_exps_of_senv_thm] THENC
*)
  REWRITE_CONV [bir_typing_expTheory.bir_vars_of_exp_def] THENC

  computeLib.RESTR_EVAL_CONV [``$DIFF``, ``$INTER``, ``$UNION``, ``$INSERT``, ``$BIGUNION``] THENC
      REWRITE_CONV [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY] THENC
      REWRITE_CONV [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY] THENC

  REFL
) >>
*)

      REWRITE_TAC [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY] >>
      REWRITE_TAC [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY] >>

(*
      (fn (al,g) => (print_term g; ([(al,g)], fn ([t]) => t))) >>
*)
      (fn (al,g) => (print "starting to proof free symbols\n"; ([(al,g)], fn ([t]) => t))) >>

(*
prove(``{BVar "sy_tmp_countw" (BType_Imm Bit64);
 BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
 BVar "sy_tmp_SP_process" (BType_Imm Bit32);
 BVar "sy_tmp_SP_main" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
 BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_R11" (BType_Imm Bit32);
 BVar "sy_tmp_R10" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
 BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
 BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
 BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
 BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
 BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
 BVar "sy_tmp_PSR_V" (BType_Imm Bit1); BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
 BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
 BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
 BVar "sy_tmp_COND" (BType_Imm Bit1); BVar "sy_tmp_PC" (BType_Imm Bit32);
 BVar "sy_countw" (BType_Imm Bit64); BVar "sy_ModeHandler" (BType_Imm Bit1);
 BVar "sy_SP_process" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
 BVar "sy_LR" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
 BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
 BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
 BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
 BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
 BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
 BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R0" (BType_Imm Bit32);
 BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
 BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_C" (BType_Imm Bit1);
 BVar "sy_MEM" (BType_Mem Bit32 Bit8)} ∩
({BVar "sy_countw" (BType_Imm Bit64); BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_tmp_countw" (BType_Imm Bit64);
  BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
  BVar "sy_tmp_SP_main" (BType_Imm Bit32);
  BVar "sy_tmp_LR" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
  BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
  BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
  BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
  BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
  BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
  BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R0" (BType_Imm Bit32);
  BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
  BVar "sy_tmp_PSR_N" (BType_Imm Bit1); BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
  BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_tmp_COND" (BType_Imm Bit1); BVar "sy_tmp_PC" (BType_Imm Bit32);
  BVar "sy_ModeHandler" (BType_Imm Bit1);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_main" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
  BVar "sy_R12" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
  BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
  BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
  BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
  BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
  BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
  BVar "sy_R0" (BType_Imm Bit32); BVar "sy_PSR_Z" (BType_Imm Bit1);
  BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
  BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_SP_process" (BType_Imm Bit32); BVar "sy_countw" (BType_Imm Bit64)} DIFF
 {BVar "sy_countw" (BType_Imm Bit64); BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_tmp_countw" (BType_Imm Bit64);
  BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
  BVar "sy_tmp_SP_main" (BType_Imm Bit32);
  BVar "sy_tmp_LR" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
  BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
  BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
  BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
  BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
  BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
  BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R0" (BType_Imm Bit32);
  BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
  BVar "sy_tmp_PSR_N" (BType_Imm Bit1); BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
  BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_tmp_COND" (BType_Imm Bit1); BVar "sy_tmp_PC" (BType_Imm Bit32);
  BVar "sy_countw" (BType_Imm Bit64); BVar "sy_ModeHandler" (BType_Imm Bit1);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_main" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
  BVar "sy_R12" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
  BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
  BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
  BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
  BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
  BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
  BVar "sy_R0" (BType_Imm Bit32); BVar "sy_PSR_Z" (BType_Imm Bit1);
  BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
  BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_SP_process" (BType_Imm Bit32)}) ⊆ ∅
``,
);
*)


      CONV_TAC (RATOR_CONV (RAND_CONV (aux_setLib.freevarset_CONV))) >>
      (fn (al,g) => (print "finished to proof free symbols operation\n"; ([(al,g)], fn ([t]) => t))) >>

      REWRITE_TAC [pred_setTheory.EMPTY_SUBSET]
      >> (fn (al,g) => (print "finished to proof free symbols\n"; ([(al,g)], fn ([t]) => t)))

(*
      EVAL_TAC (* TODO: speed this up... *)
*)

(*
      FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_thm] >>

      CONV_TAC (conv) >>
      REPEAT (
        CHANGED_TAC ( fn xyz =>
            REWRITE_TAC [Once (prove(``!x. (IMAGE bir_vars_of_exp x) = I (IMAGE bir_vars_of_exp x)``, REWRITE_TAC [combinTheory.I_THM]))]
            xyz
        ) >>
        CONV_TAC (GEN_match_conv combinSyntax.is_I (RAND_CONV birs_exps_of_senv_CONV))
      ) >>

      EVAL_TAC
*)
(*
      CONV_TAC (conv)
      CONV_TAC (fn tm => (print_term tm; REFL tm))
      CONV_TAC (DEPTH_CONV (PAT_CONV ``\A. (I:((bir_var_t->bool)->bool)->((bir_var_t->bool)->bool)) A`` (fn tm => (print_term tm; raise Fail "abcdE!!!"))))



(combinSyntax.is_I o snd o dest_comb) tm





      CONV_TAC (ONCE_DEPTH_CONV (PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` (birs_exps_of_senv_CONV)))


FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
      EVAL_TAC

      CONV_TAC (PAT_CONV ``\A. (A DIFF C)`` (conv))





      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] >>

      EVAL_TAC
    (*
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.GSPECIFICATION]
    *)
*)
    );
  in
    freesymbols_thm
  end;

(*
val step_A_thm = single_step_A_thm;
val step_B_thm = single_step_B_thm;
val freesymbols_B_thm_o = SOME (prove(T, cheat));
*)
fun birs_rule_SEQ_fun birs_rule_SEQ_thm step_A_thm step_B_thm freesymbols_B_thm_o =
  let
    val get_SEQ_thm_concl_symb_struct_fun = snd o strip_imp o snd o strip_binder (SOME boolSyntax.universal) o concl;
    val symb_struct_get_bprog_fun = snd o dest_comb o hd o snd o strip_comb;
    val bprog_tm   = (symb_struct_get_bprog_fun o get_SEQ_thm_concl_symb_struct_fun) birs_rule_SEQ_thm;
    val bprog_A_tm = (symb_struct_get_bprog_fun o concl) step_A_thm;
    val bprog_B_tm = (symb_struct_get_bprog_fun o concl) step_B_thm;
    val _ = if identical bprog_tm bprog_A_tm andalso identical bprog_tm bprog_B_tm then () else
            raise Fail "birs_rule_SEQ_fun:: the programs have to match";

    (*
    val (sys_A_tm, _, _)       = (symb_sound_struct_get_sysLPi_fun o concl) step_A_thm;
    val (sys_B_tm, _, Pi_B_tm) = (symb_sound_struct_get_sysLPi_fun o concl) step_B_thm;
    *)

    val prep_thm =
      HO_MATCH_MP (HO_MATCH_MP birs_rule_SEQ_thm step_A_thm) step_B_thm;
    val freesymbols_tm = (hd o fst o strip_imp o concl) prep_thm;

    val freesymbols_thm = birs_rule_SEQ_free_symbols_fun freesymbols_tm freesymbols_B_thm_o;
    val _ = print "finished to proof free symbols altogether\n";
    (*
    val bprog_composed_thm = save_thm(
       "bprog_composed_thm",
    *)

    val bprog_composed_thm =
           (MATCH_MP
              prep_thm
              freesymbols_thm);
    val _ = print "composed\n";

    (* TODO: tidy up set operations to not accumulate (in both, post state set and label set) - does this simplification work well enough? *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss) [] bprog_composed_thm; *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [pred_setTheory.INSERT_UNION] bprog_composed_thm; *)

(*
val tm = (snd o dest_comb o snd o dest_comb o snd o dest_comb o concl) bprog_composed_thm;
*)

(*
    val conv = aux_setLib.birs_state_DIFF_UNION_CONV;
*)
    fun Pi_CONV conv tm =
      RAND_CONV (RAND_CONV (conv)) tm;

    fun L_CONV conv tm =
      RAND_CONV (LAND_CONV (conv)) tm;

    val bprog_Pi_fixed_thm = CONV_RULE (RAND_CONV (Pi_CONV aux_setLib.birs_state_DIFF_UNION_CONV)) bprog_composed_thm;

    val bprog_L_fixed_thm  = CONV_RULE (RAND_CONV (L_CONV (
      EVAL (* TODO: this has to be fixed as list of address spaces that can be merged and so on... (can we make this only involve the block label part, not the block index?) *)
      (*SIMP_CONV
        (std_ss++HolBACoreSimps.holBACore_ss++birs_state_ss++pred_setLib.PRED_SET_ss++wordsLib.WORD_ss)
        [bir_symbTheory.birs_symb_to_symbst_EQ_thm, pred_setTheory.INSERT_UNION]*)
        ))) bprog_Pi_fixed_thm;

(*
    val bprog_composed_thm_1 =
      (SIMP_RULE
        (std_ss++HolBACoreSimps.holBACore_ss++birs_state_ss++pred_setLib.PRED_SET_ss)
        [bir_symbTheory.birs_symb_to_symbst_EQ_thm, pred_setTheory.INSERT_UNION]
        bprog_composed_thm);
    val _ = print "UNION\n";

    (* reconstruct IMAGE in the post state set *)
    val IMAGE_EMPTY_thm =
      Q.SPEC `birs_symb_to_symbst` (
        INST_TYPE [beta |-> Type`:(bir_programcounter_t, string, bir_exp_t, bir_status_t) symb_symbst_t`, alpha |-> Type`:birs_state_t`] 
        pred_setTheory.IMAGE_EMPTY
      );
    val _ = print "FIX\n";
    val bprog_composed_thm_2 =
      CONV_RULE
        (PAT_CONV ``\A. symb_hl_step_in_L_sound B (C, D, A)`` (REWRITE_CONV [GSYM IMAGE_EMPTY_thm, GSYM pred_setTheory.IMAGE_INSERT]))
        bprog_composed_thm_1
    val _ = print "IMAGE_INSERT\n";
*)

    val _ = if symb_sound_struct_is_normform (concl bprog_L_fixed_thm) then () else
            (print_term (concl bprog_L_fixed_thm);
             raise ERR "birs_rule_SEQ_fun" "something is not right, the produced theorem is not evaluated enough");
  in
    bprog_L_fixed_thm
  end;


end (* local *)

end (* struct *)
