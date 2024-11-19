structure aux_setLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open pred_setTheory;

  open bir_symbTheory;

  open birs_auxTheory;

  open HolBACoreSimps;

  open birsSyntax;
  open birs_utilsLib;

  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "aux_setLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* ---------------------------------------------------------------------------------- *)
(* generic fast set operations (conversions)                                          *)
(* ---------------------------------------------------------------------------------- *)
  (*
  (* speedy, cheating version of INTER_CONV for prototyping *)
  fun INTER_CONV_cheat conv tm =
    let
      val (s1, s2) = pred_setSyntax.dest_inter tm
      val s1_l = pred_setSyntax.strip_set s1;
      val s2_l = pred_setSyntax.strip_set s2;
      val eq_fun = (identical T) o rhs o concl o conv o (fn x => fn y => mk_eq (x,y));
      fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
      val l = List.foldr (fn (x, l) => if in_f s2_l x then x::l else l) [] s1_l;
      val tm_l_set = if List.null l then pred_setSyntax.mk_empty(pred_setSyntax.eltype tm) else pred_setSyntax.mk_set l;
    in
      mk_oracle_thm "INTER_CONV_cheat" ([], mk_eq (tm, tm_l_set))
    end;
  *)
  (* the functions in pred_setLib seem to have handling for syntactic equality inbuilt,
     so it seems we don't need to wrap the EQ_CONVs we define with this, can even use NO_CONV for UNION for example *)
  (*
  val id_thm = prove(``!x. x ==> (x = T)``, rewrite_tac[]);
  fun wrap_EQ_CONV_id conv tm =
    let
      val (x,y) = dest_eq tm;
    in
      if identical x y then
        let
          val a = REFL x;
          val b = SPEC (concl a) id_thm;
        in
          MP b a
        end
      else
        conv tm
    end;
  val ID_EQ_CONV = wrap_EQ_CONV_id NO_CONV;
  val ID_EQ_CONV = Profile.profile "ID_EQ_CONV" ID_EQ_CONV;
  *)
  (*
  (* useful function for debugging. pred_setLib change exception so that issues are otherwise masked *)
  fun wrap_EQ_CONV_check s conv tm =
    let
      val t = conv tm
        handle e => (print_term tm; print ("conversion "^s^" failed\n"); raise e);
      val r = (rhs o concl) t;
    in
      if (identical T r) orelse (identical F r) then
        t
      else (
        print_term tm;
        print "output wrong\n";
        raise ERR s "not T or F"
      )
    end;
  *)

  fun resolve_ite_CONV conv =
    RATOR_CONV (RATOR_CONV (RAND_CONV conv)) THENC
    TRY_CONV (REWR_CONV ((CONJUNCT1 o SPEC_ALL) boolTheory.COND_CLAUSES)) THENC
    TRY_CONV (REWR_CONV ((CONJUNCT2 o SPEC_ALL) boolTheory.COND_CLAUSES));

  fun INTER_CONV el_EQ_CONV tm =
    IFC
      (REWR_CONV pred_setTheory.INSERT_INTER)
      (resolve_ite_CONV (pred_setLib.IN_CONV el_EQ_CONV) THENC
       (fn tm_ =>
         (if pred_setSyntax.is_empty tm_ then
            REFL
          else if pred_setSyntax.is_insert tm_ then
            RAND_CONV (INTER_CONV el_EQ_CONV)
          else if pred_setSyntax.is_inter tm_ then
            INTER_CONV el_EQ_CONV
          else raise ERR "INTER_CONV" "unexpected")
         tm_))
      (REWR_CONV (CONJUNCT1 pred_setTheory.INTER_EMPTY))
      tm;


  fun DIFF_CONV_helper el_EQ_CONV tm =
    IFC
      (REWR_CONV DIFF_INSERT)
      (LAND_CONV (pred_setLib.DELETE_CONV el_EQ_CONV) THENC
       DIFF_CONV_helper el_EQ_CONV)
      (REWR_CONV DIFF_EMPTY)
      tm;

  fun is_sing tm =
    pred_setSyntax.is_insert tm andalso
    ((pred_setSyntax.is_empty o snd o pred_setSyntax.dest_insert) tm);
  fun DIFF_CONV el_EQ_CONV tm =
    (if (is_sing o snd o pred_setSyntax.dest_diff) tm then
      REWR_CONV (GSYM DELETE_DEF) THENC
      pred_setLib.DELETE_CONV el_EQ_CONV
    else
      DIFF_CONV_helper el_EQ_CONV) tm;


  fun BIGUNION_CONV_helper el_EQ_CONV tm =
    IFC
      (RAND_CONV (REWR_CONV BIGUNION_INSERT))
      (REWR_CONV UNION_ASSOC THENC
       LAND_CONV (pred_setLib.UNION_CONV el_EQ_CONV) THENC
       BIGUNION_CONV_helper el_EQ_CONV)
      (RAND_CONV (REWR_CONV BIGUNION_EMPTY) THENC
       REWR_CONV (CONJUNCT2 UNION_EMPTY))
      tm;

  fun BIGUNION_CONV el_EQ_CONV =
    IFC
      (REWR_CONV BIGUNION_INSERT)
      (BIGUNION_CONV_helper el_EQ_CONV)
      (REWR_CONV BIGUNION_EMPTY);

(* ================================================================================== *)
(* ================================================================================== *)

(* ---------------------------------------------------------------------------------- *)
(*  label set equality checker                                                      *)
(* ---------------------------------------------------------------------------------- *)
  val num_EQ_CONV =
    numLib.REDUCE_CONV; (*could also just use EVAL here*)
  val num_EQ_CONV = aux_moveawayLib.wrap_cache_result_EQ_BEQ Term.compare num_EQ_CONV;

  val word_EQ_CONV =
    wordsLib.word_EQ_CONV;

  val bir_label_EQ_CONV =
    (TRY_CONV (LHS_CONV (REWR_CONV bir_program_labelsTheory.BL_Address_HC_def))) THENC
    (TRY_CONV (RHS_CONV (REWR_CONV bir_program_labelsTheory.BL_Address_HC_def))) THENC
    (* this assumes 32 or 63 bit addresses only, no labels, also doesn't take care of the case where Imms don't match (mixed Imms in Addresses) *)
    (*(fn tm => (print "\n"; print_term tm; print "\n"; REFL tm)) THENC*)
    (REWR_CONV ((GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) bir_programTheory.bir_label_t_11)) THENC
    (TRY_CONV (REWR_CONV ((GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) bir_immTheory.bir_imm_t_11))) THENC
    (TRY_CONV (REWR_CONV ((GEN_ALL o (fn x => List.nth(x,4)) o CONJUNCTS o SPEC_ALL) bir_immTheory.bir_imm_t_11))) THENC
    word_EQ_CONV;
  (*val bir_label_EQ_CONV = aux_moveawayLib.wrap_cache_result_EQ_BEQ Term.compare bir_label_EQ_CONV;*)

  val bir_pc_EQ_CONV =
    (REWR_CONV bir_programTheory.bir_programcounter_t_literal_11) THENC
    (RAND_CONV (num_EQ_CONV)) THENC
    IFC
      ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)))
      (REFL)
      ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)) THENC
      bir_label_EQ_CONV);
  (*val bir_pc_EQ_CONV = aux_moveawayLib.wrap_cache_result_EQ_BEQ Term.compare bir_pc_EQ_CONV;*)

(* ---------------------------------------------------------------------------------- *)
(*  bir var set equality checker                                                      *)
(* ---------------------------------------------------------------------------------- *)
  val bir_var_EQ_thm = prove(``
    !a0 a1 a0' a1'.
      BVar a0 a1 = BVar a0' a1' <=>
      a1 = a1' /\ a0 = a0'
  ``,
    METIS_TAC [bir_envTheory.bir_var_t_11]
  );
  (* this seems to be well optimized now, maybe need to turn off caching if there are much more variables around so that the dictionary lookups are more expensive *)
  val bir_var_EQ_CONV =
    (REWR_CONV bir_var_EQ_thm) THENC
    (*type*)
    LAND_CONV (
      REWRITE_CONV [
        bir_valuesTheory.bir_type_t_distinct,
        GSYM bir_valuesTheory.bir_type_t_distinct,
        bir_valuesTheory.bir_type_t_11,
        bir_immTheory.bir_immtype_t_distinct,
        GSYM bir_immTheory.bir_immtype_t_distinct]) THENC
    IFC
      ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)))
      ((*name*)
       stringLib.string_EQ_CONV)
      ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)));
  val bir_var_EQ_CONV = aux_moveawayLib.wrap_cache_result_EQ_BEQ Term.compare bir_var_EQ_CONV;

(* ---------------------------------------------------------------------------------- *)
(*  birs state equality checker                                                       *)
(* ---------------------------------------------------------------------------------- *)
  val bir_status_EQ_CONV =
    (* this seems to be well optimized now *)
    EVAL;

  (* could speed this up, maybe take inspiration from string or word EQ_CONV functions *)
  val bir_exp_EQ_CONV =
    EVAL (*SIMP_CONV (std_ss++holBACore_ss++birs_state_ss) [] THENC EVAL*);

  fun birs_gen_env_check_eq env1 env2 =
    let
      val mappings1 = get_env_mappings env1;
      val mappings2 = get_env_mappings env2;
    in
      birs_utilsLib.list_eq_contents (fn (x,y) => pair_eq identical identical x y) mappings1 mappings2
    end;

  (* TODO: have to make provide a proof-producing version of this *)
  fun birs_env_EQ_CONV tm =
    let
      val (env1_tm, env2_tm) = dest_eq tm;
      (* need two symbolic environments with birs_gen_env *)
      val _ = birs_check_env_norm ("birs_env_EQ_CONV", ": 1") env1_tm;
      val _ = birs_check_env_norm ("birs_env_EQ_CONV", ": 2") env2_tm;
      val is_eq = birs_gen_env_check_eq env1_tm env2_tm;
      val _ = print (if is_eq then "symbolic environments are equal\n" else "symbolic environments are not equal\n");
      (* TODO: the false case might be wrong *)
      val _ = if is_eq then () else (
        print_term tm;
        print "the symbolic environments seem to be unequal, but they might be equal\n";
        raise ERR "birs_env_EQ_CONV" "the symbolic environments seem to be unequal, but they might be equal");
      val eq_thm = mk_oracle_thm "BIRS_ENV_EQ" ([], mk_eq (tm, if is_eq then T else F));
    in
      eq_thm
    end;

  val birs_state_EQ_thm = prove(``
      !b21 f1 b11 b01 b22 f2 b12 b02.
       <|bsst_pc := b21; bsst_environ := f1; bsst_status := b11; bsst_pcond := b01|> =
       <|bsst_pc := b22; bsst_environ := f2; bsst_status := b12; bsst_pcond := b02|> <=>
       b11 = b12 /\ (b21 = b22 /\ (b01 = b02 /\ f1 = f2))
    ``,
      METIS_TAC [bir_symbTheory.birs_state_t_literal_11]
    ); (*status, pc, pcond, senv*)
  val birs_state_EQ_CONV =
    (REWR_CONV birs_state_EQ_thm) THENC
    (*status*)
    (LAND_CONV bir_status_EQ_CONV) THENC
    IFC
      ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)))
      (REFL)
      ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)) THENC
       (*pc*)
       LAND_CONV bir_pc_EQ_CONV THENC
       IFC
         ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)))
         (REFL)
         ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)) THENC
         (*pcond*)
         LAND_CONV bir_exp_EQ_CONV THENC
         IFC
           ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)))
           (REFL)
           ((REWR_CONV ((GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES)) THENC
           (*senv*)
           birs_env_EQ_CONV)
         )
       );
  val birs_state_EQ_CONV = aux_moveawayLib.wrap_cache_result_EQ_BEQ Term.compare birs_state_EQ_CONV;

(* ---------------------------------------------------------------------------------- *)
(*  programcounter operations                                                    *)
(* ---------------------------------------------------------------------------------- *)
  val programcounter_UNION_CONV =
      (* TODO: this has to be fixed as list of address spaces that can be merged and so on...
         (can we make this only involve the block label part, not the block index?) *)
      pred_setLib.UNION_CONV bir_pc_EQ_CONV;

(* ---------------------------------------------------------------------------------- *)
(* faster set operations for bir variable sets (for example for: computing freevarset, symbexec composition, merging, etc) *)
(* ---------------------------------------------------------------------------------- *)
  (* for UNION and BIGUNION it should be possible to use ID_EQ_CONV,
     but current implementation of the library functions does not fully support this use.
     the problem likely starts from IN_CONV,
     which does not prove syntactical elements further into the set, only first element works *)
  val varset_UNION_CONV =
    pred_setLib.UNION_CONV bir_var_EQ_CONV;

  val varset_BIGUNION_CONV =
    BIGUNION_CONV bir_var_EQ_CONV;

  val varset_INTER_CONV =
    INTER_CONV bir_var_EQ_CONV;

  val varset_DIFF_CONV =
    DIFF_CONV bir_var_EQ_CONV;

  (* A INTER (B DIFF C) *)
  val varset_INTER_DIFF_CONV =
    (* first DIFF *) 
    (RAND_CONV varset_DIFF_CONV) THENC
    (* then INTER *)
    varset_INTER_CONV;


(* ---------------------------------------------------------------------------------- *)
(* set operation for composition, using the state equality checker above              *)
(* ---------------------------------------------------------------------------------- *)
  val birs_state_DIFF_UNION_CONV =
      LAND_CONV (DIFF_CONV birs_state_EQ_CONV) THENC
      pred_setLib.UNION_CONV birs_state_EQ_CONV;

end (* local *)

end (* struct *)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR: set operation for composition *)
(* ---------------------------------------------------------------------------------- *)
(*
val tm = ``
  ({^st1_tm; ^st2_tm} DIFF
    {^st1_tm})
UNION
  {^st4_tm}
``;

val tm = ``
  {<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
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
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
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
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
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
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>} DIFF
{  <|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
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
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
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
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
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
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>} ∪
  {<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 2|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
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
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
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
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
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
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>}``;

birs_state_DIFF_UNION_CONV tm;
*)

(* ---------------------------------------------------------------------------------- *)
(*  TEST CASE FOR: state equality checker                                             *)
(* ---------------------------------------------------------------------------------- *)
(*
fun stx_tm addr_tm index_tm symbname_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm32 (^addr_tm)); bpc_index := (^index_tm)|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar (^symbname_tm) (BType_Imm Bit1)))];
     bsst_status := BST_Running;
     bsst_pcond :=
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>
``;
val st1_tm = stx_tm ``2824w:word32`` ``1:num`` ``"sy_PSR_Z"``;
val st2_tm = stx_tm ``2824w:word32`` ``2:num`` ``"sy_PSR_Z"``;
val st3_tm = stx_tm ``2825w:word32`` ``1:num`` ``"sy_PSR_A"``;
val st4_tm = stx_tm ``2824w:word32`` ``3:num`` ``"sy_PSR_Z"``;

val st_eq_1_tm = ``^st1_tm = ^st1_tm``;
val st_eq_2_tm = ``^st1_tm = ^st2_tm``;
val st_eq_3_tm = ``^st1_tm = ^st3_tm``;
val st_eq_4_tm = ``^st2_tm = ^st3_tm``;

val tm = st_eq_2_tm;
val tm = st_eq_3_tm;
val tm = st_eq_4_tm;

birs_state_EQ_CONV st_eq_1_tm
birs_state_EQ_CONV st_eq_2_tm
birs_state_EQ_CONV st_eq_3_tm
birs_state_EQ_CONV st_eq_4_tm
*)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR:                                                                     *)
(* faster set operations for bir variable sets (for computing freevarset, symbexec composition, merging, etc) *)
(* also for sets of symbolic BIR states                                               *)
(* ---------------------------------------------------------------------------------- *)
(*
EVAL tm

           val birs_exps_of_senv_CONV = (
    debug_conv2 THENC
    REPEATC (CHANGED_CONV (
      (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x) THENC
      (SIMP_CONV (std_ss) []) THENC
      (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (REWRITE_CONV [pred_setTheory.COMPONENT] THENC SIMP_CONV std_ss [pred_setTheory.IN_INSERT])))) THENC
      SIMP_CONV (std_ss) []
    ))
  );

           val birs_symb_symbols_CONV = (
    SIMP_CONV std_ss [birs_symb_symbols_thm] THENC
    SIMP_CONV (std_ss++birs_state_ss) [] THENC
    SIMP_CONV (std_ss) [birs_exps_of_senv_thm]
    (*(PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` birs_exps_of_senv_CONV)*)
  );
           val conv = birs_symb_symbols_CONV (*THENC EVAL*);
           val conv_ = computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC conv;
*)

(*
val tm = ``
{BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
    BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
    BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
    BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
    BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
    BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
    BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
    BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
    BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
    BVar "sy_SP_process" (BType_Imm Bit32);
    BVar "sy_ModeHandler" (BType_Imm Bit1);
    BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
    BVar "sy_tmp_COND" (BType_Imm Bit1);
    BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
    BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_R0" (BType_Imm Bit32);
    BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
    BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
    BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
    BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
    BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
    BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
    BVar "sy_tmp_LR" (BType_Imm Bit32);
    BVar "sy_tmp_SP_main" (BType_Imm Bit32);
    BVar "sy_tmp_SP_process" (BType_Imm Bit32);
    BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
    BVar "sy_tmp_countw" (BType_Imm Bit64)} ∩
   ({BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64);
     BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)} DIFF
    {BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)})
``;

val tm = ``
{BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);BVar "sy_countw" (BType_Imm Bit64);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1)} ∩
   ({BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);BVar "sy_countw" (BType_Imm Bit64);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1)} DIFF
    {
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)})
``;

val tm = (snd o dest_comb o fst o dest_comb o snd o dest_eq o concl o REWRITE_CONV [REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER]) tm;
val tm = (snd o dest_comb o snd o dest_eq o concl o REWRITE_CONV [Once (prove(``
!s t g.
g INTER (s DIFF t) =
s INTER (g DIFF t)
``,
(*REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER*)
METIS_TAC [pred_setTheory.INTER_COMM, pred_setTheory.DIFF_INTER]
))]) tm;

++pred_setSimps.PRED_SET_ss
val char_ss = rewrites (type_rws ``:char``);



val tm = ``
BVar "sy_countw" (BType_Imm Bit64) ∈
       {BVar "sy_MEM" (BType_Mem Bit32 Bit8);
        BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
        BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_Z" (BType_Imm Bit1);
        BVar "sy_R0" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
        BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
        BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
        BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
        BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
        BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
        BVar "sy_R12" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
        BVar "sy_SP_main" (BType_Imm Bit32);
        BVar "sy_SP_process" (BType_Imm Bit32);
        BVar "sy_ModeHandler" (BType_Imm Bit1);
        BVar "sy_countw" (BType_Imm Bit64);
        BVar "sy_tmp_PC" (BType_Imm Bit32);
        BVar "sy_tmp_COND" (BType_Imm Bit1);
        BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
        BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32);
        BVar "sy_tmp_R6" (BType_Imm Bit32);
        BVar "sy_tmp_R7" (BType_Imm Bit32);
        BVar "sy_tmp_R8" (BType_Imm Bit32);
        BVar "sy_tmp_R9" (BType_Imm Bit32);
        BVar "sy_tmp_R10" (BType_Imm Bit32);
        BVar "sy_tmp_R11" (BType_Imm Bit32);
        BVar "sy_tmp_R12" (BType_Imm Bit32);
        BVar "sy_tmp_LR" (BType_Imm Bit32);
        BVar "sy_tmp_SP_main" (BType_Imm Bit32);
        BVar "sy_tmp_SP_process" (BType_Imm Bit32);
        BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
        BVar "sy_tmp_countw" (BType_Imm Bit64)}
``;


*)
(*
val tm = ``
  EMPTY DIFF
     {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32)
     }
``;

val tm = ``
  {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32)
  } DIFF
     EMPTY
``;

val tm = ``
  {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32)
  } DIFF
     {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32)
     }
``;

val tm = ``
{
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32);
        BVar "sy_tmp_R8" (BType_Imm Bit32)
} INTER (^tm)
``; (* R4 and R5 *)
*)
