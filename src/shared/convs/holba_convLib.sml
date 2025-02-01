structure holba_convLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open pred_setSyntax;
  open pred_setTheory;
  
  open listSyntax;

  open holba_cacheLib;

  (* error handling *)
  val libname = "holba_convLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* ============================================================================ *)

  (* TODO: this is stolen from exec tool, better unify them later: bir_exec_auxLib *)
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

  (* TODO: this is a modified version of the above function, better unify them later *)
  fun GEN_match_extract is_tm_fun acc [] = acc
    | GEN_match_extract is_tm_fun acc (tm::l) =
      if is_tm_fun tm then
        GEN_match_extract is_tm_fun (tm::acc) l
      else if is_comb tm then
        let
          val (rator_tm, rand_tm) = dest_comb tm;
        in
          GEN_match_extract is_tm_fun acc (rand_tm::rator_tm::l)
        end
      else if is_abs tm then
          GEN_match_extract is_tm_fun acc (((snd o dest_abs) tm)::l)
      else
        GEN_match_extract is_tm_fun acc l (* raise ERR "GEN_match_extract" "unknown" *)
      ;


(* ---------------------------------------------------------------------------------------- *)

  fun TRY_LIST_REWR_CONV [] _ = raise UNCHANGED
    | TRY_LIST_REWR_CONV (rw_thm::rw_thms) tm =
        REWR_CONV rw_thm tm
        handle _ => TRY_LIST_REWR_CONV rw_thms tm;

  (* eliminate left conjuncts first *)
  val CONJL_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
    in
      fn lconv => fn rconv =>
      (LAND_CONV lconv) THENC
      (fn tm =>
        if (identical T o fst o dest_conj) tm then
          (REWR_CONV thm_T THENC rconv) tm
        else
          (REWR_CONV thm_F) tm)
    end;
  (* eliminate right conjuncts first *)
  val CONJR_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
    in
      fn lconv => fn rconv =>
      (RAND_CONV rconv) THENC
      (fn tm =>
        if (identical T o snd o dest_conj) tm then
          (REWR_CONV thm_T THENC lconv) tm
        else
          (REWR_CONV thm_F) tm)
    end;

  (* eliminate left disjuncts first *)
  val DISJL_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
    in
      fn lconv => fn rconv =>
      (LAND_CONV rconv) THENC
      (fn tm =>
        if (identical F o fst o dest_disj) tm then
          (REWR_CONV thm_F THENC lconv) tm
        else
          (REWR_CONV thm_T) tm)
    end;
  (* eliminate right disjuncts first *)
  val DISJR_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
    in
      fn lconv => fn rconv =>
      (RAND_CONV rconv) THENC
      (fn tm =>
        if (identical F o snd o dest_disj) tm then
          (REWR_CONV thm_F THENC lconv) tm
        else
          (REWR_CONV thm_T) tm)
    end;
  
  fun NEG_CONV conv =
    RAND_CONV conv THENC
    REWRITE_CONV [boolTheory.NOT_CLAUSES];

  local
    val thm_T = (CONJUNCT1 o SPEC_ALL) boolTheory.COND_CLAUSES;
    val thm_F = (CONJUNCT2 o SPEC_ALL) boolTheory.COND_CLAUSES;
    fun get_cond_c tm =
      let val (c,_,_) = dest_cond tm;
      in c end;
    fun clean_conv tm =
      if (identical T o get_cond_c) tm then
        REWR_CONV thm_T tm
      else
        REWR_CONV thm_F tm;
  in
    fun ITE_CONV conv =
      RATOR_CONV (RATOR_CONV (RAND_CONV conv)) THENC
      clean_conv;
  end

  
(* ---------------------------------------------------------------------------------- *)
(* generic fast set operations (conversions)                                          *)
(* ---------------------------------------------------------------------------------- *)
  (*
  (* speedy, cheating version of INTER_CONV for prototyping *)
  fun INTER_CONV_cheat conv tm =
    let
      val (s1, s2) = dest_inter tm
      val s1_l = strip_set s1;
      val s2_l = strip_set s2;
      val eq_fun = (identical T) o rhs o concl o conv o (fn x => fn y => mk_eq (x,y));
      fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
      val l = List.foldr (fn (x, l) => if in_f s2_l x then x::l else l) [] s1_l;
      val tm_l_set = if List.null l then mk_empty(eltype tm) else mk_set l;
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
  val ID_EQ_CONV = Profile.profile "auxset_ID_EQ_CONV" ID_EQ_CONV;
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

  local
    val filter_empty_thm = CONJUNCT1 listTheory.FILTER;
    val filter_cons_thm = CONJUNCT2 listTheory.FILTER;
    (* this function is not end-recursive *)
    fun FILTER_CONV_helper ite_conv tm =
      (if (is_cons o snd o dest_filter) tm then
        REWR_CONV filter_cons_thm THENC
        ite_conv THENC
        (fn tm_ =>
          (if is_filter tm_ then
              FILTER_CONV_helper ite_conv
            else if is_cons tm_ then
              RAND_CONV (FILTER_CONV_helper ite_conv)
            (*else if is_nil tm_ then
              ALL_CONV*)
            else raise ERR "FILTER_CONV" "unexpected")
          tm_)
      else
        REWR_CONV filter_empty_thm) tm;
  in
    fun FILTER_CONV p_conv tm =
      let
        val ite_conv = ITE_CONV p_conv;
      in
        FILTER_CONV_helper ite_conv tm
        handle e => (print_term tm; raise wrap_exn ("@FILTER_CONV") e)
      end;
  end

  local
    val inter_empty_thm = CONJUNCT1 INTER_EMPTY;
    (* this function is not end-recursive *)
    fun INTER_CONV_helper ite_conv tm =
      (if (is_insert o fst o dest_inter) tm then
        REWR_CONV INSERT_INTER THENC
        ite_conv THENC
        (fn tm_ =>
          (if is_inter tm_ then
              INTER_CONV_helper ite_conv
            else if is_insert tm_ then
              RAND_CONV (INTER_CONV_helper ite_conv)
            (*else if is_empty tm_ then
              ALL_CONV*)
            else raise ERR "INTER_CONV" "unexpected")
          tm_)
      else
        REWR_CONV inter_empty_thm) tm;
  in
    fun INTER_CONV el_EQ_CONV tm =
      let
        val ite_conv = ITE_CONV (pred_setLib.IN_CONV el_EQ_CONV);
      in
        INTER_CONV_helper ite_conv tm
        handle e => (print_term tm; raise wrap_exn ("@INTER_CONV") e)
      end;
  end

  local
    fun DIFF_CONV_helper delete_conv thm =
      if (is_insert o snd o dest_diff o rhs o concl) thm then
          let
            val thm0 =
              CONV_RULE (RHS_CONV (
                REWR_CONV DIFF_INSERT THENC
                LAND_CONV delete_conv
              )) thm;
          in
            DIFF_CONV_helper delete_conv thm0
          end
      else
        CONV_RULE (RHS_CONV (REWR_CONV DIFF_EMPTY)) thm;

    val delete_thm = GSYM DELETE_DEF;
  in
    fun is_sing tm =
      is_insert tm andalso
      ((is_empty o snd o dest_insert) tm);

    fun DIFF_CONV el_EQ_CONV tm =
      let
        val delete_conv = pred_setLib.DELETE_CONV el_EQ_CONV;
      in
        if (is_sing o snd o dest_diff) tm then
          (REWR_CONV delete_thm THENC delete_conv) tm
        else
          DIFF_CONV_helper delete_conv $ REFL $ tm
        handle e => (print_term tm; raise wrap_exn ("@DIFF_CONV") e)
      end;
  end

  local
    val union_empty_thm = CONJUNCT2 UNION_EMPTY;
    fun BIGUNION_CONV_helper union_conv thm =
      if (is_insert o dest_bigunion o snd o dest_union o rhs o concl) thm then
        let
          val thm0 =
            CONV_RULE (RHS_CONV (
              RAND_CONV (REWR_CONV BIGUNION_INSERT) THENC
              REWR_CONV UNION_ASSOC THENC
              LAND_CONV union_conv
            )) thm;
        in
          BIGUNION_CONV_helper union_conv thm0
        end
      else
        CONV_RULE (RHS_CONV (
          RAND_CONV (REWR_CONV BIGUNION_EMPTY) THENC
          REWR_CONV union_empty_thm
        )) thm;
  in
    fun BIGUNION_CONV el_EQ_CONV tm =
      let
        val union_conv = pred_setLib.UNION_CONV el_EQ_CONV;
      in
        if (is_insert o dest_bigunion) tm then
          BIGUNION_CONV_helper union_conv (REWR_CONV BIGUNION_INSERT tm)
        else
          REWR_CONV BIGUNION_EMPTY tm
        handle e => (print_term tm; raise wrap_exn ("@BIGUNION_CONV") e)
      end;
  end

  fun SUBSET_CONV el_EQ_CONV tm = (
    if (is_insert o fst o dest_subset) tm then (
      REWR_CONV INSERT_SUBSET THENC
      CONJL_CONV
        (pred_setLib.IN_CONV el_EQ_CONV)
        (SUBSET_CONV el_EQ_CONV)
    ) else (
      REWRITE_CONV [EMPTY_SUBSET]
    )
  ) tm;

(* ================================================================================== *)
(* ================================================================================== *)

  val num_EQ_CONV =
    numLib.REDUCE_CONV; (*could also just use EVAL here*)
  val num_EQ_CONV = wrap_cache_result_EQ_BEQ Term.compare num_EQ_CONV;

  val word_EQ_CONV =
    wordsLib.word_EQ_CONV;



end (* local *)

end (* struct *)
