structure bir_htLib =
struct

  local

    (* For compilation *)
    open HolKernel Parse boolLib bossLib liteLib simpLib;

    (* Theories from theory/bir *)
    open bir_programTheory;

    (* Syntax function libraries from theory/bir *)
    open bir_programSyntax;

    (* Syntax function libraries from HOL4 *)
    open boolSyntax listSyntax;

    (* Simpsets from theory/bir *)
    open HolBACoreSimps;

    (* Local theories *)
    open bir_htTheory;

    val holba_ss = (std_ss++holBACore_ss)

    val [stmtsB_empty_na, stmtsB_nempty_na] =
      CONJUNCTS bir_stmtsB_has_no_assumes_def;

  in

    fun bir_stmtb_is_not_assume_pp stmtb_is_na =
      EQT_ELIM (
	SIMP_CONV holba_ss [bir_stmtb_is_not_assume_def] stmtb_is_na
      );

    fun bir_stmtsB_has_no_assumes_pp stmtsB_is_na =
      if ((is_nil o snd o dest_comb) stmtsB_is_na)
      then EQT_ELIM (REWRITE_CONV [stmtsB_empty_na] stmtsB_is_na)
      else
	let
	  val thm1 =
            SIMP_CONV std_ss [stmtsB_nempty_na] stmtsB_is_na

	  val thm1_lhs_tm = (snd o dest_eq o concl) thm1
	  (* Can split with boolSyntax.strip_conj and prove
           * conjuncts individually using
           * bir_stmtb_is_not_assume_pp. What is faster? *)
	  val thm1_lhs_thm =
	    EQT_ELIM (
	      SIMP_CONV holba_ss [bir_stmtb_is_not_assume_def,
				  stmtsB_empty_na] thm1_lhs_tm
	    )
	  val thm1_rhs = REWRITE_RULE [thm1_lhs_thm] thm1
	in
	  thm1_rhs
	end
    ;

    fun bir_block_has_no_assumes_pp block_is_na =
      let
	val thm1 =
	  SIMP_CONV holba_ss [bir_block_has_no_assumes_def]
            block_is_na
	val thm1_lhs_tm = (snd o dest_eq o concl) thm1
	val thm1_lhs_thm = bir_stmtsB_has_no_assumes_pp thm1_lhs_tm
	val thm1_rhs = REWRITE_RULE [thm1_lhs_thm] thm1
      in
	thm1_rhs
      end
    ;

    fun bir_prog_has_no_assumes_pp prog_is_na =
      let
	val thm1 =
	  SIMP_CONV holba_ss [bir_prog_has_no_assumes_def]
            prog_is_na
	val thm1_lhs_conj_tms =
	  (boolSyntax.strip_conj o snd o dest_eq o concl) thm1
	val thm1_lhs_conj_thms =
	  map bir_block_has_no_assumes_pp thm1_lhs_conj_tms
	val thm1_rhs = REWRITE_RULE thm1_lhs_conj_thms thm1
      in
	thm1_rhs
      end
    ;

  end

end
