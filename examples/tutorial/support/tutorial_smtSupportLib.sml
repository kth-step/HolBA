structure tutorial_smtSupportLib =
struct

open HolKernel Parse;
open bir_exp_to_wordsLib bslSyntax;
open bir_exp_tautologiesTheory;
open bir_expTheory bir_expSyntax;
open optionSyntax;

val wrap_exn = Feedback.wrap_exn "tutorial_smtSupportLib"

fun print_model model = List.foldl
  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
  () (rev model);

fun Z3_prove_or_print_model term =
  HolSmtLib.Z3_ORACLE_PROVE term
    handle HOL_ERR e =>
      (* Print a SAT model if the solver reports "SAT" *)
      let
        (* TODO: Check soundness of using strip_forall *)
        val (_, qf_tm) = strip_forall term
        val neg_tm = mk_neg qf_tm
        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL neg_tm
        val _ = print ( "Failed to prove the given term. "
                      ^ "Here is a counter-example:\n")
        val _ = print_model model;
        val _ = print "\n";
      in
        raise HOL_ERR e
      end
        handle _ => raise HOL_ERR e

(* TODO: Rewrite this to something more sensible *)
fun prove_bir_eval_exp_with_SMT_then_cheat_TAC (assum_list, goal) =
  let
    val (eval_tm, rhs_opt_tm) = dest_eq goal
    val _ = if (is_some rhs_opt_tm) then () else
      raise Fail "Cannot prove the goal because the RHS isn't SOME btrue.";
    val rhs_tm = dest_some rhs_opt_tm
    val _ = if (rhs_tm = ``BVal_Imm (Imm1 1w)``) then () else
      raise Fail "Cannot prove the goal because the RHS isn't btrue.";
    (**)
    val (bir_tm, env_tm) = dest_bir_eval_exp eval_tm
    val w_tm = bir2bool bir_tm
    (**)
    val w_thm = Z3_prove_or_print_model w_tm;
  in
    ([], K (prove (goal, cheat)))
  end;

fun prove_exp_is_taut imp_tm = (GEN_ALL o prove) (
  ``bir_exp_is_taut ^(imp_tm)``,
  PURE_REWRITE_TAC [bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >| [
    computeLib.RESTR_EVAL_TAC [``bir_is_bool_exp``] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [],

    (* TODO: Prove bir_var_set_is_well_typed *)
    computeLib.EVAL_TAC >>
    FULL_SIMP_TAC (srw_ss()) [] >>
    (* This is as far as we get with brute force... Format should be same for all situations.
     * Consider not simplifying this much if it fits better with theories you want to use *)
    cheat,

    (* Prove ''bir_eval_exp imp env'' using the bir2bool function and SMT solver *)
    computeLib.RESTR_EVAL_TAC [``bir_eval_exp``] >>
    prove_bir_eval_exp_with_SMT_then_cheat_TAC
  ]
);

fun bimp (ante, conseq) = bor (bnot ante, conseq)
  handle e => raise pretty_exnLib.pp_exn_s
    ( "Failed to create the implication. "
    ^ "Make sure that `ante` and `conseq` are BIR expression terms.")
    (wrap_exn "bimp" e)

local
  open bir_env_oldTheory;
  open bir_envTheory;

  val bir_var_set_is_well_typed_REWRS = prove(``
    (bir_var_set_is_well_typed (set [])) /\
    (!v vs. bir_var_set_is_well_typed (set (v::vs)) =
       EVERY (\v'. (bir_var_name v = bir_var_name v') ==> (bir_var_type v = bir_var_type v')) vs /\
       bir_var_set_is_well_typed (set vs)
       )
  ``,

    REPEAT STRIP_TAC >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [listTheory.LIST_TO_SET,
                              bir_var_set_is_well_typed_def, bir_vs_consistent_def]
    ) >>
    FULL_SIMP_TAC std_ss [listTheory.LIST_TO_SET,
              bir_var_set_is_well_typed_INSERT, listTheory.EVERY_MEM] >>
    METIS_TAC []
  );

  val pred_set_helper_thm = prove (
    ``!x s t. t UNION (x INSERT s) = if x IN t then t UNION s else (x INSERT t) UNION s``,
    METIS_TAC [
      pred_setTheory.INSERT_UNION,
      pred_setTheory.UNION_COMM,
      pred_setTheory.INSERT_UNION_EQ
    ]);


  val string_ss = rewrites (type_rws ``:string``);
  val char_ss = rewrites (type_rws ``:char``);

  val simp_conv_for_bir_var_set_is_well_typed = (
      (* first, convert the set to a list *)
      (RAND_CONV (REWRITE_CONV [pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]))
      THENC
      REPEATC (
	(fn x => REWRITE_CONV [Once pred_set_helper_thm] x)
	THENC (
	  (RATOR_CONV o LAND_CONV) (
	    (REWRITE_CONV [pred_setTheory.IN_INSERT])
	    THENC
	    (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss)
	      [pred_setTheory.NOT_IN_EMPTY])
	  )
	)
      ) THENC
      REWRITE_CONV [pred_setTheory.UNION_EMPTY]
    ) THENC
    (REWRITE_CONV [GSYM listTheory.LIST_TO_SET])
    THENC
    (* normalize to bir_var_set_is_well_typed *)
    (REWRITE_CONV [GSYM bir_var_set_is_well_typed_EQ_bir_vs_consistent])
    THENC
    (* then, repeatedly check for inconsistency of the first list element with the rest *)
    REPEATC (
      (fn x => REWRITE_CONV [Once bir_var_set_is_well_typed_REWRS] x)
      THENC
      (LAND_CONV EVAL) THENC
      (REWRITE_CONV [])
    ) THENC
    (* and finish when the end of the list is reached *)
    (REWRITE_CONV [bir_var_set_is_well_typed_REWRS]);

  (*
    val s = ``{BVar "hello"  (BType_Imm Bit64);
               BVar "hello2" (BType_Imm Bit32);
               BVar "hello"  (BType_Imm Bit32);
               BVar "hello3" (BType_Imm Bit32)}``;
  *)
in
  fun bir_vs_consistent_prove s =
    let val t = ``bir_vs_consistent ^s`` in
      prove (t,
	REWRITE_TAC [simp_conv_for_bir_var_set_is_well_typed t]
      )
    end;
end (* local for bir_vs_consistent_prove *)

end
