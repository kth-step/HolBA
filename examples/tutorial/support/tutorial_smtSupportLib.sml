structure tutorial_smtSupportLib =
struct

open HolKernel Parse;
open bir_exp_to_wordsLib bslSyntax;
open bir_exp_tautologiesTheory;
open bir_expTheory bir_expSyntax;

val wrap_exn = Feedback.wrap_exn "tutorial_smtSupportLib"

fun prove_bir_eval_exp_with_SMT_then_cheat_TAC (assum_list, goal) =
  let
    val (eval_tm, rhs_tm) = dest_eq goal
    val _ = if (rhs_tm <> ``BVal_Imm (Imm1 1w)``) then
      raise Fail "Cannot prove the goal because the RHS isn't btrue." else ();
    (**)
    val (bir_tm, env_tm) = dest_bir_eval_exp eval_tm
    val w_tm = bir2bool bir_tm
    (**)
    val proved_w_thm = HolSmtLib.Z3_ORACLE_PROVE w_tm
      handle HOL_ERR e =>
        let
          fun print_model model = List.foldl
            (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
            () (rev model);
          val neg_tm = mk_neg w_tm
          val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL neg_tm
          val _ = print "Failed to prove the implication. Here is a counter-example:\n";
          val _ = print_model model;
        in
          raise HOL_ERR e
        end
          handle _ => raise HOL_ERR e
  in
    ([], K (prove (goal, cheat)))
  end;

fun prove_exp_is_taut imp_tm = prove (
  ``bir_exp_is_taut ^(imp_tm)``,
  PURE_REWRITE_TAC [bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >| [
    (* Prove bir_is_bool_exp using cheat *)
    cheat
    ,
    (* Prove bir_var_set_is_well_typed using cheat *)
    cheat
    ,
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

end
