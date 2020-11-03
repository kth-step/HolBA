structure tutorial_smtSupportLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
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

(*
val env = bir_envSyntax.mk_BEnv ``env:string -> (bir_val_t option)``;
val goal = ``^(mk_bir_eval_exp (band (btrue, btrue), env)) = SOME (BVal_Imm (Imm1 1w))``;
*)

(* TODO: Add proof and use w_thm to replace the oracle here *)
val oracletag = "tutorial_smtSupportLib";
val SmtSupportLibThm = mk_oracle_thm oracletag;
fun prove_bir_eval_exp_with_SMT_then_oracle_TAC (assum_list, goal) =
  let
    val (eval_tm, rhs_opt_tm) = dest_eq goal
    val _ = if (is_some rhs_opt_tm) then () else
      raise Fail "Cannot prove the goal because the RHS isn't SOME btrue.";
    val rhs_tm = dest_some rhs_opt_tm
    val _ = if (identical rhs_tm ``BVal_Imm (Imm1 1w)``) then () else
      raise Fail "Cannot prove the goal because the RHS isn't btrue.";
    (**)
    val (bir_tm, env_tm) = dest_bir_eval_exp eval_tm
    val w_tm = bir2bool bir_tm
    (**)
    val w_thm = Z3_prove_or_print_model w_tm;
    (* the line above fails with an exception if the goal converted
          to word theory wasn't provable*)
    val oracle_thm = SmtSupportLibThm ([], goal);
  in
    ([], K oracle_thm)
  end;

(*
val thm = prove (goal, prove_bir_eval_exp_with_SMT_then_oracle_TAC);
*)
(*
val imp_tm = bor (bnot (beq (bden (bvarimm32 "x") , bden (bvarimm32 "y"))), beq (bden (bvarimm32 "y"), bden (bvarimm32 "x")));
*)

fun prove_exp_is_taut imp_tm = (GEN_ALL o prove) (
  ``bir_exp_is_taut ^(imp_tm)``,
  PURE_REWRITE_TAC [bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >| [
    computeLib.RESTR_EVAL_TAC [``bir_is_bool_exp``] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [],

    computeLib.RESTR_EVAL_TAC [``bir_var_set_is_well_typed``] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.bir_var_set_is_well_typed_ss) [],

    (* Prove ''bir_eval_exp imp env'' using the bir2bool function and SMT solver *)
    computeLib.RESTR_EVAL_TAC [``bir_eval_exp``] >>
    prove_bir_eval_exp_with_SMT_then_oracle_TAC
  ]
);

fun bimp (ante, conseq) = bor (bnot ante, conseq)
  handle e => raise pretty_exnLib.pp_exn_s
    ( "Failed to create the implication. "
    ^ "Make sure that `ante` and `conseq` are BIR expression terms.")
    (wrap_exn "bimp" e)

end
