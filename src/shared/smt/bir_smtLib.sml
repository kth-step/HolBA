structure bir_smtLib =
struct

local

open HolKernel Parse boolLib bossLib;

open HolBA_HolSmtLib

  (* error handling *)
  val libname = "bir_smtLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname


(* ======================================= *)

local
  val debug_z3_taut_on = false;
  val fix_wtm = subst [mk_var ("MEM", ``:word64|->word8``) |-> Term`MEMV:word64|->word8`];
in
 fun holsmt_is_taut wtm =
  let val wtm_fixed = fix_wtm wtm; in
    ((Z3_ORACLE_PROVE wtm_fixed; true)
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
end;

fun holsmt_bir_check_unsat bexp =
  let
    (* little amounts of output *)
    val _ = HolBA_Library.trace := 1;
    val pcond_bexp = (snd o dest_eq o concl o EVAL) bexp;
    val wtm = bir_exp_to_wordsLib.bir2bool pcond_bexp;
  in
    holsmt_is_taut (mk_neg wtm)
  end;

local
 open bir_smtlibLib;
in
 fun birsmt_check_unsat bexp =
  let
    val exst = export_bexp bexp exst_empty;
    val result = querysmt NONE (exst_to_querysmt exst);

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "bir_smt_check_unsat" "smt solver couldn't determine satisfiability"
  in
    result = BirSmtUnsat
  end;
end;

local

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_exp_to_wordsLib bslSyntax;
open bir_exp_tautologiesTheory;
open bir_expTheory bir_expSyntax;
open optionSyntax;

fun print_model model = List.foldl
  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
  () (rev model);

fun Z3_prove_or_print_model term =
  HolBA_HolSmtLib.Z3_ORACLE_PROVE term
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
val oracletag = "bir_smtLib";
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

in

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
val Z3_prove_or_print_model = Z3_prove_or_print_model;
end

(* ======================================= *)
in (* local *)
(* ======================================= *)

fun bir_smt_check_unsat use_holsmt =
  if use_holsmt then
    Profile.profile "bir_smt_check_unsat::holsmt" holsmt_bir_check_unsat
  else
    Profile.profile "bir_smt_check_unsat::birsmt" birsmt_check_unsat;

fun bir_smt_check_sat use_holsmt ex =
  not (bir_smt_check_unsat use_holsmt ex);

fun bir_smt_check_taut use_holsmt ex =
  bir_smt_check_unsat use_holsmt (bir_expSyntax.mk_BExp_UnaryExp (bir_exp_immSyntax.BIExp_Not_tm, ex));

(* ======================================= *)

fun bir_smt_prove use_holsmt =
  if use_holsmt then
    Z3_ORACLE_PROVE
  else
    raise ERR "bir_smt_prove" "not implemented";

fun bir_smt_tac use_holsmt =
  if use_holsmt then
    Z3_ORACLE_TAC
  else
    raise ERR "bir_smt_tac" "not implemented";

fun bir_smt_set_trace use_holsmt =
  if use_holsmt then
    (fn x => HolBA_Library.trace := x) (* same as Feedback.set_trace "HolBA_HolSmtLib" *)
  else
    (fn _ => ());

fun bir_smt_get_model use_holsmt =
  if use_holsmt then
    Z3_SAT_modelLib.Z3_GET_SAT_MODEL
  else
    raise ERR "bir_smt_get_model" "not implemented";

(* ======================================= *)

val bir_smt_prove_is_taut = prove_exp_is_taut;

val bir_smt_prove_or_print_model = Z3_prove_or_print_model;

end (* local *)

end (* struct *)
