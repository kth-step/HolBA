structure birs_smtLib =
struct

local

open HolKernel Parse boolLib bossLib;

  (* error handling *)
  val libname = "birs_smtLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)



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

fun bir_check_taut use_holsmt ex =
  bir_check_unsat use_holsmt ``BExp_UnaryExp BIExp_Not ^ex``;




end (* local *)

end (* struct *)
