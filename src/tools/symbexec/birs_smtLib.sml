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
local
  val debug_z3_taut_on = false;
  val fix_wtm = subst [mk_var ("MEM", ``:word64|->word8``) |-> Term`MEMV:word64|->word8`];
in
 fun holsmt_is_taut wtm =
  let val wtm_fixed = fix_wtm wtm; in
    ((HolBA_HolSmtLib.Z3_ORACLE_PROVE wtm_fixed; true)
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

open bir_smtLib;

fun birsmt_check_unsat bexp =
  let
    val exst = export_bexp bexp exst_empty;
    val result = querysmt NONE (exst_to_querysmt exst);

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "bir_smt_check_unsat" "smt solver couldn't determine satisfiability"
  in
    result = BirSmtUnsat
  end;

(* ======================================= *)

fun bir_check_unsat use_holsmt =
  if use_holsmt then
    Profile.profile "bir_check_unsat::holsmt" holsmt_bir_check_unsat
  else
    Profile.profile "bir_check_unsat::birsmt" birsmt_check_unsat;

fun bir_check_sat use_holsmt ex =
  not (bir_check_unsat use_holsmt ex);

fun bir_check_taut use_holsmt ex =
  bir_check_unsat use_holsmt (bir_expSyntax.mk_BExp_UnaryExp (bir_exp_immSyntax.BIExp_Not_tm, ex));


end (* local *)

end (* struct *)
