(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolBA_HolSmtLib :> HolBA_HolSmtLib = struct

  open Abbrev

  fun GENERIC_SMT_TAC solver goal =
  let
    val ERR = Feedback.mk_HOL_ERR "HolBA_HolSmtLib" "GENERIC_SMT_TAC"
  in
    case solver goal of
      HolBA_SolverSpec.SAT NONE =>
      raise ERR "solver reports negated term to be 'satisfiable'"
    | HolBA_SolverSpec.SAT (SOME _) =>
      raise ERR
        "solver reports negated term to be 'satisfiable' (model returned)"
    | HolBA_SolverSpec.UNSAT NONE =>
      ([], fn _ => Thm.mk_oracle_thm "HolBA_HolSmtLib" goal)
    | HolBA_SolverSpec.UNSAT (SOME thm) =>
      (* 'thm' should be of the form "A' |- concl", where A' \subseteq A, and
         (A, concl) is the input goal (cf. HolBA_SolverSpec.sml) *)
      ([], fn _ => thm)
    | HolBA_SolverSpec.UNKNOWN NONE =>
      raise ERR
        "solver reports 'unknown' (solver not installed/problem too hard?)"
    | HolBA_SolverSpec.UNKNOWN (SOME message) =>
      raise ERR ("solver reports 'unknown' (" ^ message ^ ")")
  end

  val YICES_TAC = GENERIC_SMT_TAC HolBA_Yices.Yices_Oracle
  val Z3_ORACLE_TAC = GENERIC_SMT_TAC HolBA_Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC HolBA_Z3.Z3_SMT_Prover

  fun prove (tm, tac) = Tactical.TAC_PROOF(([], tm), tac)
  fun YICES_PROVE tm = prove (tm, YICES_TAC)
  fun Z3_ORACLE_PROVE tm = prove (tm, Z3_ORACLE_TAC)
  fun Z3_PROVE tm = prove (tm, Z3_TAC)

  (* report whether solvers are available *)
  val _ =
    let
      fun check_available prove_fn name =
        (
          prove_fn boolSyntax.T;  (* try to prove ``T`` *)
          Feedback.HOL_MESG ("HolBA_HolSmtLib: solver " ^ name ^ " is available.")
        )
      fun provoke_err prove_fn =
        ignore (prove_fn boolSyntax.T)  (* should fail *)
          handle Feedback.HOL_ERR {message, ...} =>
            Feedback.HOL_MESG ("HolBA_HolSmtLib: " ^ message)
    in
      Feedback.set_trace "HolBA_HolSmtLib" 0;
      if HolBA_Yices.is_configured () then
        check_available YICES_PROVE "Yices"
      else
        provoke_err YICES_PROVE;
      if HolBA_Z3.is_configured () then (
        check_available Z3_ORACLE_PROVE "Z3 (oracle)";
        check_available Z3_PROVE "Z3 (with proofs)"
      ) else
        provoke_err Z3_ORACLE_PROVE;
      Feedback.reset_trace "HolBA_HolSmtLib"
    end

end
