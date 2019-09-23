structure bir_auxiliaryLib :> bir_auxiliaryLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

(* This file contains tactics and other handy functions which are
 * not specific to BIR. *)

(* Utility tactics *)
fun QSPECL_ASSUM pat ls = PAT_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun QSPECL_X_ASSUM pat ls = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun FULLSIMP_BY_THM ss thm = FULL_SIMP_TAC ss [thm];

end
