structure bir_auxiliaryLib :> bir_auxiliaryLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

(* This file contains tactics and other handy functions which are
 * not specific to BIR. *)

(* Utility tactics *)
fun QSPECL_ASSUM pat ls = PAT_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun QSPECL_X_ASSUM pat ls = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun FULLSIMP_BY_THM ss thm = FULL_SIMP_TAC ss [thm];

(* Utility rules *)
fun HO_MATCH_MPL thm []     = thm
  | HO_MATCH_MPL thm (h::t) = HO_MATCH_MPL (HO_MATCH_MP thm h) t;

local
  fun insert_tm x [] = [x]
    | insert_tm x (y::ys) = 
	if Term.compare (x, y) = LESS
	then x::(y::ys)
	else y::(insert_tm x ys)
in
  (* Good for sorting short lists of terms *)
  fun ins_sort_tm [] = []
    | ins_sort_tm (x::xs) = insert_tm x (ins_sort_tm xs)
end;

end
