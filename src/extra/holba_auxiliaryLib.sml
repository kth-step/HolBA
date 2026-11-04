structure holba_auxiliaryLib :> holba_auxiliaryLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

(* This file contains tactics and other handy functions which are
 * not specific to BIR. *)

(* Utility tactics *)
fun QSPECL_ASSUM pat ls = PAT_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun QSPECL_X_ASSUM pat ls = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun FULLSIMP_BY_THM ss thm = FULL_SIMP_TAC ss [thm];

(* Like irule, but first instantiates universally quantified variables
 * of thm by name, e.g. QINST_IRULE [("pre1", `P x`)] thm. Free variables
 * of the instantiations (here x) are kept fixed, unlike with irule
 * followed by qexists_tac, and the instantiation does not depend on
 * the order in which irule would generate existentials. *)
fun QINST_IRULE substs thm =
  let
    val th = SPEC_ALL thm;
    val vs = free_vars (concl th);
    fun inst1 (n, q) =
      case List.find (fn v => fst (dest_var v) = n) vs of
          SOME v => v |-> Parse.typedTerm q (type_of v)
        | NONE => raise mk_HOL_ERR "holba_auxiliaryLib" "QINST_IRULE"
                          ("no quantified variable named " ^ n);
  in
    MATCH_MP_TAC (REWRITE_RULE [boolTheory.AND_IMP_INTRO] (INST (map inst1 substs) th))
  end;

(* Like irule, but first rewrites both the goal and thm with the
 * theorems ths, e.g. definitions of constants that name the same
 * value differently in the goal and in thm. *)
fun UNFOLD_IRULE ths thm =
  REWRITE_TAC ths >> irule (REWRITE_RULE ths thm);

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

(* Utility functions *)
  fun list_split_pred_aux acc p [] = fail ()
    | list_split_pred_aux acc p (x::xs) =
      (if x = p then (List.rev acc, xs)
       else list_split_pred_aux (x::acc) p xs)

  fun list_split_pred p = list_split_pred_aux [] p

end
