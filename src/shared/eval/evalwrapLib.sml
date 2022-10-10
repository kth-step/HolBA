structure evalwrapLib :> evalwrapLib =
struct

open HolKernel Parse boolLib bossLib;
open computeLib;

(*
 * This file offers functionality to evaluate a term given preconditions.
 *
 * TODO
 * - each free variable from preconditions and conclusion should probably have
 *   matching type
 *)

(*
 * evaluate a term  tm  in a context  ctxt : term list
 * given list of constants   stop_consts1  and  stop_consts2
 * whose definition should not be unfolded in the first and second evaluation
 * step, respectively.
 *)
fun eval_ctxt_gen stop_consts1 stop_consts2 ctxt tm =
  let
    val assl = List.map ASSUME ctxt;
    val depth = length assl;
  in
    RESTR_EVAL_CONV stop_consts1 tm
    |> CONJ $ LIST_CONJ assl
    |> CONV_RULE $ RAND_CONV $ RAND_CONV $ REWRITE_CONV assl
    |> DISCH_ALL
    |> REWRITE_RULE[IMP_CONJ_THM]
    (* evaluated term comes last in above CONJ *)
    |> CONJUNCTS |> last
    (* eval the rightmost path (depth-many implications plus one for
       right-hand side of EVAL equality) *)
    |> CONV_RULE $ PATH_CONV (funpow depth (fn x => x ^ "r") "r") $ RESTR_EVAL_CONV stop_consts2
    |> GEN_ALL
  end;

(*
 * evaluate a term  tm  given a list of preconditions
 * Example:
 *   qeval_ctxt [`f 3n = 24n`]  `g o f:num -> num $ 1 + 2`
 * returns
 *   ⊢ ∀g f. f 3 = 24 ⇒ (g ∘ f) (1 + 2) = g 24: thm
 *)
fun qeval_ctxt ctxt tm =
  eval_ctxt_gen [] [] (map Term ctxt) $ Term tm

(*
*)

end
