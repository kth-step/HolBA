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
 * evaluate a term  tm  in a non-empty context  ctxt : term list
 * given list of constants   stop_consts1  and  stop_consts2
 * whose definition should not be unfolded in the first and second evaluation
 * step, respectively.
 *)
fun eval_ctxt_gen stop_consts1 stop_consts2 ctxt tm =
  let
    val assl = map ASSUME ctxt;
  in
    RESTR_EVAL_CONV stop_consts1 tm
    |> CONJ (PROVE_HYP (LIST_CONJ assl) TRUTH)
    |> CONJUNCT2
    |> CONV_RULE $ RAND_CONV $ REWRITE_CONV assl
    |> CONV_RULE $ RAND_CONV $ RESTR_EVAL_CONV stop_consts2
    |> DISCH_ALL
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
