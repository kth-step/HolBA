(* ------------------------------------------------------------------------- *)
(*  Computation lib to evaluate BIR expressions                              *)
(* ------------------------------------------------------------------------- *)

structure bir_computeLib :> bir_computeLib =
struct

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory ;
open bir_computeTheory ;
open wordsLib ;
open cv_transLib ;
open bir_cv_computeTheory bir_cv_envLib ;

(* Takes a BIR expression and evaluates it using EVAL *)
fun compute_exp_EVAL (exp : term) (env: term) : thm =
  EVAL ``bir_compute_exp ^exp ^env``


(* CV COMPUTE *)


(* Takes an expression definition and evaluates it using cv_eval and deep embedding translation *)
fun compute_exp_cv (exp_def:thm) (env: term) : thm = 
let 
  (* Translate computation function, might have already been done *)
  val _ = cv_auto_trans bir_cv_compute_exp_def ;
  (* Deep embedding of our expression *)
  val _ = cv_trans_deep_embedding EVAL exp_def ;

  (* EVAL env if needed so it has the form of sequential updates *)
  val eval_env_thm = EVAL env ;
  val eval_env = rhs (concl eval_env_thm) ;
  (* Converts the env to a cv_env *)
  val cv_env_thm = env_to_cv_env_conv eval_env ;
  val cv_env = rand (rhs (concl cv_env_thm)) ;
  (* Get the expression term *)
  val exp = lhs (concl exp_def) ;
  (* Term to be computed *)
  val compute_term = ``bir_cv_compute_exp ^exp ^cv_env`` ;

  (* Evaluates term *)
  val evaled_term_thm = cv_eval compute_term ;
  
  (* Rewrites for correct theorem *)
  val rewritten_term_thm = 
      REWRITE_RULE [GSYM bir_compute_exp_eq_cv_compute_exp, GSYM cv_env_thm, GSYM eval_env_thm] 
        evaled_term_thm
in 
  rewritten_term_thm
end



end
