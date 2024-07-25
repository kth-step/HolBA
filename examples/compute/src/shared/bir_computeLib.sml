(* ------------------------------------------------------------------------- *)
(*  Computation lib to evaluate BIR expressions                              *)
(* ------------------------------------------------------------------------- *)

structure bir_computeLib :> bir_computeLib =
struct

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory bir_cv_basicTheory ;
open bir_computeTheory ;
open wordsLib ;
open cv_transLib cv_stdTheory cvTheory ;
open bir_cv_computeTheory bir_cv_envLib ;
open bir_cv_memTheory ;

(* Takes a BIR expression and evaluates it using EVAL *)
fun compute_exp_EVAL (exp : term) (env: term) : thm =
  EVAL ``bir_compute_exp ^exp ^env``


(* CV COMPUTE *)
(* Translate computation function when loading lib *)
val _  = cv_auto_trans_rec bir_cv_compute_exp_def 
  (WF_REL_TAC `measure (cv_size)` >> Cases_on `cv_n` >> rw [cv_size_def]) ;



(* Deep embedding of our expression *)
fun translate_exp_cv (exp_def:thm) = 
let 
  val _ = print "Translating with deep embedding...\n" ;
  val _ = time (cv_trans_deep_embedding EVAL) exp_def ;
in () end

(* Takes an expression definition and evaluates it using cv_eval and deep embedding translation *)
fun compute_exp_cv (exp_def:thm) (env: term) : thm = 
let 
  (* EVAL env if needed so it has the form of sequential updates *)
  val eval_env_thm = EVAL env ;
  val eval_env = rhs (concl eval_env_thm) ;
  (* Converts the env to a cv_env *)
  val cv_env_thm = env_to_cv_env_conv eval_env ;
  val cv_env = rand (rhs (concl cv_env_thm)) ;
  (* Get the expression term *)
  val exp = lhs (concl exp_def) ;
  val to_cv_exp_thm = EVAL ``to_cv_exp ^exp`` ;
  (* TODO : Deep embedding isn’t good here... *)
  val cv_exp = rhs (concl to_cv_exp_thm)
  (* from_cv_exp to_cv_exp exp = from_cv_exp exp *)
  val from_to_exp_thm = AP_TERM ``from_cv_exp`` to_cv_exp_thm;
  val from_exp_thm = REWRITE_RULE [from_to_cv_exp] from_to_exp_thm
  (* Term to be computed *)
  val compute_term = ``bir_cv_compute_exp ^cv_exp ^cv_env`` ;

  (* Evaluates term *)
  val evaled_term_thm = cv_eval compute_term ;
  
  (* Apply from to match bir_compute_exp_eq_cv_compute_exp *)
  val from_opt_evaled_term_thm = AP_TERM ``from_cv_val_option`` evaled_term_thm ;
  (* Evaluates the from_cv_val_option conversion of the response *)
  val evaled_from_result = EVAL (rhs (concl from_opt_evaled_term_thm)) ;
  
  (* Rewrites for correct theorem *)
  val rewritten_term_thm = 
      REWRITE_RULE [GSYM bir_compute_exp_eq_cv_compute_exp, GSYM cv_env_thm,
      GSYM eval_env_thm, GSYM from_exp_thm, evaled_from_result] 
        from_opt_evaled_term_thm
in 
  rewritten_term_thm
end



end
