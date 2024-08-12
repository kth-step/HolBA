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
open bir_cv_basicLib ;
open bir_programTheory bir_cv_programTheory ;
open bir_cv_programLib ;

(* Takes a BIR expression and evaluates it using EVAL *)
fun compute_exp_EVAL (exp : term) (env: term) : thm =
  EVAL ``bir_compute_exp ^exp ^env``


(* CV COMPUTE *)
(* Translate computation function when loading lib *)
val _  = cv_auto_trans_rec cv_n2l_def 
  (WF_REL_TAC `measure (cv_size)` >> Cases_on `cv_n` >> rw [cv_size_def]) ;


val bir_cv_compute_exp_pre_cases  = cv_auto_trans_pre bir_cv_compute_exp_def ;
val _ = store_thm("bir_cv_compute_exp_pre[cv_pre]", ``!v env. bir_cv_compute_exp_pre v env``,
  Induct_on `v` >>
  rw [Once bir_cv_compute_exp_pre_cases]) ;

val _ = cv_auto_trans bir_cv_compute_step_def ;

(* Deep embedding of our expression *)
(* WARNING : this creates theorems suffixed by _bir_cv_def, _bir_cv_eq. *)
fun translate_exp_cv (exp_def:thm) = 
let 
  (* Fetch expression information *)
  val exp = lhs (concl exp_def) ;
  val exp_val = rhs (concl exp_def) ;
  val exp_name = fst (dest_const exp) ;
  (* Translate to cv_exp *)
  val _ = print "Translating to cv_exp...\n" ;
  val from_exp_val_thm = time bir_exp_conv exp_val ;
  val from_exp_thm = REWRITE_RULE [GSYM exp_def] from_exp_val_thm ;
  val cv_exp = rand (rhs (concl from_exp_thm)) ;
  (* Create the new constant term *)
  val cv_exp_name = exp_name ^ "_bir_cv" ;
  val _ = new_constant (cv_exp_name, ``:bir_cv_exp_t``) ;
  val cv_exp_constant = mk_const (cv_exp_name, ``:bir_cv_exp_t``) ;
  val cv_exp_def = new_definition (cv_exp_name ^ "_def", ``^cv_exp_constant = ^cv_exp``) ;
  val _ = save_thm (cv_exp_name ^ "_eq", from_exp_thm) ;

  val _ = print "Translating with deep embedding...\n" ;
  val _ = time (cv_trans_deep_embedding EVAL) cv_exp_def ;
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
  (* Fetches the translation theorems *)
  val exp_name = fst (dest_const exp) ;
  val cv_exp_name = exp_name ^ "_bir_cv" ;
  val from_exp_thm = DB.fetch "-" (cv_exp_name ^ "_eq") ;
  val cv_exp_def = DB.fetch "-" (cv_exp_name ^ "_def") ;
  val cv_exp = lhs (concl cv_exp_def) ;
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


(* ----------------------------------------------- *)
(* ------------------- PROGRAMS ------------------ *)
(* ----------------------------------------------- *)

(* Use EVAL to compute a program step *)
fun compute_step_EVAL (program : term) (state: term) : thm =
  EVAL ``bir_compute_step ^program ^state``

(* Deep embedding of our programs (same as above with expressions *)
(* Note : here, we only do a deep embedding of program, not the expressions inside *)
(* WARNING : this creates theorems suffixed by _bir_cv_def, _bir_cv_eq. *)
fun translate_program_cv (program_def:thm) = 
let 
  (* Fetch expression information *)
  val program = lhs (concl program_def) ;
  val program_val = rhs (concl program_def) ;
  val program_name = fst (dest_const program) ;
  (* Translate to cv_program *)
  val _ = print "Translating to cv_program...\n" ;
  val from_program_val_thm = time bir_program_conv program_val ;
  val from_program_thm = REWRITE_RULE [GSYM program_def] from_program_val_thm ;
  val cv_program = rand (rhs (concl from_program_thm)) ;
  (* Create the new constant term *)
  val cv_program_name = program_name ^ "_bir_cv" ;
  val _ = new_constant (cv_program_name, ``:bir_cv_program_t``) ;
  val cv_program_constant = mk_const (cv_program_name, ``:bir_cv_program_t``) ;
  val cv_program_def = new_definition (cv_program_name ^ "_def", ``^cv_program_constant = ^cv_program``) ;
  val _ = save_thm (cv_program_name ^ "_eq", from_program_thm) ;

  val _ = print "Translating with deep embedding...\n" ;
  (* WARNING : Deep embedding program doesn’t work. We want to deep embed each exp *)
  (* val _ = time (cv_trans_deep_embedding EVAL) cv_program_def ; *)
  val _ = time cv_trans cv_program_def ;
in () end

fun compute_step_cv (program_def : thm) (state_tm : term) : thm =
let
  (* Quickly EVAl the state so that the env inside as a correct form *)
  val eval_state_thm = EVAL state_tm ;
  val eval_state_tm = rhs (concl eval_state_thm) ;
  (* Converts state to cv_state *)
  val cv_state_thm = bir_state_conv eval_state_tm ;
  val cv_state_tm = rand (rhs (concl cv_state_thm)) ;
  (* Get the program term *)
  val program = lhs (concl program_def) ;
  (* Fetches theorems from prior translation of program *)
  val program_name = fst (dest_const program) ;
  val cv_program_name = program_name ^ "_bir_cv" ;
  val from_program_thm = DB.fetch "-" (cv_program_name ^ "_eq") ;
  val cv_program_def = DB.fetch "-" (cv_program_name ^ "_def") ;
  val cv_program = lhs (concl cv_program_def) ;
  (* Term to be computed *)
  val compute_term = ``bir_cv_compute_step ^cv_program ^cv_state_tm`` ;

  (* Evaluates step *)
  val evaled_term_thm = cv_eval compute_term ;
  
  (* Apply from_cv_state to match bir_cv_compute_step_eq_compute_exp *)
  val from_evaled_term_thm = AP_TERM ``from_cv_state`` evaled_term_thm ;
  (* Evaluates the from_cv_state conversion of the response *)
  val evaled_from_result = EVAL (rhs (concl from_evaled_term_thm)) ;
  
  (* Rewrites for correct theorem *)
  val rewritten_term_thm = 
      REWRITE_RULE [evaled_from_result, bir_cv_compute_step_eq_compute_exp, GSYM
                   cv_state_thm, cv_program_def, GSYM from_program_thm, 
                   Once $ GSYM eval_state_thm] 
        from_evaled_term_thm

in rewritten_term_thm end






end
