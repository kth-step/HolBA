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
open optionSyntax listSyntax bir_cv_programSyntax ;
open computeLib ;



(* ------------------------------------------------ *)
(* ------------------- UTILITIES ------------------ *)
(* ------------------------------------------------ *)

val ERR = mk_HOL_ERR "bir_computeLib" ;

(* Map the function f on a list by feeding arguments name1, name2 etc… *)
fun map_string_increasing (name : string) (f : string -> 'a -> 'b) (l : 'a list): 'b list  = 
  snd (foldl (fn (tm,(n,t)) => (n+1, (f (name ^ (Int.toString n)) tm)::t)) 
    (1, []) l );


(* Return a list where NONEs are filtered out and SOMEs are stripped *)
fun filter_option (l : 'a option list) : 'a list =
  rev $ foldl (fn (h,t) => if isSome h then (valOf h)::t else t) [] l

(* Deep embed a term and returns the definition *)
(* Creates name_bir_cv_def *)
fun deep_embed_term (name:string) (tm:term) : thm =
let
  val deep_name = name ^ "_bir_cv" ;
  val _ = new_constant (deep_name, type_of tm) ;
  val deep_constant = mk_const (deep_name, type_of tm) ;
  val deep_constant_def = new_definition (deep_name ^ "_def", ``^deep_constant = ^tm``) ;
  (* Add to compset *)
  val _ = add_thms [deep_constant_def] the_compset ;

  val _ = print "Translating with deep embedding...\n" ;
  val _ = time (cv_trans_deep_embedding EVAL) deep_constant_def ;
in deep_constant_def end

(* Translates a raw term (unamed), outputing a theorem tm = from v *)
(* Creates name_bir_cv_eq *)
fun translate_raw_term (bir_conv : conv) (name : string) (tm : term) : thm =
let
  (* Translate to cv_exp *)
  val _ = print "Translating one raw term...\n" ;
  val from_thm = time bir_conv tm ;
  val _ = save_thm (name ^ "_bir_cv_eq", from_thm) ;
in from_thm end


(* Translates a name term, outputing a theorem tm = from v *)
(* Creates name_bir_cv_eq *)
(* NOTE : The term has to be EVALable *)
fun translate_named_term (bir_conv : conv) (tm : term) : thm = 
let 
  (* Fetch expression information *)
  val name = fst (dest_const tm) ;
  (* Get the actual value *)
  val evaled_thm = EVAL tm ;
  val evaled_tm = rhs (concl evaled_thm) ;
  (* Translate using conversion *)
  val _ = print "Translating one named term...\n" ;
  val from_val_thm = time bir_conv evaled_tm ;
  val from_named_thm = REWRITE_RULE [GSYM evaled_thm] from_val_thm ;
  val _ = save_thm (name ^ "_bir_cv_eq", from_named_thm) ;
in from_named_thm end



(* ----------------------------------------------- *)
(* ----------------- EXPRESSIONS ----------------- *)
(* ----------------------------------------------- *)


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
  val exp_name = fst $ dest_const exp ;
  val from_exp_thm = translate_named_term bir_exp_conv exp ;
  val cv_exp = rand (rhs (concl from_exp_thm)) ;
  (* Create the new constant term *)
  val cv_exp_def = deep_embed_term exp_name cv_exp ;
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

(* Deep embeds the expression, if any, in the label expression *)
fun deep_embed_label_exp (name : string) (cv_le_tm : term) : thm option = 
  if is_cv_le_exp cv_le_tm then
    let val cv_exp_tm = dest_cv_le_exp cv_le_tm ;
    in SOME (deep_embed_term (name ^ "_label_exp") cv_exp_tm) end
  else NONE


(* Deep embeds a basic statement *)
fun deep_embed_basic_stmt (name : string) (cv_stmt_tm : term) : thm =
let 
  (* Deep embed the nested expressions *)
  val thms_for_rewrite = 
    if is_cv_stmt_assign cv_stmt_tm then 
      let val (_, cv_exp_tm) = dest_cv_stmt_assign cv_stmt_tm ;
      in [deep_embed_term (name ^ "_exp") cv_exp_tm] end
    else 
      raise (ERR "deep_embed_basic_stmt" "not a basic statement")
  val thms_for_rewrite_gsym = map GSYM thms_for_rewrite ;
  (* Rewrite the statement with the embedded expressions *)
  val stmt_embed_exp_thm = REWRITE_CONV thms_for_rewrite_gsym cv_stmt_tm ;
  val stmt_embed_exp_tm = rhs (concl stmt_embed_exp_thm) ;
  (* Embeds the whole statement *)
  val deep_embed_stmt_thm = deep_embed_term name stmt_embed_exp_tm
in REWRITE_RULE [GSYM stmt_embed_exp_thm] deep_embed_stmt_thm end

(* Deep embeds a end statement *)
fun deep_embed_end_stmt (name : string) (cv_stmt_tm : term) : thm =
let
  (* Deep embed the nested expressions *)
  val thms_for_rewrite = 
    if is_cv_stmt_jmp cv_stmt_tm then 
      let val cv_le_tm = dest_cv_stmt_jmp cv_stmt_tm ;
        val embed_le_thm_opt = deep_embed_label_exp (name ^ "_le") cv_le_tm ;
      in filter_option [embed_le_thm_opt] end
    else if is_cv_stmt_cjmp cv_stmt_tm then
      let val (cv_exp_tm, cv_le_tm1, cv_le_tm2) = dest_cv_stmt_cjmp cv_stmt_tm ;
        val embed_exp_thm = deep_embed_term (name ^ "_cexp") cv_exp_tm ;
        val embed_le_thm_opt1 = deep_embed_label_exp (name ^ "_leT") cv_le_tm1 ;
        val embed_le_thm_opt2 = deep_embed_label_exp (name ^ "_leF") cv_le_tm2 ;
      in (embed_exp_thm) :: (filter_option [embed_le_thm_opt1, embed_le_thm_opt2]) end
    else 
      raise (ERR "deep_embed_end_stmt" "not an end statement")
  val thms_for_rewrite_gsym = map GSYM thms_for_rewrite ;
  (* Rewrite the statement with the embedded expressions *)
  val stmt_embed_exp_thm = QCONV (REWRITE_CONV thms_for_rewrite_gsym) cv_stmt_tm ;
  val stmt_embed_exp_tm = rhs (concl stmt_embed_exp_thm) ;
  (* Embeds the whole statement *)
  val deep_embed_stmt_thm = deep_embed_term name stmt_embed_exp_tm
in REWRITE_RULE [Once $ GSYM stmt_embed_exp_thm] deep_embed_stmt_thm end

(* Deep embeds a block and its statements *)
fun deep_embed_block (name : string) (cv_block_tm : term) : thm =
let
  val (_, basic_list_tm, end_stmt_tm) = dest_cv_block cv_block_tm ;
  (* Get basic statements *)
  val basic_tm_list = fst $ dest_list basic_list_tm ;
  (* Deep embeds all basic statements *)
  val embed_basic_thm_list = 
    map_string_increasing (name ^ "_stmt_basic_") deep_embed_basic_stmt basic_tm_list ;

  (* Deep embeds end statement *)
  val embed_end_thm = deep_embed_end_stmt (name ^ "_stmt_end") end_stmt_tm ;

  val thm_for_rewrite = map GSYM (embed_end_thm::embed_basic_thm_list) ;

  val rw_thm = ONCE_REWRITE_CONV thm_for_rewrite cv_block_tm ;

in rw_thm end
  


(* Deep embedding of our programs (same as above with expressions *)
(* Note : here, we only do a deep embedding of program, not the expressions inside *)
(* WARNING : this creates theorems suffixed by _bir_cv_def, _bir_cv_eq. *)
fun translate_program_cv (program_def:thm) = 
let 
  (* Fetch expression information *)
  val program = lhs (concl program_def) ;
  val program_name = fst (dest_const program) ;
  (* Translate to cv_program *)
  val _ = print "Translating to cv_program...\n" ;
  val from_program_thm = translate_named_term bir_program_conv program
  val cv_program = rand (rhs (concl from_program_thm)) ;
  (* Get the block list of the cv program *)
  val cv_block_list_tm = dest_cv_program cv_program ;
  val cv_block_tm_list = fst $ dest_list cv_block_list_tm ;
  (* Recursively deep embeds blocks, statements and expressions *)
  val _ = print "Starting recursive deep embedding...\n" ;
  val embed_block_thm_list = 
    map_string_increasing (program_name ^ "_block_") deep_embed_block cv_block_tm_list
  val embed_program_thm = REWRITE_CONV embed_block_thm_list cv_program ;
  (* Get the program with embed statements *)
  val embed_program_tm = rhs (concl embed_program_thm) ;

  val cv_program_def = deep_embed_term program_name embed_program_tm ;
  (* val _ = time (cv_trans_deep_embedding EVAL) cv_program_def ; *)
  (* This translation is rather slow... Can we skip it ? *)
  (* val _ = time cv_trans cv_program_def ; *)
in cv_program_def end

fun compute_step_cv (program_def : thm) (state_tm : term) : thm =
let
  (* Quickly EVAl the state so that the env inside as a correct form *)
  val eval_state_thm = EVAL state_tm ;
  val eval_state_tm = rhs (concl eval_state_thm) ;
  (* Converts state to cv_state *)
  val _ = print "Translating state...\n" ;
  val cv_state_thm = time bir_state_conv eval_state_tm ;
  val cv_state_tm = rand (rhs (concl cv_state_thm)) ;
  (* Get the program term *)
  val program = lhs (concl program_def) ;
  (* Fetches theorems from prior translation of program *)
  val program_name = fst (dest_const program) ;
  val cv_program_name = program_name ^ "_bir_cv" ;
  val from_program_thm = DB.fetch "-" (cv_program_name ^ "_eq") ;
  val cv_program_def = DB.fetch "-" (cv_program_name ^ "_def") ;
  val cv_program = rhs (concl cv_program_def) ;
  (* Term to be computed *)
  val compute_term = ``bir_cv_compute_step ^cv_program ^cv_state_tm`` ;

  (* Evaluates step *)
  val _  = print "Applying cv_eval...\n"
  val evaled_term_thm = time cv_eval compute_term ;
  
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
