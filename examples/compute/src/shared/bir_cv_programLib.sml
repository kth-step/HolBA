structure bir_cv_programLib :> bir_cv_programLib =
struct

open HolKernel Parse boolLib bossLib ;
open bir_cv_programTheory ;
open bir_programSyntax bir_cv_programSyntax ;
open bir_cv_basicLib bir_cv_envLib ;
open listSyntax ;


val ERR = mk_HOL_ERR "bir_cv_programLib" ;

(* TODO : Remove test *)
val exp = ``BExp_Const (Imm64 1w)``


(* Returns bir_le_label_tm = from_cv_label_exp v *)
fun bir_le_label_conv (bir_le_label_tm : term) : thm =
  let
    val label = dest_le_label bir_le_label_tm ;
    val cv_le_label_tm = mk_cv_le_label label ;
    val rw_thm = REWRITE_CONV [from_cv_label_exp_def] ``from_cv_label_exp ^cv_le_label_tm`` ;
  in GSYM rw_thm end

(* Returns bir_le_exp_tm = from_cv_label_exp v *)
fun bir_le_exp_conv (bir_le_exp_tm : term) : thm =
  let 
    val exp_tm = dest_le_exp bir_le_exp_tm ;
    val cv_exp_thm = bir_exp_conv exp_tm ;
    val cv_exp_tm = rand (rhs (concl cv_exp_thm)) ;
    val cv_le_exp_tm = mk_cv_le_exp cv_exp_tm ;
    val rw_thm = REWRITE_CONV [from_cv_label_exp_def, GSYM cv_exp_thm] ``from_cv_label_exp ^cv_le_exp_tm`` ;
  in GSYM rw_thm end

(* Returns tm = from_cv_label_exp v *)
fun bir_label_exp_conv (tm : term) : thm = 
  if is_le_label tm then
    bir_le_label_conv tm
  else if is_le_exp tm then
    bir_le_exp_conv tm
  else raise (ERR "bir_label_exp_conv" "not bir_label_exp_t")




(* Returns tm = from_cv_stmt_basic v *)
fun bir_stmt_assign_conv (tm : term) : thm = 
  let
    val (var_tm, exp_tm) = dest_stmt_assign tm ;
    val cv_exp_thm = bir_exp_conv exp_tm ;
    val cv_exp_tm = rand (rhs (concl cv_exp_thm)) ;
    val cv_assign_tm = mk_cv_stmt_assign (var_tm, cv_exp_tm) ;
    val rw_thm = REWRITE_CONV [from_cv_stmt_basic_def, GSYM cv_exp_thm] ``from_cv_stmt_basic ^cv_assign_tm`` ;
  in GSYM rw_thm end

(* Returns tm = from_cv_stmt_basic v *)
fun bir_stmt_basic_conv (tm : term) : thm = 
  if is_stmt_assign tm then
    bir_stmt_assign_conv tm
  else raise (ERR "bir_stmt_basic_conv" "not bir_stmt_basic_t")



(* Returns tm = from_cv_stmt_end v *)
fun bir_stmt_jmp_conv (tm : term) : thm = 
  let
    val le_tm = dest_stmt_jmp tm ;
    val cv_le_thm = bir_label_exp_conv le_tm ;
    val cv_le_tm = rand (rhs (concl cv_le_thm)) ;
    val cv_jmp_tm = mk_cv_stmt_jmp cv_le_tm ;
    val rw_thm = REWRITE_CONV [from_cv_stmt_end_def, GSYM cv_le_thm] 
      ``from_cv_stmt_end ^cv_jmp_tm`` ;
  in GSYM rw_thm end

(* Returns tm = from_cv_stmt_end v *)
fun bir_stmt_cjmp_conv (tm : term) : thm =
  let
    val (exp_tm, le1_tm, le2_tm) = dest_stmt_cjmp tm ;
    val cv_exp_thm = bir_exp_conv exp_tm ;
    val cv_exp_tm = rand (rhs (concl cv_exp_thm)) ;
    val cv_le1_thm = bir_label_exp_conv le1_tm ;
    val cv_le1_tm = rand (rhs (concl cv_le1_thm)) ;
    val cv_le2_thm = bir_label_exp_conv le2_tm ;
    val cv_le2_tm = rand (rhs (concl cv_le2_thm)) ;
    val cv_cjmp_tm = mk_cv_stmt_cjmp (cv_exp_tm, cv_le1_tm, cv_le2_tm) ;
    val thm_for_rw = [from_cv_stmt_end_def, GSYM cv_exp_thm, GSYM cv_le1_thm, GSYM cv_le2_thm] ;
    val rw_thm = REWRITE_CONV thm_for_rw ``from_cv_stmt_end ^cv_cjmp_tm`` ;
  in GSYM rw_thm end

(* Returns tm = from_cv_stmt_end v *)
fun bir_stmt_end_conv (tm : term) : thm = 
  if is_stmt_jmp tm then
    bir_stmt_jmp_conv tm
  else if is_stmt_cjmp tm then
    bir_stmt_cjmp_conv tm
  else raise (ERR "bir_stmt_end_conv" "not bir_stmt_end_t")



(* Returns tm = from_cv_block v *)
fun bir_block_conv (tm : term) : thm =
  let
    val (label_tm, stmt_basic_list_tm, stmt_end_tm) = dest_block tm ;

    val stmt_basic_tm_list = fst $ dest_list stmt_basic_list_tm ; 
    val cv_stmt_basic_thm_list = map bir_stmt_basic_conv stmt_basic_tm_list ;
    val cv_stmt_basic_tm_list = map (rand o rhs o concl) cv_stmt_basic_thm_list ;
    val cv_stmt_basic_list_tm = mk_list (cv_stmt_basic_tm_list, ``:bir_cv_stmt_basic_t``) ;

    val cv_stmt_end_thm = bir_stmt_end_conv stmt_end_tm ;
    val cv_stmt_end_tm = rand (rhs (concl cv_stmt_end_thm)) ;

    val cv_block_tm = mk_cv_block (label_tm, cv_stmt_basic_list_tm, cv_stmt_end_tm) ;

    val thms_for_rewrite = map GSYM
      ((GSYM from_cv_block_def)::cv_stmt_end_thm::cv_stmt_basic_thm_list)
    val thms_for_rewrite = 
      bir_cv_block_get_stmts_def::bir_cv_block_get_end_def::
        bir_cv_block_get_label_def :: thms_for_rewrite ;

    (* We are using SIMP_CONV to simplify record accessors *)
    val rw_thm = SIMP_CONV (srw_ss()) 
      thms_for_rewrite ``from_cv_block ^cv_block_tm`` ;
  in GSYM rw_thm end



(* Returns tm = from_cv_program v *)
fun bir_program_conv (tm : term) : thm =
  let
    val block_list_tm = dest_program tm ;
    val block_tm_list = fst $ dest_list block_list_tm ;
    val cv_block_thm_list = map bir_block_conv block_tm_list ;
    val cv_block_tm_list = map (rand o rhs o concl) cv_block_thm_list ;
    val cv_block_list_tm = mk_list (cv_block_tm_list, ``:bir_cv_block_t``) ;

    val cv_program_tm = mk_cv_program cv_block_list_tm ;

    val thms_for_rewrite = map GSYM ((GSYM from_cv_program_def)::cv_block_thm_list) ;

    val rw_thm = SIMP_CONV (srw_ss ()) thms_for_rewrite ``from_cv_program ^cv_program_tm`` ;
  in GSYM rw_thm end


(* Returns tm = from_cv_programcounter v *)
fun bir_pc_conv (tm : term) : thm = 
  let 
    val (label_tm, index_tm) = dest_programcounter tm ;

    val cv_programcounter_tm = mk_cv_programcounter (label_tm, index_tm) ;

    val thms_for_rewrite = [from_cv_programcounter_def]

    val rw_thm = SIMP_CONV (srw_ss ()) thms_for_rewrite ``from_cv_programcounter ^cv_programcounter_tm``
  in GSYM rw_thm end


(* Returns tm = from_cv_state v *)
fun bir_state_conv (tm : term) : thm =
  let
    val (pc_tm, env_tm, status_tm) = dest_state tm ;

    val cv_env_thm = env_to_cv_env_conv env_tm ;
    val cv_env_tm = rand (rhs (concl cv_env_thm)) ;

    val cv_pc_thm = bir_pc_conv pc_tm ;
    val cv_pc_tm = rand (rhs (concl cv_pc_thm)) ;

    val cv_state_tm = mk_cv_state (cv_pc_tm, cv_env_tm, status_tm) ;
  
    val thms_for_rewrite = [from_cv_state_def, GSYM cv_env_thm, GSYM cv_pc_thm,
        bir_cv_state_get_environ_def, bir_cv_state_get_pc_def, bir_cv_state_get_status_def] ;

    val rw_thm = SIMP_CONV (srw_ss()) thms_for_rewrite ``from_cv_state ^cv_state_tm`` ;
  in GSYM rw_thm end



end
