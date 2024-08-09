structure bir_cv_programSyntax :>  bir_cv_programSyntax =
struct

open HolKernel Parse bossLib boolLib ;
open bir_cv_programTheory ;

val ERR = mk_HOL_ERR "bir_cv_programSyntax" ;


(* Utilities *)
fun dest_tri_record (ty : hol_type) (err : exn) (tm: term) =
  let val (ty_rec, attributes) = TypeBase.dest_record tm ;
      val _ = if ty_rec = ty then () else raise err ;
  in case map snd attributes of 
      [tm1, tm2, tm3] => (tm1,tm2,tm3) 
    | _ => raise err end


val cv_le_label_tm = prim_mk_const{Name="BCVLE_Label", Thy="bir_cv_program"} ;
val cv_le_exp_tm = prim_mk_const{Name="BCVLE_Exp", Thy="bir_cv_program"} ;
val cv_stmt_assign_tm = prim_mk_const{Name="BCVStmt_Assign", Thy="bir_cv_program"} ;
val cv_stmt_jmp_tm = prim_mk_const{Name="BCVStmt_Jmp", Thy="bir_cv_program"} ;
val cv_stmt_cjmp_tm = prim_mk_const{Name="BCVStmt_CJmp", Thy="bir_cv_program"} ;
val cv_program_tm = prim_mk_const{Name="BirCVProgram", Thy="bir_cv_program"} ;


fun mk_cv_le_label tm =
  list_mk_comb (cv_le_label_tm, [tm])

fun mk_cv_le_exp tm =
  list_mk_comb (cv_le_exp_tm, [tm])

fun mk_cv_stmt_assign (tm1,tm2) =
  list_mk_comb (cv_stmt_assign_tm, [tm1, tm2])

fun mk_cv_stmt_jmp tm =
  list_mk_comb (cv_stmt_jmp_tm, [tm])

fun mk_cv_stmt_cjmp (tm1,tm2,tm3) =
  list_mk_comb (cv_stmt_cjmp_tm, [tm1, tm2, tm3])

fun mk_cv_block (tm1, tm2, tm3) = 
  TypeBase.mk_record (``:bir_cv_block_t``,
    [("bb_label",tm1), ("bb_statements", tm2), ("bb_last_statement", tm3)])

fun mk_cv_program tm =
  list_mk_comb (cv_program_tm, [tm])

fun mk_cv_state (tm1, tm2, tm3) = 
  TypeBase.mk_record (``:bir_cv_state_t``,
    [("bst_pc",tm1), ("bst_environ", tm2), ("bst_status", tm3)])


  

fun dest_cv_le_label tm = 
  dest_monop cv_le_label_tm (ERR "dest_cv_le_label" "not BCVLE_Label") tm

fun dest_cv_le_exp tm =
  dest_monop cv_le_exp_tm (ERR "dest_cv_le_exp" "not BCVLE_Exp") tm

fun dest_cv_stmt_assign tm =
  dest_binop cv_stmt_assign_tm (ERR "dest_cv_stmt_assign" "not BCVStmt_Assign") tm

fun dest_cv_stmt_jmp tm =
  dest_monop cv_stmt_jmp_tm (ERR "dest_cv_stmt_jmp" "not BCVStmt_Jmp") tm

fun dest_cv_stmt_cjmp tm =
  dest_triop cv_stmt_cjmp_tm (ERR "dest_cv_stmt_cjmp" "not BCVStmt_CJmp") tm

fun dest_cv_block tm =
  dest_tri_record ``:bir_cv_block_t`` (ERR "dest_cv_block" "not bir_cv_block_t") tm

fun dest_cv_program tm =
  dest_monop cv_program_tm (ERR "dest_cv_program" "not BirCVProgram") tm

fun dest_cv_state tm =
  dest_tri_record ``:bir_cv_state_t`` (ERR "dest_cv_state" "not bir_cv_state_t") tm



fun is_cv_le_label tm =
  can dest_cv_le_label tm

fun is_cv_le_exp tm =
  can dest_cv_le_exp tm

fun is_cv_stmt_assign tm =
  can dest_cv_stmt_assign tm

fun is_cv_stmt_jmp tm =
  can dest_cv_stmt_jmp tm

fun is_cv_stmt_cjmp tm =
  can dest_cv_stmt_cjmp tm

fun is_cv_block tm =
  can dest_cv_block tm

fun is_cv_program tm =
  can dest_cv_program tm

fun is_cv_state tm =
  can dest_cv_state tm



end
