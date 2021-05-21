structure bir_programSyntax :> bir_programSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_valuesTheory bir_programTheory;


val ERR = mk_HOL_ERR "bir_programSyntax"
val wrap_exn = Feedback.wrap_exn "bir_programSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;



(* bir_label_t *)

val bir_label_t_ty = mk_type ("bir_label_t", []);

val (BL_Label_tm,  mk_BL_Label, dest_BL_Label, is_BL_Label)  = syntax_fns1 "BL_Label";
val (BL_Address_tm,  mk_BL_Address, dest_BL_Address, is_BL_Address)  = syntax_fns1 "BL_Address";

val dest_BL_Label_string = stringSyntax.fromHOLstring o dest_BL_Label
fun mk_BL_Label_string s = mk_BL_Label (stringSyntax.fromMLstring s)

(* bir_label_t *)

val bir_label_exp_t_ty = mk_type ("bir_label_exp_t", []);

val (BLE_Label_tm,  mk_BLE_Label, dest_BLE_Label, is_BLE_Label)  = syntax_fns1 "BLE_Label";
val (BLE_Exp_tm,  mk_BLE_Exp, dest_BLE_Exp, is_BLE_Exp)  = syntax_fns1 "BLE_Exp";

(* bir_memop_t *)

val bir_memop_t_ty = mk_type ("bir_memop_t", []);

val (BM_Read_tm,  is_BM_Read)  = syntax_fns0 "BM_Read";
val (BM_Write_tm,  is_BM_Write)  = syntax_fns0 "BM_Write";
val (BM_ReadWrite_tm,  is_BM_ReadWrite)  = syntax_fns0 "BM_ReadWrite";

(* bir_stmt_basic_t *)

fun mk_bir_stmt_basic_t_ty ty = mk_type ("bir_stmt_basic_t", [ty]);

fun dest_bir_stmt_basic_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="bir_stmt_basic_t", Thy="bir_program", Args=[ty]} => ty
     | other => raise ERR "dest_bir_stmt_basic_t_ty" ""

val is_bir_stmt_basic_t_ty = can dest_bir_stmt_basic_t_ty;

val (BStmt_Assign_tm,  mk_BStmt_Assign, dest_BStmt_Assign, is_BStmt_Assign)  = syntax_fns2 "BStmt_Assign";
val (BStmt_Assert_tm,  mk_BStmt_Assert, dest_BStmt_Assert, is_BStmt_Assert)  = syntax_fns1 "BStmt_Assert";
val (BStmt_Assume_tm,  mk_BStmt_Assume, dest_BStmt_Assume, is_BStmt_Assume)  = syntax_fns1 "BStmt_Assume";
val (BStmt_Observe_tm,  mk_BStmt_Observe, dest_BStmt_Observe, is_BStmt_Observe)  = syntax_fns4 "BStmt_Observe";
val (BStmt_Fence_tm,  mk_BStmt_Fence, dest_BStmt_Fence, is_BStmt_Fence)  = syntax_fns2 "BStmt_Fence";



(* bir_stmt_end_t *)

val bir_stmt_end_t_ty = mk_type ("bir_stmt_end_t", []);

val (BStmt_Jmp_tm,  mk_BStmt_Jmp, dest_BStmt_Jmp, is_BStmt_Jmp)  = syntax_fns1 "BStmt_Jmp";
val (BStmt_CJmp_tm,  mk_BStmt_CJmp, dest_BStmt_CJmp, is_BStmt_CJmp)  = syntax_fns3 "BStmt_CJmp";
val (BStmt_Halt_tm,  mk_BStmt_Halt, dest_BStmt_Halt, is_BStmt_Halt)  = syntax_fns1 "BStmt_Halt";



(* bir_stmt_t *)

fun mk_bir_stmt_t_ty ty = mk_type ("bir_stmt_t", [ty]);

fun dest_bir_stmt_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="bir_stmt_t", Thy="bir_program", Args=[ty]} => ty
     | other => raise ERR "dest_bir_stmt_t_ty" ""

val is_bir_stmt_t_ty = can dest_bir_stmt_t_ty;

val (BStmtB_tm,  mk_BStmtB, dest_BStmtB, is_BStmtB)  = syntax_fns1 "BStmtB";
val (BStmtE_tm,  mk_BStmtE, dest_BStmtE, is_BStmtE)  = syntax_fns1 "BStmtE";



(* bir_block_t *)

fun mk_bir_block_t_ty ty = mk_type ("bir_block_t", [ty]);

fun dest_bir_block_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="bir_block_t", Thy="bir_program", Args=[ty]} => ty
     | other => raise ERR "dest_bir_block_t_ty" ""

val is_bir_block_t_ty = can dest_bir_block_t_ty;


fun dest_bir_block tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if is_bir_block_t_ty ty then () else fail()
  val lbl = Lib.assoc "bb_label" l
  val is_atomic = Lib.assoc "bb_atomic" l
  val stmts = Lib.assoc "bb_statements" l
  val last_stmt = Lib.assoc "bb_last_statement" l
in
  (lbl, is_atomic, stmts, last_stmt)
end handle e => raise wrap_exn "dest_bir_block" e;

val is_bir_block = can dest_bir_block;

fun mk_bir_block (tm_lbl, tm_is_atomic, tm_stmts, tm_last_stmt) = let
  val ty0 = dest_bir_stmt_basic_t_ty (listSyntax.dest_list_type (type_of tm_stmts))
  val ty = mk_bir_block_t_ty ty0

  val l = [("bb_label", tm_lbl),
           ("bb_atomic", tm_is_atomic),
           ("bb_statements", tm_stmts),
           ("bb_last_statement", tm_last_stmt)];
in
  TypeBase.mk_record (ty, l)
end handle e => raise wrap_exn "mk_bir_block" e;

fun dest_bir_block_list tm = let
  val (tm_lbl, tm_is_atomic, tm_stmts, tm_last_stmt) = dest_bir_block tm;
  val (l_stmts, ty') = listSyntax.dest_list tm_stmts;
  val ty'' = dest_bir_stmt_basic_t_ty ty'
in
  (ty'', tm_lbl, tm_is_atomic, l_stmts, tm_last_stmt)
end handle e => raise wrap_exn "dest_bir_block_list" e;

fun mk_bir_block_list (ty, tm_lbl, tm_is_atomic, l_stmts, tm_last_stmt) = let
  val ty' = mk_bir_stmt_basic_t_ty ty
  val tm_stmts = listSyntax.mk_list (l_stmts, ty')
in
  mk_bir_block (tm_lbl, tm_is_atomic, tm_stmts, tm_last_stmt)
end handle e => raise wrap_exn "mk_bir_block_list" e;


(* bir_program_t *)

fun mk_bir_program_t_ty ty = mk_type ("bir_program_t", [ty]);

fun dest_bir_program_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="bir_program_t", Thy="bir_program", Args=[ty]} => ty
     | other => raise ERR "dest_bir_program_t_ty" ""

val is_bir_program_t_ty = can dest_bir_program_t_ty;

val (BirProgram_tm,  mk_BirProgram, dest_BirProgram, is_BirProgram)  = syntax_fns1 "BirProgram";

val tm = ``BirProgram []``

fun dest_BirProgram_list tm = let
  val l_tm = dest_BirProgram tm;
  val (l, ty) = listSyntax.dest_list l_tm
in
  (dest_bir_block_t_ty ty, l)
end handle e => raise wrap_exn "dest_BirProgram_list" e;

fun mk_BirProgram_list (ty, tms) = let
  val ty' = mk_bir_block_t_ty ty
  val l_tm = listSyntax.mk_list (tms, ty')
in
  mk_BirProgram l_tm
end handle e => raise wrap_exn "mk_BirProgram_list" e;


(* bir_programcounter_t *)
val bir_programcounter_t_ty = mk_type ("bir_programcounter_t", []);

fun dest_bir_programcounter tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if bir_programcounter_t_ty = ty then () else fail()
  val lbl = Lib.assoc "bpc_label" l
  val index = Lib.assoc "bpc_index" l
in
  (lbl, index)
end handle e => raise wrap_exn "dest_bir_programcounter" e;

val is_bir_programcounter = can dest_bir_programcounter;

fun mk_bir_programcounter (tm_lbl, tm_index) = let
  val l = [("bpc_label", tm_lbl),
           ("bpc_index", tm_index)];
in
  TypeBase.mk_record (bir_programcounter_t_ty, l)
end handle e => raise wrap_exn "mk_bir_programcounter" e;


val (bir_block_pc_tm,  mk_bir_block_pc, dest_bir_block_pc, is_bir_block_pc)  = syntax_fns1 "bir_block_pc";

val (bir_pc_first_tm,  mk_bir_pc_first, dest_bir_pc_first, is_bir_pc_first)  = syntax_fns1 "bir_pc_first";



(* bir_status_t *)

val bir_status_t_ty = mk_type ("bir_status_t", []);

val (BST_Running_tm,  is_BST_Running)  = syntax_fns0 "BST_Running";
val (BST_Failed_tm,  is_BST_Failed)  = syntax_fns0 "BST_Failed";
val (BST_AssumptionViolated_tm,  is_BST_AssumptionViolated)  = syntax_fns0 "BST_AssumptionViolated";
val (BST_Halted_tm,  mk_BST_Halted, dest_BST_Halted, is_BST_Halted)  = syntax_fns1 "BST_Halted";
val (BST_JumpOutside_tm,  mk_BST_JumpOutside, dest_BST_JumpOutside, is_BST_JumpOutside)  = syntax_fns1 "BST_JumpOutside";




(* bir_stmt_t *)

fun mk_bir_stmt_t_ty ty = mk_type ("bir_stmt_t", [ty]);

fun dest_bir_stmt_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="bir_stmt_t", Thy="bir_program", Args=[ty]} => ty
     | other => raise ERR "dest_bir_stmt_t_ty" ""

val is_bir_stmt_t_ty = can dest_bir_stmt_t_ty;

val (BStmtB_tm,  mk_BStmtB, dest_BStmtB, is_BStmtB)  = syntax_fns1 "BStmtB";
val (BStmtE_tm,  mk_BStmtE, dest_BStmtE, is_BStmtE)  = syntax_fns1 "BStmtE";



(* bir_state_t *)

val bir_state_t_ty = mk_type ("bir_state_t", []);

fun dest_bir_state tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if ty = bir_state_t_ty then () else fail()
  val pc = Lib.assoc "bst_pc" l
  val env = Lib.assoc "bst_environ" l
  val status = Lib.assoc "bst_status" l
in
  (pc, env, status)
end handle e => raise wrap_exn "dest_bir_state" e;

val is_bir_state = can dest_bir_state;

fun mk_bir_state (pc, env, status) = let
  val l = [("bst_pc", pc),
           ("bst_environ", env),
           ("bst_status", status)];
in
  TypeBase.mk_record (bir_state_t_ty, l)
end handle e => raise wrap_exn "mk_bir_state" e;


val (bst_status_tm,  mk_bst_status, dest_bst_status, is_bst_status)  = syntax_fns1 "bir_state_t_bst_status";

val (bst_environ_tm,  mk_bst_environ, dest_bst_environ, is_bst_environ)  = syntax_fns1 "bir_state_t_bst_environ";

val (bst_pc_tm,  mk_bst_pc, dest_bst_pc, is_bst_pc)  = syntax_fns1 "bir_state_t_bst_pc";


val (bir_state_init_tm,  mk_bir_state_init, dest_bir_state_init, is_bir_state_init)  = syntax_fns1 "bir_state_init";

val (bir_state_is_terminated_tm,  mk_bir_state_is_terminated, dest_bir_state_is_terminated, is_bir_state_is_terminated)  = syntax_fns1 "bir_state_is_terminated";



(* various functions *)
val (bir_exec_step_tm,  mk_bir_exec_step, dest_bir_exec_step, is_bir_exec_step)  = syntax_fns2 "bir_exec_step";

val (bir_exec_steps_tm,  mk_bir_exec_steps, dest_bir_exec_steps, is_bir_exec_steps)  = syntax_fns2 "bir_exec_steps";

val (bir_exec_step_n_tm,  mk_bir_exec_step_n, dest_bir_exec_step_n, is_bir_exec_step_n)  = syntax_fns3 "bir_exec_step_n";

val (bir_get_program_block_info_by_label_tm,  mk_bir_get_program_block_info_by_label, dest_bir_get_program_block_info_by_label, is_bir_get_program_block_info_by_label)  = syntax_fns2 "bir_get_program_block_info_by_label";

val (bir_exec_stmt_jmp_to_label_tm,  mk_bir_exec_stmt_jmp_to_label, dest_bir_exec_stmt_jmp_to_label, is_bir_exec_stmt_jmp_to_label)  = syntax_fns3 "bir_exec_stmt_jmp_to_label";

val (bir_labels_of_program_tm,  mk_bir_labels_of_program, dest_bir_labels_of_program, is_bir_labels_of_program)  = syntax_fns1 "bir_labels_of_program";


end
