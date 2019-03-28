(* Vim users execute the following loads *)
(*
app load ["HolKernel", "Parse", "boolLib" ,"bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["bir_auxiliaryTheory", "bir_immTheory", "bir_valuesTheory"];
app load ["bir_symb_envTheory"];
app load ["bir_programTheory", "bir_expTheory", "bir_envTheory"];
app load ["llistTheory", "wordsLib"];
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_envTheory;
open bir_expTheory;
open bir_programTheory;
open llistTheory wordsLib;

open bir_envTheory bir_symb_envTheory;

val _ = new_theory "bir_symb_exec";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)


(* *
 * Symbolic State contains of:
 * PC: current program counter 
 * environment: Mapping vars to expressions 
 * memory: Mapping memory addresses to expressions
 * pred: expression representing the path condition
 * bsst_status : a status bit (mainly used for errors) 
 * *)

val _ = Datatype `bir_symb_state_t = <|
  bsst_pc           : bir_programcounter_t; 
  bsst_environ      : bir_symb_var_environment_t; (* Mapping Vars to Exps *)
  bsst_pred         : bir_exp_t; (* Path predicate *)
  bsst_status       : bir_status_t;
 |>`;
    

val CONJ_def = Define `
    CONJ a b = a ∧ b`;

(* Expression that always evaluates to True *)
val TRUE_EXP_def = Define `
    TRUE_EXP = BExp_BinPred BIExp_Equal 
        (BExp_Const (Imm1 1w)) (BExp_Const (Imm1 1w))`;

(* ------------------------------------------------------------------------- *)
(* Symbolic State                                                            *)
(* ------------------------------------------------------------------------- *)

(* Initially, Environment is empty and predicate set to True *)
val bir_symb_state_init_def = Define `bir_symb_state_init p env = <|
    bsst_pc         := bir_pc_first p;
    bsst_environ    := env;
    bsst_pred       := TRUE_EXP;
    bsst_status     := BST_Running |>`;

val bir_symb_state_set_failed_def = Define `
    bir_symb_state_set_failed st = 
    st with bsst_status := BST_Failed`;

val bir_symb_state_is_terminated_def = Define `
    bir_symb_state_is_terminated st = 
        if st.bsst_status = BST_Running then F else T`;

(* ------------------------------------------------------------------------- *)
(* Eval certain expressions                                                  *)
(* Different from concrete Execution, this returns a BIR Expression          *)        
(* ------------------------------------------------------------------------- *)

val bir_symb_eval_cast_def =  Define `
    bir_symb_eval_cast ct e ty = BExp_Cast ct e ty`;

val bir_symb_eval_unary_def = Define `
    bir_symb_eval_unary et e = BExp_UnaryExp et e`;

val bir_symb_eval_binary_def = Define `
    bir_symb_eval_binary et e1 e2 = BExp_BinExp et e1 e2`;

val bir_symb_eval_bin_pred_def = Define `
    bir_symb_eval_bin_pred pt e1 e2 = BExp_BinPred pt e1 e2`;

val bir_symb_eval_memeq_def = Define `
    bir_symb_eval_memeq e1 e2 = BExp_MemEq e1 e2`;

val bir_symb_eval_ite_def = Define `
    bir_symb_eval_ite c et ef = BExp_IfThenElse c et ef`;

val bir_symb_eval_store_def = Define `
    bir_symb_eval_store mem_e a_e v_e = BExp_Store mem_e a_e v_e`;

val bir_symb_eval_load_def = Define `
    bir_symb_eval_load mem_e a_e en ty = BExp_Load mem_e a_e en ty`;


val bir_symb_eval_exp_def = Define `
    (bir_symb_eval_exp (BExp_Const n) env = BExp_Const n) /\
    
    (bir_symb_eval_exp (BExp_Den v) env = bir_symb_env_read v env) /\
    
    (bir_symb_eval_exp (BExp_Cast ct e ty) env = 
        bir_symb_eval_cast ct (bir_symb_eval_exp e env) ty) /\
    
    (bir_symb_eval_exp (BExp_UnaryExp et e) env =
        bir_symb_eval_unary et (bir_symb_eval_exp e env)) /\
    
    (bir_symb_eval_exp (BExp_BinExp et e1 e2) env = 
        bir_symb_eval_binary et 
            (bir_symb_eval_exp e1 env) (bir_symb_eval_exp e2 env)) /\
    
    (bir_symb_eval_exp (BExp_BinPred pt e1 e2) env = 
        bir_symb_eval_bin_pred pt (
            bir_symb_eval_exp e1 env) (bir_symb_eval_exp e2 env)) /\
    
    (bir_symb_eval_exp (BExp_MemEq e1 e2) env = 
        bir_symb_eval_memeq
            (bir_symb_eval_exp e1 env) (bir_symb_eval_exp e2 env)) /\
    
    (bir_symb_eval_exp (BExp_IfThenElse c et ef) env = 
        bir_symb_eval_ite 
            (bir_symb_eval_exp c env) 
            (bir_symb_eval_exp et env) (bir_symb_eval_exp ef env)) /\
    
    (bir_symb_eval_exp (BExp_Load mem_e a_e en ty) env =
        bir_symb_eval_load 
            (bir_symb_eval_exp mem_e env) 
            (bir_symb_eval_exp a_e env) en ty) /\
    
    (bir_symb_eval_exp (BExp_Store mem_e a_e en v_e) env = 
        bir_symb_eval_store (bir_symb_eval_exp mem_e env)
            (bir_symb_eval_exp a_e env) en (bir_symb_eval_exp v_e env))`;


(* ------------------------------------------------------------------------- *)
(* Symbolic Execution Semantics                                              *)
(* ------------------------------------------------------------------------- *)

(* We can have symbolic label expressions, these are to be 
 * "solved" with SAT solver and every possible solution to be considered *)
val bir_symb_eval_label_exp_def = Define `
    (bir_symb_eval_label_exp (BLE_Label l) env = SOME l) ∧
    (bir_symb_eval_label_exp (BLE_Exp e) env = NONE)`;
 
(********************)
(* Jumps/Halt       *)
(********************)

(* direct jump *)
val bir_symb_exec_stmt_jmp_to_label_def = Define`
    bir_symb_exec_stmt_jmp_to_label p (l: bir_label_t) (st: bir_symb_state_t) = 
    if (MEM l (bir_labels_of_program p)) then 
      st with bsst_pc := bir_block_pc l
    else (st with bsst_status := (BST_JumpOutside l))`;
    

(* We ignore symbolic/indirect jump targets currently! *)  
val bir_symb_exec_stmt_jmp_def = Define `
    bir_symb_exec_stmt_jmp 
        (p: 'a bir_program_t) (le: bir_label_exp_t) (st: bir_symb_state_t) = 
    case bir_symb_eval_label_exp le st.bsst_environ of 
    | NONE   => bir_symb_state_set_failed st 
    | SOME l => bir_symb_exec_stmt_jmp_to_label p l st`;

(* End of execution *)
val bir_symb_exec_stmt_halt_def = Define `
    bir_symb_exec_stmt_halt ex (st: bir_symb_state_t) = 
    (st with bsst_status := BST_Halted ex)`;

(* Conditional, so "fork":
 * Return a list containing of two states with 
 * updated path predicate accordingly *)

(* )
val bir_symb_exec_stmt_cjmp_def = Define `
    bir_symb_exec_stmt_cjmp p (BExp_Den (BVar reg BType_Bool)) l1 l2 st = 
    case (bir_symb_env_lookup reg st.bsst_environ) of 
    | SOME (ty, jmp_exp) => 
        let st_true  = bir_symb_exec_stmt_jmp p l1 st in
        let st_false = bir_symb_exec_stmt_jmp p l2 st in
        [
        st_true with bsst_pred := (BExp_BinExp BIExp_And jmp_exp st.bsst_pred);
        st_false with bsst_pred := 
            (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not jmp_exp) st.bsst_pred)
        ] 
    | NONE => [st with bsst_status := BST_Failed]`;
 *)

(* Switch to a purely expressional conditional jump *)
val bir_symb_stmt_cjmp_def = Define `
    bir_symb_exec_stmt_cjmp p ex l1 l2 st = 
    let st_true = bir_symb_exec_stmt_jmp p l1 st in
    let st_false = bir_symb_exec_stmt_jmp p l2 st in
    [   st_true with bsst_pred := (BExp_BinExp BIExp_And ex st.bsst_pred);
        st_false with bsst_pred := (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not ex) st.bsst_pred)
    ]`;

(* Execute "End" (Jump/Halt) Statement *)
val bir_symb_exec_stmtE_def = Define `
    (bir_symb_exec_stmtE p (BStmt_Jmp l) st = [bir_symb_exec_stmt_jmp p l st]) /\ 
    (bir_symb_exec_stmtE p (BStmt_CJmp ex l1 l2 ) st =
         bir_symb_exec_stmt_cjmp p ex l1 l2 st ) /\
    (bir_symb_exec_stmtE p (BStmt_Halt ex) st = 
    [st with bsst_status := BST_Halted (BVal_Imm (Imm1 1w))])`;
    (* )[bir_symb_exec_stmt_halt ex st])`;  <-- Halt expects immediate !*)


(********************)
(* Declare / Assign *)
(********************)

(* We declare all variables before execution, so raise error is this occurs *)
val bir_symb_exec_stmt_declare_def = Define `
    bir_symb_exec_stmt_declare var_name var_type st = 
        st with bsst_status := BST_Failed `;

val bir_symb_exec_stmt_assign_def = Define `
    bir_symb_exec_stmt_assign v ex (st: bir_symb_state_t) = 
    case (bir_symb_env_write v (bir_symb_eval_exp ex st.bsst_environ) st.bsst_environ) of 
    | SOME env => st with bsst_environ := env
    | NONE => st with bsst_status := BST_Failed`;

(* Assertions are simply added to the Path Predicate *)
val bir_symb_exec_stmt_assert_def = Define `
    bir_symb_exec_stmt_assert ex st = 
    st with bsst_pred := BExp_BinExp BIExp_And ex st.bsst_pred`;

(* Basic Statement execution *)
val bir_symb_exec_stmtB_def = Define `
    (bir_symb_exec_stmtB (BStmt_Declare v) st  
        = bir_symb_exec_stmt_declare (bir_var_name v) (bir_var_type v) st) ∧
    (bir_symb_exec_stmtB (BStmt_Assign v ex) st 
        = bir_symb_exec_stmt_assign v ex st) /\
    (bir_symb_exec_stmtB (BStmt_Assert ex) st 
        =  bir_symb_exec_stmt_assert ex st) /\ 
    (bir_symb_exec_stmtB (_)  st  = st)`;

(* Execute one statement *)
val bir_symb_exec_stmt_def = Define`
    (bir_symb_exec_stmt (p: 'a bir_program_t) (BStmtB (bst: 'a bir_stmt_basic_t)) (st: bir_symb_state_t) 
        = [bir_symb_exec_stmtB bst st]) /\
    (bir_symb_exec_stmt p (BStmtE (bst: bir_stmt_end_t)) st 
        = (bir_symb_exec_stmtE p bst st))
    `;

(* ---------------------------------------------------- *)
(* Execute a program                                    *)
(* -----------------------------------------------------*)

(* Execute a Basic Block  *)
val bir_symb_exec_stmtB_list_def = Define `
    (bir_symb_exec_stmtB_list (p: 'a bir_program_t) (st: bir_symb_state_t)
        [] = st) ∧
    (bir_symb_exec_stmtB_list p st (stmt :: stmt_list) = 
        bir_symb_exec_stmtB_list p (bir_symb_exec_stmtB stmt st) stmt_list)`;


val bir_symb_exec_blk_def = Define `
    (bir_symb_exec_blk 
        (p: 'a bir_program_t) (blk: 'a bir_block_t) (st: bir_symb_state_t ) = 
        bir_symb_exec_stmtE p (blk.bb_last_statement) 
            (bir_symb_exec_stmtB_list p st (blk.bb_statements))
    )`;
        
val bir_symb_exec_first_blk_def = Define`
    (bir_symb_exec_first_blk 
        (BirProgram (blk_list : ('a bir_block_t) list)) (st: bir_symb_state_t) = 
        bir_symb_exec_blk (BirProgram blk_list) (HD blk_list) st)`;

(* Execute each BB  in a program *)

val bir_symb_exec_label_block_def = Define`
    bir_symb_exec_label_block (p: 'a bir_program_t) (st: bir_symb_state_t) = 
    case (bir_get_program_block_info_by_label p st.bsst_pc.bpc_label) of 
    | NONE => [bir_symb_state_set_failed st] 
    | SOME (_, blk) => bir_symb_exec_blk p blk st`;
    
val _ = export_theory();
