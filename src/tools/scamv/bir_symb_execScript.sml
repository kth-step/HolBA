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

(** Observations
 * obs_cond : Observation Condition
 * obs: Observation
 **)
val _ = Datatype `bir_symb_obs_t = <|
  obs_cond     : bir_exp_t;
  obs          : bir_exp_t list;
  obs_fun      : bir_val_t list -> 'a;
 |>`;

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
  bsst_status       : bir_status_t; (* State *)
  bsst_obs          : 'a bir_symb_obs_t list; (* Observations *)
 |>`;

(* Expression that always evaluates to True *)
val TRUE_EXP_def = Define `
    TRUE_EXP = BExp_Const (Imm1 1w)`;

(* ------------------------------------------------------------------------- *)
(* Symbolic State                                                            *)
(* ------------------------------------------------------------------------- *)

(* Initially, Environment is empty and predicate set to True *)
val bir_symb_state_init_def = Define `bir_symb_state_init (p : 'a bir_program_t) env = <|
    bsst_pc         := bir_pc_first p;
    bsst_environ    := env;
    bsst_pred       := TRUE_EXP;
    bsst_status     := BST_Running;
    bsst_obs        := ([] : 'a bir_symb_obs_t list) |>`;

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

val bir_symb_eval_exp_empty_def = Define `
    bir_symb_eval_exp_empty e = bir_eval_exp e (BEnv FEMPTY)
    `;


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
    bir_symb_exec_stmt_jmp_to_label p (l: bir_label_t) (st: 'a bir_symb_state_t) = 
    if (MEM l (bir_labels_of_program p)) then 
      st with bsst_pc := bir_block_pc l
    else (st with bsst_status := (BST_JumpOutside l))`;
    

(* We ignore symbolic/indirect jump targets currently! *)  
val bir_symb_exec_stmt_jmp_def = Define `
    bir_symb_exec_stmt_jmp 
        (p: 'a bir_program_t) (le: bir_label_exp_t) (st: 'a bir_symb_state_t) = 
    case bir_symb_eval_label_exp le st.bsst_environ of 
    | NONE   => bir_symb_state_set_failed st 
    | SOME l => bir_symb_exec_stmt_jmp_to_label p l st`;

(* End of execution *)
val bir_symb_exec_stmt_halt_def = Define `
    bir_symb_exec_stmt_halt ex (st: 'a bir_symb_state_t) = 
    (st with bsst_status := BST_Halted (bir_symb_eval_exp_empty (bir_symb_eval_exp ex st.bsst_environ)))`;

(* Conditional, so "fork":
 * Return a list containing of two states with 
 * updated path predicate accordingly *)

(* Switch to a purely expressional conditional jump *)
val bir_symb_stmt_cjmp_def = Define `
    bir_symb_exec_stmt_cjmp p ex l1 l2 st = 
    let
      st_true  = bir_symb_exec_stmt_jmp p l1 st;
      st_false = bir_symb_exec_stmt_jmp p l2 st;
      ex_subst = (bir_symb_eval_exp ex st.bsst_environ);
    in
    [
      st_true  with bsst_pred :=
                (BExp_BinExp BIExp_And                           ex_subst st.bsst_pred)
     ;
      st_false with bsst_pred :=
                (BExp_BinExp BIExp_And (BExp_UnaryExp BIExp_Not ex_subst) st.bsst_pred)
    ]`;

(* Execute "End" (Jump/Halt) Statement *)
val bir_symb_exec_stmtE_def = Define `
    (bir_symb_exec_stmtE p (BStmt_Jmp l)          st = [bir_symb_exec_stmt_jmp p l st]) /\ 
    (bir_symb_exec_stmtE p (BStmt_CJmp ex l1 l2 ) st =  bir_symb_exec_stmt_cjmp p ex l1 l2 st ) /\
    (bir_symb_exec_stmtE p (BStmt_Halt ex)        st = [bir_symb_exec_stmt_halt ex st])`;


(********************)
(* Declare / Assign *)
(********************)


(* We declare all variables before execution, so raise error is this occurs *)
val bir_symb_exec_stmt_declare_def = Define `
    bir_symb_exec_stmt_declare var_name var_type st = 
        [bir_symb_state_set_failed st] `;

(* same behavior for assume *)
val bir_symb_exec_stmt_assume_def = Define `
    bir_symb_exec_stmt_assume ex st = 
        [bir_symb_state_set_failed st] `;

val bir_symb_exec_stmt_assign_def = Define `
    bir_symb_exec_stmt_assign v ex (st: 'a bir_symb_state_t) = 
    case (bir_symb_env_write v (bir_symb_eval_exp ex st.bsst_environ) st.bsst_environ) of 
    | SOME env => [st with bsst_environ := env]
    | NONE     => [bir_symb_state_set_failed st]`;

(* Assertions create two follow up states: 
 * One in which the assertion holds and One in which the Assertion is violated *)
val bir_symb_exec_stmt_assert_def = Define `
    bir_symb_exec_stmt_assert ex st = 
      let
	ex_subst     = (bir_symb_eval_exp ex st.bsst_environ);
	ex_subst_not = BExp_UnaryExp BIExp_Not ex_subst;
	st_true  = 
	  st with bsst_pred := BExp_BinExp BIExp_And ex_subst st.bsst_pred; 
	st_false = 
	  st with 
	       <| bsst_status := BST_AssertionViolated;
		  bsst_pred   := BExp_BinExp BIExp_And ex_subst_not st.bsst_pred |>;
      in
	[st_true; st_false]
    `;


(* Evaluate and add observations *)
val bir_symb_exec_stmt_observe_def = Define `
    bir_symb_exec_stmt_observe c_ex obs_lst f st =
(*
      if f <> (\x. x) then
        [bir_symb_state_set_failed st]
      else
*)
	let
	  obs_cond_ex = bir_symb_eval_exp c_ex st.bsst_environ;
	  obs_lst_e   = MAP (\o_ex. bir_symb_eval_exp o_ex st.bsst_environ) obs_lst;
	  obs         = <| obs_cond := obs_cond_ex; obs := obs_lst_e; obs_fun := f |>;
	in
	  [st with bsst_obs := (obs :: st.bsst_obs)]
    `;

(* Basic Statement execution *)
val bir_symb_exec_stmtB_def = Define `
    (bir_symb_exec_stmtB (BStmt_Declare v) st  
           = bir_symb_exec_stmt_declare (bir_var_name v) (bir_var_type v) st) ∧
    (bir_symb_exec_stmtB (BStmt_Assign v ex) st 
           = bir_symb_exec_stmt_assign v ex st) /\
    (bir_symb_exec_stmtB (BStmt_Assert ex) st 
           = bir_symb_exec_stmt_assert ex st) /\ 
    (bir_symb_exec_stmtB (BStmt_Assume ex) st 
           = bir_symb_exec_stmt_assume ex st) /\ 
    (bir_symb_exec_stmtB (BStmt_Observe ex ex_lst f) st
           = bir_symb_exec_stmt_observe ex ex_lst f st)
    `;

(* Execute one statement *)
val bir_symb_exec_stmt_def = Define`
    (bir_symb_exec_stmt (p: 'a bir_program_t)
                        (BStmtB (bst: 'a bir_stmt_basic_t))
                        (st: 'a bir_symb_state_t) 
        = (bir_symb_exec_stmtB bst st)) /\

    (bir_symb_exec_stmt p (BStmtE (bst: bir_stmt_end_t)) st 
        = (bir_symb_exec_stmtE p bst st))
    `;

(* ---------------------------------------------------- *)
(* Execute a program                                    *)
(* -----------------------------------------------------*)

(* Execute the non-ending statements of a BB.
 * Produces one running state and a list of halted states *)
val bir_symb_exec_stmtB_list_rec_def = Define `
    (bir_symb_exec_stmtB_list_rec 
        (p: 'a bir_program_t) (st: 'a bir_symb_state_t) [] sts_halted =
        (st, sts_halted))  /\
    (bir_symb_exec_stmtB_list_rec 
        p st (stmt :: stmt_lst) sts_halted = 
        let st_lst = bir_symb_exec_stmtB stmt st in
        case (LENGTH st_lst) of
          (* There is either 1 follow-up state (no assertion) or 
           * 2 follow up-states (assetion failed and assertion holds) *)
          | 1 => 
             (bir_symb_exec_stmtB_list_rec p (HD st_lst) stmt_lst sts_halted)
          | 2 =>
              let st_n0 = EL 0 st_lst in
              let st_n1 = EL 1 st_lst in
              (case (st_n0.bsst_status) of 
                 (* Continue Execution with the Running state, collect the other
                  * one in the halted list *)
                 | BST_Running =>
                    bir_symb_exec_stmtB_list_rec p st_n0 stmt_lst (st_n1::sts_halted)
                 | _ => 
                    bir_symb_exec_stmtB_list_rec p st_n1 stmt_lst (st_n0::sts_halted))
          | _ => (* this does not happen *)
                 (bir_symb_state_set_failed st, sts_halted))`;
               
(* helper function for the recursive function above ... *)
val bir_symb_exec_bb_statements = Define `
    bir_symb_exec_bb_statements p st stmt_lst = 
        bir_symb_exec_stmtB_list_rec p st stmt_lst []`;

(* Execute the End Statemens of a BB
 * May produce one or two follow-up states *)
val bir_symb_exec_bb_last_statement = Define `
    bir_symb_exec_bb_last_statement p st stmt = 
        bir_symb_exec_stmtE p stmt st`;

(* Execute a single basic block.
 * Returns a list of blocks with assertions violated 
 * and a list of potential follow-up states *)
val bir_symb_exec_blk_def = Define `
    bir_symb_exec_blk (p: 'a bir_program_t) (blk: 'a bir_block_t) st = 
        let (st_e, sts_halted) = 
            bir_symb_exec_bb_statements p st blk.bb_statements in 
        let sts = bir_symb_exec_bb_last_statement p st_e blk.bb_last_statement in 
            (sts_halted, sts)`; 

(* Given a Program and a State, find the respective block and execute it *)
val bir_symb_exec_label_block_def = Define`
    bir_symb_exec_label_block (p: 'a bir_program_t) (st: 'a bir_symb_state_t) = 
    case (bir_get_program_block_info_by_label p st.bsst_pc.bpc_label) of 
    | NONE => ([], [bir_symb_state_set_failed st])
    | SOME (_, blk) => bir_symb_exec_blk p blk st`;
    
val _ = export_theory();
