(* Vim users execute the following loads *)
(*
app load ["HolKernel", "Parse", "boolLib" ,"bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["holba_auxiliaryTheory", "bir_immTheory", "bir_valuesTheory"];
app load ["bir_symb_envTheory"];
app load ["bir_programTheory", "bir_expTheory", "bir_envTheory"];
app load ["llistTheory", "wordsLib"];
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open holba_auxiliaryTheory bir_immTheory bir_valuesTheory;
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
Datatype:
  bir_symb_obs_t = <|
  obs_id       : num;
  obs_cond     : bir_exp_t;
  obs          : bir_exp_t list;
  obs_fun      : bir_val_t list -> 'a;
 |>
End

(* *
 * Symbolic State contains of:
 * PC: current program counter 
 * environment: Mapping vars to expressions 
 * memory: Mapping memory addresses to expressions
 * pred: expression representing the path condition
 * bsst_status : a status bit (mainly used for errors) 
 * obs: list of conditional observations
 * *)

Datatype:
  bir_symb_state_t = <|
  bsst_pc           : bir_programcounter_t; 
  bsst_environ      : bir_symb_var_environment_t; (* Mapping Vars to Exps *)
  bsst_pred         : bir_exp_t; (* Path predicate *)
  bsst_status       : bir_status_t; (* State *)
  bsst_obs          : 'a bir_symb_obs_t list; (* Observations *)
 |>
End

(* Expression that always evaluates to True *)
Definition TRUE_EXP_def:
  TRUE_EXP = BExp_Const (Imm1 1w)
End

(* ------------------------------------------------------------------------- *)
(* Symbolic State                                                            *)
(* ------------------------------------------------------------------------- *)

(* Initially, Environment is empty and predicate set to True *)
Definition bir_symb_state_init_def:
  bir_symb_state_init (p : 'a bir_program_t) env pred = <|
    bsst_pc         := bir_pc_first p;
    bsst_environ    := env;
    bsst_pred       := pred;
    bsst_status     := BST_Running;
    bsst_obs        := ([] : 'a bir_symb_obs_t list) |>
End

Definition bir_symb_state_set_failed_def:
  bir_symb_state_set_failed st = 
    st with bsst_status := BST_Failed
End

Definition bir_symb_state_set_typeerror_def:
  bir_symb_state_set_typeerror st = 
    st with bsst_status := BST_TypeError
End

Definition bir_symb_state_is_terminated_def:
  bir_symb_state_is_terminated st = 
        if st.bsst_status = BST_Running then F else T
End

(* ------------------------------------------------------------------------- *)
(* Eval certain expressions                                                  *)
(* Different from concrete Execution, this returns a BIR Expression          *)        
(* ------------------------------------------------------------------------- *)

Definition bir_symb_eval_cast_def:
  bir_symb_eval_cast ct e ty = BExp_Cast ct e ty
End

Definition bir_symb_eval_unary_def:
  bir_symb_eval_unary et e = BExp_UnaryExp et e
End

Definition bir_symb_eval_binary_def:
  bir_symb_eval_binary et e1 e2 = BExp_BinExp et e1 e2
End

Definition bir_symb_eval_bin_pred_def:
  bir_symb_eval_bin_pred pt e1 e2 = BExp_BinPred pt e1 e2
End

Definition bir_symb_eval_memeq_def:
  bir_symb_eval_memeq e1 e2 = BExp_MemEq e1 e2
End

Definition bir_symb_eval_ite_def:
  bir_symb_eval_ite c et ef = BExp_IfThenElse c et ef
End

Definition bir_symb_eval_store_def:
  bir_symb_eval_store mem_e a_e v_e = BExp_Store mem_e a_e v_e
End

Definition bir_symb_eval_load_def:
  bir_symb_eval_load mem_e a_e en ty = BExp_Load mem_e a_e en ty
End


Definition bir_symb_eval_exp_def:
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
            (bir_symb_eval_exp a_e env) en (bir_symb_eval_exp v_e env))
End

Definition bir_symb_eval_exp_empty_def:
  bir_symb_eval_exp_empty e = bir_eval_exp e (BEnv (K NONE))
End


(* ------------------------------------------------------------------------- *)
(* Symbolic Execution Semantics                                              *)
(* ------------------------------------------------------------------------- *)

(* We can have symbolic label expressions, these are to be 
 * "solved" with SAT solver and every possible solution to be considered *)
Definition bir_symb_eval_label_exp_def:
  (bir_symb_eval_label_exp (BLE_Label l) env = SOME l) ∧
    (bir_symb_eval_label_exp (BLE_Exp e) env = NONE)
End
 
(********************)
(* Jumps/Halt       *)
(********************)

(* direct jump *)
Definition bir_symb_exec_stmt_jmp_to_label_def:
  bir_symb_exec_stmt_jmp_to_label p (l: bir_label_t) (st: 'a bir_symb_state_t) = 
    if (MEM l (bir_labels_of_program p)) then 
      st with bsst_pc := bir_block_pc l
    else (st with bsst_status := (BST_JumpOutside l))
End
    

(* We ignore symbolic/indirect jump targets currently! *)  
Definition bir_symb_exec_stmt_jmp_def:
  bir_symb_exec_stmt_jmp 
        (p: 'a bir_program_t) (le: bir_label_exp_t) (st: 'a bir_symb_state_t) = 
    case bir_symb_eval_label_exp le st.bsst_environ of 
    | NONE   => bir_symb_state_set_failed st 
    | SOME l => bir_symb_exec_stmt_jmp_to_label p l st
End

(* End of execution *)
Definition bir_symb_exec_stmt_halt_def:
  bir_symb_exec_stmt_halt ex (st: 'a bir_symb_state_t) = 
      case bir_symb_eval_exp_empty (bir_symb_eval_exp ex st.bsst_environ) of
	| NONE => bir_symb_state_set_typeerror st
	| SOME v => st with bsst_status := BST_Halted v
End

(* Conditional jump:
 * Return a list with two states where 
 * path predicate is updated accordingly *)
Definition bir_symb_stmt_cjmp_def:
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
    ]
End

(* Execute "End" (Jump/Halt) Statement *)
Definition bir_symb_exec_stmtE_def:
  (bir_symb_exec_stmtE p (BStmt_Jmp l)          st = [bir_symb_exec_stmt_jmp p l st]) /\ 
    (bir_symb_exec_stmtE p (BStmt_CJmp ex l1 l2 ) st =  bir_symb_exec_stmt_cjmp p ex l1 l2 st ) /\
    (bir_symb_exec_stmtE p (BStmt_Halt ex)        st = [bir_symb_exec_stmt_halt ex st])
End


(********************)
(* Declare / Assign *)
(********************)


(* same behavior for assume *)
Definition bir_symb_exec_stmt_assume_def:
  bir_symb_exec_stmt_assume ex st = 
        [bir_symb_state_set_failed st]
End

(* assign... *)
Definition bir_symb_exec_stmt_assign_def:
  bir_symb_exec_stmt_assign v ex (st: 'a bir_symb_state_t) = 
    case (bir_symb_env_write v (bir_symb_eval_exp ex st.bsst_environ) st.bsst_environ) of 
    | SOME env => [st with bsst_environ := env]
    | NONE     => [bir_symb_state_set_typeerror st]
End

(* Assertions create two follow up states: 
 * One in which the assertion holds and One in which the Assertion is violated *)
Definition bir_symb_exec_stmt_assert_def:
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
End


(* add observations as symbolic stubstitutions *)
Definition bir_symb_exec_stmt_observe_def:
  bir_symb_exec_stmt_observe oid c_ex obs_lst f st =
(*
      if f <> (\x. x) then
        [bir_symb_state_set_failed st]
      else
*)
	let
	  obs_cond_ex = bir_symb_eval_exp c_ex st.bsst_environ;
	  obs_lst_e   = MAP (\o_ex. bir_symb_eval_exp o_ex st.bsst_environ) obs_lst;
	  obs         = <| obs_id := oid; obs_cond := obs_cond_ex; obs := obs_lst_e; obs_fun := f |>;
	in
	  [st with bsst_obs := (SNOC obs st.bsst_obs)]
End

(* Basic Statement execution *)
Definition bir_symb_exec_stmtB_def:
  (bir_symb_exec_stmtB (BStmt_Assign v ex) st 
           = bir_symb_exec_stmt_assign v ex st) /\
    (bir_symb_exec_stmtB (BStmt_Assert ex) st 
           = bir_symb_exec_stmt_assert ex st) /\ 
    (bir_symb_exec_stmtB (BStmt_Assume ex) st 
           = bir_symb_exec_stmt_assume ex st) /\ 
    (bir_symb_exec_stmtB (BStmt_Observe oid ex ex_lst f) st
           = bir_symb_exec_stmt_observe oid ex ex_lst f st)
End

(* Execute one statement *)
Definition bir_symb_exec_stmt_def:
  (bir_symb_exec_stmt (p: 'a bir_program_t)
                        (BStmtB (bst: 'a bir_stmt_basic_t))
                        (st: 'a bir_symb_state_t) 
        = (bir_symb_exec_stmtB bst st)) /\

    (bir_symb_exec_stmt p (BStmtE (bst: bir_stmt_end_t)) st 
        = (bir_symb_exec_stmtE p bst st))
End

(* ---------------------------------------------------- *)
(* Execute a program                                    *)
(* -----------------------------------------------------*)

(* helper definition to partition a list of states
   into running and terminated ones *)
Definition bir_symb_exec_partition_running_def:
  (bir_symb_exec_partition_running [] (sr, sh) = (REVERSE sr, REVERSE sh)) /\
    (bir_symb_exec_partition_running (st::sts) (sr, sh) =
       bir_symb_exec_partition_running (sts) (if bir_symb_state_is_terminated st then (sr, st::sh) else (st::sr, sh)))
End

(* Execute the non-ending statements of a BB.
 * generalized: produces list of running states and a list of terminated states *)
Definition bir_symb_exec_stmtB_list_rec_def:
  (bir_symb_exec_stmtB_list_rec 
        (p: 'a bir_program_t)
        (sts_running: 'a bir_symb_state_t list)
        []
        sts_halted
          = (sts_running, sts_halted)
    )  /\

    (bir_symb_exec_stmtB_list_rec p sts_running (stmt :: stmt_lst) sts_halted
         =
        let
          st_lst = FLAT (MAP (bir_symb_exec_stmtB stmt) sts_running);
          (sts_running', sts_halted') = bir_symb_exec_partition_running st_lst ([],[]);
        in
          bir_symb_exec_stmtB_list_rec  p sts_running' stmt_lst (APPEND sts_halted' sts_halted)
    )
End

(* helper function for the recursive function above ... *)
Definition bir_symb_exec_bb_statements:
  bir_symb_exec_bb_statements p sts stmt_lst = 
        bir_symb_exec_stmtB_list_rec p sts stmt_lst []
End

(* Execute the End Statemens of a BB
 * same output as above *)
Definition bir_symb_exec_bb_last_statement:
  bir_symb_exec_bb_last_statement p sts_running stmt = 
        bir_symb_exec_partition_running (FLAT (MAP (bir_symb_exec_stmtE p stmt) sts_running)) ([],[])
End

(* Execute a single basic block.
 * same output as above *)
Definition bir_symb_exec_blk_def:
  bir_symb_exec_blk (p: 'a bir_program_t) (blk: 'a bir_block_t) sts_running = 
        let
          (sts_running', sts_halted') = bir_symb_exec_bb_statements p sts_running blk.bb_statements;
          (sts_running'', sts_halted'') = bir_symb_exec_bb_last_statement p sts_running' blk.bb_last_statement;
        in
          (sts_running'', APPEND sts_halted' sts_halted'')
End 

(* Given a Program and a State, find the respective block and execute it *)
Definition bir_symb_exec_label_block_def:
  (bir_symb_exec_label_block (p: 'a bir_program_t) (st: 'a bir_symb_state_t))
       = 
    case (bir_get_program_block_info_by_label p st.bsst_pc.bpc_label) of 
    | NONE => ([], [bir_symb_state_set_failed st])
    | SOME (_, blk) => if bir_symb_state_is_terminated st
                       then ([], [st]) else (bir_symb_exec_blk p blk [st])
End
    
val _ = export_theory();
