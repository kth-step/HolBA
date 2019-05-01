signature bir_programSyntax =
sig
   include Abbrev

   (***************)
   (* bir_label_t *)
   (***************)

   val bir_label_t_ty : hol_type

   val BL_Label_tm          : term
   val dest_BL_Label        : term -> term
   val dest_BL_Label_string : term -> string
   val is_BL_Label          : term -> bool
   val mk_BL_Label          : term -> term
   val mk_BL_Label_string   : string -> term


   val BL_Address_tm   : term
   val dest_BL_Address : term -> term
   val is_BL_Address   : term -> bool
   val mk_BL_Address   : term -> term


   (*******************)
   (* bir_label_exp_t *)
   (*******************)

   val bir_label_exp_t_ty : hol_type

   val BLE_Label_tm   : term
   val dest_BLE_Label : term -> term
   val is_BLE_Label   : term -> bool
   val mk_BLE_Label   : term -> term

   val BLE_Exp_tm   : term
   val dest_BLE_Exp : term -> term
   val is_BLE_Exp   : term -> bool
   val mk_BLE_Exp   : term -> term


   (********************)
   (* bir_stmt_basic_t *)
   (********************)

   val mk_bir_stmt_basic_t_ty   : hol_type -> hol_type
   val dest_bir_stmt_basic_t_ty : hol_type -> hol_type
   val is_bir_stmt_basic_t_ty   : hol_type -> bool

   val BStmt_Declare_tm   : term
   val dest_BStmt_Declare : term -> term
   val is_BStmt_Declare   : term -> bool
   val mk_BStmt_Declare   : term -> term

   val BStmt_Assign_tm   : term
   val dest_BStmt_Assign : term -> term * term
   val is_BStmt_Assign   : term -> bool
   val mk_BStmt_Assign   : term * term -> term

   val BStmt_Assert_tm   : term
   val dest_BStmt_Assert : term -> term
   val is_BStmt_Assert   : term -> bool
   val mk_BStmt_Assert   : term -> term

   val BStmt_Assume_tm   : term
   val dest_BStmt_Assume : term -> term
   val is_BStmt_Assume   : term -> bool
   val mk_BStmt_Assume   : term -> term

   val BStmt_Observe_tm   : term
   val dest_BStmt_Observe : term -> term * term * term
   val is_BStmt_Observe   : term -> bool
   val mk_BStmt_Observe   : term * term * term -> term


   (******************)
   (* bir_stmt_end_t *)
   (******************)

   (* The type itself *)
   val bir_stmt_end_t_ty  : hol_type

   val BStmt_Jmp_tm   : term
   val dest_BStmt_Jmp : term -> term
   val is_BStmt_Jmp   : term -> bool
   val mk_BStmt_Jmp   : term -> term

   val BStmt_CJmp_tm   : term
   val dest_BStmt_CJmp : term -> term * term * term
   val is_BStmt_CJmp   : term -> bool
   val mk_BStmt_CJmp   : term * term * term -> term

   val BStmt_Halt_tm   : term
   val dest_BStmt_Halt : term -> term
   val is_BStmt_Halt   : term -> bool
   val mk_BStmt_Halt   : term -> term


   (**************)
   (* bir_stmt_t *)
   (**************)

   val mk_bir_stmt_t_ty   : hol_type -> hol_type
   val dest_bir_stmt_t_ty : hol_type -> hol_type
   val is_bir_stmt_t_ty   : hol_type -> bool

   val BStmtB_tm   : term
   val dest_BStmtB : term -> term
   val is_BStmtB   : term -> bool
   val mk_BStmtB   : term -> term

   val BStmtE_tm   : term
   val dest_BStmtE : term -> term
   val is_BStmtE   : term -> bool
   val mk_BStmtE   : term -> term


   (***************)
   (* bir_block_t *)
   (***************)

   val mk_bir_block_t_ty   : hol_type -> hol_type
   val dest_bir_block_t_ty : hol_type -> hol_type
   val is_bir_block_t_ty   : hol_type -> bool


   val dest_bir_block : term -> term * term * term
   val is_bir_block   : term -> bool
   val mk_bir_block   : term * term * term -> term

   (* Often one is interested in the list of basic statements in a block.
      The following code splits the term containing a list of basic statements
      into an SML list of terms. In case the empty list is used, thereby the
      type ob observation is lost and therefore made explicit. *)
   val dest_bir_block_list : term -> hol_type * term * term list * term
   val mk_bir_block_list   : hol_type * term * term list * term -> term


   (*****************)
   (* bir_program_t *)
   (*****************)

   val mk_bir_program_t_ty   : hol_type -> hol_type
   val dest_bir_program_t_ty : hol_type -> hol_type
   val is_bir_program_t_ty   : hol_type -> bool

   val BirProgram_tm        : term
   val dest_BirProgram      : term -> term
   val dest_BirProgram_list : term -> hol_type * term list
   val is_BirProgram        : term -> bool
   val mk_BirProgram        : term -> term
   val mk_BirProgram_list   : hol_type * term list -> term


   (************************)
   (* bir_programcounter_t *)
   (************************)

   val bir_programcounter_t_ty : hol_type

   val dest_bir_programcounter : term -> term * term
   val is_bir_programcounter   : term -> bool
   val mk_bir_programcounter   : term * term -> term

   val bir_block_pc_tm   : term
   val dest_bir_block_pc : term -> term
   val is_bir_block_pc   : term -> bool
   val mk_bir_block_pc   : term -> term

   val bir_pc_first_tm   : term
   val dest_bir_pc_first : term -> term
   val is_bir_pc_first   : term -> bool
   val mk_bir_pc_first   : term -> term


   (****************)
   (* bir_status_t *)
   (****************)

   val bir_status_t_ty : hol_type

   val BST_Running_tm : term
   val is_BST_Running : term -> bool

   val BST_Failed_tm : term
   val is_BST_Failed : term -> bool

   val BST_AssumptionViolated_tm : term
   val is_BST_AssumptionViolated : term -> bool

   val BST_Halted_tm   : term
   val dest_BST_Halted : term -> term
   val is_BST_Halted   : term -> bool
   val mk_BST_Halted   : term -> term

   val BST_JumpOutside_tm   : term
   val dest_BST_JumpOutside : term -> term
   val is_BST_JumpOutside   : term -> bool
   val mk_BST_JumpOutside   : term -> term


   (***************)
   (* bir_state_t *)
   (***************)

   val bir_state_t_ty : hol_type

   val dest_bir_state : term -> term * term * term
   val is_bir_state   : term -> bool
   val mk_bir_state   : term * term * term -> term

   val bir_state_init_tm   : term
   val dest_bir_state_init : term -> term
   val is_bir_state_init   : term -> bool
   val mk_bir_state_init   : term -> term

   val bir_state_is_terminated_tm   : term
   val dest_bir_state_is_terminated : term -> term
   val is_bir_state_is_terminated   : term -> bool
   val mk_bir_state_is_terminated   : term -> term

   val bst_status_tm   : term
   val dest_bst_status : term -> term
   val is_bst_status   : term -> bool
   val mk_bst_status   : term -> term

   val bst_environ_tm   : term
   val dest_bst_environ : term -> term
   val is_bst_environ   : term -> bool
   val mk_bst_environ   : term -> term

   val bst_pc_tm   : term
   val dest_bst_pc : term -> term
   val is_bst_pc   : term -> bool
   val mk_bst_pc   : term -> term


   (***************************)
   (* various functions       *)
   (***************************)

   val bir_exec_step_tm   : term
   val dest_bir_exec_step : term -> term * term
   val is_bir_exec_step   : term -> bool
   val mk_bir_exec_step   : term * term -> term

   val bir_exec_steps_tm   : term
   val dest_bir_exec_steps : term -> term * term
   val is_bir_exec_steps   : term -> bool
   val mk_bir_exec_steps   : term * term -> term

   val bir_exec_step_n_tm   : term
   val dest_bir_exec_step_n : term -> term * term * term
   val is_bir_exec_step_n   : term -> bool
   val mk_bir_exec_step_n   : term * term * term -> term

end
