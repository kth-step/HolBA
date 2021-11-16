open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;

open bir_valuesTheory;
open bir_expTheory;
open bir_envTheory;
open bir_programTheory;
open bir_typing_expTheory;

open bir_bool_expTheory;
open bir_exp_substitutionsTheory;

val _ = new_theory "bir_symb";

(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
- 'a_label    = bir_programcounter_t
- 'b_var      = string
- 'c_val      = bir_val_t
- 'd_extra    = bir_status_t

- 'e_symbol   = bir_var_t
- 'f_symbexpr = bir_exp_t
- 'g_type     = bir_type_t
*)
val _ = Datatype `bir_concst_t = symb_concst_t bir_programcounter_t string bir_val_t bir_status_t`;
val _ = Datatype `bir_symbst_t = symb_symbst_t bir_programcounter_t string bir_exp_t bir_status_t`;
(* function to convert between conrete states *)
(*
(* TODO: have to add observation in symbolic execution, could have this for another instance also?! no, probably not useful to split this *)
val bir_symb_to_concst_def = Define `
    bir_symb_to_concst s =
      (SymbConcSt
        s.bst_pc
        (\bvn. bir_env_lookup bvn (s.bst_environ s))
        s.bst_status)
`;

val bir_symb_from_concst_def = Define `
    bir_symb_from_concst (SymbConcSt lbl env status) =
      <|
        bst_pc       := lbl;
        bst_environ  := BEnv env;
        bst_status   := status
      |>
`;
*)

(* sr_step_conc is "bir_exec_step" *)
(*
val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir prog =
    <|
      sr_val_true        := bir_val_true;
      sr_mk_exp_symb_f   := BExp_Den;
      sr_mk_exp_conj_f   := BExp_BinExp BIExp_And;
      sr_mk_exp_eq_f     := \e1. if type_of_bir_exp e1 = SOME MemType then BExp_MemEq e1 else BExp_BinPred BIExp_Equal e1;

      sr_subst_f         := \(s,e). bir_exp_subst (FUPDATE (s,e) FEMPTY);

      (* symbols of symbolic exepressions *)
      sr_symbols_f       := bir_vars_of_exp;

      (* type business *)
      sr_typeof_val      := type_of_bir_val;
      sr_typeof_symb     := bir_var_type;
      sr_typeof_exp      := type_of_bir_exp;
      sr_ARB_val         := bir_val_default;

      (* interpretation business, type error produces NONE value *)
      sr_interpret_f     := \i. \e. bir_eval_exp (bir_exp_subst (FUN_FMAP (\x. THE (symb_interpr_get i x)) (bir_vars_of_exp e)) e) bir_env_empty;

      (* finally, concrete and symbolic executions *)
      sr_step_conc       := bir_symb_to_concst o SND o (bir_exec_step prog) o bir_symb_from_concst;

      sr_step_symb       := \a. \b. false;
   |>
`;
*)

(*
val _ = Datatype `birs_state_t = <|
  bsst_pc       : bir_programcounter_t;
  bsst_environ  : ;
  bsst_status   : bir_status_t;
  bsst_pcond    : 
|>`;

val birs_state_is_terminated_def = Define `
    birs_state_is_terminated st =
      (st.bsst_status <> BST_Running)
`;

(* TODO: is the following a concern or can get away without this?! *)
(* NOTICE: the assumption regarding types in the single step soundness property
           must be sufficiently strong to allow us to rule out all non-well-typed execution
   !!!!! *)
(* TODO: then probably need to add a custom predicate to the record that is the context under which the simulation holds,
         and add this as assumption to the STEP rule, and in the BIR case we would add that the program typechecks *)

val birs_state_set_failed_def = Define `
    birs_state_set_failed st =
      (st with bsst_status := BST_Failed)
`;

(* ... *)

val birs_exec_stmtB_def = Define `
   (birs_exec_stmtB (BStmt_Assert ex) st =
     (NONE, birs_exec_stmt_assert ex st)) /\
   (birs_exec_stmtB (BStmt_Assume ex) st =
     (NONE, birs_exec_stmt_assume ex st)) /\
   (birs_exec_stmtB (BStmt_Assign v ex) st =
     (NONE, birs_exec_stmt_assign v ex st)) /\
   (birs_exec_stmtB (BStmt_Observe oid ec el obf) st =
     birs_exec_stmt_observe oid ec el obf st)
`;

(* ... *)

val birs_exec_stmtE_def = Define `
   (birs_exec_stmtE p (BStmt_Jmp l) st =
     birs_exec_stmt_jmp p l st) /\
   (birs_exec_stmtE p (BStmt_CJmp e l1 l2) st =
     birs_exec_stmt_cjmp p e l1 l2 st) /\
   (birs_exec_stmtE p (BStmt_Halt ex) st =
     birs_exec_stmt_halt ex st)
`;

val birs_exec_stmt_def = Define `
   (birs_exec_stmt (p:'a bir_program_t) (BStmtB (bst:'a bir_stmt_basic_t)) st =
     let (oo, st') = birs_exec_stmtB bst st in
     if (birs_state_is_terminated st') then
       (oo, st')
     else
       (oo, st' with bst_pc updated_by bir_pc_next)) /\
   (birs_exec_stmt p (BStmtE bst) st =
     (NONE, birs_exec_stmtE p bst st))
`;

val birs_exec_step_def = Define `
    birs_exec_step p state =
  if (birs_state_is_terminated state) then (NONE, state) else
  case (bir_get_current_statement p state.bst_pc) of
    | NONE => (NONE, birs_state_set_failed state)
    | SOME stm => (birs_exec_stmt p stm state)
`;
*)

(* TODO: prove soundness of this instance here (several soundness properties) *)

(* TODO: have to think how to add memory structure expressions on top of BIR expressions, possibly make another instance! *)

val _ = export_theory();
