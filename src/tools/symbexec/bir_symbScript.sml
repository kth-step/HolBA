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

open bir_symb_supportTheory;

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
(*
"bir_concst_t = (bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t"
"bir_symbst_t = (bir_programcounter_t, string, bir_exp_t, bir_status_t) symb_symbst_t"
*)


(* functions to convert between conrete states *)
(* TODO: have to add observation in symbolic execution, could have this for another instance also?! no, probably not useful to split this *)
val birs_symb_to_concst_def = Define `
    birs_symb_to_concst s =
      (SymbConcSt
        s.bst_pc
        (\bvn. bir_env_lookup bvn s.bst_environ)
        s.bst_status)
`;

val birs_symb_from_concst_def = Define `
    birs_symb_from_concst (SymbConcSt lbl env status) =
      <|
        bst_pc       := lbl;
        bst_environ  := BEnv env;
        bst_status   := status
      |>
`;

(* sr_step_conc is in principle "bir_exec_step" *)


(* sr_step_symb, must define "birs_exec_step" now *)

(* first some general functions to deal with symbolic expressions (symbolic evaluation and interpretation) *)
val bir_exp_typeerror_def = Define `
    bir_exp_typeerror = BExp_BinExp BIExp_And (BExp_Const (Imm1 0w)) (BExp_Const (Imm8 0w))
`;
val birs_eval_exp_subst_var_def = Define `
    birs_eval_exp_subst_var x senv =
      case senv (bir_var_name x) of
                | SOME x_ex =>
                    if type_of_bir_exp (x_ex) = SOME (bir_var_type x) then
                      x_ex
                    else
                      bir_exp_typeerror
                | NONE => bir_exp_typeerror
`;
val birs_eval_exp_subst_def = Define `
    birs_eval_exp_subst e senv =
      bir_exp_subst
        (FUN_FMAP
          (\x. birs_eval_exp_subst_var x senv)
          (bir_vars_of_exp e))
        e
`;
val birs_eval_exp_subst_ALT_def = Define `
   (birs_eval_exp_subst_ALT (BExp_Const n) senv = (BExp_Const n)) /\
   (birs_eval_exp_subst_ALT (BExp_MemConst aty vty mmap) senv = (BExp_MemConst aty vty mmap)) /\
   (birs_eval_exp_subst_ALT (BExp_Den v) senv = birs_eval_exp_subst_var v senv) /\
   (birs_eval_exp_subst_ALT (BExp_Cast ct e ty) senv =
      BExp_Cast ct (birs_eval_exp_subst_ALT e senv) ty) /\
   (birs_eval_exp_subst_ALT (BExp_UnaryExp et e) senv =
      BExp_UnaryExp et (birs_eval_exp_subst_ALT e senv)) /\
   (birs_eval_exp_subst_ALT (BExp_BinExp et e1 e2) senv =
      BExp_BinExp et
        (birs_eval_exp_subst_ALT e1 senv)
        (birs_eval_exp_subst_ALT e2 senv)) /\
   (birs_eval_exp_subst_ALT (BExp_BinPred pt e1 e2) senv =
      BExp_BinPred pt
        (birs_eval_exp_subst_ALT e1 senv)
        (birs_eval_exp_subst_ALT e2 senv)) /\
   (birs_eval_exp_subst_ALT (BExp_MemEq me1 me2) senv =
      BExp_MemEq
        (birs_eval_exp_subst_ALT me1 senv)
        (birs_eval_exp_subst_ALT me2 senv)) /\
   (birs_eval_exp_subst_ALT (BExp_IfThenElse c et ef) senv =
      BExp_IfThenElse
        (birs_eval_exp_subst_ALT c senv)
        (birs_eval_exp_subst_ALT et senv)
        (birs_eval_exp_subst_ALT ef senv)) /\
   (birs_eval_exp_subst_ALT (BExp_Load mem_e a_e en ty) senv =
      BExp_Load
        (birs_eval_exp_subst_ALT mem_e senv)
        (birs_eval_exp_subst_ALT a_e senv)
        en
        ty) /\
   (birs_eval_exp_subst_ALT (BExp_Store mem_e a_e en v_e) senv =
      BExp_Store
        (birs_eval_exp_subst_ALT mem_e senv)
        (birs_eval_exp_subst_ALT a_e senv)
        en
        (birs_eval_exp_subst_ALT v_e senv))
`;
val birs_eval_exp_def = Define `
    birs_eval_exp e senv =
      let e' = birs_eval_exp_subst e senv; in
        OPTION_MAP (\et. (e', et)) (type_of_bir_exp e')
`;


val bir_val_to_constexp_def = Define `
   (bir_val_to_constexp (BVal_Imm i) = BExp_Const i) /\
   (bir_val_to_constexp (BVal_Mem aty vty mmap) = BExp_MemConst aty vty mmap)
`;
val birs_interpret_fun_def = Define `
    birs_interpret_fun i e =
      bir_eval_exp (bir_exp_subst (FUN_FMAP (\x. bir_val_to_constexp (THE (symb_interpr_get i x))) (bir_vars_of_exp e)) e) bir_env_empty
`;



(* now a symbolic state *)
val _ = Datatype `birs_state_t = <|
  bsst_pc       : bir_programcounter_t;
  bsst_environ  : string -> bir_exp_t option;
  bsst_status   : bir_status_t;
  bsst_pcond    : bir_exp_t
|>`;

val birs_symb_to_symbst_def = Define `
    birs_symb_to_symbst s =
      (SymbSymbSt
        s.bsst_pc
        s.bsst_environ
        s.bsst_pcond
        s.bsst_status)
`;

val birs_symb_from_symbst_def = Define `
    birs_symb_from_symbst (SymbSymbSt lbl env pcond status) =
      <|
        bsst_pc       := lbl;
        bsst_environ  := env;
        bsst_pcond    := pcond;
        bsst_status   := status
      |>
`;

val birs_state_is_terminated_def = Define `
    birs_state_is_terminated st =
      (st.bsst_status <> BST_Running)
`;
val birs_state_set_typeerror_def = Define `
    birs_state_set_typeerror st =
      (st with bsst_status := BST_TypeError)`;
val birs_state_set_failed_def = Define `
    birs_state_set_failed st =
      (st with bsst_status := BST_Failed)
`;


(* now the definition of a symbolic execution step *)


(* ... *)

val birs_exec_stmt_assign_def = Define `
    birs_exec_stmt_assign v ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, vaty) =>
         if vaty = bir_var_type v then
           {st with bsst_environ := ((bir_var_name v =+ (SOME vaex)) st.bsst_environ)}
         else
           {birs_state_set_typeerror st}
     | NONE => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_assert_def = Define `
    birs_exec_stmt_assert ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        {st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex;
         (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex))
            with bsst_status := BST_AssertionViolated}
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_assume_def = Define `
    birs_exec_stmt_assume ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        {st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex;
         (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex))
            with bsst_status := BST_AssumptionViolated}
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_observe_def = Define `
    birs_exec_stmt_observe oid ec el obf st = {st}
`;

val birs_exec_stmtB_def = Define `
   (birs_exec_stmtB (BStmt_Assert ex) st =
     (birs_exec_stmt_assert ex st)) /\
   (birs_exec_stmtB (BStmt_Assume ex) st =
     (birs_exec_stmt_assume ex st)) /\
   (birs_exec_stmtB (BStmt_Assign v ex) st =
     (birs_exec_stmt_assign v ex st)) /\
   (birs_exec_stmtB (BStmt_Observe oid ec el obf) st =
     birs_exec_stmt_observe oid ec el obf st)
`;

(* ... *)

(* TODO: OHHHHHHHHHHHHHH NOOOOOOOOOOOOOOOOOOO *)
val birs_exec_stmt_halt_def = Define `
    birs_exec_stmt_halt ex (st : birs_state_t) = {st}
(*
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, _) => {st with bsst_status := BST_Halted ex}
     | NONE => {birs_state_set_typeerror st}
*)
`;

val birs_exec_stmt_jmp_to_label_def = Define `
    birs_exec_stmt_jmp_to_label p (st : birs_state_t) (l : bir_label_t) =
    if MEM l (bir_labels_of_program p) then
      st with bsst_pc := bir_block_pc l
    else st with bsst_status := (BST_JumpOutside l)
`;

val birs_eval_label_exp_def = Define `
   (birs_eval_label_exp (BLE_Label l) senv pcond = SOME {l}) /\
   (birs_eval_label_exp (BLE_Exp e)   senv pcond =
     case birs_eval_exp e senv of
      | SOME (vaex, BType_Imm _) => SOME {BL_Address iv | ?i. birs_interpret_fun i pcond = SOME bir_val_true /\ birs_interpret_fun i vaex = SOME (BVal_Imm iv)}
      | _ => NONE
   )
`;

val birs_exec_stmt_jmp_def = Define `
    birs_exec_stmt_jmp p le (st : birs_state_t) =
    case birs_eval_label_exp le st.bsst_environ st.bsst_pcond of
      | NONE => {birs_state_set_typeerror st}
      | SOME ls => IMAGE (birs_exec_stmt_jmp_to_label p st) ls
`;

val birs_exec_stmt_cjmp_def = Define `
    birs_exec_stmt_cjmp p ec l1 l2 (st : birs_state_t) =
      case birs_eval_exp ec st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        (birs_exec_stmt_jmp p l1 (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex)) UNION
        (birs_exec_stmt_jmp p l2 (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex)))
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

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
     let (sts') = birs_exec_stmtB bst st in
     IMAGE (\st'.
     if (birs_state_is_terminated st') then
       (st')
     else
       (st' with bsst_pc updated_by bir_pc_next)) sts') /\
   (birs_exec_stmt p (BStmtE bst) st =
     (birs_exec_stmtE p bst st))
`;

val birs_exec_step_def = Define `
    birs_exec_step p state =
  if (birs_state_is_terminated state) then {state} else
  case (bir_get_current_statement p state.bsst_pc) of
    | NONE => {birs_state_set_failed state}
    | SOME stm => (birs_exec_stmt p stm state)
`;

(* now the symbolic execution record *)
val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir prog =
    <|
      sr_val_true        := bir_val_true;
      sr_mk_exp_symb_f   := BExp_Den;
      sr_mk_exp_conj_f   := BExp_BinExp BIExp_And;
      sr_mk_exp_eq_f     := \e1. if option_CASE (type_of_bir_exp e1) F bir_type_is_Mem then BExp_MemEq e1 else BExp_BinPred BIExp_Equal e1;

      sr_subst_f         := \(s,e). bir_exp_subst (FUPDATE FEMPTY (s,e));

      (* symbols of symbolic exepressions *)
      sr_symbols_f       := bir_vars_of_exp;

      (* type business *)
      sr_typeof_val      := type_of_bir_val;
      sr_typeof_symb     := bir_var_type;
      sr_typeof_exp      := type_of_bir_exp;
      sr_ARB_val         := bir_val_default;

      (* interpretation business, type error produces NONE value *)
      sr_interpret_f     := birs_interpret_fun;

      (* finally, concrete and symbolic executions *)
      sr_step_conc       := birs_symb_to_concst o SND o (bir_exec_step prog) o birs_symb_from_concst;

      sr_step_symb       := (IMAGE birs_symb_to_symbst) o (birs_exec_step prog) o birs_symb_from_symbst;
   |>
`;

(* TODO: single step example (with "prototypical" property transfer) *)

(* TODO: prove soundness of this instance here (several soundness properties) *)

(* TODO: multiple step example (and also propert property transfer), best to use the simple motor set function from the beginning. or something equally simple *)

(* TODO: want to have another simple instance language? *)

(* TODO: have to think how to add memory structure expressions on top of BIR expressions, possibly make another instance! *)

val _ = export_theory();
