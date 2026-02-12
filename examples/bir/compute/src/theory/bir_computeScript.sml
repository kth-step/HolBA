(* ------------------------------------------------------------------------- *)
(*  Definition of the general computation function                           *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open ottTheory birTheory;

val _ = new_theory "bir_compute";

(* Computes a binary expression of two immediates *)
Definition bir_compute_binexp_imm_def:
  (bir_compute_binexp_imm BIExp_And (Imm1 w1) (Imm1 w2) = SOME (Imm1 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm8 w1) (Imm8 w2) = SOME (Imm8 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm16 w1) (Imm16 w2) = SOME (Imm16 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm32 w1) (Imm32 w2) = SOME (Imm32 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm64 w1) (Imm64 w2) = SOME (Imm64 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm128 w1) (Imm128 w2) = SOME (Imm128 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm1 w1) (Imm1 w2) = SOME (Imm1 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm8 w1) (Imm8 w2) = SOME (Imm8 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm16 w1) (Imm16 w2) = SOME (Imm16 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm32 w1) (Imm32 w2) = SOME (Imm32 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm64 w1) (Imm64 w2) = SOME (Imm64 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm128 w1) (Imm128 w2) = SOME (Imm128 (word_add w1 w2))) /\
  (bir_compute_binexp_imm binexp _ _ = NONE)
End

(* Computes a general binary expression with values as parameters *)
Definition bir_compute_binexp_def:
  (bir_compute_binexp binexp (SOME (BVal_Imm imm1)) (SOME (BVal_Imm imm2)) =
    val_from_imm_option (bir_compute_binexp_imm binexp imm1 imm2)) /\
  (bir_compute_binexp _ _ _ = NONE)
End

(* Computes a binary expression of an immediate *)
Definition bir_compute_unaryexp_imm_def:
  (bir_compute_unaryexp_imm BIExp_Not (Imm1 w1) = SOME (Imm1 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm8 w1) = SOME (Imm8 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm16 w1) = SOME (Imm16 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm32 w1) = SOME (Imm32 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm64 w1) = SOME (Imm64 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm128 w1) = SOME (Imm128 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm1 w1) = SOME (Imm1 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm8 w1) = SOME (Imm8 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm16 w1) = SOME (Imm16 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm32 w1) = SOME (Imm32 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm64 w1) = SOME (Imm64 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm128 w1) = SOME (Imm128 (word_2comp w1)))
End

(* Computes Unary expression *)
Definition bir_compute_unaryexp_def:
  (bir_compute_unaryexp unaryexp (SOME (BVal_Imm imm1)) = 
    val_from_imm_option (bir_compute_unaryexp_imm unaryexp imm1)) /\
  (bir_compute_unaryexp _ _ = NONE)
End

(* Computes a binary predicate of two immediates *)
Definition bir_compute_binpred_imm_def:
  (bir_compute_binpred_imm BIExp_Equal (Imm1 w1) (Imm1 w2) = $= w1 w2) /\
  (bir_compute_binpred_imm BIExp_Equal (Imm8 w1) (Imm8 w2) = $= w1 w2) /\
  (bir_compute_binpred_imm BIExp_Equal (Imm16 w1) (Imm16 w2) = $= w1 w2) /\
  (bir_compute_binpred_imm BIExp_Equal (Imm32 w1) (Imm32 w2) = $= w1 w2) /\
  (bir_compute_binpred_imm BIExp_Equal (Imm64 w1) (Imm64 w2) = $= w1 w2) /\
  (bir_compute_binpred_imm BIExp_Equal (Imm128 w1) (Imm128 w2) = $= w1 w2) /\
  (bir_compute_binpred_imm BIExp_LessThan (Imm1 w1) (Imm1 w2) = word_lo w1 w2) /\
  (bir_compute_binpred_imm BIExp_LessThan (Imm8 w1) (Imm8 w2) = word_lo w1 w2) /\
  (bir_compute_binpred_imm BIExp_LessThan (Imm16 w1) (Imm16 w2) = word_lo w1 w2) /\
  (bir_compute_binpred_imm BIExp_LessThan (Imm32 w1) (Imm32 w2) = word_lo w1 w2) /\
  (bir_compute_binpred_imm BIExp_LessThan (Imm64 w1) (Imm64 w2) = word_lo w1 w2) /\
  (bir_compute_binpred_imm BIExp_LessThan (Imm128 w1) (Imm128 w2) = word_lo w1 w2) /\
  (bir_compute_binpred_imm binpred _ _ = F)
End

(* Computes a general binary predicate with values as parameters *)
Definition bir_compute_binpred_def:
  (bir_compute_binpred binpred (SOME (BVal_Imm imm1)) (SOME (BVal_Imm imm2)) =
    SOME (BVal_Imm (bool2b (bir_compute_binpred_imm binpred imm1 imm2)))) /\
  (bir_compute_binpred _ _ _ = NONE)
End

(* Computes an ifthenelse expression of two values *)
Definition bir_compute_ifthenelse_def:
  bir_compute_ifthenelse b v1 v2 = 
    if b = SOME birT then v1 
    else if b = SOME birF then v2
    else NONE
End

(* Computes an already unpacked load expression *)
Definition bir_compute_load_from_mem_def:
  bir_compute_load_from_mem
  (vty : bir_immtype_t) (rty : bir_immtype_t) (aty : bir_immtype_t) (mmap : num |-> num) (en: bir_endian_t) (addr:num) =

   case (bir_number_of_mem_splits vty rty aty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = bir_load_splits_from_mmap aty vty mmap addr n in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in
        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_mem_concat vs'' rty)
   )
End

Definition bir_compute_load_def:
  (bir_compute_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm addr)) en rty = 
    val_from_imm_option (bir_compute_load_from_mem vty rty aty mmap en (b2n addr))) /\
  (bir_compute_load _ _ _ _ = NONE)
End

(* Compute an already unpacked store expression *)
Definition bir_compute_store_in_mem_def:
  bir_compute_store_in_mem
  (vty : bir_immtype_t) (aty : bir_immtype_t) (result : bir_imm_t) (mmap : num |-> num) (en: bir_endian_t) (addr:num) =

   let rty = type_of_bir_imm result in
   case (bir_number_of_mem_splits vty rty aty) of
    | NONE => NONE
    | SOME (n:num) => (
      case  (bitstring_split (size_of_bir_immtype vty) (b2v result)) of
        | NONE => NONE
        | SOME vs =>
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in

        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (BVal_Mem aty vty (bir_update_mmap aty mmap addr vs''))
   )
End

Definition bir_compute_store_def:
  (bir_compute_store (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm addr)) en (SOME (BVal_Imm result)) = 
    bir_compute_store_in_mem vty aty result mmap en (b2n addr)) /\
  (bir_compute_store _ _ _ _ = NONE)
End

(* General Computation function *)
Definition bir_compute_exp_def:
  (bir_compute_exp (BExp_Const n) env = SOME (BVal_Imm n)) /\

  (bir_compute_exp (BExp_MemConst aty vty mmap) env = SOME (BVal_Mem aty vty mmap)) /\

  (bir_compute_exp (BExp_Den v) env = bir_env_lookup env v) /\

  (* (bir_compute (BExp_Cast ct e ty) env = ( *)
  (*    bir_eval_cast ct (bir_compute e env) ty)) /\ *)

  (bir_compute_exp (BExp_UnaryExp et e) env = (
     bir_compute_unaryexp et (bir_compute_exp e env))) /\

  (bir_compute_exp (BExp_BinExp et e1 e2) env = (
     bir_compute_binexp et (bir_compute_exp e1 env) (bir_compute_exp e2 env))) /\

  (bir_compute_exp (BExp_BinPred pt e1 e2) env = (
     bir_compute_binpred pt (bir_compute_exp e1 env) (bir_compute_exp e2 env))) /\
  (**)
  (* (bir_compute (BExp_MemEq e1 e2) env = ( *)
  (*    bir_eval_memeq (bir_compute e1 env) (bir_compute e2 env))) /\ *)
  (**)
  (**)
  (bir_compute_exp (BExp_IfThenElse c et ef) env =
     bir_compute_ifthenelse (bir_compute_exp c env) (bir_compute_exp et env) (bir_compute_exp ef env)
  ) /\

  (bir_compute_exp (BExp_Load mem_e a_e en ty) env =
     bir_compute_load (bir_compute_exp mem_e env) (bir_compute_exp a_e env) en ty) /\

  (bir_compute_exp (BExp_Store mem_e a_e en v_e) env =
     bir_compute_store (bir_compute_exp mem_e env) (bir_compute_exp a_e env) en (bir_compute_exp v_e env))
End

(* Eval and compute are similar *)
Theorem bir_eval_binexp_eq_compute_binexp:
  !binexp v1 v2 v. bir_eval_binexp binexp v1 v2 v <=> 
    bir_compute_binexp binexp (SOME v1) (SOME v2) = SOME v
Proof
  Cases_on `binexp` >>
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
  rw [bir_eval_binexp_cases, bir_compute_binexp_def] >>
  rw [bir_eval_binexp_imm_cases, bir_compute_binexp_imm_def] >>
  Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >>
  rw [bir_compute_binexp_imm_def, fetch "bir" "bir_imm_t_nchotomy", bir_binexp_get_oper_def] >>
  rw [val_from_imm_option_def,clause_name_def] >>
  metis_tac []
QED

(* Eval and Compute are similar *)
Theorem bir_eval_unaryexp_eq_compute_unaryexp:
  !unaryexp v1 v. bir_eval_unaryexp unaryexp v1 v <=> 
    bir_compute_unaryexp unaryexp (SOME v1) = SOME v
Proof
  Cases_on `unaryexp` >>
  Cases_on `v1` >> Cases_on `v` >>
  rw [bir_eval_unaryexp_cases, bir_compute_unaryexp_def] >>
  rw [bir_eval_unaryexp_imm_cases, bir_compute_unaryexp_imm_def] >>
  Cases_on `b` >> Cases_on `b'` >>
  rw [bir_compute_unaryexp_imm_def, fetch "bir" "bir_imm_t_nchotomy", bir_unaryexp_get_oper_def] >>
  rw [val_from_imm_option_def,clause_name_def] >>
  metis_tac []
QED

Theorem bir_eval_binpred_imp_compute_binpred:
  !binpred v1 v2 v. bir_eval_binpred binpred v1 v2 v ==> 
    bir_compute_binpred binpred (SOME v1) (SOME v2) = SOME v
Proof
  Cases_on `binpred` >>
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
  rw [bir_eval_binpred_cases, bir_compute_binpred_def] >>
  rw [bir_eval_binpred_imm_cases, bir_compute_binpred_imm_def] >>
  Cases_on `b` >> Cases_on `b'` >>
  rw [bool2b_def, bool2w_def, bir_compute_binpred_imm_def, fetch "bir" "bir_imm_t_nchotomy"] >>
  fs [bir_eval_binpred_imm_cases, bir_binpred_get_oper_def] >>
  metis_tac []
QED

(* If the term is well typed, then eval and compute are the same *)
Theorem well_typed_bir_eval_binpred_eq_compute_binpred:
  !binpred v1 v2 v. 
    (type_of_bir_val v1 = type_of_bir_val v2) ==>
  ( bir_eval_binpred binpred v1 v2 v <=> 
    bir_compute_binpred binpred (SOME v1) (SOME v2) = SOME v)
Proof
  Cases_on `binpred` >>
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
  rw [bir_eval_binpred_cases, bir_compute_binpred_def] >>
  rw [bir_eval_binpred_imm_cases, bir_compute_binpred_imm_def] >>
  Cases_on `b` >> Cases_on `b'` >>
  rw [bool2b_def, bool2w_def, bir_compute_binpred_imm_def, fetch "bir" "bir_imm_t_nchotomy"] >>
  fs [bir_eval_binpred_imm_cases, type_of_bir_val_def,
      type_of_bir_imm_def, bir_binpred_get_oper_def,clause_name_def] >>
  metis_tac []
QED

(* Eval and compute are similar *)
Theorem bir_eval_ifthenelse_eq_compute_ifthenelse:
  !v (v1:bir_val_t) (v2:bir_val_t) (v3:bir_val_t).
  (bir_eval_ifthenelse v v1 v2 v3 <=>
    bir_compute_ifthenelse (SOME v) (SOME v1) (SOME v2) = SOME v3)
Proof
  Cases_on `v` >> Cases_on `v1` >> Cases_on `v2` >> Cases_on `v3` >>
  rw [bir_eval_ifthenelse_cases, bir_compute_ifthenelse_def, birT_def, birF_def,clause_name_def] >>
  metis_tac []
QED

(* Eval and compute are similar *)
Theorem bir_eval_load_eq_compute_load:
  !v_mem v_addr en rty v.
    bir_eval_load v_mem v_addr en rty v <=>
    (bir_compute_load (SOME v_mem) (SOME v_addr) en rty = SOME v)
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `en` >>
    rw [bir_eval_load_def, bir_eval_load_from_mem_cases] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def] >>
    CASE_TAC >>
    simp [] >>
    rw [val_from_imm_option_def] >>
    metis_tac []
QED

(* Eval and compute are similar *)
Theorem bir_eval_store_eq_compute_store:
  !v_mem v_addr en result v.
    bir_eval_store v_mem v_addr en result v <=>
    (bir_compute_store (SOME v_mem) (SOME v_addr) en (SOME result) = SOME v)
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `en` >> Cases_on `result` >>
    rw [bir_eval_store_def, bir_eval_store_in_mem_cases] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def] >>
    CASE_TAC >> CASE_TAC >> TRY CASE_TAC >>
      simp [] >>
      metis_tac []
QED

val _ = export_theory ();
