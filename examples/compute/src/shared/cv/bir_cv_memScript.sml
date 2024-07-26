(* ------------------------------------------------------------------------- *)
(*  Definition of memory expression evaluation and theorems associated       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory bir_cv_basicTheory ;
open bir_memTheory ;
open bir_typingTheory ;
open bitstringTheory numeral_bitTheory numposrepTheory ;



val _ = new_theory "bir_cv_mem" ;


(* ****************************************** *)
(* ****************** LOAD ****************** *)
(* ****************************************** *)


(* Load a value from the mmap at the given address *)
Definition bir_cv_load_mmap_def:
  bir_cv_load_mmap (mmap_alist : (num # num) list) a =
      case ALOOKUP mmap_alist a of
        | NONE => 0
        | SOME v => v
End

(* Converts a number to its binary representation *)
Definition cv_n2l_def:
  cv_n2l n = if n < 2 then [n MOD 2] else (n MOD 2) :: cv_n2l (n DIV 2)
End

Definition cv_n2v_def:
  cv_n2v n = boolify [] (cv_n2l n)
End


(* Load a bitstring at the given address from a mmap and pad it *)
Definition bir_cv_load_bitstring_from_mmap_def:
  bir_cv_load_bitstring_from_mmap vty mmap (a:num) =
    fixwidth (size_of_bir_immtype vty) (cv_n2v (bir_cv_load_mmap mmap a))
End
  
(* Load n splits of size vty from mmap starting at addr *) 
Definition bir_cv_load_splits_from_mmap_def:
  bir_cv_load_splits_from_mmap aty vty mmap addr n =
    (MAP (\k. bir_cv_load_bitstring_from_mmap vty mmap (bir_mem_addr aty (addr + k))) (COUNT_LIST n)) 
End


(* Computes an already unpacked load expression *)
Definition bir_cv_compute_load_from_mem_def:
  bir_cv_compute_load_from_mem
  (vty : bir_immtype_t) (rty : bir_immtype_t) (aty : bir_immtype_t) (mmap_alist : (num # num) list) (en: bir_endian_t) (addr:num) =

   case (bir_number_of_mem_splits vty rty aty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = bir_cv_load_splits_from_mmap aty vty mmap_alist addr n in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in
        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_mem_concat vs'' rty)
   )
End

Definition bir_cv_compute_load_def:
  (bir_cv_compute_load (SOME (BCVVal_Mem aty vty mmap_alist)) (SOME (BCVVal_Imm addr)) en rty = 
    cv_val_from_imm_option (bir_cv_compute_load_from_mem vty rty aty mmap_alist en (b2n addr))) /\
  (bir_cv_compute_load _ _ _ _ = NONE)
End


(* ***************************************** *)
(* ***************** STORE ***************** *)
(* ***************************************** *)


(* Add all the bitstrings in the mmap at address a *)
Definition bir_cv_update_mmap_def:
  (bir_cv_update_mmap aty mmap_alist a [] = mmap_alist) /\
  (bir_cv_update_mmap aty mmap_alist a (v::vs) =
    bir_cv_update_mmap aty (((bir_mem_addr aty a), v2n v)::mmap_alist) (SUC a) vs)
End


(* Compute an already unpacked store expression *)
Definition bir_cv_compute_store_in_mem_def:
  bir_cv_compute_store_in_mem
  (vty : bir_immtype_t) (aty : bir_immtype_t) (result : bir_imm_t) (mmap_alist : (num # num) list) (en: bir_endian_t) (addr:num) =

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
                 |  SOME vs'' => SOME (BCVVal_Mem aty vty (bir_cv_update_mmap aty mmap_alist addr vs''))
   )
End


Definition bir_cv_compute_store_def:
  (bir_cv_compute_store (SOME (BCVVal_Mem aty vty mmap_alist)) (SOME (BCVVal_Imm addr)) en (SOME (BCVVal_Imm result)) = 
    bir_cv_compute_store_in_mem vty aty result mmap_alist en (b2n addr)) /\
  (bir_cv_compute_store _ _ _ _ = NONE)
End

(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)

(* ****************************************** *)
(* ****************** LOAD ****************** *)
(* ****************************************** *)

(* Intermediary theorems for cv equivalence *)
Theorem cv_n2l_eq_n2l_2:
  !n. cv_n2l n = n2l 2 n
Proof
  completeInduct_on `n` >>
    simp [Once n2l_def] >>
    simp [Once cv_n2l_def]
QED
  

Theorem bir_cv_load_splits_from_mmap_eq_load_splits_from_mmap:
  !aty vty mmap_alist addr n.
    bir_cv_load_splits_from_mmap aty vty mmap_alist addr n = 
    bir_load_splits_from_mmap aty vty (alist_to_fmap mmap_alist) addr n
Proof
  rw [bir_cv_load_splits_from_mmap_def, bir_load_splits_from_mmap_def] >>
  simp [bir_cv_load_bitstring_from_mmap_def, bir_load_bitstring_from_mmap_def] >>
  simp [bir_cv_load_mmap_def, bir_load_mmap_def] >>
  simp [cv_n2l_eq_n2l_2, cv_n2v_def, n2v_def]
QED

Theorem bir_compute_load_from_mem_alist_to_fmap:
  !vty rty aty mmap_alist en addr.
    bir_cv_compute_load_from_mem vty rty aty mmap_alist en addr =
      bir_compute_load_from_mem vty rty aty (alist_to_fmap mmap_alist) en addr
Proof
  simp [bir_cv_compute_load_from_mem_def, bir_compute_load_from_mem_def] >>
  rw [bir_cv_load_splits_from_mmap_eq_load_splits_from_mmap]
QED



(* compute and cv_compute are similar *)
Theorem bir_cv_compute_load_eq_compute_load:
  !v_mem v_addr en rty.
  from_cv_val_option (bir_cv_compute_load v_mem v_addr en rty) =
    (bir_compute_load (from_cv_val_option v_mem) (from_cv_val_option v_addr) en rty)
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >| [
    ALL_TAC,
    ALL_TAC,
    Cases_on `x`,
    Cases_on `x` >> Cases_on `x'`
  ] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_cv_compute_load_def, bir_compute_load_def] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_compute_load_from_mem_alist_to_fmap] >>
    rw [val_from_cv_val_option_from_imm_option]
QED

(* ***************************************** *)
(* ***************** STORE ***************** *)
(* ***************************************** *)

Theorem bir_cv_update_mmap_eq_update_mmap:
  !aty mmap_alist a l.
    alist_to_fmap (bir_cv_update_mmap aty mmap_alist a l) =
      bir_update_mmap aty (alist_to_fmap mmap_alist) a l
Proof
  Induct_on `l` >>
  rw [bir_cv_update_mmap_def, bir_update_mmap_def]
QED

(* compute and cv_compute are similar *)
Theorem bir_cv_compute_store_eq_compute_store:
  !v_mem v_addr en result.
    from_cv_val_option (bir_cv_compute_store v_mem v_addr en result) =
    (bir_compute_store (from_cv_val_option v_mem) (from_cv_val_option v_addr) en (from_cv_val_option result))
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `en` >> Cases_on `result` >>
    TRY (Cases_on `x`) >> TRY (Cases_on `x'`) >> TRY (Cases_on `x''`) >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_cv_compute_store_def, bir_cv_compute_store_in_mem_def] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>

    Cases_on `bir_number_of_mem_splits b0 (type_of_bir_imm b'') b` >>
      rw [from_cv_val_option_def, from_cv_val_def] >>
      rw [bir_cv_update_mmap_eq_update_mmap]
QED


val _ = export_theory () ;
