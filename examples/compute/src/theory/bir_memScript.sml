(* ------------------------------------------------------------------------- *)
(*  Definition of memory expression evaluation and theorems associated       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open bir_basicTheory;
open bir_typingTheory;
open bitstringTheory numeral_bitTheory;



val _ = new_theory "bir_mem";


(* ------------------------------------------ *)
(* ----------------- UTILITY ---------------- *)
(* ------------------------------------------ *)

(* Number to Bitstring *)
Definition n2bs_def:
  (n2bs n Bit1   = Imm1   (n2w n)) /\
  (n2bs n Bit8   = Imm8   (n2w n)) /\
  (n2bs n Bit16  = Imm16  (n2w n)) /\
  (n2bs n Bit32  = Imm32  (n2w n)) /\
  (n2bs n Bit64  = Imm64  (n2w n)) /\
  (n2bs n Bit128 = Imm128 (n2w n))
End

(* Boolean list (vector) to bitstring *)
Definition v2bs_def:
  v2bs v s = n2bs (v2n v) s
End


(* Immediate to number *)
Definition b2n_def:
  (b2n ( Imm1   w ) = w2n w) /\
  (b2n ( Imm8   w ) = w2n w) /\
  (b2n ( Imm16  w ) = w2n w) /\
  (b2n ( Imm32  w ) = w2n w) /\
  (b2n ( Imm64  w ) = w2n w) /\
  (b2n ( Imm128 w ) = w2n w)
End

(* Immediate to bitstring *)
Definition b2v_def:
  (b2v ( Imm1   w ) = w2v w) /\
  (b2v ( Imm8   w ) = w2v w) /\
  (b2v ( Imm16  w ) = w2v w) /\
  (b2v ( Imm32  w ) = w2v w) /\
  (b2v ( Imm64  w ) = w2v w) /\
  (b2v ( Imm128 w ) = w2v w)
End

Definition bitstring_split_aux_def:
  (bitstring_split_aux 0 acc bs = NONE) /\
  (bitstring_split_aux n acc [] = SOME $ REVERSE acc) /\
  (bitstring_split_aux n acc bs =
    bitstring_split_aux n ((TAKE n bs)::acc) (DROP n bs))
Termination
  WF_REL_TAC `measure (\ (_, _, l). LENGTH l)` >>
  simp_tac list_ss []
End

(* Splits a bitstring in chunks of n bits *)
Definition bitstring_split_def:
  bitstring_split n bs = bitstring_split_aux n [] bs
End


(* ------------------------------------------ *)
(* ------------------ LOAD ------------------ *)
(* ------------------------------------------ *)


(* Load a value from the mmap at the given address *)
Definition bir_load_mmap_def:
  bir_load_mmap (mmap: num |-> num) a =
      case FLOOKUP mmap a of
        | NONE => 0
        | SOME v => v
End


(* Concatenate multiple bitstrings to a number on the correct number of bits *)
Definition bir_mem_concat_def:
  bir_mem_concat vl rty = v2bs (FLAT vl) rty
End

(* Compute the address modulo the address space *)
Definition bir_mem_addr_def:
  bir_mem_addr aty a = MOD_2EXP (size_of_bir_immtype aty) a
End

(* Computes the number of memory splits we will read *)
Definition bir_number_of_mem_splits_def:
  bir_number_of_mem_splits vty rty aty =
    if ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) then
      if ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)) then
          SOME ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty))
      else NONE
    else NONE
End


(* Load a bitstring at the given address from a mmap and pad it *)
Definition bir_load_bitstring_from_mmap_def:
  bir_load_bitstring_from_mmap vty mmap (a:num) =
    fixwidth (size_of_bir_immtype vty) (n2v (bir_load_mmap mmap a))
End
  
(* Load n splits of size vty from mmap starting at addr *) 
Definition bir_load_splits_from_mmap_def:
  bir_load_splits_from_mmap aty vty mmap addr n =
    (MAP (\k. bir_load_bitstring_from_mmap vty mmap (bir_mem_addr aty (addr + k))) (COUNT_LIST n)) 
End


(* Eval an already unpacked load expression *)
Inductive bir_eval_load_from_mem:
[~BEnd_BigEndian:]
  (!aty vty mmap addr rty n.
    (bir_number_of_mem_splits vty rty aty = SOME n)
    ==>
    bir_eval_load_from_mem vty rty aty mmap BEnd_BigEndian addr 
      (BVal_Imm (bir_mem_concat (bir_load_splits_from_mmap aty vty mmap addr n) rty)))

[~BEnd_LittleEndian:]
  (!aty vty mmap addr rty n.
    (bir_number_of_mem_splits vty rty aty = SOME n)
    ==>
    bir_eval_load_from_mem vty rty aty mmap BEnd_LittleEndian addr
      (BVal_Imm (bir_mem_concat (REVERSE (bir_load_splits_from_mmap aty vty mmap addr n)) rty)))

[~BEnd_NoEndian:]
  (!aty vty mmap addr rty.
    (bir_number_of_mem_splits vty rty aty = SOME 1)
    ==>
    bir_eval_load_from_mem vty rty aty mmap BEnd_NoEndian addr
      (BVal_Imm (bir_mem_concat (bir_load_splits_from_mmap aty vty mmap addr 1) rty)))
End

Definition bir_eval_load_def:
  (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm addr) en rty v = 
    bir_eval_load_from_mem vty rty aty mmap en (b2n addr) v) /\
  (bir_eval_load _ _ _ _ _ = F)
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


(* ----------------------------------------- *)
(* ----------------- STORE ----------------- *)
(* ----------------------------------------- *)


(* Add all the bitstrings in the mmap at address a *)
Definition bir_update_mmap_def:
  (bir_update_mmap aty mmap a [] = mmap) /\
  (bir_update_mmap aty mmap a (v::vs) =
    bir_update_mmap aty (FUPDATE mmap ((bir_mem_addr aty a), v2n v)) (SUC a) vs)
End


Inductive bir_eval_store_in_mem:
[~BEnd_BigEndian:]
  !vty aty result mmap addr ll.
    (bir_number_of_mem_splits vty (type_of_bir_imm result) aty = SOME _) /\
    (bitstring_split (size_of_bir_immtype vty) (b2v result) = SOME ll)
    ==>
    bir_eval_store_in_mem vty aty result mmap BEnd_BigEndian addr
      (BVal_Mem aty vty (bir_update_mmap aty mmap addr ll))

[~BEnd_LittleEndian:]
  !vty aty result mmap addr ll.
    (bir_number_of_mem_splits vty (type_of_bir_imm result) aty = SOME _) /\
    (bitstring_split (size_of_bir_immtype vty) (b2v result) = SOME ll)
    ==>
    bir_eval_store_in_mem vty aty result mmap BEnd_LittleEndian addr
      (BVal_Mem aty vty (bir_update_mmap aty mmap addr (REVERSE ll)))

[~BEnd_NoEndian:]
  !vty aty result mmap addr ll.
    (bir_number_of_mem_splits vty (type_of_bir_imm result) aty = SOME 1) /\
    (bitstring_split (size_of_bir_immtype vty) (b2v result) = SOME ll)
    ==>
    bir_eval_store_in_mem vty aty result mmap BEnd_NoEndian addr
      (BVal_Mem aty vty (bir_update_mmap aty mmap addr ll))

End

Definition bir_eval_store_def:
  (bir_eval_store (BVal_Mem aty vty mmap) (BVal_Imm addr) en (BVal_Imm result) v = 
    bir_eval_store_in_mem vty aty result mmap en (b2n addr) v) /\
  (bir_eval_store _ _ _ _ _ = F)
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

(* ------------------------------------------ *)
(* ---------------- THEOREMS ---------------- *)
(* ------------------------------------------ *)


Theorem size_of_bir_immtype_leq_1:
  !b. 1 <= 2 ** (size_of_bir_immtype b)
Proof
  Cases_on `b` >>
  rw [size_of_bir_immtype_def]
QED


(* ------------------------------------------ *)
(* ------------------ LOAD ------------------ *)
(* ------------------------------------------ *)


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



(* If the operands are correctly typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_load_bigendian:
  !aty vty v_mem v_addr rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_load v_mem v_addr BEnd_BigEndian rty v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
    rw [bir_eval_load_eq_compute_load] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    rw [val_from_imm_option_def] >>
    metis_tac []
QED

Theorem type_of_bir_val_imp_bir_eval_load_littleendian:
  !aty vty v_mem v_addr rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_load v_mem v_addr BEnd_LittleEndian rty v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
    rw [bir_eval_load_eq_compute_load] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    rw [val_from_imm_option_def] >>
    metis_tac []
QED

Theorem type_of_bir_val_imp_bir_eval_load_noendian:
  !aty vty v_mem v_addr rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) = 1))
  ==>
  ?v. bir_eval_load v_mem v_addr BEnd_NoEndian rty v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
    rw [bir_eval_load_eq_compute_load] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    rw [val_from_imm_option_def] >>
    metis_tac [size_of_bir_immtype_leq_1]
QED


(* Type of bir_mem_concat *)
Theorem type_of_bir_imm_bir_mem_concat:
  !vl rty. type_of_bir_imm (bir_mem_concat vl rty) = rty
Proof
  Cases_on `rty` >>
    rw [bir_mem_concat_def, v2bs_def, n2bs_def] >>
    rw [type_of_bir_imm_def]
QED
  

(* Type conservation theorem *)
Theorem bir_eval_load_correct_type:
  !v_mem v_addr en rty v.
    bir_eval_load v_mem v_addr en rty v ==>
    (type_of_bir_val v = (BType_Imm rty))
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
  Cases_on `en` >>

  simp [bir_eval_load_def, bir_eval_load_from_mem_cases] >>
  metis_tac [type_of_bir_val_def, type_of_bir_imm_def, type_of_bir_imm_bir_mem_concat]
QED


(* ----------------------------------------- *)
(* ----------------- STORE ----------------- *)
(* ----------------------------------------- *)

(* bitstring_split will never be NONE *)
Theorem bitstring_split_aux_size_of_bir_immtype:
  !ty acc bs. ?ll. bitstring_split_aux (size_of_bir_immtype ty) acc bs = SOME ll
Proof
  gen_tac >>
  `?n. size_of_bir_immtype ty = SUC n` by (Cases_on `ty` >> simp [size_of_bir_immtype_def]) >>
  measureInduct_on `LENGTH bs` >>
    Cases_on `bs` >>
    fs [bitstring_split_def, bitstring_split_aux_def] >>
    `LENGTH (DROP n t) < SUC (LENGTH t)` by rw [listTheory.LENGTH_DROP] >>
    metis_tac [bitstring_split_aux_def, listTheory.LENGTH_DROP]
QED

Theorem bitstring_split_size_of_bir_immtype:
  !ty bs. bitstring_split (size_of_bir_immtype ty) bs <> NONE
Proof
  simp [bitstring_split_def] >>
  metis_tac [bitstring_split_aux_size_of_bir_immtype, optionTheory.NOT_SOME_NONE]
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

(* If the operands are correctly typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_store_bigendian:
  !aty vty v_mem v_addr v_result rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
    (type_of_bir_val v_result = BType_Imm rty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_store v_mem v_addr BEnd_BigEndian v_result v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
    rw [bir_eval_store_eq_compute_store] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    TRY CASE_TAC >>
      fs [bitstring_split_size_of_bir_immtype, bitstring_split_def] >>
      metis_tac [bitstring_split_aux_size_of_bir_immtype]
QED

Theorem type_of_bir_val_imp_bir_eval_store_littleendian:
  !aty vty v_mem v_addr v_result rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
    (type_of_bir_val v_result = BType_Imm rty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_store v_mem v_addr BEnd_LittleEndian v_result v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
    rw [bir_eval_store_eq_compute_store] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    TRY CASE_TAC >>
      fs [bitstring_split_size_of_bir_immtype] >>
      metis_tac []
QED

Theorem type_of_bir_val_imp_bir_eval_store_noendian:
  !aty vty v_mem v_addr v_result rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
    (type_of_bir_val v_result = BType_Imm rty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) = 1))
  ==>
  ?v. bir_eval_store v_mem v_addr BEnd_NoEndian v_result v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
    rw [bir_eval_store_eq_compute_store] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    TRY CASE_TAC >>
      fs [bitstring_split_size_of_bir_immtype] >>
      metis_tac [size_of_bir_immtype_leq_1]
QED



(* Type conservation theorem *)
Theorem bir_eval_store_correct_type:
  !v_mem v_addr en v_result v.
    bir_eval_store v_mem v_addr en v_result v ==>
    (type_of_bir_val v = type_of_bir_val v_mem)
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
  Cases_on `en` >>

  simp [bir_eval_store_def, bir_eval_store_in_mem_cases] >>
  rw [type_of_bir_val_def, type_of_bir_imm_def] >>
  metis_tac [type_of_bir_val_def, type_of_bir_imm_def]
QED

val _ = export_theory ();
