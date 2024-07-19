(* ------------------------------------------------------------------------- *)
(*  Definition of memory expression evaluation and theorems associated       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory ;
open bir_typingTheory ;
open bitstringTheory numeral_bitTheory ;


val _ = new_theory "bir_mem" ;


(* ****************************************** *)
(* ***************** UTILITY **************** *)
(* ****************************************** *)

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



(* ****************************************** *)
(* ****************** LOAD ****************** *)
(* ****************************************** *)


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

(* Compute the address modulo the adress space *)
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
                 |  SOME vs'' => SOME (BVal_Imm (bir_mem_concat vs'' rty))
   )
End

Definition bir_compute_load_def:
  (bir_compute_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm addr)) en rty = 
    bir_compute_load_from_mem vty rty aty mmap en (b2n addr)) /\
  (bir_compute_load _ _ _ _ = NONE)
End


(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)


(* Eval and compute are similar *)
Theorem bir_eval_load_eq_compute_load:
  !v_mem v_addr en rty v.
    bir_eval_load v_mem v_addr en rty v <=>
    (bir_compute_load (SOME v_mem) (SOME v_addr) en rty = SOME v)
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `en` >>
    rw [bir_eval_load_def, bir_eval_load_from_mem_cases] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def] >>
    Cases_on `bir_number_of_mem_splits b0 rty b` >>
    Cases_on `x = 1` >>
    simp [] >>
    METIS_TAC []
QED








val _ = export_theory () ;
