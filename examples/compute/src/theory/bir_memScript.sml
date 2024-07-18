(* ------------------------------------------------------------------------- *)
(*  Definition of memory expression evaluation and theorems associated       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory ;
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

(* Gives the size of an immediate as a number *)
Definition size_of_bir_immtype_def:
  (size_of_bir_immtype Bit1 = 1) /\
  (size_of_bir_immtype Bit8 = 8) /\
  (size_of_bir_immtype Bit16 = 16) /\
  (size_of_bir_immtype Bit32 = 32) /\
  (size_of_bir_immtype Bit64 = 64) /\
  (size_of_bir_immtype Bit128 = 128) 
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





val _ = export_theory () ;
