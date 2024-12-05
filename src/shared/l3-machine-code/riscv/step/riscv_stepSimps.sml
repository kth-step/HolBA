structure riscv_stepSimps :> riscv_stepSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open riscvTheory;

val cond_updates = utilsLib.mk_cond_update_thms [``:riscv_state``]
val datatype_rwts =
  utilsLib.datatype_rewrites true "riscv"
    ["riscv_state", "VM_Mode", "Architecture", "accessType", "Privilege"]

val riscv_ss = (std_ss++(rewrites (cond_updates@datatype_rwts)))



(* Syntax functions for writeCSR *)
val (writeCSR_tm,  mk_writeCSR, dest_writeCSR, is_writeCSR) = syntax_fns2 "riscv" "writeCSR"

(* Syntax functions for CSRMap *)
val (CSRMap_tm,  mk_CSRMap, dest_CSRMap, is_CSRMap) = syntax_fns2 "riscv" "CSRMap"

(* Syntax functions for System *)
val (System_tm,  mk_System, dest_System, is_System) = syntax_fns1 "riscv" "System"

(* Filters out duplicate sub-terms. *)
local
fun filter_equal_terms' []     filtered_list = filtered_list
  | filter_equal_terms' (h::t) [] = filter_equal_terms' t [h]
  | filter_equal_terms' (h::t) filtered_list =
    if isSome (List.find (term_eq h) filtered_list)
    then filter_equal_terms' t filtered_list
    else filter_equal_terms' t (h::filtered_list)
in
fun filter_equal_terms tm_list = filter_equal_terms' tm_list []
end
;

fun get_CSRMap_exps_from_tm tm = filter_equal_terms (find_terms (fn t => is_CSRMap t) tm)
fun get_CSRMap_exps thm = get_CSRMap_exps_from_tm (concl thm)

fun get_writeCSR_exps thm = filter_equal_terms (find_terms (fn t => is_writeCSR t) (concl thm))

val CSRMap_conv = (
  (SIMP_CONV (bool_ss++bitstringLib.v2w_n2w_ss)
             [CSRMap_def]
  ) THENC 
  wordsLib.WORD_CONV THENC
  SIMP_CONV riscv_ss []
  )

fun CSRMap_match_rule_conv tm =
  let
    val CSRMap_exps = get_CSRMap_exps_from_tm tm
    val CSRMap_rewrs = map CSRMap_conv CSRMap_exps
  in
    SIMP_CONV riscv_ss CSRMap_rewrs tm
  end
;

val writeCSR_conv = (
  (SIMP_CONV (bool_ss++bitstringLib.v2w_n2w_ss)
             [writeCSR_def, write'CSR_def, write'CSRMap_def]
  ) THENC
  (* TODO: Treat CSRMap using matching in a nested way here?
   *       Tests seem to imply not needed... *)
(*
  wordsLib.WORD_CONV THENC (
    SIMP_CONV riscv_ss [LET_DEF, Delta_def, write'Delta_def,
			CSR_def]
  ) THENC
  CSRMap_match_rule_conv THENC
  wordsLib.WORD_CONV THENC (
    SIMP_CONV riscv_ss []
  )
*)
  wordsLib.WORD_CONV THENC (
    SIMP_CONV riscv_ss [LET_DEF, Delta_def, write'Delta_def,
			CSR_def, CSRMap_def]
  ) THENC
  wordsLib.WORD_CONV THENC (
    SIMP_CONV riscv_ss []
  )
)

fun CSRMap_match_rule thm =
  let
    val CSRMap_exps = get_CSRMap_exps thm
    val CSRMap_rewrs = map CSRMap_conv CSRMap_exps
  in
    SIMP_RULE riscv_ss CSRMap_rewrs thm
  end
;

fun writeCSR_match_rule thm =
  let
    val writeCSR_exps = get_writeCSR_exps thm
    val writeCSR_rewrs = map writeCSR_conv writeCSR_exps
  in
    SIMP_RULE riscv_ss writeCSR_rewrs thm
  end
;

end
