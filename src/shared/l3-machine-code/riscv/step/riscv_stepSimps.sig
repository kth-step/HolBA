signature riscv_stepSimps =
sig
  include Abbrev

  (* Simplifies some RISC-V datatype stuff *)
  val riscv_ss : simpLib.simpset

  val is_System : term -> bool

  val writeCSR_match_rule : thm -> thm
  val CSRMap_match_rule : thm -> thm
end
