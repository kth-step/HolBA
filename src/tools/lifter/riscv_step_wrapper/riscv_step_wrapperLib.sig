signature riscv_step_wrapperLib =
sig
   val riscv_step_rem_ss : string list -> Term.term -> Thm.thm
   val riscv_step_rem_ss_hex : string list -> string -> Thm.thm
end
