open HolKernel boolLib Parse bossLib;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open bir_riscv_backlifterTheory;

open bir_backlifterLib;

open bir_tsTheory;

open swapTheory;

val _ = new_theory "swap_prop";

val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_swap_prog``;

(el 1)blocks;
(el 2)blocks;

bir_swap_riscv_lift_THM;

Definition swap_mem_spec_def:
 swap_mem_spec ms =
 let ms'_mem8 = (riscv_mem_store_dword (ms.c_gpr ms.procID 0w)
   (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 1w)) ms.MEM8)
 in
   (riscv_mem_store_dword (ms.c_gpr ms.procID 1w)
    (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 0w)) ms'_mem8)
End

Definition swap_spec_output_def:
 swap_spec_output ms : riscv_state = ms with MEM8 := swap_mem_spec ms
End

Definition swap_spec_def:
 swap_spec ms ms' : bool = (ms'.MEM8 = swap_mem_spec ms)
End

(*
  BINARY RISC-V PROGRAM (via DISSASSEMBLY):
  val prog_bin = ``bir_swap_progbin``;
  
  LIFTED BIR PROGRAM (via LIFTER):
  val bir_prog_def = bir_swap_prog_def;

  BIR-LEVEL CONTRACT FOR LIFTED BIR PROGRAM (via SYMBOLIC EXEC + SMT):
  val bir_ct = bir_swap_ct;

  PRECONDITION PREDICATE FOR RISC-V PROGRAM (via RISC-V SPEC):
  val riscv_pre = ``riscv_swap_pre``;

  POSTCONDITION PREDICATE FOR RISC-V PROGRAM (via RISC-V SPEC):
  val riscv_post = ``riscv_swap_post``;

  LIFTED BIR PROGRAM PRECONDITIONS (via RISC-V SPEC): 
  val bir_pre_defs = [bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def];
  val bir_pre1_def = bir_add_reg_contract_1_pre_def;

  RISC-V PRECONDITION IMPLIES BIR PRECONDITION:
  val riscv_pre_imp_bir_pre_thm = swap_riscv_pre_imp_bir_pre_thm;

  LIFTER BIR PROGRAM POSTCONDITIONS (via RISC-V SPEC):
  val bir_post_defs = [bir_add_reg_contract_4_post_def];

  BIR POSTCONDITION IMPLIES RISC-V POSTCONDITION:
  val riscv_post_imp_bir_post_thm = swap_riscv_post_imp_bir_post_thm;

  RISC-V PROGRAM THEOREM:
  val bir_is_lifted_prog_thm = bir_swap_riscv_lift_THM;

  val riscv_swap_contract_thm =

   save_thm("riscv_swap_contract_thm",

    get_riscv_contract_sing
     bir_swap_ct ``bir_swap_progbin``
     ``riscv_swap_pre`` ``riscv_swap_post`` bir_swap_prog_def
     [bir_swap_contract_pre_def, bir_swap_pre_def]
     bir_swap_contract_pre_def riscv_pre_imp_bir_pre_thm
     [bir_swap_contract_post_def] riscv_post_imp_bir_post_thm
     bir_swap_riscv_lift_THM

  get_riscv_contract_sing USES: GENERAL riscv_lift_contract_thm
*)

Definition riscv_swap_pre_def:
 riscv_swap_pre (m : riscv_state) = T
End

Definition riscv_swap_post_def:
 riscv_swap_post (m : riscv_state) = T
End

Definition bir_swap_pre_def:
  bir_swap_pre : bir_exp_t = bir_exp_true
End

Definition bir_swap_post_def:
 bir_swap_post : bir_exp_t = bir_exp_true
End

Theorem swap_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir riscv_swap_pre bir_swap_pre
Proof
 cheat
QED

Theorem swap_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv riscv_swap_post (\l. bir_swap_post) ls
Proof
 cheat
QED

Theorem bir_cont_swap:
  bir_cont bir_swap_prog bir_exp_true
   (BL_Address (Imm64 0w)) {BL_Address (Imm64 20w)} {}
  bir_swap_pre
  (\l. if l = BL_Address (Imm64 20w) then bir_swap_post else bir_exp_false)
Proof
 (* this is supposed to be proved by symbolic exec + SMT *)
 cheat
QED

(*
val riscv_swap_contract_thm =
   save_thm("riscv_swap_contract_thm",
    get_riscv_contract_sing
     bir_cont_swap ``bir_swap_progbin``
     ``riscv_swap_pre`` ``riscv_swap_post`` bir_swap_prog_def
     [bir_swap_pre_def]
     bir_swap_pre_def swap_riscv_pre_imp_bir_pre_thm
     [bir_swap_post_def] swap_riscv_post_imp_bir_post_thm
     bir_swap_riscv_lift_THM);
*)

val _ = export_theory ();
