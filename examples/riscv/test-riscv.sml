open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open swapTheory swap_symb_execTheory swap_propTheory;
open isqrtTheory isqrt_propTheory;
open mod2Theory mod2_propTheory;
open incrTheory incr_propTheory;

fun print_and_check_thm name thm t_concl =
  let
    val _ = print (name ^ ":\n");
    val _ = print "===============================\n";
    val _ = (Hol_pp.print_thm thm; print "\n");
    val _ = if identical (concl thm) t_concl then () else
            raise Fail "print_and_check_thm::conclusion is not as expected"
    val _ = print "\n\n";
  in
    ()
  end;

val _ = print_and_check_thm
  "swap RISC-V lift theorem"
  bir_swap_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0w : word64) (32w : word64))
   bir_swap_progbin
   (bir_swap_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "swap BIR contract theorem"
  bir_cont_swap
  ``bir_cont (bir_swap_prog : 'observation_type bir_program_t)
    bir_exp_true (BL_Address (Imm64 0w))
    {BL_Address (Imm64 20w)} {} bir_swap_pre
    (\l. if l = BL_Address (Imm64 20w) then bir_swap_post
        else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "swap RISC-V backlifted theorem"
  riscv_swap_contract_thm
  ``riscv_cont
     bir_swap_progbin
     0w {20w}
     riscv_swap_pre riscv_swap_post``;
  
val _ = print_and_check_thm
  "incr RISC-V lift theorem"
  bir_incr_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0w : word64) (8w : word64))
   bir_incr_progbin
   (bir_incr_prog : 'observation_type bir_program_t)
  ``;
