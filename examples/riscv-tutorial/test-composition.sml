open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open tutorial_compositionTheory;
open tutorial_backliftingTheory;
open tutorialExtra_compositionTheory;
open tutorialExtra2_compositionTheory;

fun print_and_check_thm name thm t_concl =
  let
    val _ = print (name ^ ":\n");
    val _ = print "===============================\n";
    val _ = (Hol_pp.print_thm thm; print "\n");
    val _ = if identical (concl thm) t_concl then () else
            raise ERR "print_and_check_thm" "conclusion is not as expected"
    val _ = print "\n\n";
  in
    ()
  end;


val _ = print_and_check_thm
  "HolBA tutorial example (BIR only)"
  bir_add_reg_ct
  ``
  bir_simp_jgmt
    (bir_add_reg_prog:'observation_type bir_program_t)
    bir_exp_true
    (BL_Address (Imm64 28w))
    {BL_Address (Imm64 72w)} EMPTY bir_add_reg_contract_1_pre
    (\l.
       if l = BL_Address (Imm64 72w) then bir_add_reg_contract_4_post
       else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "HolBA tutorial example (back to ARMv8)"
  arm_add_reg_contract_thm
  ``arm8_triple
      bir_add_reg_progbin
      (28w:word64)
      {(72w:word64)}
      arm8_add_reg_pre
      arm8_add_reg_post
  ``;

val _ = print_and_check_thm
  "Example \"BIR function reuse\""
  bir_att_ct
  ``
  bir_simp_jgmt
    bprog_add_times_two
    bir_exp_true
    (BL_Address (Imm32 (0w :word32)))
    {BL_Address (Imm32 (8w :word32))}
    (EMPTY :bir_label_t -> bool)
    (BExp_BinExp BIExp_And
          (BExp_BinPred BIExp_Equal (BExp_Den (BVar "x" (BType_Imm Bit32)))
             (BExp_Const (Imm32 (v1 :word32))))
          (BExp_BinPred BIExp_Equal (BExp_Den (BVar "y" (BType_Imm Bit32)))
             (BExp_Const (Imm32 (v2 :word32)))))
    (λ(l :bir_label_t).
            if l = BL_Address (Imm32 (8w :word32)) then
              BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "c" (BType_Imm Bit32)))
                (BExp_BinExp BIExp_Mult (BExp_Const (Imm32 (2w :word32)))
                   (BExp_BinExp BIExp_Plus (BExp_Const (Imm32 v1))
                      (BExp_Const (Imm32 v2))))
            else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "Example \"BIR optimized mutual recursion\" - is_even"
  bir_ieo_is_even_ht
  ``
  bir_simp_jgmt
    bprog_is_even_odd
    bir_exp_true
    (BL_Address (Imm32 (0w :word32)))
    {BL_Address (Imm32 (516w :word32)); BL_Address (Imm32 (512w :word32))}
    {}
    (bir_ieo_pre (v1 :word64)) (bir_ieo_sec_iseven_exit_post v1)
  ``;

val _ = print_and_check_thm
  "Example \"BIR optimized mutual recursion\" - is_odd"
  bir_ieo_is_odd_ht
  ``
  bir_simp_jgmt
    bprog_is_even_odd
    bir_exp_true
    (BL_Address (Imm32 (256w :word32)))
    {BL_Address (Imm32 (516w :word32)); BL_Address (Imm32 (512w :word32))}
    {}
    (bir_ieo_pre (v1 :word64)) (bir_ieo_sec_isodd_exit_post v1)
  ``;
