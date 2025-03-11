open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open aes_symb_execTheory;
open aes_unopt_symb_execTheory;
open chacha20Theory chacha20_column_round_propTheory chacha20_diagonal_round_propTheory;
open isqrtTheory isqrt_propTheory;
open kernel_trapTheory kernel_trap_entry_propTheory kernel_trap_return_propTheory;
open incrTheory incr_symb_transfTheory incr_propTheory;
open mod2Theory mod2_symb_transfTheory mod2_propTheory;
open modexpTheory modexp_symb_execTheory;
open motorTheory motor_symb_execTheory;
open swapTheory swap_symb_transfTheory swap_propTheory;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

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

(* --- *)
(* aes *)
(* --- *)

val _ = print "checking aes_symb_analysis_thm:\n";

val term_sz = term_size (concl aes_symb_analysis_thm);
val _ = print ("\nterm size = " ^ (Int.toString term_sz) ^ "\n\n");
val expected_term_sz = 21001;

val _ = if term_sz = expected_term_sz then () else
        raise Fail "term size of aes symbolic execution theorem is not as expected";

val triple_tm = ((snd o dest_comb o concl) aes_symb_analysis_thm);
val [init_st_tm, prog_frag_L_tm, final_sts_tm] = pairSyntax.strip_pair triple_tm;
val final_sts_birs_tm = final_sts_tm;

val _ = if (length o pred_setSyntax.strip_set) final_sts_birs_tm = 1 then () else
        raise Fail "number of symbolic final states in aes is not as expected";

(* --------- *)
(* aes-unopt *)
(* --------- *)

val _ = print "checking aes_unopt_symb_analysis_thm:\n";

val term_sz = term_size (concl aes_unopt_symb_analysis_thm);
val _ = print ("\nterm size = " ^ (Int.toString term_sz) ^ "\n\n");
val expected_term_sz = 38593;

val _ = if term_sz = expected_term_sz then () else
        raise Fail "term size of aes-unopt symbolic execution theorem is not as expected";

val triple_tm = ((snd o dest_comb o concl) aes_unopt_symb_analysis_thm);
val [init_st_tm, prog_frag_L_tm, final_sts_tm] = pairSyntax.strip_pair triple_tm;
val final_sts_birs_tm = final_sts_tm;

val _ = if (length o pred_setSyntax.strip_set) final_sts_birs_tm = 1 then () else
        raise Fail "number of symbolic final states in aes-unopt is not as expected";

(* -------- *)
(* chacha20 *)
(* -------- *)

val _ = print_and_check_thm
  "chacha20 RISC-V lift theorem"
  bir_chacha20_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x10488w : word64) (0x111C4w : word64))
   bir_chacha20_progbin
   (bir_chacha20_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "chacha20 column round RISC-V backlifted theorem"
  riscv_cont_chacha20_column_round
  ``riscv_cont bir_chacha20_progbin chacha20_column_round_init_addr {chacha20_column_round_end_addr}
     (riscv_chacha20_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
       pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
     (riscv_chacha20_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
       pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)``;

val _ = print_and_check_thm
  "chacha20 diagonal round RISC-V backlifted theorem"
  riscv_cont_chacha20_diagonal_round
  ``riscv_cont bir_chacha20_progbin chacha20_diagonal_round_init_addr {chacha20_diagonal_round_end_addr}
    (riscv_chacha20_diagonal_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
      pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
    (riscv_chacha20_diagonal_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
      pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)``;

(* ---- *)
(* incr *)
(* ---- *)
  
val _ = print_and_check_thm
  "incr RISC-V lift theorem"
  bir_incr_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x10488w : word64) (0x10498w : word64))
   bir_incr_progbin
   (bir_incr_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "incr BSPEC contract theorem"
  bspec_cont_incr
 ``bir_cont (bir_incr_prog : 'a bir_program_t)
  bir_exp_true (BL_Address (Imm64 0x10488w))
  {BL_Address (Imm64 0x1048cw)} {} (bspec_incr_pre pre_x10)
  (\l. if l = BL_Address (Imm64 0x1048cw)
       then bspec_incr_post pre_x10
       else bir_exp_false)``;

val _ = print_and_check_thm
  "incr RISC-V backlifted theorem"
  riscv_cont_incr
  ``riscv_cont
     bir_incr_progbin
     incr_init_addr {incr_end_addr}
     (riscv_incr_pre pre_x10) (riscv_incr_post pre_x10)``;

(* ----- *)
(* isqrt *)
(* ----- *)

val _ = print_and_check_thm
  "isqrt RISC-V lift theorem"
  bir_isqrt_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x10488w : word64) (0x104c4w : word64))
   bir_isqrt_progbin
   (bir_isqrt_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "isqrt RISC-V backlifted theorem 1"
  riscv_cont_isqrt_1
  ``riscv_cont bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr_1}
     (riscv_isqrt_pre_1 pre_x10)
     (riscv_isqrt_post_1 pre_x10)``;

val _ = print_and_check_thm
  "isqrt RISC-V backlifted theorem 2"
  riscv_cont_isqrt_2
  ``riscv_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr_2}
     (riscv_isqrt_pre_2 pre_x13 pre_x15)
     (riscv_isqrt_post_2 pre_x13 pre_x15)``;

val _ = print_and_check_thm
  "isqrt RISC-V backlifted theorem 3"
  riscv_cont_isqrt_3
  ``riscv_cont bir_isqrt_progbin isqrt_init_addr_3
     {isqrt_end_addr_3_loop; isqrt_end_addr_3_ret}
     (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14)
     (riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14)``;

(* ----------- *)
(* kernel-trap *)
(* ----------- *)

val _ = print_and_check_thm
  "kernel_trap RISC-V lift theorem"
  bir_kernel_trap_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x800000e0w : word64) (0x8000026Cw : word64))
   bir_kernel_trap_progbin
   (bir_kernel_trap_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "kernel_trap entry RISC-V backlifted theorem"
  riscv_cont_kernel_trap_entry
  ``riscv_cont bir_kernel_trap_progbin kernel_trap_entry_init_addr {kernel_trap_entry_end_addr}
      (riscv_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause pre_mhartid
        pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6 pre_x7 pre_x8
        pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14 pre_x15 pre_x16 pre_x17
        pre_x18 pre_x19 pre_x20 pre_x21 pre_x22 pre_x23 pre_x24 pre_x25 pre_x26
        pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
      (riscv_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause pre_mhartid
        pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6 pre_x7 pre_x8
        pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14 pre_x15 pre_x16 pre_x17
        pre_x18 pre_x19 pre_x20 pre_x21 pre_x22 pre_x23 pre_x24 pre_x25 pre_x26
        pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)``;

val _ = print_and_check_thm
  "kernel_trap return RISC-V backlifted theorem"
  riscv_cont_kernel_trap_return
  ``riscv_cont bir_kernel_trap_progbin kernel_trap_return_init_addr {kernel_trap_return_end_addr}
     (riscv_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
       pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
       pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
       pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
       pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
       pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
     (riscv_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
       pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
       pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
       pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
       pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
       pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)``;

(* ---- *)
(* mod2 *)
(* ---- *)

val _ = print_and_check_thm
  "mod2 RISC-V lift theorem"
  bir_mod2_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x10488w : word64) (0x10498w : word64))
   bir_mod2_progbin
   (bir_mod2_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "mod2 BSPEC contract theorem"
  bspec_cont_mod2
 ``bir_cont (bir_mod2_prog : 'a bir_program_t)
  bir_exp_true (BL_Address (Imm64 0x10488w))
  {BL_Address (Imm64 0x1048cw)} {} (bspec_mod2_pre pre_x10)
   (\l. if l = BL_Address (Imm64 0x1048cw)
        then bspec_mod2_post pre_x10
        else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "mod2 BIR contract theorem"
  bir_cont_mod2
 ``bir_cont (bir_mod2_prog : 'a bir_program_t)
  bir_exp_true
  (BL_Address (Imm64 mod2_init_addr)) {BL_Address (Imm64 mod2_end_addr)} {}
  (bir_mod2_pre pre_x10)
   (\l. if l = BL_Address (Imm64 mod2_end_addr)
        then bir_mod2_post pre_x10
        else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "mod2 RISC-V backlifted theorem"
  riscv_cont_mod2
  ``riscv_cont
     bir_mod2_progbin
     mod2_init_addr {mod2_end_addr}
     (riscv_mod2_pre pre_x10) (riscv_mod2_post pre_x10)``;

(* ------ *)
(* modexp *)
(* ------ *)

val _ = print_and_check_thm
  "modexp RISC-V lift theorem"
  bir_modexp_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x0w : word64) (0x100w : word64))
   bir_modexp_progbin
   (bir_modexp_prog : 'observation_type bir_program_t)
  ``;

val _ = print "checking modexp_symb_analysis_thm:\n";

val term_sz = term_size (concl modexp_symb_analysis_thm);
val _ = print ("\nterm size = " ^ (Int.toString term_sz) ^ "\n\n");
val expected_term_sz = 4827;

val _ = if term_sz = expected_term_sz then () else
        raise Fail "term size of modexp symbolic execution theorem is not as expected";

val triple_tm = ((snd o dest_comb o concl) modexp_symb_analysis_thm);
val [init_st_tm, prog_frag_L_tm, final_sts_tm] = pairSyntax.strip_pair triple_tm;
val final_sts_birs_tm = final_sts_tm;

val _ = if (length o pred_setSyntax.strip_set) final_sts_birs_tm = 2 then () else
        raise Fail "number of symbolic final states in modexp is not as expected";

(* ----- *)
(* motor *)
(* ----- *)

val _ = print_and_check_thm
  "motor RISC-V lift theorem"
  bir_motor_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x0w : word64) (0x900w : word64))
   bir_motor_progbin
   (bir_motor_prog : 'observation_type bir_program_t)
  ``;

val _ = print "checking motor_symb_analysis_thm:\n";

val term_sz = term_size (concl motor_symb_analysis_thm);
val _ = print ("\nterm size = " ^ (Int.toString term_sz) ^ "\n\n");
val expected_term_sz = 25634;

val _ = if term_sz = expected_term_sz then () else
        raise Fail "term size of motor symbolic execution theorem is not as expected";

val triple_tm = ((snd o dest_comb o concl) motor_symb_analysis_thm);
val [init_st_tm, prog_frag_L_tm, final_sts_tm] = pairSyntax.strip_pair triple_tm;
val final_sts_birs_tm = final_sts_tm;

val _ = if (length o pred_setSyntax.strip_set) final_sts_birs_tm = 7 then () else
        raise Fail "number of symbolic final states in motor is not as expected";

(* ---- *)
(* swap *)
(* ---- *)

val _ = print_and_check_thm
  "swap RISC-V lift theorem"
  bir_swap_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0x10488w : word64) (0x104A8w : word64))
   bir_swap_progbin
   (bir_swap_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "swap BSPEC contract theorem"
  bspec_cont_swap
  ``bir_cont (bir_swap_prog : 'a bir_program_t)
    bir_exp_true (BL_Address (Imm64 0x10488w))
    {BL_Address (Imm64 0x1049cw)} {}
    (bspec_swap_pre pre_x10 pre_x11 pre_x10_deref pre_x11_deref)
    (\l. if l = BL_Address (Imm64 0x1049cw)
         then bspec_swap_post pre_x10 pre_x11 pre_x10_deref pre_x11_deref
         else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "swap RISC-V backlifted theorem"
  riscv_cont_swap
  ``riscv_cont
     bir_swap_progbin
     swap_init_addr {swap_end_addr}
     (riscv_swap_pre pre_x10 pre_x11 pre_x10_deref pre_x11_deref)
     (riscv_swap_post pre_x10 pre_x11 pre_x10_deref pre_x11_deref)``;
