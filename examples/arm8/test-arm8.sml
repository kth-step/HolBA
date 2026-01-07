open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open swapTheory swap_symb_transfTheory swap_propTheory;
open incrTheory incr_symb_transfTheory incr_propTheory;

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

(* ---- *)
(* swap *)
(* ---- *)

val _ = print_and_check_thm
  "swap ARMv8 lift theorem"
  bir_swap_arm8_lift_THM
  ``
  bir_is_lifted_prog arm8_bmr (WI_end (0x718w : word64) (0x73cw : word64))
   bir_swap_progbin
   (bir_swap_prog : 'obs_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "swap BSPEC contract theorem"
  bspec_cont_swap
  ``bir_cont (bir_swap_prog : 'a bir_program_t)
    bir_exp_true (BL_Address (Imm64 0x718w))
    {BL_Address (Imm64 0x730w)} {}
    (bspec_swap_pre pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
    (\l. if l = BL_Address (Imm64 0x730w)
         then bspec_swap_post pre_x0 pre_x1 pre_x0_deref pre_x1_deref
         else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "swap ARMv8 backlifted theorem"
  arm8_cont_swap
  ``arm8_cont
     bir_swap_progbin
     swap_init_addr {swap_end_addr}
     (arm8_swap_pre pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
     (arm8_swap_post pre_x0 pre_x1 pre_x0_deref pre_x1_deref)``;

(* ---- *)
(* incr *)
(* ---- *)
  
val _ = print_and_check_thm
  "incr ARMv8 lift theorem"
  bir_incr_arm8_lift_THM
  ``
  bir_is_lifted_prog arm8_bmr (WI_end (0x718w : word64) (0x728w : word64))
   bir_incr_progbin
   (bir_incr_prog : 'obs_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "incr BSPEC contract theorem"
  bspec_cont_incr
 ``bir_cont (bir_incr_prog : 'a bir_program_t)
  bir_exp_true (BL_Address (Imm64 0x718w))
  {BL_Address (Imm64 0x71cw)} {} (bspec_incr_pre pre_x0)
  (\l. if l = BL_Address (Imm64 0x71cw)
       then bspec_incr_post pre_x0
       else bir_exp_false)``;

val _ = print_and_check_thm
  "incr ARMv8 backlifted theorem"
  arm8_cont_incr
  ``arm8_cont
     bir_incr_progbin
     incr_init_addr {incr_end_addr}
     (arm8_incr_pre pre_x0) (arm8_incr_post pre_x0)``;
