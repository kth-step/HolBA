open HolKernel Parse;
open testutils;
open bir_inst_liftingLib;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;
open PPBackEnd;

open selftestLib;

(******************)
(* Config options *)
(******************)

val unicode = false;
val raw_output = false;

(* Test M0 *)
val test_m0 = true;

(* Test ARM8 *)
val test_arm8 = true;

(* Run only manual tests *)
val test_fast = false;


val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else
                                     PPBackEnd.vt100_terminal);
val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)



(* TODO: Any other way to supply this to the functor? *)
structure log_name =
struct
  val log_name = "selftest_arm8.log";
end;
structure test_ARM8 = test_bmr(structure MD = bmil_arm8; structure log_name_str = log_name);

structure log_name =
struct
  val log_name = "selftest_m0_le_proc.log";
end;
structure test_m0_le_proc = test_bmr(structure MD = bmil_m0_LittleEnd_Process;
                                     structure log_name_str = log_name
);
structure log_name =
struct
  val log_name = "selftest_m0_be_proc.log";
end;
structure test_m0_be_proc = test_bmr(structure MD = bmil_m0_BigEnd_Process;
                                     structure log_name_str = log_name
);
structure log_name =
struct
  val log_name = "selftest_m0_le_main.log";
end;
structure test_m0_le_main = test_bmr(structure MD = bmil_m0_LittleEnd_Main;
                                     structure log_name_str = log_name
);
structure log_name =
struct
  val log_name = "selftest_m0_be_main.log";
end;
structure test_m0_be_main = test_bmr(structure MD = bmil_m0_BigEnd_Main;
                                     structure log_name_str = log_name
);


structure log_name =
struct
  val log_name = "selftest_m0_mod_le_proc.log";
end;
structure test_m0_mod_le_proc = test_bmr(structure MD = bmil_m0_mod_LittleEnd_Process;
                                     structure log_name_str = log_name
);
structure log_name =
struct
  val log_name = "selftest_m0_mod_be_proc.log";
end;
structure test_m0_mod_be_proc = test_bmr(structure MD = bmil_m0_mod_BigEnd_Process;
                                     structure log_name_str = log_name
);
structure log_name =
struct
  val log_name = "selftest_m0_mod_le_main.log";
end;
structure test_m0_mod_le_main = test_bmr(structure MD = bmil_m0_mod_LittleEnd_Main;
                                     structure log_name_str = log_name
);
structure log_name =
struct
  val log_name = "selftest_m0_mod_be_main.log";
end;
structure test_m0_mod_be_main = test_bmr(structure MD = bmil_m0_mod_BigEnd_Main;
                                     structure log_name_str = log_name
);


(**************************)
(* SOME MANUAL TESTS ARM8 *)
(**************************)

fun arm8_hex_code_of_asm asm = StringCvt.padLeft #"0" 8 $ hd $ arm8AssemblerLib.arm8_code [QUOTE asm]
fun arm8_lift_instr_asm mu_b mu_e pc asm =
  test_ARM8.lift_instr mu_b mu_e pc (arm8_hex_code_of_asm asm) (SOME asm);


val mu_b = Arbnum.fromInt 0;
val mu_e = Arbnum.fromInt 0x1000000;
val pc =   Arbnum.fromInt 0x10030;
val arm8_test_asm = arm8_lift_instr_asm mu_b mu_e pc
fun arm8_test_hex hex = test_ARM8.lift_instr mu_b mu_e pc hex NONE

val _ = if not test_arm8 then () else let
  val res = test_ARM8.print_log_with_style sty_HEADER true "\nMANUAL TESTS - ARMv8\n\n";
  val res = arm8_test_asm "add x0, x1, x2";
  val res = arm8_test_asm "add x1, x1, x1";
  val res = arm8_test_asm "adds x0, x1, x2";
  val res = arm8_test_asm "add x0, x0, x2";
  val res = arm8_test_asm "sub x0, x1, x2";
  val res = arm8_test_asm "adc x0, x1, x2";
  val res = arm8_test_asm "adc x0, x1, x1";
  val res = arm8_test_asm "adc w0, w1, w1";
  val res = arm8_test_asm "adcs x0, x1, x2";
  val res = arm8_test_asm "adcs x0, x1, x1";
  val res = arm8_test_asm "adcs w0, w1, w2";
  val res = arm8_test_asm "adcs w0, w1, w1";
  val res = arm8_test_asm "sbcs x0, x0, x2";
  val res = arm8_test_asm "sbcs x0, x1, x1";
  val res = arm8_test_asm "sbcs w0, w1, w2";
  val res = arm8_test_asm "sbcs w0, w1, w1";
  val res = arm8_test_asm "sbc x0, x0, x2";
  val res = arm8_test_asm "sub x0, x1, x2";
  val res = arm8_test_asm "mul x0, x1, x2";
  val res = arm8_test_asm "mul w0, w1, w1";
  val res = arm8_test_asm "cmp w0, #0";
  val res = arm8_test_asm "cmn w0, #0";
  val res = arm8_test_asm "cmn w0, w1";
  val res = arm8_test_asm "cmn x0, x9";
  val res = arm8_test_asm "ret";
  val res = arm8_test_asm "mov x0, #4";
  val res = arm8_test_asm "mov x0, x1";
  val res = arm8_test_asm "mvn x0, x1";
  val res = arm8_test_asm "adds x0, x2, #8";
  val res = arm8_test_asm "subs x0, x2, #8";
  val res = arm8_test_asm "adds x0, x1, x2";
  val res = arm8_test_asm "add x0, x0, x2";
  val res = arm8_test_asm "sub x0, x1, x2";
  val res = arm8_test_asm "add x0, x0, x2, LSL #2";
  val res = arm8_test_asm "add x0, x0, x2, ASR #2";
  val res = arm8_test_asm "add x0, x0, x2, LSR #2";
  val res = arm8_test_asm "add x0, x0, x2, LSL #0";
  val res = arm8_test_asm "add x0, x0, x2, ASR #0";
  val res = arm8_test_asm "add x0, x0, x2, LSR #0";
  val res = arm8_test_asm "add x4, SP, #8";
  val res = arm8_test_asm "add x4, SP, #8";
  val res = arm8_test_asm "adds x1, x1, #0";
  val res = arm8_test_asm "lsr x1, x2, #5";
  val res = arm8_test_asm "lsr x1, x2, #0";
  val res = arm8_test_asm "lsr x1, x1, #0";
  val res = arm8_test_asm "lsr x1, x2, x3";
  val res = arm8_test_asm "lsl x1, x2, #5";
  val res = arm8_test_asm "lsl x1, x2, #0";
  val res = arm8_test_asm "lsl x1, x1, #0";
  val res = arm8_test_asm "lsl x1, x2, x3";
  val res = arm8_test_asm "asr x1, x2, #5";
  val res = arm8_test_asm "asr x1, x2, #0";
  val res = arm8_test_asm "asr x1, x1, #0";
  val res = arm8_test_asm "asr x1, x2, x3";
  val res = arm8_test_asm "ror x1, x2, x3";
  val res = arm8_test_asm "ror x1, x2, #0";
  val res = arm8_test_asm "ror x1, x2, #2";
  val res = arm8_test_asm "ror x1, x2, #32";
  val res = arm8_test_asm "ror x1, x2, #63";
  val res = arm8_test_asm "ror w1, w2, #0";
  val res = arm8_test_asm "ror w1, w2, #2";
  val res = arm8_test_asm "l: b.eq l";
  val res = arm8_test_asm "l: cbnz w0, l";
  val res = arm8_test_asm "l: cbnz x0, l";
  val res = arm8_test_asm "l: tbnz w0, #3, l";
  val res = arm8_test_asm "l: tbnz x0, #3, l";
  val res = arm8_test_asm "l: cbz w0, l";
  val res = arm8_test_asm "l: cbz x0, l";
  val res = arm8_test_asm "l: tbz w0, #3, l";
  val res = arm8_test_asm "l: tbz x0, #3, l";
  val res = arm8_test_asm "ldr x0, [x2, #0]";
  val res = arm8_test_asm "lsl x0, x2, #8";
  val res = arm8_test_asm "lsl x0, x2, #8";
  val res = arm8_test_asm "lsr x0, x2, #8";
  val res = arm8_test_asm "str x0, [x2, #8]";
  val res = arm8_test_asm "ldp x1, x2, [x3]";
  val res = arm8_test_asm "ldp w1, w2, [x3]";
  val res = arm8_test_asm "stp x1, x2, [x3]";
  val res = arm8_test_asm "stp w1, w2, [x3]";
  val res = arm8_test_asm "ldpsw x1, x2, [x3]";
  val res = arm8_test_asm "movz w0, #4";
  val res = arm8_test_asm "movz x0, #4";
  val res = arm8_test_asm "movn x0, #4";
  val res = arm8_test_asm "movn w0, #4";
  val res = arm8_test_asm "movk w0, #4";
  val res = arm8_test_asm "movk x0, #4";
  val res = arm8_test_asm "bfm w1, w2, #2, #4";
  val res = arm8_test_asm "bfm w1, w2, #2, #8";
  val res = arm8_test_asm "bfm w1, w2, #8, #2";
  val res = arm8_test_asm "sbfm w1, w2, #2, #4";
  val res = arm8_test_asm "sbfm w1, w2, #2, #8";
  val res = arm8_test_asm "sbfm w1, w2, #8, #2";
  val res = arm8_test_asm "ubfm w1, w2, #2, #4";
  val res = arm8_test_asm "ubfm w1, w2, #2, #8";
  val res = arm8_test_asm "ubfm w1, w2, #8, #2";
  val res = arm8_test_asm "extr w1, w2, w3, #2";
  val res = arm8_test_asm "extr x1, x2, x3, #2";
  val res = arm8_test_asm "extr x1, x3, x2, #2";
  val res = arm8_test_asm "sxth w1, w2";
  val res = arm8_test_asm "sxtb w1, w2";
  val res = arm8_test_asm "sxtw x1, x2";
  val res = arm8_test_asm "uxth w1, w2";
  val res = arm8_test_asm "uxtb w1, w2";
  val res = arm8_test_asm "add x0, x1, w3, UXTB #2";
  val res = arm8_test_asm "add x0, x1, w3, SXTB #2";
  val res = arm8_test_asm "add w0, w1, w3, SXTB #0";
  val res = arm8_test_asm "adds x0, x1, w3, SXTB #4";
  val res = arm8_test_asm "adds x0, x1, w3, SXTB #0";
  val res = arm8_test_asm "sub x0, x1, w3, UXTB #2";
  val res = arm8_test_asm "sub x0, x1, w3, SXTB #2";
  val res = arm8_test_asm "sub w0, w1, w3, SXTB #0";
  val res = arm8_test_asm "subs x0, x1, w3, SXTB #4";
  val res = arm8_test_asm "subs x0, x1, w3, SXTB #0";
  val res = arm8_test_asm "bic x1, x2, x3, LSL #2"
  val res = arm8_test_asm "bic x1, x2, x3, LSR #2"
  val res = arm8_test_asm "bic x1, x2, x3, ASR #2"
  val res = arm8_test_asm "bic x1, x2, x2"
  val res = arm8_test_asm "bics x1, x2, x3, LSL #2"
  val res = arm8_test_asm "bics x1, x2, x3, LSR #2"
  val res = arm8_test_asm "bics x1, x2, x3, ASR #2"
  val res = arm8_test_asm "bics x1, x2, x2"
  val res = arm8_test_asm "eon x1, x2, x3, LSL #2"
  val res = arm8_test_asm "eon x1, x2, x3, LSR #2"
  val res = arm8_test_asm "eon x1, x2, x3, ASR #2"
  val res = arm8_test_asm "eon x1, x2, x2"
  val res = arm8_test_asm "lslv w1, w2, w3"
  val res = arm8_test_asm "lslv x1, x2, x3"
  val res = arm8_test_asm "lsrv w1, w2, w3"
  val res = arm8_test_asm "lsrv x1, x2, x3"
  val res = arm8_test_asm "asrv w1, w2, w3"
  val res = arm8_test_asm "asrv x1, x2, x3"
  val res = arm8_test_asm "rorv w1, w2, w3"
  val res = arm8_test_asm "rorv x1, x2, x3"
  val res = arm8_test_asm "cls w1, w2"
  val res = arm8_test_asm "cls x1, x2"
  val res = arm8_test_asm "clz w1, w2"
  val res = arm8_test_asm "clz x1, x2"
  val res = arm8_test_asm "rbit x1, x2"
  val res = arm8_test_asm "rbit w1, w2"
  val res = arm8_test_asm "rev w1, w2"
  val res = arm8_test_asm "rev x1, x2"
  val res = arm8_test_asm "rev16 w1, w2"
  val res = arm8_test_asm "rev16 x1, x2"
  val res = arm8_test_asm "rev32 x1, x2"
  val res = arm8_test_asm "csel w1, w2, w3, EQ"
  val res = arm8_test_asm "csel x1, x2, x3, EQ"
  val res = arm8_test_asm "csel x1, x2, x3, LE"
  val res = arm8_test_asm "csel x1, x2, x3, LT"
  val res = arm8_test_asm "csel x1, x2, x3, NE"

  val res = arm8_test_asm "csinc w1, w2, w3, LE"
  val res = arm8_test_asm "csinc x1, x2, x3, EQ"
  val res = arm8_test_asm "csinv w1, w2, w3, LE"
  val res = arm8_test_asm "csinv x1, x2, x3, EQ"
  val res = arm8_test_asm "csneg w1, w2, w3, LE"
  val res = arm8_test_asm "csneg x1, x2, x3, EQ"
  val res = arm8_test_asm "cset w1, LE"
  val res = arm8_test_asm "cset x1, LE"
  val res = arm8_test_asm "csetm w1, LE"
  val res = arm8_test_asm "csetm x1, LE"

  val res = arm8_test_asm "cinc w1, w2, LE"
  val res = arm8_test_asm "cinc x1, x2, EQ"
  val res = arm8_test_asm "cinv w1, w2, LE"
  val res = arm8_test_asm "cinv x1, x2, EQ"
  val res = arm8_test_asm "cneg w1, w2, LE"
  val res = arm8_test_asm "cneg x1, x2, EQ"
  val res = arm8_test_asm "ngc w1, w2"
  val res = arm8_test_asm "ngc x1, x2"
  val res = arm8_test_asm "ngcs w1, w2"
  val res = arm8_test_asm "ngcs x1, x2"

  val res = arm8_test_asm "ccmn w1, w2, #3, le"
  val res = arm8_test_asm "ccmp w1, w2, #3, le"
  val res = arm8_test_asm "ccmn x1, x2, #3, le"
  val res = arm8_test_asm "ccmp x1, x2, #3, le"

  val res = arm8_test_asm "madd w1, w2, w3, w4"
  val res = arm8_test_asm "madd x1, x2, x3, x4"
  val res = arm8_test_asm "msub w1, w2, w3, w4"
  val res = arm8_test_asm "msub x1, x2, x3, x4"
  val res = arm8_test_asm "msub x1, x2, x3, xzr"
  val res = arm8_test_asm "mneg w1, w2, w3"
  val res = arm8_test_asm "mneg x1, x2, x3"

  val res = arm8_test_asm "smaddl x1, w2, w3, x4"
  val res = arm8_test_asm "smsubl x1, w2, w3, x4"
  val res = arm8_test_asm "smull x1, w2, w3"
  val res = arm8_test_asm "smulh x1, x2, x3"

  val res = arm8_test_asm "umaddl x1, w2, w3, x4"
  val res = arm8_test_asm "umsubl x1, w2, w3, x4"
  val res = arm8_test_asm "umull x1, w2, w3"
  val res = arm8_test_asm "umulh x1, x2, x3"

  val res = arm8_test_asm "sdiv w1, w2, w3"
  val res = arm8_test_asm "sdiv x1, x2, x3"
  val res = arm8_test_asm "udiv w1, w2, w3"
  val res = arm8_test_asm "udiv x1, x2, x3"


    (* some instructions I din't see in this file *)
  (*  4003a0:     d61f0220        br      x17 *)
  val res = arm8_test_asm "br  x17";
  (*  4003a4:     d503201f        nop *)
  val res = arm8_test_asm "nop";
  (*  400510:     d63f0020        blr     x1 *)
  val res = arm8_test_asm "blr x1";
  (*  400430:     b4000040        cbz     x0, 400438 <call_weak_fn+0x10> *)
  val res = arm8_test_hex "B4000040";
  (*  4004cc:     35000080        cbnz    w0, 4004dc <__do_global_dtors_aux+0x24> *)
  val res = arm8_test_hex "35000080";

    (* another one, load with lsl, decode error *)
  (*  4005f8:     b8617801        ldr     w1, [x0,x1,lsl #2] *)
  val res = arm8_test_hex "b8617801";




  (* dummy prog lifting tests *)
  val region_1 = mk_bir_inst_lifting_region (Arbnum.fromInt 0x400470) [
    "D101C3FF","F9000FE0","B90017E1","F90007E2","F90003E3","B94017E0","51000400",
    "B9004FE0","F94007E0","B9400000","B9002FE0","F94007E0","B9400400","B90033E0"]

  val region_2 = mk_bir_inst_lifting_data_region (Arbnum.fromInt 0x400584) [
    "D101C3FF","F9000FE0","B90017E1","F90007E2","F90003E3"]

  val region_3 = BILMR (Arbnum.fromInt 0x401970, [
    ("D101C3FF", BILME_unknown), ("F9000FE0", BILME_code (SOME "???")) ,
     ("B90017E1", BILME_code NONE), ("F90007E2", BILME_data)])

  val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;
  val (res, fl) = test_ARM8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
    [region_1, region_2, region_3]

in () end;


(************************)
(* SOME MANUAL TESTS M0 *)
(************************)


fun m0_lift_instr mu_b mu_e pc hex_code desc = let
  val r1 = (print "LP "; test_m0_le_proc.lift_instr mu_b mu_e pc hex_code desc)
in if (test_fast) then (r1, r1, r1, r1, r1, r1, r1, r1) else let
  val r2 = (print "BP "; test_m0_be_proc.lift_instr mu_b mu_e pc hex_code desc)
  val r3 = (print "LM "; test_m0_le_main.lift_instr mu_b mu_e pc hex_code desc)
  val r4 = (print "BM "; test_m0_be_main.lift_instr mu_b mu_e pc hex_code desc)

  val r5 = (print "LP_mod "; test_m0_mod_le_proc.lift_instr mu_b mu_e pc hex_code desc)
  val r6 = (print "BP_mod "; test_m0_mod_be_proc.lift_instr mu_b mu_e pc hex_code desc)
  val r7 = (print "LM_mod "; test_m0_mod_le_main.lift_instr mu_b mu_e pc hex_code desc)
  val r8 = (print "BM_mod "; test_m0_mod_be_main.lift_instr mu_b mu_e pc hex_code desc)
in
  (r1, r2, r3, r4, r5, r6, r7, r8)
end end;

fun m0_hex_code_of_asm asm = hd (m0AssemblerLib.m0_code [QUOTE asm])
fun m0_lift_instr_asm mu_b mu_e pc asm =
  m0_lift_instr mu_b mu_e pc (m0_hex_code_of_asm asm) (SOME asm);


val mu_b = Arbnum.fromInt 0;
val mu_e = Arbnum.fromInt 0x10000;
val pc = Arbnum.fromInt 0x130;
val m0_test_asm = m0_lift_instr_asm mu_b mu_e pc
fun m0_test_hex hex = m0_lift_instr mu_b mu_e pc hex NONE

val _ = if not test_m0 then () else let
  val res = test_m0_le_proc.print_log_with_style sty_HEADER true "\nMANUAL TESTS - M0\n\n";

  val res = m0_test_asm "mov r0, r1";
  val res = m0_test_asm "movs r0, r1";
  val res = m0_test_asm "mov pc, r1";


  val res = m0_test_asm "adds r0, r1, #0";
  val res = m0_test_asm "adds r0, r1, #2";
  val res = m0_test_asm "adds r0, r1, r2";
  val res = m0_test_asm "add r0, r1";
  val res = m0_test_asm "add pc, r1"; (* TODO: improve result *)
  val res = m0_test_asm "adds r0, #128";
  val res = m0_test_asm "adcs r0, r1";
  val res = m0_test_asm "add sp, #128";
  val res = m0_test_asm "add r0, sp, #128";


  val res = m0_test_asm "subs r0, r1, r2";
  val res = m0_test_asm "subs r0, r1, #3";
  val res = m0_test_asm "subs r0, r1, r1";
  val res = m0_test_asm "subs r0, r1, #0";
  val res = m0_test_asm "subs r0, #128";
  val res = m0_test_asm "subs r0, #0";
  val res = m0_test_asm "sbcs r0, r3";
  val res = m0_test_asm "sub sp, #8";
  val res = m0_test_asm "sub sp, #16";
  val res = m0_test_asm "rsbs r1, r2, #0";
  val res = m0_test_asm "muls r1, r3";
  val res = m0_test_asm "cmp r1, r3";
  val res = m0_test_asm "cmp r1, r1";
  val res = m0_test_asm "cmp r1, #0";
  val res = m0_test_asm "cmp r1, #12";
  val res = m0_test_asm "cmn r1, r3";
  val res = m0_test_asm "cmn r1, r1";

  val res = m0_test_asm "ands r1, r1";
  val res = m0_test_asm "ands r1, r2";
  val res = m0_test_asm "eors r1, r2";
  val res = m0_test_asm "eors r1, r1";
  val res = m0_test_asm "orrs r1, r2";
  val res = m0_test_asm "orrs r1, r1";
  val res = m0_test_asm "bics r1, r2";
  val res = m0_test_asm "bics r1, r1";
  val res = m0_test_asm "mvns r1, r2";
  val res = m0_test_asm "mvns r1, r1";
  val res = m0_test_asm "tst r1, r2";
  val res = m0_test_asm "tst r1, r1";
  val res = m0_test_asm "lsls r0, r1";
  val res = m0_test_asm "lsls r0, #2";
  val res = m0_test_asm "lsls r0, #0";
  val res = m0_test_asm "lsrs r0, r1";
  val res = m0_test_asm "lsrs r0, #2";
  val res = m0_test_asm "asrs r0, r1";
  val res = m0_test_asm "asrs r0, #2";

  val res = m0_test_asm "rors r0, r1";


  val res = m0_test_asm "ldr r1, [r0]"
  val res = m0_test_asm "ldr r1, [r0, #4]"
  val res = m0_test_asm "ldr r1, [r0, #8]"
  val res = m0_test_asm "ldrh r1, [r0, #8]"
  val res = m0_test_asm "ldrh r1, [r0, #0]"
  val res = m0_test_asm "ldrh r1, [r0, #2]"
  val res = m0_test_asm "ldrb r1, [r0]"
  val res = m0_test_asm "ldrb r1, [r0, #1]"
  val res = m0_test_asm "ldrb r1, [r0, #19]"
  val res = m0_test_asm "ldr r1, [r0, r2]"
  val res = m0_test_asm "ldrh r1, [r0, r2]"
  val res = m0_test_asm "ldrsh r1, [r0, r2]"
  val res = m0_test_asm "ldrb r1, [r0, r2]"
  val res = m0_test_asm "ldrsb r1, [r0, r2]"
  val res = m0_test_asm "ldr r1, [pc, #8]"
  val res = m0_test_asm "ldr r1, [sp, #8]"
  val res = m0_test_asm "ldm r3, {r1, r2, r3}"

  val res = m0_test_asm "str r1, [r0]"
  val res = m0_test_asm "str r1, [r0, #4]"
  val res = m0_test_asm "str r1, [r0, #8]"
  val res = m0_test_asm "strh r1, [r0, #8]"
  val res = m0_test_asm "strh r1, [r0, #0]"
  val res = m0_test_asm "strh r1, [r0, #2]"
  val res = m0_test_asm "strb r1, [r0]"
  val res = m0_test_asm "strb r1, [r0, #1]"
  val res = m0_test_asm "strb r1, [r0, #19]"
  val res = m0_test_asm "str r1, [r0, r2]"
  val res = m0_test_asm "strh r1, [r0, r2]"
  val res = m0_test_asm "strb r1, [r0, r2]"
  val res = m0_test_asm "str r1, [sp, #8]"
  val res = m0_test_asm "stm r1!, {r1, r2, r3}"

  val res = m0_test_asm "push {r1, r2, r3}"
  val res = m0_test_asm "pop {r1, r2, r3}"
  val res = m0_test_asm "push {r1, r2, r3, lr}"
  val res = m0_test_asm "pop {r1, r2, r3, pc}"

  val res = m0_test_asm "bx r1"
  val res = m0_test_asm "blx r1"

  val res = m0_test_asm "sxth r1, r2"
  val res = m0_test_asm "sxtb r1, r2"
  val res = m0_test_asm "uxth r1, r2"
  val res = m0_test_asm "uxtb r1, r2"

  val res = m0_test_asm "rev r1, r2"
  val res = m0_test_asm "rev16 r1, r2"
  val res = m0_test_asm "revsh r1, r2"

  val res = m0_test_hex "3104";
  val res = m0_test_hex "b007";
  val res = m0_test_hex "4A15";
  val res = m0_test_hex "4011";
  val res = m0_test_hex "b510";
  val res = m0_test_hex "BA18";
  val res = m0_test_hex "f000f858";
  val res = m0_test_hex "BDF7";
  val res = m0_test_hex "3202";
  val res = m0_test_hex "635c";
  val res = m0_test_hex "70E8";
  val res = m0_test_hex "B285";
  val res = m0_test_hex "8028";
  val res = m0_test_hex "DFB8";
  val res = m0_test_hex "A1BC";
  val res = m0_test_hex "4182";
  val res = m0_test_hex "1000";
  val res = m0_test_hex "4088";
  val res = m0_test_hex "B5F7";
  val res = m0_test_hex "C29C";

in () end;


(******************)
(* AES_EXAMPLE M0 *)
(******************)

val instrs = [ "4b1b", "cb04", "0010", "0019", "3010", "7814",
"700c", "7854", "704c", "7894", "708c", "78d4", "70cc", "3104",
"4282", "d1f3", "4913", "2204", "468c", "4813", "2703", "7b19",
"7b5e", "7b9d", "7bdc", "423a", "d109", "4667", "5d86", "9601",
"5d46", "5d05", "5c44", "0891", "5c79", "9f01", "781f", "3201",
"4079", "7419", "404e", "7899", "745e", "404d", "78d9", "749d",
"404c", "74dc", "3304", "2a2c", "d1de", "4b0b", "4c0c", "6b5f",
"1d23", "0100", "1811", "1859", "18be", "5cf5", "46ac", "4664",
"5ccd", "4065", "54f5", "2b04", "d1f6", "d1ee", "4b07", "4807",
"1d19", "5d04", "4299", "785a", "7059", "7b59", "735a", "73d9",
"71da", "231b", "09c2", "4353", "0040", "b2c0", "4b08", "4907",
"1d18", "310b", "2200", "5c9c", "5d0c", "549c", "3204", "2a10",
"d1f9", "4298", "d1f5", "4b0d", "6b5b", "7a59", "7b5a", "7359",
"7959", "7259", "7859", "705a", "7159", "7a99", "789a", "7099",
"7b99", "729a", "799a", "7199", "79d9", "739a", "78da", "70d9",
"7ad9", "71d9", "7bd9", "73da", "72d9", "4770", "2000", "b087",
"2501", "f7ffff8c", "4b22", "6b5c", "0023", "7823", "7867", "0018",
"78a3", "9302", "78e3", "9303", "001e", "f7ffffa6", "9b01", "7020",
"9802", "4078", "f7ffff9e", "7067", "f7ffff98", "9b02", "70a0",
"f7ffff8f", "9b03", "4046", "70e6", "3404", "429c", "d1cf", "3501",
"b2ed", "f7ffff32", "2d0a", "d1bf", "f7ffff4c", "f7ffff5e",
"f7ffff29", "b007", "b5f0", "200a", "b08f", "f7ffff1f", "2409",
"f7ffff88", "f7ffff71", "f7ffff17", "4b48", "6b5d", "002b", "3310",
"930d", "782b", "9304", "786b", "9804", "9305", "78ab", "9300",
"78eb", "9301", "f7ffff57", "9006", "f7ffff54", "9007", "f7ffff51",
"9002", "9805", "f7ffff4d", "9008", "f7ffff4a", "9009", "f7ffff47",
"9003", "9800", "f7ffff43", "900a", "f7ffff40", "0007", "f7ffff3d",
"9801", "f7ffff39", "900b", "f7ffff36", "900c", "f7ffff33", "9b06",
"9a08", "407b", "9a05", "702b", "9a02", "9b08", "9a09", "9a03",
"9a0a", "9a0c", "4073", "4043", "706b", "9a04", "9b05", "4053",
"9a07", "990a", "9a0b", "4077", "4047", "4057", "9902", "9a06",
"405f", "9909", "70af", "9903", "990b", "4072", "9e0c", "4056",
"9a00", "4070", "4050", "4058", "9b0d", "70e8", "3504", "42ab",
"d181", "1e63", "b2dc", "d000", "e770", "f7fffef9", "f7fffee2",
"f7fffe88", "b00f", "bdf0", "4b05", "b510", "6b9c", "2300", "5cc1",
"5ce2", "404a", "54c2", "3301", "2b10", "d1f8", "bd10", "f7fffe2a",
"f7fffef0", "b570", "0014", "0001", "4b04", "601d", "f7fffe14",
"f7ffff2c", "bd70", "f7fffdfd", "0028", "f7ffffab", "4f0b",
"f7fffeaf", "63bc", "f7fffea0", "b5f7", "9201", "220f", "000d",
"9901", "0006", "4011", "9c08", "9100", "d003", "4a15", "6013",
"f7fffdc3", "2c00", "d001", "4b13", "639c", "0034", "9a01", "1ba3",
"429a", "d90f", "2210", "4f0d", "637c", "f7fffecb", "f7ffff68",
"3410", "63bd", "3510", "e7eb", "9b00", "2b00", "d008", "001a",
"0029", "0020", "f7fffffe", "4b03", "635c", "f7fffeb8", "bdf7",
"46c0"]

val _ = if (test_fast orelse not test_m0) then () else let
  val _ = print_with_style_ sty_HEADER "\n\n\nTESTING AES CODE - M0 LittleEnd, Main SP\n\n";
  val _ = test_m0_le_main.lift_instr_list (Arbnum.fromInt 0) (Arbnum.fromInt 0x100000) (Arbnum.fromInt 0x470) instrs
in () end


(*********************)
(* AES_EXAMPLE ARM 8 *)
(*********************)

(* Test it with the instructions from aes example *)
val instrs = [
  "D101C3FF","F9000FE0","B90017E1","F90007E2","F90003E3","B94017E0","51000400",
  "B9004FE0","F94007E0","B9400000","B9002FE0","F94007E0","B9400400","B90033E0",
  "F94007E0","B9400800","B90037E0","F94007E0","B9400C00","B9003BE0","F9400FE0",
  "B9400000","B9402FE1","4A000020","B9002FE0","F9400FE0","91001000","B9400000",
  "B94033E1","4A000020","B90033E0","F9400FE0","91002000","B9400000","B94037E1",
  "4A000020","B90037E0","F9400FE0","91003000","B9400000","B9403BE1","4A000020",
  "B9003BE0","F9400FE0","91004000","F9000FE0","140000E6","B9402FE0","53187C00",
  "B90053E0","B94033E0","53107C00","12001C00","B90057E0","B94037E0","53087C00",
  "12001C00","B9005BE0","B9403BE0","12001C00","B9005FE0","B94053E0","D37EF401",
  "90000000","91394000","8B000020","B9400000","B90063E0","B94057E0","D37EF401",
  "B0000000","91094000","8B000020","B9400000","B90067E0","B9405BE0","D37EF401",
  "B0000000","91194000","8B000020","B9400000","B9006BE0","B9405FE0","D37EF401",
  "B0000000","91294000","8B000020","B9400000","B9006FE0","B94063E1","B94067E0",
  "4A000021","B9406BE0","4A000021","B9406FE0","4A000021","F9400FE0","B9400000",
  "4A000020","B9003FE0","B94033E0","53187C00","B90053E0","B94037E0","53107C00",
  "12001C00","B90057E0","B9403BE0","53087C00","12001C00","B9005BE0","B9402FE0",
  "12001C00","B9005FE0","B94053E0","D37EF401","90000000","91394000","8B000020",
  "B9400000","B90063E0","B94057E0","D37EF401","B0000000","91094000","8B000020",
  "B9400000","B90067E0","B9405BE0","D37EF401","B0000000","91194000","8B000020",
  "B9400000","B9006BE0","B9405FE0","D37EF401","B0000000","91294000","8B000020",
  "B9400000","B9006FE0","B94063E1","B94067E0","4A000021","B9406BE0","4A000021",
  "B9406FE0","4A000021","F9400FE0","91001000","B9400000","4A000020","B90043E0",
  "B94037E0","53187C00","B90053E0","B9403BE0","53107C00","12001C00","B90057E0",
  "B9402FE0","53087C00","12001C00","B9005BE0","B94033E0","12001C00","B9005FE0",
  "B94053E0","D37EF401","90000000","91394000","8B000020","B9400000","B90063E0",
  "B94057E0","D37EF401","B0000000","91094000","8B000020","B9400000","B90067E0",
  "B9405BE0","D37EF401","B0000000","91194000","8B000020","B9400000","B9006BE0",
  "B9405FE0","D37EF401","B0000000","91294000","8B000020","B9400000","B9006FE0",
  "B94063E1","B94067E0","4A000021","B9406BE0","4A000021","B9406FE0","4A000021",
  "F9400FE0","91002000","B9400000","4A000020","B90047E0","B9403BE0","53187C00",
  "B90053E0","B9402FE0","53107C00","12001C00","B90057E0","B94033E0","53087C00",
  "12001C00","B9005BE0","B94037E0","12001C00","B9005FE0","B94053E0","D37EF401",
  "90000000","91394000","8B000020","B9400000","B90063E0","B94057E0","D37EF401",
  "B0000000","91094000","8B000020","B9400000","B90067E0","B9405BE0","D37EF401",
  "B0000000","91194000","8B000020","B9400000","B9006BE0","B9405FE0","D37EF401",
  "B0000000","91294000","8B000020","B9400000","B9006FE0","B94063E1","B94067E0",
  "4A000021","B9406BE0","4A000021","B9406FE0","4A000021","F9400FE0","91003000",
  "B9400000","4A000020","B9004BE0","B9403FE0","B9002FE0","B94043E0","B90033E0",
  "B94047E0","B90037E0","B9404BE0","B9003BE0","F9400FE0","91004000","F9000FE0",
  "B9404FE0","51000400","B9004FE0","B9404FE0","7100001F","54FFE321","B9403FE0",
  "53187C00","B90053E0","B94043E0","53107C00","12001C00","B90057E0","B94047E0",
  "53087C00","12001C00","B9005BE0","B9404BE0","12001C00","B9005FE0","B94053E0",
  "D37EF401","B0000000","91194000","8B000020","B9400000","B90063E0","B94057E0",
  "D37EF401","B0000000","91294000","8B000020","B9400000","B90067E0","B9405BE0",
  "D37EF401","90000000","91394000","8B000020","B9400000","B9006BE0","B9405FE0",
  "D37EF401","B0000000","91094000","8B000020","B9400000","B9006FE0","B94063E0",
  "12081C01","B94067E0","12101C00","4A000021","B9406BE0","12181C00","4A000021",
  "B9406FE0","12001C00","4A000021","F9400FE0","B9400000","4A000020","B9002FE0",
  "B94043E0","53187C00","B90053E0","B94047E0","53107C00","12001C00","B90057E0",
  "B9404BE0","53087C00","12001C00","B9005BE0","B9403FE0","12001C00","B9005FE0",
  "B94053E0","D37EF401","B0000000","91194000","8B000020","B9400000","B90063E0",
  "B94057E0","D37EF401","B0000000","91294000","8B000020","B9400000","B90067E0",
  "B9405BE0","D37EF401","90000000","91394000","8B000020","B9400000","B9006BE0",
  "B9405FE0","D37EF401","B0000000","91094000","8B000020","B9400000","B9006FE0",
  "B94063E0","12081C01","B94067E0","12101C00","4A000021","B9406BE0","12181C00",
  "4A000021","B9406FE0","12001C00","4A000021","F9400FE0","91001000","B9400000",
  "4A000020","B90033E0","B94047E0","53187C00","B90053E0","B9404BE0","53107C00",
  "12001C00","B90057E0","B9403FE0","53087C00","12001C00","B9005BE0","B94043E0",
  "12001C00","B9005FE0","B94053E0","D37EF401","B0000000","91194000","8B000020",
  "B9400000","B90063E0","B94057E0","D37EF401","B0000000","91294000","8B000020",
  "B9400000","B90067E0","B9405BE0","D37EF401","90000000","91394000","8B000020",
  "B9400000","B9006BE0","B9405FE0","D37EF401","B0000000","91094000","8B000020",
  "B9400000","B9006FE0","B94063E0","12081C01","B94067E0","12101C00","4A000021",
  "B9406BE0","12181C00","4A000021","B9406FE0","12001C00","4A000021","F9400FE0",
  "91002000","B9400000","4A000020","B90037E0","B9404BE0","53187C00","B90053E0",
  "B9403FE0","53107C00","12001C00","B90057E0","B94043E0","53087C00","12001C00",
  "B9005BE0","B94047E0","12001C00","B9005FE0","B94053E0","D37EF401","B0000000",
  "91194000","8B000020","B9400000","B90063E0","B94057E0","D37EF401","B0000000",
  "91294000","8B000020","B9400000","B90067E0","B9405BE0","D37EF401","90000000",
  "91394000","8B000020","B9400000","B9006BE0","B9405FE0","D37EF401","B0000000",
  "91094000","8B000020","B9400000","B9006FE0","B94063E0","12081C01","B94067E0",
  "12101C00","4A000021","B9406BE0","12181C00","4A000021","B9406FE0","12001C00",
  "4A000021","F9400FE0","91003000","B9400000","4A000020","B9003BE0","F94003E0",
  "B9402FE1","B9000001","F94003E0","91001000","B94033E1","B9000001","F94003E0",
  "91002000","B94037E1","B9000001","F94003E0","91003000","B9403BE1","B9000001",
  "D503201F","9101C3FF","D65F03C0"
];


val _ = if (test_fast orelse not test_arm8) then () else let
  val _ = print_with_style_ sty_HEADER "\n\n\nTESTING AES CODE - ARM 8\n\n";
  val _ = test_ARM8.lift_instr_list (Arbnum.fromInt 0) (Arbnum.fromInt 0x1000000) (Arbnum.fromInt 0x400570)
    instrs

  val _ = print_with_style_ sty_HEADER "\n\n\nTESTING AES CODE - ARM 8 - Whole program\n\n";

  val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;
  val (thm, errors) = test_ARM8.bir_lift_prog ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
    (Arbnum.fromInt 0x400570) instrs

(*  val _ = print_thm thm; *)
in () end;


(***************************************)
(* AES_EXAMPLE_WITH_FUNNY_INSTRUCTIONS *)
(***************************************)

val instrs = [
  "D10143FF","F9000FE0","B90017E1","F90007E2","F90003E3","B94017E0","51000400",
  "B9002FE0","F94007E0","B9400000","B9004FE0","F94007E0","B9400400","B9004BE0",
  "F94007E0","B9400800","B90047E0","F94007E0","B9400C00","B90043E0","F9400FE0",
  "B9400000","B9404FE1","4A000020","B9004FE0","F9400FE0","91001000","B9400000",
  "B9404BE1","4A000020","B9004BE0","F9400FE0","91002000","B9400000","B94047E1",
  "4A000020","B90047E0","F9400FE0","91003000","B9400000","B94043E1","4A000020",
  "B90043E0","F9400FE0","91004000","F9000FE0","140000B6","B9404FE0","53187C00",
  "53001C00","2A0003E1","90000000","9131E000","2A0103E1","B8617801","B9404BE0",
  "53107C00","53001C00","2A0003E2","90000000","9131E000","2A0203E2","91040042",
  "B8627800","4A000021","B94047E0","53087C00","53001C00","2A0003E2","90000000",
  "9131E000","2A0203E2","91080042","B8627800","4A000021","B94043E0","53001C00",
  "2A0003E2","90000000","9131E000","2A0203E2","910C0042","B8627800","4A000021",
  "F9400FE0","B9400000","4A000020","B9003FE0","B9404BE0","53187C00","53001C00",
  "2A0003E1","90000000","9131E000","2A0103E1","B8617801","B94047E0","53107C00",
  "53001C00","2A0003E2","90000000","9131E000","2A0203E2","91040042","B8627800",
  "4A000021","B94043E0","53087C00","53001C00","2A0003E2","90000000","9131E000",
  "2A0203E2","91080042","B8627800","4A000021","B9404FE0","53001C00","2A0003E2",
  "90000000","9131E000","2A0203E2","910C0042","B8627800","4A000021","F9400FE0",
  "91001000","B9400000","4A000020","B9003BE0","B94047E0","53187C00","53001C00",
  "2A0003E1","90000000","9131E000","2A0103E1","B8617801","B94043E0","53107C00",
  "53001C00","2A0003E2","90000000","9131E000","2A0203E2","91040042","B8627800",
  "4A000021","B9404FE0","53087C00","53001C00","2A0003E2","90000000","9131E000",
  "2A0203E2","91080042","B8627800","4A000021","B9404BE0","53001C00","2A0003E2",
  "90000000","9131E000","2A0203E2","910C0042","B8627800","4A000021","F9400FE0",
  "91002000","B9400000","4A000020","B90037E0","B94043E0","53187C00","53001C00",
  "2A0003E1","90000000","9131E000","2A0103E1","B8617801","B9404FE0","53107C00",
  "53001C00","2A0003E2","90000000","9131E000","2A0203E2","91040042","B8627800",
  "4A000021","B9404BE0","53087C00","53001C00","2A0003E2","90000000","9131E000",
  "2A0203E2","91080042","B8627800","4A000021","B94047E0","53001C00","2A0003E2",
  "90000000","9131E000","2A0203E2","910C0042","B8627800","4A000021","F9400FE0",
  "91003000","B9400000","4A000020","B90033E0","B9403FE0","B9004FE0","B9403BE0",
  "B9004BE0","B94037E0","B90047E0","B94033E0","B90043E0","F9400FE0","91004000",
  "F9000FE0","B9402FE0","51000400","B9002FE0","B9402FE0","6B1F001F","54FFE921",
  "B9403FE0","53187C00","53001C00","2A0003E1","90000000","9131E000","2A0103E1",
  "91080021","B8617800","12081C01","B9403BE0","53107C00","53001C00","2A0003E2",
  "90000000","9131E000","2A0203E2","910C0042","B8627800","12101C00","4A000021",
  "B94037E0","53087C00","53001C00","2A0003E2","90000000","9131E000","2A0203E2",
  "B8627800","12181C00","4A000021","B94033E0","53001C00","2A0003E2","90000000",
  "9131E000","2A0203E2","91040042","B8627800","12001C00","4A000021","F9400FE0",
  "B9400000","4A000020","B9004FE0","B9403BE0","53187C00","53001C00","2A0003E1",
  "90000000","9131E000","2A0103E1","91080021","B8617800","12081C01","B94037E0",
  "53107C00","53001C00","2A0003E2","90000000","9131E000","2A0203E2","910C0042",
  "B8627800","12101C00","4A000021","B94033E0","53087C00","53001C00","2A0003E2",
  "90000000","9131E000","2A0203E2","B8627800","12181C00","4A000021","B9403FE0",
  "53001C00","2A0003E2","90000000","9131E000","2A0203E2","91040042","B8627800",
  "12001C00","4A000021","F9400FE0","91001000","B9400000","4A000020","B9004BE0",
  "B94037E0","53187C00","53001C00","2A0003E1","90000000","9131E000","2A0103E1",
  "91080021","B8617800","12081C01","B94033E0","53107C00","53001C00","2A0003E2",
  "90000000","9131E000","2A0203E2","910C0042","B8627800","12101C00","4A000021",
  "B9403FE0","53087C00","53001C00","2A0003E2","90000000","9131E000","2A0203E2",
  "B8627800","12181C00","4A000021","B9403BE0","53001C00","2A0003E2","90000000",
  "9131E000","2A0203E2","91040042","B8627800","12001C00","4A000021","F9400FE0",
  "91002000","B9400000","4A000020","B90047E0","B94033E0","53187C00","53001C00",
  "2A0003E1","90000000","9131E000","2A0103E1","91080021","B8617800","12081C01",
  "B9403FE0","53107C00","53001C00","2A0003E2","90000000","9131E000","2A0203E2",
  "910C0042","B8627800","12101C00","4A000021","B9403BE0","53087C00","53001C00",
  "2A0003E2","90000000","9131E000","2A0203E2","B8627800","12181C00","4A000021",
  "B94037E0","53001C00","2A0003E2","90000000","9131E000","2A0203E2","91040042",
  "B8627800","12001C00","4A000021","F9400FE0","91003000","B9400000","4A000020",
  "B90043E0","F94003E0","B9404FE1","B9000001","F94003E0","91001000","B9404BE1",
  "B9000001","F94003E0","91002000","B94047E1","B9000001","F94003E0","91003000",
  "B94043E1","B9000001","910143FF","D65F03C0"
];



val _ = if (test_fast orelse not test_arm8) then () else let
  val _ = print_with_style_ sty_HEADER "\n\n\nTESTING AES CODE WITH FUNNY INSTRUCTIONS - ARM 8\n\n";
  val _ = test_ARM8.lift_instr_list (Arbnum.fromInt 0) (Arbnum.fromInt 0x1000000) (Arbnum.fromInt 0x400570)
    instrs
in () end



(**********)
(* BIGNUM *)
(**********)

(* precompiled bignum lib as binary blob with unspecified location *)

val instrs_bignum_from_bytes = [
  "A9BC7BFD","910003FD","F9000FA0","B90017A1","B94017A0","11000400","531F7C01",
  "0B000020","13017C00","B9003BA0","B9403BA0","94000000","F9001BA0","52800020",
  "B9003FA0","14000009","B9803FA0","D37FF800","F9401BA1","8B000020","7900001F",
  "B9403FA0","11000400","B9003FA0","B9403FA1","B9403BA0","6B00003F","54FFFEAD",
  "B94017A0","B9003FA0","14000036","F9400FA0","91000401","F9000FA1","39400000",
  "3900BFA0","B9403FA0","12000000","6B1F001F","54000320","B9403FA0","531F7C01",
  "0B000020","13017C00","11000401","93407C21","D37FF821","F9401BA2","8B010041",
  "11000400","93407C00","D37FF800","F9401BA2","8B000040","79400000","13003C02",
  "3940BFA0","53185C00","13003C00","2A000040","13003C00","53003C00","79000020",
  "14000015","B9403FA0","531F7C01","0B000020","13017C00","11000401","93407C21",
  "D37FF821","F9401BA2","8B010041","11000400","93407C00","D37FF800","F9401BA2",
  "8B000040","79400002","3940BFA0","53003C00","2A000040","53003C00","79000020",
  "B9403FA0","51000401","B9003FA1","6B1F001F","54FFF8E1","14000007","F9401BA0",
  "79400000","51000400","53003C01","F9401BA0","79000001","F9401BA0","79400000",
  "7100041F","54000149","F9401BA0","79400000","53003C00","D37FF800","F9401BA1",
  "8B000020","79400000","6B1F001F","54FFFDC0","F9401BA0","A8C47BFD","D65F03C0"
];
val instrs_bytes_from_bignum = [
  "A9BD7BFD","910003FD","F9000FA0","F9000BA1","F9400FA0","79400000","790057A0",
  "794057A0","D37FF800","F9400FA1","8B000020","79400000","7103FC1F","54000128",
  "794057A0","531F7800","53003C00","51000400","53003C01","F9400BA0","79000001",
  "14000006","794057A0","531F7800","53003C01","F9400BA0","79000001","F9400BA0",
  "79400000","53003C00","D2800201","94000000","F90013A0","52800020","79005FA0",
  "794057A0","79005BA0","14000037","79405FA0","7100041F","540002E1","794057A0",
  "D37FF800","F9400FA1","8B000020","79400000","7103FC1F","54000208","79405FA0",
  "D1000400","F94013A1","8B000020","79405BA1","D37FF821","F9400FA2","8B010041",
  "79400021","53001C21","39000001","79405FA0","51000400","79005FA0","14000018",
  "79405FA0","D1000400","F94013A1","8B000020","79405BA1","D37FF821","F9400FA2",
  "8B010041","79400021","53087C21","53003C21","53001C21","39000001","79405FA0",
  "F94013A1","8B000020","79405BA1","D37FF821","F9400FA2","8B010041","79400021",
  "53001C21","39000001","79405FA0","11000800","79005FA0","79405BA0","51000400",
  "79005BA0","F9400BA0","79400000","79405FA1","6B00003F","54FFF8C3","F94013A0",
  "A8C37BFD","D65F03C0"
];
val instrs_freebn = [
  "A9BE7BFD","910003FD","F9000FA0","F9400FA0","79400000","11000400","93407C00",
  "D37FF800","AA0003E2","52800001","F9400FA0","94000000","F9400FA0","94000000",
  "A8C27BFD","D65F03C0"
];
val instrs_internal_add_shifted = [
  "D100C3FF","F90007E0","B90007E1","B90003E2","B94003E0","11003C01","6B1F001F",
  "1A80B020","13047C00","11000400","B9002FE0","B94003E1","131F7C20","531C7C00",
  "0B000021","12000C21","4B000020","B9001FE0","B9401FE0","B94007E1","1AC02020",
  "2A0003E0","F90013E0","14000017","B9802FE0","D37FF800","F94007E1","8B000020",
  "79400000","53003C00","F94013E1","8B000020","F90013E0","B9802FE0","D37FF800",
  "F94007E1","8B000020","F94013E1","53003C21","79000001","F94013E0","D350FC00",
  "F90013E0","B9402FE0","11000400","B9002FE0","F94013E0","EB1F001F","54FFFD01",
  "9100C3FF","D65F03C0"
];
val instrs_internal_mod = [
  "A9B97BFD","910003FD","F9001FA0","B90037A1","F90017A2","B90033A3","F90013A4",
  "B9001FA5","F94017A0","79400000","790097A0","B94033A0","7100041F","540000AD",
  "F94017A0","79400400","7900DFA0","14000002","7900DFBF","B90067BF","140000DE",
  "B94067A0","6B1F001F","54000061","B9006BBF","1400000E","B98067A0","D37FF800",
  "D1000800","F9401FA1","8B000020","79400000","B9006BA0","B98067A0","D37FF800",
  "D1000800","F9401FA1","8B000020","7900001F","B94037A0","51000401","B94067A0",
  "6B00003F","54000061","B9004FBF","14000008","B98067A0","91000400","D37FF800",
  "F9401FA1","8B000020","79400000","B9004FA0","B9406BA0","D370BC01","B98067A0",
  "D37FF800","F9401FA2","8B000040","79400000","53003C00","8B000020","F9002FA0",
  "794097A0","F9402FA1","9AC00820","B90057A0","794097A1","F9402FA0","9AC10802",
  "9B017C41","CB010000","B90047A0","7940DFA1","B94057A0","9B007C20","F9002FA0",
  "B94047A0","D370BC01","B9404FA0","8B000021","F9402FA0","EB00003F","54000362",
  "B94057A0","51000400","B90057A0","7940DFA0","F9402FA1","CB000020","F9002FA0",
  "794097A1","B94047A0","0B000020","12003C00","B90047A0","794097A1","B94047A0",
  "6B00003F","54000168","B94047A0","D370BC01","B9404FA0","8B000021","F9402FA0",
  "EB00003F","54000082","B94057A0","51000400","B90057A0","B90053BF","B94033A0",
  "51000400","B90063A0","14000037","B94057A1","B98063A0","D37FF800","F94017A2",
  "8B000040","79400000","53003C00","9B007C20","F9002FA0","B94053A0","F9402FA1",
  "8B000020","F9002FA0","F9402FA0","D350FC00","B90053A0","F9402FA0","53003C01",
  "B94067A2","B94063A0","0B000040","93407C00","D37FF800","F9401FA2","8B000040",
  "79400000","6B00003F","54000089","B94053A0","11000400","B90053A0","B94067A1",
  "B94063A0","0B000020","93407C00","D37FF800","F9401FA1","8B000020","B94067A2",
  "B94063A1","0B010041","93407C21","D37FF821","F9401FA2","8B010041","79400022",
  "F9402FA1","53003C21","4B010041","53003C21","79000001","B94063A0","51000400",
  "B90063A0","B94063A0","6B1F001F","54FFF90A","B94053A1","B9406BA0","6B00003F",
  "54000620","F9002FBF","B94033A0","51000400","B90063A0","14000026","B98063A0",
  "D37FF800","F94017A1","8B000020","79400000","53003C00","F9402FA1","8B000020",
  "F9002FA0","B94067A1","B94063A0","0B000020","93407C00","D37FF800","F9401FA1",
  "8B000020","79400000","53003C00","F9402FA1","8B000020","F9002FA0","B94067A1",
  "B94063A0","0B000020","93407C00","D37FF800","F9401FA1","8B000020","F9402FA1",
  "53003C21","79000001","F9402FA0","D350FC00","F9002FA0","B94063A0","51000400",
  "B90063A0","B94063A0","6B1F001F","54FFFB2A","B94057A0","51000400","B90057A0",
  "F94013A0","EB1F001F","540001A0","B94037A1","B94033A0","4B000021","B94067A0",
  "4B000020","531C6C01","B9401FA0","0B000020","2A0003E2","B94057A1","F94013A0",
  "94000000","B94067A0","11000400","B90067A0","B94037A1","B94033A0","4B000021",
  "B94067A0","6B00003F","54FFE3CA","A8C77BFD","D65F03C0"
];
val instrs_internal_mul = [
  "D10103FF","F9000FE0","F9000BE1","F90007E2","B90007E3","B9003BFF","14000009",
  "B9803BE0","D37FF800","F94007E1","8B000020","7900001F","B9403BE0","11000400",
  "B9003BE0","B94007E0","531F7801","B9403BE0","6B00003F","54FFFE8C","B94007E0",
  "51000400","B9003FE0","14000043","B9803FE0","D37FF800","F9400FE1","8B000020",
  "79400000","53003C00","F90017E0","F9001BFF","B94007E0","51000400","B9003BE0",
  "1400002A","B9803BE0","D37FF800","F9400BE1","8B000020","79400000","53003C01",
  "F94017E0","9B007C20","F9401BE1","8B000020","F9001BE0","B9403FE1","B9403BE0",
  "0B000020","93407C00","91000400","D37FF800","F94007E1","8B000020","79400000",
  "53003C00","F9401BE1","8B000020","F9001BE0","B9403FE1","B9403BE0","0B000020",
  "93407C00","91000400","D37FF800","F94007E1","8B000020","F9401BE1","53003C21",
  "79000001","F9401BE0","D350FC00","F9001BE0","B9403BE0","51000400","B9003BE0",
  "B9403BE0","6B1F001F","54FFFAAA","B9803FE0","D37FF800","F94007E1","8B000020",
  "F9401BE1","53003C21","79000001","B9403FE0","51000400","B9003FE0","B9403FE0",
  "6B1F001F","54FFF78A","910103FF","D65F03C0"
];
val instrs_newbn = [
  "A9BD7BFD","910003FD","B9001FA0","B9401FA0","11000400","93407C00","D37FF800",
  "D2800201","94000000","F90017A0","F94017A0","EB1F001F","54000061","D2800000",
  "1400000E","B9401FA0","11000400","93407C00","D37FF800","AA0003E2","52800001",
  "F94017A0","94000000","B9401FA0","53003C01","F94017A0","79000001","F94017A0",
  "A8C37BFD","D65F03C0"
];

val instrs_bignumlib = instrs_bignum_from_bytes @
             instrs_bytes_from_bignum @
             instrs_freebn @
             instrs_internal_add_shifted @
             instrs_internal_mod @
             instrs_internal_mul @
             instrs_newbn;

val _ = if (test_fast orelse not test_arm8) then () else let
  val _ = print_with_style_ sty_HEADER "\n\n\nTESTING BIGNUM LIB CODE - ARM 8\n\n";
  val _ = test_ARM8.lift_instr_list (Arbnum.fromInt 0) (Arbnum.fromInt 0x1000000) (Arbnum.fromInt 0x400570)
    instrs_bignumlib
in () end;



val _ = if (not test_arm8) then () else let
  val disassemble_fun = arm8AssemblerLib.arm8_disassemble;
  fun asm_of_hex_code_fun code = hd (disassemble_fun [QUOTE code]);
  fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm);

  val test_insts_movk_raw = ["movk w3, #0x5, lsl #0", "movk w3, #0x5, lsl #16",
                             "movk x3, #0x5, lsl #0", "movk x3, #0x5, lsl #16",
                             "movk x3, #0x5, lsl #32", "movk x3, #0x5, lsl #48",
                             "strh w1, [x19, x0]", "ldrh w1, [x19, x0]"];

  val test_insts_misc_raw = ["negs xzr, x0, lsr #1", "negs wzr, w1, lsr #4",
                             "negs w0, w19"        , "negs xzr, x3, lsl #7",
                             "cmp w4, w3, uxtb"    , "cmp w26, w0, uxth",
                             "sbc x0, x0, xzr"     , "sbcs x0, x0, xzr"];

  val test_insts_misc_hex = ["0B200180" (* "add w0, w12, w0, uxtb" *),
                             "0B202034" (* "add w20, w1, w0, uxth" *)
                            ];

  val test_insts_raw = test_insts_movk_raw @ test_insts_misc_raw;

  val test_insts = List.map (fn x => [(QUOTE:string -> string frag) x]) test_insts_raw;
  val test_insts_hex = (List.map (hex_code_of_asm) test_insts) @ test_insts_misc_hex;

  val _ = print_with_style_ sty_HEADER "\n\n\nTESTING VARIOUS INSTRUCTIONS - ARM 8\n\n";
  val _ = test_ARM8.lift_instr_list (Arbnum.fromInt 0) (Arbnum.fromInt 0x1000000) (Arbnum.fromInt 0x400570)
    test_insts_hex
in () end;




(*****************)
(* final summary *)
(*****************)

val arm8_expected_failed_hexcodes:string list =
[
   "9BC37C41" (* umulh x1, x2, x3 lifting of ``Imm64 ((127 >< 64) (w2w (ms.REG 3w) * w2w (ms.REG 2w)))`` failed *),
   "9B437C41" (* smulh x1, x2, x3 lifting of ``Imm64 ((127 >< 64) (sw2sw (ms.REG 3w) * sw2sw (ms.REG 2w)))`` failed *)
];

val _ = if (not test_arm8) then () else let
  val _ = test_ARM8.final_results "ARM 8" arm8_expected_failed_hexcodes;
in () end

val m0_expected_failed_hexcodes:string list =
[
   "A1BC" (* manual decoding: ADR r1, PC, #0xBC *),
   "DFB8" (* manual decoding: SVC #0xB8 *)
];


val _ = if (not test_m0) then () else let
  val _ = test_m0_le_proc.final_results "M0 LittleEnd, Process SP" m0_expected_failed_hexcodes;
  val _ = test_m0_be_proc.final_results "M0 BigEnd, Process SP" m0_expected_failed_hexcodes;
  val _ = test_m0_le_main.final_results "M0 LittleEnd, Main SP" m0_expected_failed_hexcodes;
  val _ = test_m0_be_main.final_results "M0 BigEnd, Main SP" m0_expected_failed_hexcodes;
in () end;

val _ = test_ARM8.close_log();

val _ = test_m0_le_proc.close_log();
val _ = test_m0_be_proc.close_log();
val _ = test_m0_le_main.close_log();
val _ = test_m0_be_main.close_log();

val _ = test_m0_mod_le_proc.close_log();
val _ = test_m0_mod_be_proc.close_log();
val _ = test_m0_mod_le_main.close_log();
val _ = test_m0_mod_be_main.close_log();

(* check whether the result is different *)
local
  val diff_cmd = "git diff --exit-code ";
in
  fun check_logs []     = ()
    | check_logs (h::t) = 
        if OS.Process.isSuccess (OS.Process.system (diff_cmd^h))
        then ()
        else
          raise Fail ("selftest_arm.sml::Output in "^h^" has diverged")
end;

val _ = check_logs ["selftest_arm8.log",
                    "selftest_m0_le_proc.log",
                    "selftest_m0_be_proc.log",
                    "selftest_m0_le_main.log",
                    "selftest_m0_be_main.log",
                    "selftest_m0_mod_le_proc.log",
                    "selftest_m0_mod_be_proc.log",
                    "selftest_m0_mod_le_main.log",
                    "selftest_m0_mod_be_main.log"]
; 
