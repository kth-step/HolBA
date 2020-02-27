open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val symbs_sec_text = [
    "imu_handler",
    "imu_handler_pid_entry",
    "motor_set_f",
    "motor_set",
    "motor_set_l",
    "motor_set_r",
    "motor_prep_input",
    "timer_read",
    "atan2f_own",
    "abs_own",
    "pid_msg_write",
    "timer_start",
    "__aeabi_f2iz",
    "__aeabi_fmul",
    "__aeabi_i2f",
    "__aeabi_fadd",
    "__aeabi_fcmplt",
    "__aeabi_fsub",
    "__aeabi_fdiv",
    "__lesf2",
    "__clzsi2",
    "__gesf2"
  ];

val _ = new_theory "binaries";

val arch_str    = "m0";
val da_file     = "balrob.elf.da";
val prog_range  = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x8000));
val thm_name    = "balrob_program_THM";
val symb_filter = fn secname =>
  case secname of
      ".text" => (fn symbname => List.exists (fn x => x = symbname) symbs_sec_text)
    | _       => (K false);

val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ da_file ^ " (" ^ arch_str ^ ")\n");

val (region_map, sections) = read_disassembly_file_regions_filter symb_filter da_file;

val (thm, errors) = bmil_m0_mod_LittleEnd_Process.bir_lift_prog_gen prog_range sections;

val _ = save_thm (thm_name, thm);

val _ = export_theory();
