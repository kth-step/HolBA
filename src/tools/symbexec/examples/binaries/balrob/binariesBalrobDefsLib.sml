structure binariesBalrobDefsLib =
struct


val symbs_sec_text = [
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
    "__aeabi_f2iz",
    "__aeabi_fmul",
    "__aeabi_i2f",
    "__aeabi_fadd",
    "__aeabi_fcmplt",
    "__aeabi_fsub",
    "__aeabi_fdiv",
    "__lesf2",
    "__clzsi2"
  ];

val arch_str         = "m0";
val da_file_lift     = "balrob.elf.da";
val prog_range       = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x8000));
val thm_name         = "balrob_program_THM";
val symb_filter_lift = fn secname =>
  case secname of
      ".text" => (fn symbname => List.exists (fn x => x = symbname) symbs_sec_text)
    | _       => (K false);


end (* struct *)
