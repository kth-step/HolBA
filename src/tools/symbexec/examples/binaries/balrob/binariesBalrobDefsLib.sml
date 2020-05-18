structure binariesBalrobDefsLib =
struct


val symbs_sec_text = [
    "imu_handler_pid_entry",
    "motor_set_f",
    "motor_set",
    "motor_set_l",
    "motor_set_r",
    "motor_prep_input",
    "motor_prep_input_ct",
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
val prog_range       = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x8000));

val configs          = [("balrob",
                           ("balrob.elf.da", "balrob/balrob.elf.da.plus", "balrob/balrob.elf.mem"),
                           "balrob_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003564),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
                        ),
                        ("balrob_opt",
                           ("balrob_opt.elf.da", "balrob/balrob_opt.elf.da.plus", "balrob/balrob_opt.elf.mem"),
                           "balrob_opt_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003414),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x310)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
                        ),
                        ("balrob_ct",
                           ("balrob_ct.elf.da", "balrob/balrob_ct.elf.da.plus", "balrob/balrob_ct.elf.mem"),
                           "balrob_ct_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003564),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
                        )];

val symb_filter_lift = fn secname =>
  case secname of
      ".text" => (fn symbname => List.exists (fn x => x = symbname) symbs_sec_text)
    | _       => (K false);


end (* struct *)
