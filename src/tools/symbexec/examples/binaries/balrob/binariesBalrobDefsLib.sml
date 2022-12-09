structure binariesBalrobDefsLib =
struct


val arch_str         = "m0";

val configs          = [("balrob",
                           ("balrob.elf.da", "balrob/balrob.elf.da.plus", "balrob/balrob.elf.mem"),
                           "balrob_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x10001c54),
                            (Arbnum.fromInt 0x10001c54, Arbnum.fromInt (0x0000001c + 0x338 - 0x80 - 0x10)),
                            (Arbnum.fromInt (0x10001ff0 - 0x48 - 0x80 - 0x10), Arbnum.fromInt (0x00000010 + 0x48 + 0x80 + 0x10))),
((Arbnum.fromInt 0), (Arbnum.fromInt 0x10001c54)),
[
    "imu_handler_pid_entry",
    "atan2f_own",
    "abs_own",
    "__aeabi_f2iz",
    "__aeabi_fmul",
    "__aeabi_i2f",
    "__aeabi_fadd",
    "__aeabi_fcmplt",
    "__aeabi_fsub",
    "__aeabi_fdiv",
    "__lesf2",
    "__clzsi2"
  ]
                        ),
                        ("balrob_otherbenchs",
                           ("balrob_otherbenchs.elf.da", "balrob/balrob_otherbenchs.elf.da.plus", "balrob/balrob_otherbenchs.elf.mem"),
                           "balrob_otherbenchs_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x10001574),
                            (Arbnum.fromInt 0x10001574, Arbnum.fromInt (0x0000001c + 0x338)),
                            (Arbnum.fromInt (0x10001574 + 0x1c + 0x338), Arbnum.fromInt (0x10002000 - (0x10001574 + 0x1c + 0x338)))),
((Arbnum.fromInt 0), (Arbnum.fromInt 0x10001574)),
[
    "_mymodexp",
    "l6",
    "l10",
    "l12",
    "__aeabi_uidivmod",
    "__udivsi3",
    "__aeabi_idiv0"
]
                        )];


end (* struct *)
