open HolKernel Parse

open binariesLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")\n");

val _ = print_option (print o Int.toString)
                     (read_byte_from_init_mem_ (Arbnum.fromInt 0x10000002));

val _ = print_option print_term
                     (get_block_byAddr_ (Arbnum.fromInt 440));

val _ = print_option (print o Arbnum.toString)
                     (find_label_addr_ "imu_handler");

val _ = print_option (print)
                     (find_label_by_addr_ (Arbnum.fromInt 0x10000002));



