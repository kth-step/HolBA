open HolKernel Parse

open binariesLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


val _ = case (read_byte_from_init_mem (Arbnum.fromInt 0x10000002)) of
	    NONE   => print "NONE\n"
	  | SOME x => print ("SOME " ^ (Int.toString x) ^ "\n");
