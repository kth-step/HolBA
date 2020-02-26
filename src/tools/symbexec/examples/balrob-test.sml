open HolKernel Parse

open binariesTheory;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


val _ = (print_term o concl) balrob_program_THM;

