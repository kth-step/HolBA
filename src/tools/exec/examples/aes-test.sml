open HolKernel Parse;

open bir_execLib;

open aesBinaryTheory;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;



val _ = print "loading...";

val name = "lifted_aes_enc_part";


val liftertheorem = aes_arm8_program_THM;
val prog = ((snd o dest_comb o concl) liftertheorem);


val n_max = 50;

val _ = print "ok\n"


val _ = bir_exec_prog_output name prog n_max;


