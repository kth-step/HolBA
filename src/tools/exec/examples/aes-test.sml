open HolKernel Parse;

open bir_inst_liftingTheory;
open bir_program_valid_stateTheory;


open bir_execLib;

open aesBinaryTheory;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;



val _ = print "loading...\n";

val name = "lifted_aes_enc_part";

(* load lifter theorem *)
val liftertheorem = aes_arm8_program_THM;
val prog_l = ((dest_BirProgram o snd o dest_comb o concl) liftertheorem);

(* define a constant for the program, obtain validprog theorem *)
val prog_l_def = Define [QUOTE (name ^ "_prog_l = "), ANTIQUOTE prog_l];
val prog_const = (mk_BirProgram o fst o dest_eq o concl) prog_l_def;
val prog = prog_const;

val liftertheorem = REWRITE_RULE [GSYM prog_l_def] liftertheorem;

val validprog_thm = prove(``
  bir_is_valid_program ^prog_const
``,
  REWRITE_TAC [bir_is_valid_program_def] >>
  STRIP_TAC >- (
    ASM_REWRITE_TAC [REWRITE_RULE [bir_is_lifted_prog_def] liftertheorem]
  ) >>
  SIMP_TAC list_ss [bir_program_is_empty_def, prog_l_def]
);

val validprog_o = SOME validprog_thm;
val welltypedprog_o = NONE;

(* set the number of steps *)
val n_max = 50;

val _ = print "ok\n"



(* run the execution *)
val _ = bir_exec_prog_print name prog_const n_max validprog_o welltypedprog_o;


