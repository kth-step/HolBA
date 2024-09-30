open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open aes_symb_execTheory;

(* for now we just have a leightweight check; this is to include aes into the test *)
val _ = print "checking aes_symb_analysis_thm:\n";

val _ = if term_size (concl aes_symb_analysis_thm) = 23403 then () else
        raise Fail "term size of aes symbolic execution theorem is not as expected";

val triple_tm = ((snd o dest_comb o concl) aes_symb_analysis_thm);
val [init_st_tm, prog_frag_L_tm, final_sts_tm] = pairSyntax.strip_pair triple_tm;
val final_sts_birs_tm = final_sts_tm;

val _ = if (length o pred_setSyntax.strip_set) final_sts_birs_tm = 1 then () else
        raise Fail "number of final states is not as expected";

val _ = print "ok!\n";
