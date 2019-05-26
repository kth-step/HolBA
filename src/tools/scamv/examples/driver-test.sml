open bir_scamv_driverLib;
open bir_rel_synthLib;

(* scamv_test_main "asm/branch.s"; *)
scamv_test_asmf "asm/branch.s";

(*
val (_,sections) = prog_gen_from_file "asm/branch.s";
val lifted_prog = lift_program_from_sections sections;
val lifted_prog_w_obs =
    bir_arm8_cache_line_model.add_obs lifted_prog;
(*print_term(lifted_prog_w_obs);*)
val (paths, all_exps) = symb_exec_phase lifted_prog_w_obs;
(*List.map (print_term o fst) paths; *)

val relation = mkRel paths;
(*print_term(relation);*)

val word_relation = make_word_relation relation all_exps;
print_term (word_relation);

val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
*)

(*TODO try to make 'complement' relation that doesn't include the invalid paths,
  since the paths will be selected by the driver anyway
 *)
