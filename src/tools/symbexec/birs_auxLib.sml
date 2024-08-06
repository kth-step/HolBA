structure birs_auxLib =
struct

local

open HolKernel Parse boolLib bossLib;

open birs_auxTheory;

  (* error handling *)
  val libname = "bir_auxLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in


(* TODO: this is stolen from exec tool *)
  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;
(* TODO: this is stolen from exec tool, and then modified for extraction of the expressions *)
  fun GEN_match_extract is_tm_fun acc [] = acc
    | GEN_match_extract is_tm_fun acc (tm::l) =
    if is_tm_fun tm then
      GEN_match_extract is_tm_fun (tm::acc) l
    else if is_comb tm then
      let
        val (rator_tm, rand_tm) = dest_comb tm;
      in
        GEN_match_extract is_tm_fun acc (rand_tm::rator_tm::l)
      end
    else if is_abs tm then
        GEN_match_extract is_tm_fun acc (((snd o dest_abs) tm)::l)
    else
      GEN_match_extract is_tm_fun acc l (* raise ERR "GEN_match_extract" "unknown" *)
    ;


fun gen_prog_vars_set_thm bir_prog_def =
 let
  val prog_tm = (fst o dest_eq o concl) bir_prog_def;
 in
  (SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_prog_def] THENC
   EVAL)
  ``bir_vars_of_program ^prog_tm``
 end;

fun gen_prog_vars_list_def_thm progname prog_vars_set_thm =
 let
  val prog_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) prog_vars_set_thm;
  (*
  List.filter ((fn s => s <> "MEM8") o (stringSyntax.fromHOLstring o fst o bir_envSyntax.dest_BVar)) prog_vars;
  *)
  val prog_vars_list_tm = listSyntax.mk_list (prog_vars, (type_of o hd) prog_vars);
  val prog_vars_list_var = mk_var(progname ^ "_prog_vars_list", type_of prog_vars_list_tm);
  val prog_vars_list_def = Define `^prog_vars_list_var = ^prog_vars_list_tm`;
  val prog_vars_thm_goal = ``set ^((fst o dest_eq o concl) prog_vars_list_def) = ^((fst o dest_eq o concl) prog_vars_set_thm)``;
 in
  prove(prog_vars_thm_goal,
    REWRITE_TAC [prog_vars_set_thm, prog_vars_list_def] >>
    SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
     [] >>
    EVAL_TAC)
 end;

fun gen_prog_vars_defthms progname bir_prog_def =
 let
  val prog_vars_set_thm_name = progname ^ "_prog_vars_set_thm";
  val prog_vars_set_thm = save_thm (prog_vars_set_thm_name, gen_prog_vars_set_thm bir_prog_def);
  val prog_vars_thm_name = progname ^ "_prog_vars_thm";
  val prog_vars_thm = save_thm (prog_vars_thm_name, gen_prog_vars_list_def_thm progname prog_vars_set_thm);
 in
  ()
 end;

fun gen_birenvtyl_def progname =
 let
  val prog_vars_list_tm = Parse.Term [QUOTE (progname ^ "_prog_vars_list")];
  val birenvtyl_tm = ``MAP BVarToPair ^prog_vars_list_tm``;
  val birenvtyl_var = mk_var(progname ^ "_birenvtyl", type_of birenvtyl_tm);
  val _ = Define `^birenvtyl_var = ^birenvtyl_tm`;
 in
  ()
 end;

(* val gen_prog_vars_birenvtyl_defthms : string -> thm -> unit; *)

fun gen_prog_vars_birenvtyl_defthms progname bir_prog_def =
 (gen_prog_vars_defthms progname bir_prog_def;
  gen_birenvtyl_def progname);


end (* local *)

end (* struct *)
