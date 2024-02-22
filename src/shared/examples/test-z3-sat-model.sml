open HolKernel Parse boolLib bossLib;

open finite_mapTheory;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "../Z3_SAT_modelLib"; (* ../ *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(*
val _ = Globals.linewidth := 100;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolBA_HolSmtLib" 4;
val _ = Globals.show_assums := true;
val _ = Globals.show_types := true;
*)

(* Prints a model, one variable per line. *)
fun print_model model = List.foldl
  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
  () (rev model);

(* Builds a theorem from a model and a term. *)
fun produce_sat_thm term model =
  let
    val eq_list = List.map (fn (name, tm) => Term [QUOTE name, QUOTE " = ", ANTIQUOTE tm]) model;
    val conj_assign_tm = list_mk_conj eq_list;
    val imp_tm = mk_imp (conj_assign_tm, term);
  in
    EVAL imp_tm
  end;
fun produce_sat_thm term model =
  let
    val eq_list = List.map (fn (name, tm) => Term [QUOTE name, QUOTE " = ", ANTIQUOTE tm]) model;
    val conj_assign_tm = list_mk_conj eq_list;
    val imp_tm = mk_imp (conj_assign_tm, term);
  in
    prove (imp_tm, SIMP_TAC std_ss [] >> EVAL_TAC)
  end;

val model_eq = list_eq (pair_eq (fn (a:string) => fn (b:string) => a=b) identical);


(* ============================================================= *)

(* Get a SAT model using Z3 (this function assumes that the given term is SAT) *)
val term = ``(z + y = 2 * x) /\ ((x * x + y - 25) = z:int)``;
(* (FUN_MAP2 (K 0w) (UNIV)) *)
(*
val term = ``(m2 = FUPDATE (m1: word32 |-> word8) (3w, 2w)) /\ (FAPPLY m2 3w = 2w)``;
*)
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL term;
val _ = (print "SAT model:\n"; print_model model(*; print "\n"*));
val sat_thm = produce_sat_thm term model;
val _ = (print "SAT thm:\n"; Hol_pp.print_thm sat_thm; print "\n");

val model_expected = [("z", “19:int”), ("y", “(-5):int”), ("x", “7:int”)];

val _ = if model_eq model model_expected then () else
        raise Fail "model for simple int constraint not as expected.";


(* ============================================================= *)

val term = “mem123 <> (FUN_FMAP (K (144w :word8) :word64 -> word8) 𝕌(:word64))”;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL term;
val model_expected = [("mem123", “FUN_FMAP ((K 144w) :word64 -> word8) 𝕌(:word64) |+ (0w,111w)”)];

val _ = if model_eq model model_expected then () else
        raise Fail "model for memory inequality not as expected.";


(* ============================================================= *)

val term = “mem123 <> (FUN_FMAP ((K 144w) :word64 -> word8) 𝕌(:word64) |+ (0w,111w))”;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL term;
val model_expected = [("mem123", “FUN_FMAP ((K 144w) :word64 -> word8) 𝕌(:word64) |+ (0w,144w)”)];

val _ = if model_eq model model_expected then () else
        raise Fail "model for memory inequality not as expected.";
