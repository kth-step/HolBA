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

local
 fun map_in_model m s =
  case List.find (fn (x,_) => x = s) m of
     NONE => raise Fail "could not find variable in model"
   | SOME x => snd x;

 val finite_word32_thm = prove(``FINITE (UNIV:word32->bool)``, cheat);
 val fmap_rewr_thm = MATCH_MP finite_mapTheory.FUN_FMAP_DEF finite_word32_thm;
 val word32_conr_thm = prove(``!x. (x :word32) IN (UNIV:word32->bool)``, cheat);
 val fmap_rewr_thms = [finite_mapTheory.FUN_FMAP_DEF, finite_word32_thm, word32_conr_thm];
in
 fun check_model query model =
  let
     val fvs = free_vars query;
      val fv_insts = foldl (fn (x, acc) => ((x, (map_in_model model o fst o dest_var) x)::acc)) [] fvs;
      val s = foldl (fn ((x,y),acc) => ((x |-> y)::acc)) [] fv_insts;
      val inst_tm = subst s query;
      val eval_thm = (EVAL THENC SIMP_CONV std_ss fmap_rewr_thms THENC EVAL) inst_tm;
      val res = identical T ((snd o dest_eq o concl) eval_thm);
  in
    (res, eval_thm)
  end;
end;

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

val (res, _) = check_model term model;

val _ = if res then () else
        raise Fail "model for simple int constraint not as expected.";


(* ============================================================= *)

(* TODO: too complicated/too much time to port these two now *)
(*
val term = “mem123 <> (FUN_FMAP (K (144w :word8) :word64 -> word8) 𝕌(:word64))”;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL term;
val (res, _) = check_model term model;

val _ = if res then () else
        raise Fail "model for memory inequality not as expected.";

(* ============================================================= *)

val term = “mem123 <> (FUN_FMAP ((K 144w) :word64 -> word8) 𝕌(:word64) |+ (0w,111w))”;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL term;
val (res, _) = check_model term model;

val _ = if res then () else
        raise Fail "model for memory inequality not as expected.";
*)
