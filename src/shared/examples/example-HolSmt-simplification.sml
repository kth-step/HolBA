open HolKernel Parse boolLib bossLib;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = wordsLib.add_word_cast_printer ();
val _ = Globals.show_types := true;

(*
(* for debugging the z3 input and output (keep the temporary files) *)
val _ = Library.trace := 5;
*)

val mem1_var = mk_var ("MEM", “:word64 |-> word8”);
val mem2_var = mk_var ("MEM", “:word64 |-> word8”);

val term = “
(w2w (w2w (^mem1_var ' R1) :word64):word1)
=
w2w (^mem2_var ' R2)”;

(*
val term = “
((((if
      (0x80100000w :word64) ≤₊
      (R26 :word64) +
      (w2w
         (w2w
            (w2w
               (((^mem1_var :word64 |-> word8) '
                 ((R28 :word64) + (12w :word64) + (0w :word64)))
                  :word8) :word64) :word32) :word64) <<~ (3w :word64) ∧
      R26 +
      (w2w
         (w2w
            (w2w ((^mem1_var ' (R28 + (12w :word64) + (0w :word64))) :word8) :
             word64) :word32) :word64) <<~ (3w :word64) <₊ (0x8013FF80w
        :word64)
    then
      (1w :word1)
    else (0w :word1)) &&
   (if
      R26 +
      (w2w
         (w2w
            (w2w ((^mem1_var ' (R28 + (12w :word64) + (0w :word64))) :word8) :
             word64) :word32) :word64) <<~ (3w :word64) && (7w :word64) =
      (0w
        :word64)
    then
      (1w :word1)
    else (0w :word1)) &&
   (if (0x80100000w :word64) ≤₊ R28 ∧ R28 <₊ (0x8013FF80w :word64) then
      (1w :word1)
    else (0w :word1)) && (1w :word1)) &&
  ((if
      (0x80100000w :word64) ≤₊
      (R26' :word64) +
      (w2w
         (w2w
            (w2w
               (((^mem2_var :word64 |-> word8) '
                 ((R28' :word64) + (12w :word64) + (0w :word64)))
                  :word8) :word64) :word32) :word64) <<~ (3w :word64) ∧
      R26' +
      (w2w
         (w2w
            (w2w ((^mem2_var ' (R28' + (12w :word64) + (0w :word64))) :word8) :
             word64) :word32) :word64) <<~ (3w :word64) <₊ (0x8013FF80w
        :word64)
    then
      (1w :word1)
    else (0w :word1)) &&
   (if
      R26' +
      (w2w
         (w2w
            (w2w ((^mem2_var ' (R28' + (12w :word64) + (0w :word64))) :word8) :
             word64) :word32) :word64) <<~ (3w :word64) && (7w :word64) =
      (0w
        :word64)
    then
      (1w :word1)
    else (0w :word1)) &&
   (if (0x80100000w :word64) ≤₊ R28' ∧ R28' <₊ (0x8013FF80w :word64) then
      (1w :word1)
    else (0w :word1)) && (1w :word1)) && ((1w :word1) && (1w :word1)) &&
  ((1w :word1) && (1w :word1)) &&
  (if
     R28 >>>~ (6w :word64) = R28' >>>~ (6w :word64) ∧
     (R26 +
      (w2w
         (w2w
            (w2w ((^mem1_var ' (R28 + (12w :word64) + (0w :word64))) :word8) :
             word64) :word32) :word64) <<~ (3w :word64)) >>>~ (6w :word64) =
     (R26' +
      (w2w
         (w2w
            (w2w ((^mem2_var ' (R28' + (12w :word64) + (0w :word64))) :word8) :
             word64) :word32) :word64) <<~ (3w :word64)) >>>~ (6w :word64)
   then
     (1w :word1)
   else (0w :word1)) && ¬(0w :word1)) && (1w :word1)) && (1w :word1) =
(1w
  :word1) ∧ (R26 ≠ R26' ∨ R28 ≠ R28')
”;
*)

      val goal = ([], term)
      val (simplified_goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC false) goal

      open HolKernel boolLib liteLib simpLib Parse bossLib;
      val (sg_tl, sg_t) = simplified_goal;
      val _ = print ((Int.toString (List.length sg_tl)) ^ "\n");
      val _ = print_term sg_t;
      val _ = List.map print_term sg_tl;

(*
type_of term

      val goal = ([]:term list, “^term”)
(Library.WORD_SIMP_TAC)
 goal
*)

(*
Z3_SAT_modelLib.Z3_GET_SAT_MODEL term
*)
