open HolKernel Parse boolLib bossLib;

(* This theory contains the definition of the modified m0 step
   (, where clock cycles are counted with word64 instead if num). *)

val _ = new_theory "m0_mod_step";

(*
open m0Theory m0_stepTheory;
open m0_stepLib;


val hex_code = "b510"
val hex_code = "f000f858"
val hex_code = "3202"
val hex_code = "4A15"

val hex_code = "635C"
val hex_code = "70E8"
val hex_code = "B570"
val hex_code = "BD70"
val hex_code = "B510"
val hex_code = "4770"
val hex_code = "0100"

val hex_code = "B285"
val hex_code = "8028"
val hex_code = "4182"
val hex_code = "4088";
val hex_code = "BA18";
val hex_code = "BDF7";
val hex_code = "B5F7"
val hex_code = "2200";
val hex_code = "2204";
val hex_code = "4084"
val hex_code = "40C4"
val hex_code = "1ACC";
val hex_code = "1E08"
val hex_code = "4251"
val hex_code = "40C4"
val hex_code = "4088"
val hex_code = "BA51";
val hex_code = "BAD1"
val hex_code = "41C8"


val endian_fl = false;
val sel_fl = true;

val thms = m0_stepLib.thumb_step_hex (endian_fl, sel_fl) hex_code;


NextStateM0_def


Next_def

Fetch_def
Decode_def
Run_def

DecodeThumb_def

dfn'Undefined_def
*)
(*
bir_is_lifted_prog_def
*)


typedef m0_mod_state
``<| base : ...;
     countw : word64 |>``

(*
m0_mod_eq s sm = if s.count < 2^64 then s = sm.base andalso sm.countw = n2w s.count else false;

 (s.count < 2^64) ==> m0_mod_eq s <| base := s; countw := n2w s.count |>
~(s.count < 2^64) ==> ~(m0_mod_eq s sm)
*)


(* Definitions *)
m0_mod s = if s.count < 2^64 then SOME (<| base := s; countw := n2w s.count |>) else NONE;
m0_mod_inv sm = sm.base with <| count := w2n sm.countw |>;


NextStateM0_mod sm = case NextStateM0 (m0_mod_inv sm) of
                       | NONE    => NONE
                       | SOME s' => m0_mod s';


(* mod step theorem gen *)
("", ``
 (m0_mod_inv sm = s) ==>
 (NextStateM0 s = SOME s') ==>
 (s'.count = s.count + (w2n i)) =>
 (i < (2w^64)) ==>

 (sm.countw < (2w^64 - 1w) - i) ==>
 (NextStateM0_mod sm = SOME (<| base := s'; countw := sm.countw + i |>))
``,
)

(* step function *)
thumb_mod_step_hex


val _ = export_theory();
