(* Selftest of bir_condLib through its arm8 and riscv instances: which
   conditions the translation rejects, and that a rejection names what is
   wrong and leaves the current theory unchanged.

   The rejected conditions fall in two groups:
   - outside the fragment by design: too much HOL for a contract condition,
     or a misuse of the interface
   - possible future extensions: when the translator learns one of these, its
     test here fails and should be turned into a positive test.

   Run with "Holmake test". *)

open HolKernel Parse boolLib bossLib;
open testutils;

open wordsTheory;
open bir_arm8_backlifterTheory bir_riscv_extrasTheory;

open arm8_bir_condLib riscv_bir_condLib;

(* proofs (also inside libraries) need a current theory *)
val _ = new_theory "scratch";

fun def name tm = new_definition (name ^ "_def", tm);

(* ------- *)
(* Harness *)
(* ------- *)

fun theory_contents () =
  (map fst (current_definitions ()), map fst (current_theorems ()),
   map (fst o dest_const) (constants "-"));

(* tr must raise a HOL_ERR whose text contains all of expected, and must
   leave the current theory unchanged. Any other exception ends the test. *)
fun rejects title tr expected = let
  val _ = tprint title
  val before_contents = theory_contents ()
  val result = (tr (); NONE)
    handle e as HOL_ERR _ => SOME (Feedback.exn_to_string e)
in
  case result of
    NONE => die "translated, but should be rejected"
  | SOME msg =>
      if not (List.all (fn s => String.isSubstring s msg) expected)
      then die ("wrong error: " ^ msg)
      else if theory_contents () <> before_contents
      then die "rejection changed the current theory"
      else OK ()
end;

fun arm8_pre_rejected title th expected =
  rejects title (fn () => ignore (arm8_pre_to_bir th)) expected;
fun riscv_post_rejected title th expected =
  rejects title (fn () => ignore (riscv_post_to_bir th)) expected;
fun arm8_cases_rejected title th ths expected =
  rejects title (fn () => ignore (arm8_post_cases_to_bir th ths)) expected;

(* ---------------- *)
(* Positive controls *)
(* ---------------- *)

(* Without these, a broken translator would pass all rejection tests. Checks
   that the BIR definition and relation theorem are saved under their names. *)
fun translates title name_c tr = let
  val _ = tprint title
  val (bir_def, rel_thm) = tr ()
  fun saved n = DB.fetch "-" n
    handle HOL_ERR _ => raise Fail ("not saved: " ^ n)
  val saved_def = saved (name_c ^ "_bir_def")
  val saved_rel = saved (name_c ^ "_to_bir_thm")
in
  if not (aconv (concl saved_def) (concl bir_def))
  then die "saved definition differs from the returned one"
  else if not (aconv (concl saved_rel) (concl rel_thm))
  then die "saved theorem differs from the returned one"
  else OK ()
end;

val arm8_ok_pre_def = def "arm8_ok_pre"
  ``arm8_ok_pre (x:word64) (m:arm8_state) =
    (m.PC = 0x100w /\ m.REG 0w = x /\ arm8_load_64 m.MEM (m.REG 1w) <+ 5w)``;
val _ = translates "arm8 precondition" "arm8_ok_pre"
  (fn () => arm8_pre_to_bir arm8_ok_pre_def);

val arm8_ok_post_def = def "arm8_ok_post"
  ``arm8_ok_post (x:word64) (m:arm8_state) =
    (m.PC = 0x104w /\ m.REG 0w = x + 1w)``;
val _ = translates "arm8 postcondition" "arm8_ok_post"
  (fn () => arm8_post_to_bir arm8_ok_post_def);

val riscv_ok_pre_def = def "riscv_ok_pre"
  ``riscv_ok_pre (x:word64) (m:riscv_state) =
    (m.c_PC m.procID = 0x100w /\ m.c_gpr m.procID 10w = x /\
     riscv_mem_load_dword m.MEM8 (m.c_gpr m.procID 11w) <+ 5w)``;
val _ = translates "riscv precondition" "riscv_ok_pre"
  (fn () => riscv_pre_to_bir riscv_ok_pre_def);

val riscv_ok_post_def = def "riscv_ok_post"
  ``riscv_ok_post (x:word64) (m:riscv_state) =
    (m.c_PC m.procID = 0x104w /\ m.c_gpr m.procID 10w = x + 1w)``;
val _ = translates "riscv postcondition" "riscv_ok_post"
  (fn () => riscv_post_to_bir riscv_ok_post_def);

(* The M-mode contract of lifted RISC-V code, which the translation unfolds
   with riscv_mmode_cond: its translation is bir_riscv_mmode_post *)
val riscv_mmode_ok_pre_def = def "riscv_mmode_ok_pre"
  ``riscv_mmode_ok_pre (x:word64) (m:riscv_state) =
    (riscv_mmode m /\ m.c_gpr m.procID 10w = x)``;
val _ = translates "riscv precondition with the M-mode contract"
  "riscv_mmode_ok_pre" (fn () => riscv_pre_to_bir riscv_mmode_ok_pre_def);

val riscv_mmode_ok_post_def = def "riscv_mmode_ok_post"
  ``riscv_mmode_ok_post (m:riscv_state) =
    (m.c_PC m.procID = 0x104w /\ riscv_mmode m)``;
val _ = tprint "riscv postcondition with the M-mode contract";
val (riscv_mmode_ok_post_bir_def, _) =
  riscv_post_to_bir riscv_mmode_ok_post_def;
val _ =
  if aconv (rhs (concl riscv_mmode_ok_post_bir_def))
       (rhs (concl bir_riscv_backlifterTheory.bir_riscv_mmode_post_def))
  then OK () else die "translation is not bir_riscv_mmode_post";

val case_a_def = def "case_a"
  ``case_a (x:word64) (m:arm8_state) = (m.REG 0w = x)``;
val case_b_def = def "case_b"
  ``case_b (m:arm8_state) = (m.REG 1w = 0w)``;
val arm8_ok_cases_def = def "arm8_ok_cases"
  ``arm8_ok_cases (x:word64) (m:arm8_state) =
    if m.PC = 0x100w then case_a x m
    else if m.PC = 0x200w then case_b m
    else F``;
val _ = tprint "arm8 postcondition by PC cases";
val (arm8_ok_case_defs, _) =
  arm8_post_cases_to_bir arm8_ok_cases_def [case_a_def, case_b_def];
val _ =
  if length arm8_ok_case_defs = 2 andalso
     can (DB.fetch "-") "arm8_ok_cases_to_bir_thm" andalso
     can (DB.fetch "-") "case_a_bir_def" andalso
     can (DB.fetch "-") "case_b_bir_def"
  then OK () else die "definitions or theorem not saved";

(* -------------- *)
(* Name freshness *)
(* -------------- *)

val _ = rejects "translating a condition twice"
  (fn () => ignore (arm8_pre_to_bir arm8_ok_pre_def))
  ["already exists", "arm8_ok_pre_to_bir_thm"];

val taken_thm_def = def "taken_thm" ``taken_thm (m:arm8_state) = (m.REG 0w = 0w)``;
val _ = save_thm ("taken_thm_to_bir_thm", TRUTH);
val _ = arm8_pre_rejected "theorem name taken" taken_thm_def
  ["already exists", "taken_thm_to_bir_thm"];

val taken_const_def = def "taken_const"
  ``taken_const (m:arm8_state) = (m.REG 0w = 0w)``;
val _ = def "taken_const_bir" ``taken_const_bir = T``;
val _ = arm8_pre_rejected "BIR constant name taken" taken_const_def
  ["already exists", "taken_const_bir"];

(* ------------------------------------------- *)
(* Outside the fragment by design: too much HOL *)
(* ------------------------------------------- *)

(* as in examples/riscv/mod2/mod2_spec_riscvScript.sml, with the arithmetic
   stated on numbers instead of words *)
val mod2_post_def = def "mod2_post"
  ``mod2_post (pre_x10:word64) (m:riscv_state) =
    (m.c_gpr m.procID 10w = n2w ((w2n pre_x10) MOD 2))``;
val _ = riscv_post_rejected "numeric arithmetic through n2w (mod2)" mod2_post_def
  ["unsupported word term", "n2w"];

val num_cmp_def = def "num_cmp"
  ``num_cmp (m:arm8_state) = (w2n (m.REG 0w) < 5)``;
val _ = arm8_pre_rejected "comparison on numbers" num_cmp_def
  ["unsupported condition"];

val num_eq_def = def "num_eq"
  ``num_eq (m:arm8_state) = (w2n (m.REG 0w) = 5)``;
val _ = arm8_pre_rejected "equation on numbers" num_eq_def
  ["unsupported word type"];

val forall_def = def "forall_cond"
  ``forall_cond (m:arm8_state) = !a. arm8_load_64 m.MEM a = 0w``;
val _ = arm8_pre_rejected "universal quantifier" forall_def
  ["unsupported condition"];

val exists_def = def "exists_cond"
  ``exists_cond (m:arm8_state) = ?v:word64. m.REG 0w = v``;
val _ = arm8_pre_rejected "existential quantifier" exists_def
  ["unsupported condition"];

val reg_var_def = def "reg_var"
  ``reg_var (r:word5) (m:arm8_state) = (m.REG r = 0w)``;
val _ = arm8_pre_rejected "register index that is not a literal" reg_var_def
  ["unsupported word term"];

val mem_eq_def = def "mem_eq"
  ``mem_eq (pre_mem:word64 -> word8) (m:arm8_state) = (m.MEM = pre_mem)``;
val _ = arm8_pre_rejected "equation on whole memories" mem_eq_def
  ["unsupported word type"];

val fun_param_def = def "fun_param"
  ``fun_param (f:word64 -> word64) (m:arm8_state) = (f (m.REG 0w) = 0w)``;
val _ = arm8_pre_rejected "function as a parameter" fun_param_def
  ["unsupported word term"];

val word128_def = def "word128_cond"
  ``word128_cond (m:arm8_state) = ((w2w (m.REG 0w) : word128) = 0w)``;
val _ = arm8_pre_rejected "word size without a BIR counterpart here" word128_def
  ["unsupported word type"];

(* ---------------------------------------------------- *)
(* Outside the fragment by design: the program counter *)
(* ---------------------------------------------------- *)

val pc_var_def = def "pc_var"
  ``pc_var (a:word64) (m:arm8_state) = (m.PC = a)``;
val _ = arm8_pre_rejected "PC compared with a parameter" pc_var_def
  ["unsupported PC address"];

val pc_disj_def = def "pc_disj"
  ``pc_disj (m:arm8_state) = (m.PC = 0x100w \/ m.REG 0w = 0w)``;
val _ = arm8_pre_rejected "PC below the top-level conjunction" pc_disj_def
  ["unsupported word term"];

val pc_twice_def = def "pc_twice"
  ``pc_twice (m:arm8_state) = (m.PC = 0x100w /\ m.PC = 0x104w)``;
val _ = arm8_pre_rejected "two PC conjuncts" pc_twice_def
  ["more than one PC conjunct"];

(* ------------------------------------- *)
(* Outside the interface: input shapes *)
(* ------------------------------------- *)

val _ = arm8_pre_rejected "not an equation" TRUTH ["not an equation"];

val not_bool_def = def "not_bool"
  ``not_bool (m:arm8_state) = m.REG 0w``;
val _ = arm8_pre_rejected "body that is not boolean" not_bool_def ["expected c"];

val no_state_def = def "no_state" ``no_state (x:word64) = (x = 0w)``;
val _ = arm8_pre_rejected "no state argument" no_state_def ["expected c"];

val riscv_state_def = def "riscv_state_cond"
  ``riscv_state_cond (m:riscv_state) = (m.c_gpr m.procID 10w = 0w)``;
val _ = arm8_pre_rejected "state of another architecture" riscv_state_def
  ["expected c"];

val inst_param_def = def "inst_param"
  ``inst_param (x:word64) (m:arm8_state) = (m.REG 0w = x)``;
val _ = arm8_pre_rejected "argument that is not a variable"
  (ISPEC ``0w:word64`` inst_param_def) ["expected c"];

(* ------------------------------ *)
(* Outside the interface: PC cases *)
(* ------------------------------ *)

val pc_case_a_def = def "pc_case_a"
  ``pc_case_a (m:arm8_state) = (m.REG 0w = 0w)``;
val pc_case_b_def = def "pc_case_b"
  ``pc_case_b (m:arm8_state) = (m.REG 1w = 0w)``;
val pc_case_pc_def = def "pc_case_pc"
  ``pc_case_pc (m:arm8_state) = (m.PC = 0x100w /\ m.REG 1w = 0w)``;

val no_final_F_def = def "no_final_F"
  ``no_final_F (m:arm8_state) =
    if m.PC = 0x100w then pc_case_a m else pc_case_b m``;
val _ = arm8_cases_rejected "PC cases not ending in F" no_final_F_def
  [pc_case_a_def, pc_case_b_def] ["unsupported PC case"];

val two_cases_def = def "two_cases"
  ``two_cases (m:arm8_state) =
    if m.PC = 0x100w then pc_case_a m
    else if m.PC = 0x200w then pc_case_b m
    else F``;
val _ = arm8_cases_rejected "PC case without a case definition" two_cases_def
  [pc_case_a_def] ["no case definition given"];

val one_case_def = def "one_case"
  ``one_case (m:arm8_state) = if m.PC = 0x100w then pc_case_a m else F``;
val _ = arm8_cases_rejected "unused case definition" one_case_def
  [pc_case_a_def, pc_case_b_def] ["case definition not used", "pc_case_b"];

val pc_in_case_def = def "pc_in_case"
  ``pc_in_case (m:arm8_state) = if m.PC = 0x100w then pc_case_pc m else F``;
val _ = arm8_cases_rejected "PC conjunct in a case condition" pc_in_case_def
  [pc_case_pc_def] ["PC conjunct in case condition", "pc_case_pc"];

val case_addr_var_def = def "case_addr_var"
  ``case_addr_var (a:word64) (m:arm8_state) =
    if m.PC = a then pc_case_a m else F``;
val _ = arm8_cases_rejected "PC case address that is not closed"
  case_addr_var_def [pc_case_a_def] ["unsupported PC address"];

val no_cases_def = def "no_cases" ``no_cases (m:arm8_state) = F``;
val _ = arm8_cases_rejected "no PC cases at all" no_cases_def []
  ["unsupported postcondition by PC cases"];

(* ---------------------------------------------- *)
(* Possible future extensions: words, for chacha20 *)
(* ---------------------------------------------- *)

val rotate_def = def "rotate_cond"
  ``rotate_cond (m:arm8_state) = (m.REG 0w #>> 7 = 0w)``;
val _ = arm8_pre_rejected "rotation" rotate_def ["unsupported word term"];

val lsl_num_def = def "lsl_num"
  ``lsl_num (m:arm8_state) = (m.REG 0w << 3 = 0w)``;
val _ = arm8_pre_rejected "shift by a number" lsl_num_def
  ["unsupported word term"];

val concat_def = def "concat_cond"
  ``concat_cond (m:arm8_state) =
    (((w2w (m.REG 0w) : word32) @@ (w2w (m.REG 1w) : word32)) : word64 = 0w)``;
val _ = arm8_pre_rejected "word concatenation" concat_def
  ["unsupported word term"];

val extract_def = def "extract_cond"
  ``extract_cond (m:arm8_state) = (((7 >< 0) (m.REG 0w) : word8) = 0w)``;
val _ = arm8_pre_rejected "word extraction" extract_def
  ["unsupported word term"];

val word_if_def = def "word_if"
  ``word_if (m:arm8_state) =
    ((if m.REG 0w = 0w then 1w else 0w) = m.REG 1w)``;
val _ = arm8_pre_rejected "if-then-else on words" word_if_def
  ["unsupported word term"];

(* --------------------------------------------------------- *)
(* Possible future extensions: gradual buildup of conditions *)
(* --------------------------------------------------------- *)

val let_def = def "let_cond"
  ``let_cond (m:arm8_state) = let x = m.REG 0w in x = 0w``;
val _ = arm8_pre_rejected "let" let_def ["unsupported condition"];

val let_pair_def = def "let_pair"
  ``let_pair (m:arm8_state) =
    let (x, y) = (m.REG 0w, m.REG 1w) in x = y``;
val _ = arm8_pre_rejected "let on a pair" let_pair_def ["unsupported condition"];

val aux_cond_def = def "aux_cond"
  ``aux_cond (m:arm8_state) = (m.REG 0w = 0w)``;
val aux_cond_user_def = def "aux_cond_user"
  ``aux_cond_user (m:arm8_state) = (aux_cond m /\ m.REG 1w = 0w)``;
val _ = arm8_pre_rejected "auxiliary condition" aux_cond_user_def
  ["unsupported condition"];

val aux_word_def = def "aux_word"
  ``aux_word (m:arm8_state) = m.REG 0w + 1w``;
val aux_word_user_def = def "aux_word_user"
  ``aux_word_user (m:arm8_state) = (aux_word m = 0w)``;
val _ = arm8_pre_rejected "auxiliary word function" aux_word_user_def
  ["unsupported word term"];

(* ----------------------------------------- *)
(* Possible future extensions: other features *)
(* ----------------------------------------- *)

val cond_if_def = def "cond_if"
  ``cond_if (m:arm8_state) =
    if m.REG 0w = 0w then m.REG 1w = 0w else m.REG 1w = 1w``;
val _ = arm8_pre_rejected "if-then-else on conditions" cond_if_def
  ["unsupported condition"];

val bool_param_def = def "bool_param"
  ``bool_param (b:bool) (m:arm8_state) = (b /\ m.REG 0w = 0w)``;
val _ = arm8_pre_rejected "boolean parameter" bool_param_def
  ["unsupported condition"];

val flag_def = def "flag_cond" ``flag_cond (m:arm8_state) = m.PSTATE.Z``;
val _ = arm8_pre_rejected "processor flag" flag_def ["unsupported condition"];

val word_bit_def = def "word_bit_cond"
  ``word_bit_cond (m:arm8_state) = word_bit 3 (m.REG 0w)``;
val _ = arm8_pre_rejected "single bit of a word" word_bit_def
  ["unsupported condition"];

val byte_load_arm8_def = def "byte_load_arm8"
  ``byte_load_arm8 (m:arm8_state) = (m.MEM (m.REG 0w) = 0w)``;
val _ = arm8_pre_rejected "arm8 byte load" byte_load_arm8_def
  ["unsupported word term"];

val byte_load_riscv_def = def "byte_load_riscv"
  ``byte_load_riscv (m:riscv_state) =
    (m.MEM8 (m.c_gpr m.procID 10w) = 0w)``;
val _ = riscv_post_rejected "riscv byte load" byte_load_riscv_def
  ["unsupported word term"];

val word_load_riscv_def = def "word_load_riscv"
  ``word_load_riscv (m:riscv_state) =
    (riscv_mem_load_word m.MEM8 (m.c_gpr m.procID 10w) = 0w)``;
val _ = riscv_post_rejected "riscv 32-bit load" word_load_riscv_def
  ["unsupported word term"];

val _ = print "bir_condLib selftest: all tests passed.\n";
