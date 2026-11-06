signature arm8_bir_condLib =
sig
  include Abbrev

  (* Proof-producing translation of ARMv8 state conditions to BIR, the
     ARMv8 instance of bir_condLib (riscv_bir_condLib is the RISC-V one).

     The input is a definition of the form

       |- !x1 ... xn m. c x1 ... xn m = body

     where m : arm8_state and body is in the supported fragment:
       - /\, \/, ~, ==>
       - =, <+, <=+, >+, >=+, <, <=, >, >= on words of size 8, 16, 32
         or 64
       - words built with +, -, unary -, *, //, /, word_mod, &&, ||,
         ??, ~, <<~, >>>~, >>~, w2w and sw2sw from m.REG k with k a
         word literal (and the other state reads arm8_bmr_LIFTED lifts,
         e.g. m.SP_EL0), 64-bit little-endian loads arm8_load_64 m.MEM a
         with a such a word, free variables (among x1 ... xn), word
         literals and closed words (evaluated to literals)
       - at most one top-level conjunct m.PC = A, with A a closed
         word64 term (a literal or an address constant)

     Anything else makes the translation fail with a HOL_ERR naming
     the offending subterm. A failing translation leaves the current
     theory unchanged: the new constant below is defined last, and
     the translation first checks that the names of the new constant,
     its definition and the saved theorem are free.

     The translation defines a new constant b (named as c with a
     leading "arm8_" replaced by "bspec_", otherwise prefixed with
     "bspec_") in the current theory:

       |- !x1 ... xn. b x1 ... xn = <BIR expression>

     and proves the lifting judgment

       |- !bs m. bmr_rel arm8_bmr bs m ==>
            bir_is_lifted_imm_exp bs.bst_environ (b x1 ... xn) (bool2b Q)

     where Q is body without its PC conjunct. *)

  type arm8_bir_cond_result =
    { bir_def    : thm,
      lifted_thm : thm,
      pc_addr    : term option }

  val arm8_cond_to_bir : thm -> arm8_bir_cond_result

  (* Both return the new BIR definition and the relation theorem, which
     they also save in the current theory as c_to_bir_thm (so a script
     can just call them with val _ = ...):

       |- bir_pre_arm8_to_bir (c x1 ... xn) (b x1 ... xn)

       |- !ls. bir_post_bir_to_arm8 (c x1 ... xn) (\l. b x1 ... xn) ls

     where, if body has a PC conjunct m.PC = A, the BIR postcondition is

       \l. if l = BL_Address (Imm64 A) then b x1 ... xn else bir_exp_false

     In a precondition, the PC conjunct is dropped. *)
  val arm8_pre_to_bir  : thm -> thm * thm
  val arm8_post_to_bir : thm -> thm * thm

  (* Postconditions by cases on the PC. The input is a definition

       |- !x1 ... xn m. c x1 ... xn m =
            if m.PC = A1 then c1 ys1 m
            else ... if m.PC = Ak then ck ysk m
            else F

     with each Ai a closed word64 term, and each ci one of the constants
     defined by the given case definitions, applied to terms ysi over
     x1 ... xn. Each case definition is a condition as for
     arm8_cond_to_bir, without a PC conjunct, and must be used. The
     translation defines a BIR constant bi for each case definition, as
     arm8_cond_to_bir does, and returns these definitions in the given
     order, and

       |- !ls. bir_post_bir_to_arm8 (c x1 ... xn)
            (\l. if l = BL_Address (Imm64 A1) then b1 ys1
                 else ... if l = BL_Address (Imm64 Ak) then bk ysk
                 else bir_exp_false) ls

     The relation theorem is saved as c_to_bir_thm. As above, the BIR
     constants are defined last. *)
  val arm8_post_cases_to_bir : thm -> thm list -> thm list * thm
end
