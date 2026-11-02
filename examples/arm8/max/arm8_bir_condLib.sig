signature arm8_bir_condLib =
sig
  include Abbrev

  (* Proof-producing translation of ARMv8 state conditions to BIR.

     The input is a definition of the form

       |- !x1 ... xn m. c x1 ... xn m = body

     where m : arm8_state and body is in the supported fragment:
       - /\, \/, ~, ==>
       - =, <+, <=+, >+, >=+, <, <=, >, >= on word64
       - m.REG k with k a word literal, free word64 variables
         (among x1 ... xn) and word64 literals
       - at most one top-level conjunct m.PC = A, with A a closed
         word64 term (a literal or an address constant)

     Anything else makes the translation fail with a HOL_ERR naming
     the offending subterm. A failing translation leaves the current
     theory unchanged: the new constant below is defined last.

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

  (* Both return the new BIR definition and the relation theorem:

       |- bir_pre_arm8_to_bir (c x1 ... xn) (b x1 ... xn)

       |- !ls. bir_post_bir_to_arm8 (c x1 ... xn) (\l. b x1 ... xn) ls

     where, if body has a PC conjunct m.PC = A, the BIR postcondition is

       \l. if l = BL_Address (Imm64 A) then b x1 ... xn else bir_exp_false

     In a precondition, the PC conjunct is dropped. *)
  val arm8_pre_to_bir  : thm -> thm * thm
  val arm8_post_to_bir : thm -> thm * thm
end
