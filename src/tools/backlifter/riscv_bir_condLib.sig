signature riscv_bir_condLib =
sig
  include Abbrev

  (* Proof-producing translation of RISC-V state conditions to BIR, the
     RISC-V instance of bir_condLib (arm8_bir_condLib is the ARMv8 one).

     The input is a definition of the form

       |- !x1 ... xn m. c x1 ... xn m = body

     where m : riscv_state and body is in the supported fragment:
       - /\, \/, ~, ==>
       - =, <+, <=+, >+, >=+, <, <=, >, >= on words of size 8, 16, 32
         or 64
       - words built with +, -, unary -, *, //, /, word_mod, &&, ||,
         ??, ~, <<~, >>>~, >>~, w2w and sw2sw from m.c_gpr m.procID k
         with k a word literal (and the other state reads
         riscv_bmr_LIFTED lifts, e.g. (m.c_MCSR m.procID).mscratch),
         64-bit little-endian loads riscv_mem_load_dword m.MEM8 a with
         a such a word, free variables (among x1 ... xn), word literals
         and closed words (evaluated to literals)
       - an equation t = c with c a literal and t a narrow field that
         riscv_bmr_LIFTED lifts only as w2w t, e.g.
         (m.c_MCSR m.procID).mstatus.MPRV = 3w
       - at most one top-level conjunct m.c_PC m.procID = A, with A a
         closed word64 term (a literal or an address constant)

     Anything else makes the translation fail with a HOL_ERR naming
     the offending subterm. A failing translation leaves the current
     theory unchanged: the new constant below is defined last, and
     the translation first checks that the names of the new constant,
     its definition and the saved theorem are free.

     The translation defines a new constant b (named as c with a
     leading "riscv_" replaced by "bspec_", otherwise prefixed with
     "bspec_") in the current theory:

       |- !x1 ... xn. b x1 ... xn = <BIR expression>

     and proves the lifting judgment

       |- !bs m. bmr_rel riscv_bmr bs m ==>
            bir_is_lifted_imm_exp bs.bst_environ (b x1 ... xn) (bool2b Q)

     where Q is body without its PC conjunct. *)

  type riscv_bir_cond_result =
    { bir_def    : thm,
      lifted_thm : thm,
      pc_addr    : term option }

  val riscv_cond_to_bir : thm -> riscv_bir_cond_result

  (* Both return the new BIR definition and the relation theorem, which
     they also save in the current theory as c_to_bir_thm (so a script
     can just call them with val _ = ...):

       |- bir_pre_riscv_to_bir (c x1 ... xn) (b x1 ... xn)

       |- !ls. bir_post_bir_to_riscv (c x1 ... xn) (\l. b x1 ... xn) ls

     where, if body has a PC conjunct m.c_PC m.procID = A, the BIR
     postcondition is

       \l. if l = BL_Address (Imm64 A) then b x1 ... xn else bir_exp_false

     In a precondition, the PC conjunct is dropped. *)
  val riscv_pre_to_bir  : thm -> thm * thm
  val riscv_post_to_bir : thm -> thm * thm

  (* Postconditions by cases on the PC. The input is a definition

       |- !x1 ... xn m. c x1 ... xn m =
            if m.c_PC m.procID = A1 then c1 ys1 m
            else ... if m.c_PC m.procID = Ak then ck ysk m
            else F

     with each Ai a closed word64 term, and each ci one of the constants
     defined by the given case definitions, applied to terms ysi over
     x1 ... xn. Each case definition is a condition as for
     riscv_cond_to_bir, without a PC conjunct, and must be used. The
     translation defines a BIR constant bi for each case definition, as
     riscv_cond_to_bir does, and returns these definitions in the given
     order, and

       |- !ls. bir_post_bir_to_riscv (c x1 ... xn)
            (\l. if l = BL_Address (Imm64 A1) then b1 ys1
                 else ... if l = BL_Address (Imm64 Ak) then bk ysk
                 else bir_exp_false) ls

     The relation theorem is saved as c_to_bir_thm. As above, the BIR
     constants are defined last. *)
  val riscv_post_cases_to_bir : thm -> thm list -> thm list * thm
end
