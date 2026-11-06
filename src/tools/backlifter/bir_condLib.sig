signature bir_condLib =
sig
  include Abbrev

  (* Architecture-independent part of the proof-producing translation of
     ISA state conditions to BIR, used by arm8_bir_condLib and
     riscv_bir_condLib (see there for the interface and the supported
     fragment).

     The input is a definition

       |- !x1 ... xn m. c x1 ... xn m = body

     where m is an ISA state and body is in the supported fragment:
       - /\, \/, ~, ==>
       - =, <+, <=+, >+, >=+, <, <=, >, >= on words of size 8, 16, 32
         or 64
       - words built with +, -, unary -, *, //, /, word_mod, &&, ||,
         ??, ~, <<~, >>>~, >>~, w2w and sw2sw from
         - state reads of m that the architecture's lifting theorem
           lifts, e.g. registers and control/status registers,
         - 64-bit loads from the memory of m at such a word,
         - free variables (among x1 ... xn),
         - closed words, e.g. address constants, which are evaluated
           to literals with EVAL
       - an equation t = c or c = t with c a literal and t a narrow state
         component that the lifting theorem lifts only as a widening
         cast w2w t (e.g. a 2-bit field), translated as w2w t = w2w c
       - at most one top-level conjunct PC = A, with PC the program
         counter of m and A a closed word64 term (a literal or an
         address constant)

     The translation defines a new constant b, named as c with a leading
     "<arch>_" replaced by "bspec_", otherwise prefixed with "bspec_".
     pre_to_bir, post_to_bir and post_cases_to_bir also save the relation
     theorem as c_to_bir_thm. The names are checked to be free first, and
     the constant is defined last, so that a failing translation leaves
     the current theory unchanged. *)

  (* What the translation needs to know about an architecture:
       arch            its name, e.g. "arm8"
       state_ty        the type of its states
       bmr             its bir_lifting_machine_rec_t, e.g. arm8_bmr
       bmr_lifted      lifting theorems for the parts of its state
                       (registers, memory), e.g. arm8_bmr_LIFTED; the
                       lifted state reads are the readable ones
       dest_load m tm  SOME a if tm is a 64-bit load at a from the memory
                       of m
       pc_of m         the program counter of m
       load_thms       rewrites unfolding loads to the byte concatenation
                       that bir_exp_liftingLib lifts to a little-endian
                       BExp_Load
       pre_lifted, post_lifted, post_lifted_PC, post_cases_nil,
       post_cases_cons
                       the bridge lemmas from the lifting judgment to the
                       architecture's pre/postcondition relations, as in
                       arm8_bir_condTheory *)
  type arch_info =
    { arch            : string,
      state_ty        : hol_type,
      bmr             : term,
      bmr_lifted      : thm,
      dest_load       : term -> term -> term option,
      pc_of           : term -> term,
      load_thms       : thm list,
      pre_lifted      : thm,
      post_lifted     : thm,
      post_lifted_PC  : thm,
      post_cases_nil  : thm,
      post_cases_cons : thm }

  type bir_cond_result =
    { bir_def    : thm,
      lifted_thm : thm,
      pc_addr    : term option }

  val cond_to_bir       : arch_info -> thm -> bir_cond_result
  val pre_to_bir        : arch_info -> thm -> thm * thm
  val post_to_bir       : arch_info -> thm -> thm * thm
  val post_cases_to_bir : arch_info -> thm -> thm list -> thm list * thm
end
