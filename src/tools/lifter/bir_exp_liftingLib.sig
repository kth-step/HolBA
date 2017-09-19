signature bir_exp_liftingLib =
sig
   include Abbrev

   (**********)
   (* Syntax *)
   (**********)

   val mk_bir_lift_val_t      : hol_type * hol_type -> hol_type
   val dest_bir_lift_val_t    : hol_type -> hol_type * hol_type
   val is_bir_lift_val_t      : hol_type -> bool

   val BLV_Imm_tm             : term;
   val mk_BLV_Imm             : term -> term;
   val dest_BLV_Imm           : term -> term;
   val is_BLV_Imm             : term -> bool;

   val BLV_Mem_tm             : term;
   val mk_BLV_Mem             : term -> term;
   val dest_BLV_Mem           : term -> term;
   val is_BLV_Mem             : term -> bool;


   (* a function constructiong either a BLV_Imm or a BLV_Mem term
      depending on the type of input terms. Valid input term types are
      booleans, words of supported sizes and functions from words to words. *)
   val gen_mk_BLV             : term -> term

   val bir_is_lifted_exp_tm   : term;
   val mk_bir_is_lifted_exp   : (term * term * term) -> term;
   val dest_bir_is_lifted_exp : term -> (term * term * term);
   val is_bir_is_lifted_exp   : term -> bool;



   (********************************)
   (* Expression Lifting functions *)
   (********************************)

   (* The lifter works by backchainging using theorems of the form

      [some assumptions] |- bir_is_lifted_exp env e v

      We need to somehow find such theorems to apply. This is done
      via exp_lifting_fun - records. Their job is given terms "env" and "v"
      produce a theorem like above. Usually the variables in expression e
      should be freshly generated and constrained via the assumptions.

      If no such theorem can be created, a HOL_ERR exception should be raised.
      This core functionality is available via elf_apply.
   *)
   type exp_lifting_fun_rec;

   val elf_apply : exp_lifting_fun_rec -> term -> term -> thm


   (* Later, we need to select efficiently between many lifting functions to
      check, which to try first. To implement this, there is guard term
      available. If this guard does not match a term "v", then
      "elf_apply r env v" should fail. Using this guard, many lifting functions
      can be quickly discared without actually calling them.

      To construct a exp_lifting_fun_rec one needs to provide the actual
      function creating theorems as well as an optional guard term. If no guard is
      given, the lifting function will always be tried (WARNING: inefficient). *)
   val mk_elf : term option (* Guard *) -> (term -> term -> thm) (* apply_fun *) -> exp_lifting_fun_rec

   (* To further select between many possible lifting functions, they contain a
      precedence. The precedence is an integer. Functions with lower precedence are
      tried first. There are a few predefined precedences, by default the precedence
      elf_precedence_default is used. *)

   val elf_precedence_high    : int (*  5 *)
   val elf_precedence_default : int (* 10 *)
   val elf_precedence_low     : int (* 15 *)

   val elf_set_precedence : exp_lifting_fun_rec -> int -> exp_lifting_fun_rec


   (* Sometimes it is handy to make the apply function fail more frequently.
      "elf_add_check cf" adds a check. If for terms "env" and "v" "cf env v" either
      returns "false" or raises a HOL_ERR, then also elf_apply is made to raise a HOL_ERR. *)
   val elf_add_check : exp_lifting_fun_rec -> (term -> term -> bool) -> exp_lifting_fun_rec


   (**********************************************)
   (* Expression lifting functions from theorems *)
   (**********************************************)

   (* Given a list of theorems, "elfs_of_thms" preprocesses these theorems and creates
      expression lifting functions. Usually all variables in these theorems can be
      freely instantiated by the expression lifter. A list of variables that should not be
      instantiated, they can be passed as an extra argument.

      For debugging purposes, also the preprocessing function
      is exported. *)
   val elfs_of_thms : term list -> thm list -> exp_lifting_fun_rec list
   val prepare_exp_lifting_thms : term list -> thm list -> thm list


   (***************************)
   (* Expression lifting nets *)
   (***************************)

   (* finite sets of expression lifting functions are stored in an indexed form
      in expression lifting nets. This is the datastructure used to hand them around
      to functions acually using them. *)

   type exp_lifting_net;

   val eln_empty       : exp_lifting_net;
   val eln_insert      : exp_lifting_net -> exp_lifting_fun_rec -> exp_lifting_net
   val eln_union       : exp_lifting_net -> exp_lifting_net -> exp_lifting_net

   val eln_list_insert : exp_lifting_net -> exp_lifting_fun_rec list -> exp_lifting_net
   val eln_of_elfs     : exp_lifting_fun_rec list -> exp_lifting_net

   (* combinations with elfs_of_thms for convenience *)
   val eln_add_thms                 : exp_lifting_net ->        term list -> thm list -> exp_lifting_net
   val eln_add_thms_with_precedence : exp_lifting_net -> int -> term list -> thm list -> exp_lifting_net
   val eln_of_thms                  : term list -> thm list -> exp_lifting_net


   (****************************************************)
   (* Predefined expression lifting functions and nets *)
   (****************************************************)

   (* A function lifting literal immediate values, i.e. values like
      "BLV_Imm (Imm8 0w)" or "BLV_Imm (Imm32 175w)", but not
      for example "BLV_Imm (Imm32 w1)". *)
   val elf_literal_imm : exp_lifting_fun_rec

   (* the expression lifting net resulting from theorem
      bir_is_lifted_imm_exp_DEFAULT_THMS and elf_literal_imm *)
   val eln_default : exp_lifting_net;



   (******************************)
   (* Main lifting functionality *)
   (******************************)

   (* This is the main workhorse. Given an environment term env_t,
      a lifting net eln and a value to lift v

      bir_exp_lift env_t eln v

      tries to produce a theorem with conclusion

      "bir_is_lifted_imm_exp env ... v".

      The value v actually processed via gen_mk_BLV allowing some freedom. *)
   val bir_exp_lift : term -> exp_lifting_net -> term -> thm

   (* often one does not care about the environment. Therefore, it is convenient to
      just use a suitable named var. *)
   val bir_var_environment_t_default : term
   val bir_exp_lift_default_env : exp_lifting_net -> term -> thm


   (* Interally bir_exp_lift is implemented using several steps.

      First an initial theorem is created via "bir_exp_lift env v".
      Next this theorem is processed via

      "bir_exp_lift_continue eln (cache, thm)"

      The cache is a special datastructure of used to
      avoid lifting multiple subexpressions several times.
      One starts with an empty on which is augmented.
      bir_exp_lift_continue can be called multiple times
      always using the results of the previous call.

      Finally the cache is thrown away and the theorem processed via
      bir_exp_lift_final.

      These functions are exported, since they might be helpful to
      write specialed lifters. *)

   type exp_lifting_cache
   val elc_empty : exp_lifting_cache

   val bir_exp_lift_init     : term -> term -> thm
   val bir_exp_lift_continue : exp_lifting_net -> exp_lifting_cache * thm -> exp_lifting_cache * thm
   val bir_exp_lift_final    : thm -> thm

end
