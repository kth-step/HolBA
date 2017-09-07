signature bir_lifting_machinesLib =
sig
   include Abbrev

   (***************)
   (* Some Syntax *)
   (***************)

   (* record type bir_lifting_machine_rec_t has 3 type arguments. MK and DEST
      below expect them in the following order:

      - machine state type
      - size of memory addresses
      - size of memory values
   *)
   val mk_bir_lifting_machine_rec_t_ty   : hol_type * hol_type * hol_type -> hol_type
   val dest_bir_lifting_machine_rec_t_ty : hol_type -> hol_type * hol_type * hol_type
   val is_bir_lift_machine_rec_t_ty      : hol_type -> bool

   val bmr_ok_tm   : term
   val dest_bmr_ok : term -> term
   val is_bmr_ok   : term -> bool
   val mk_bmr_ok   : term -> term

   val bmr_rel_tm   : term
   val dest_bmr_rel : term -> term * term * term
   val is_bmr_rel   : term -> bool
   val mk_bmr_rel   : term * term * term -> term

   val bmr_vars_tm   : term
   val dest_bmr_vars : term -> term
   val is_bmr_vars   : term -> bool
   val mk_bmr_vars   : term -> term

   val bmr_temp_vars_tm   : term
   val dest_bmr_temp_vars : term -> term
   val is_bmr_temp_vars   : term -> bool
   val mk_bmr_temp_vars   : term -> term


   (******************)
   (* Simplification *)
   (******************)

   val bmr_REWRS : thm list
   val bmr_ss : simpLib.ssfrag


   (***************)
   (* Record Type *)
   (***************)

   (* for each machine, information is collected in a special record type *)
   type bmr_rec = {
      (* The constant for the dest_bir_lifting_machine_rec_t constant *)
      bmr_const              : term,

      (* A theorem of form "brm_ok r" where r is the constant above *)
      bmr_ok_thm             : thm,

      (* A theorem evaluating the record constant. All auxilary definitions
         should be expanded in this theorem. *)
      bmr_eval_thm           : thm,

      (* evaluation for ``bmr_rel r bs ms`` *)
      bmr_eval_rel_thm       : thm,

      (* Rewrite for the vars used. Should be of form
         ``bmr_vars r = [v1; v2; ...]`` *)
      bmr_eval_vars_thm      : thm,

      (* Rewrite for the temp_vars used. Should be of form
         ``bmr_temp_vars r = [v1; v2; ...]`` *)
      bmr_eval_temp_vars_thm : thm,

      (* Some lifting theorem, should be of from
         |- !bs ms. bmr_rel r bs ms ==>
                    (bir_is_lifted_exp bs.bst_environ . .) /\
                    ....
                    (bir_is_lifted_exp bs.bst_environ . .)
      *)
      bmr_lifted_thm         : thm,

      (* Extra lifting theorem useful for this machine type,
         some special rewrites for e.g. OVERFLOWS ... *)
      bmr_extra_lifted_thms  : thm list,

      (* A useful ssfrag for this machine type. It should
         contain e.g. information for deal with the machine state type. *)
      bmr_extra_ss           : simpLib.ssfrag,

      (* Function evaluationg an instruction given as a hex string and returns
         a set of step theorems. *)
      bmr_step_hex           : string -> thm list
   };

   (* The record for arm8 *)
   val arm8_bmr_rec : bmr_rec;

end
