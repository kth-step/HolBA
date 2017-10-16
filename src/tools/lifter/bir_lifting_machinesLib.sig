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

   val bmr_ms_mem_contains_tm   : term
   val dest_bmr_ms_mem_contains : term -> term * term * term
   val is_bmr_ms_mem_contains   : term -> bool
   val mk_bmr_ms_mem_contains   : term * term * term -> term

   (* Fields of the record *)
   val dest_bir_lifting_machine_rec :
     term -> term list (*imms*) * term (* mem *) * term (*pc*) * term (*extra*) * term (* step *)

   val bmr_pc_lf_tm       : term;
   val bmr_pc_var_tm      : term;
   val bmr_pc_var_cond_tm : term;
   val bmr_mem_lf_tm      : term;
   val bmr_mem_var_tm     : term;

   val BMLI_tm   : term
   val dest_BMLI : term -> term * term
   val is_BMLI   : term -> bool
   val mk_BMLI   : term * term -> term

   val BMLPC_tm   : term
   val dest_BMLPC : term -> term * term * term
   val is_BMLPC   : term -> bool
   val mk_BMLPC   : term * term * term -> term

   val BMLM_tm   : term
   val dest_BMLM : term -> term * term
   val is_BMLM   : term -> bool
   val mk_BMLM   : term * term -> term


   val bmr_field_extra_tm   : term
   val dest_bmr_field_extra : term -> term * term
   val is_bmr_field_extra   : term -> bool
   val mk_bmr_field_extra   : term * term -> term

   val bmr_field_imms_tm   : term
   val dest_bmr_field_imms : term -> term
   val is_bmr_field_imms   : term -> bool
   val mk_bmr_field_imms   : term -> term

   val bmr_field_pc_tm   : term
   val dest_bmr_field_pc : term -> term
   val is_bmr_field_pc   : term -> bool
   val mk_bmr_field_pc   : term -> term

   val bmr_field_mem_tm   : term
   val dest_bmr_field_mem : term -> term
   val is_bmr_field_mem   : term -> bool
   val mk_bmr_field_mem   : term -> term

   val bmr_field_step_fun_tm   : term
   val dest_bmr_field_step_fun : term -> term * term
   val is_bmr_field_step_fun   : term -> bool
   val mk_bmr_field_step_fun   : term * term -> term



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

      (* A list of FUNS_EQ_OUTSIDE_WI_size theorems used to compute
         the intervals of addressed updated by memory stores. *)
      bmr_change_interval_thms : thm list,

      (* A useful theorem for computing the PC value from a label value.
         It is expected to be a theorem of the from

         !ms n. (BL_Address (bmr_pc_lf r ms) = BL_Address (ImmX (n2w n))) ==>
                (PC of ms = something of n)
      *)
      bmr_label_thm : thm,

      (* Tries to destruct some memory application. it returns the state and the address
         of the memory lookup. E.g. "ms.MEM 0x10000" is destructed to (``ms``, ``0x10000``) *)
      bmr_dest_mem : term -> term * term,

      (* A useful ssfrag for this machine type. It should
         contain e.g. information for deal with the machine state type. *)
      bmr_extra_ss           : simpLib.ssfrag,

      (* Function evaluationg an instruction given as a hex string and returns
         a set of step theorems. *)
      bmr_step_hex           : term -> string -> thm list,

      (* To add data blocks, a function that encode a memory address and a hex-code
         as a memory-contains tuple *)
      bmr_mk_data_mm           : Arbnum.num -> string -> term,

      (* This is the number of memory addressed used by a hex-code. If
         bmr_step_hex or bmr_mk_data_mm succeed, this number of addresses is used. *)
      bmr_hex_code_size        : string -> Arbnum.num,

      (* Parameter used for decoding and encoding Intel HEX files. If set to NONE,
         no encoding / decoding is supported. If used, all instructions must have the
         same length. This length in bytes is the first part of this paramter. The
         second one is a flag whether instructions are encoded little (true) or
         big (false) endian. *)
      bmr_ihex_param           : (int * bool) option
   };

   (* The record for arm8 *)
   val arm8_bmr_rec : bmr_rec;



   (* extracting the record fields. Output is the same as of
      dest_bir_lifting_machine_rec *)
  val bmr_rec_extract_fields : bmr_rec -> term list * term * term * term * term;

  (* The PC always corresponds to some immediate. This function
     returns a the size of this immediate.

     As a second component a function for constructing terms "mk_get_pc_term" is
     returned. Given a term "t" of the suitable machine state type, this
     function constructs a term returning the PC of this machine state. *)
  val bmr_rec_mk_pc_of_term : bmr_rec -> int * (term -> term)

  (* Given a PC as an Arbnum, we need to be able to construct a label.
     The form of the label depends on the size of the PC and therefore the record. *)
  val bmr_rec_mk_label_of_num : bmr_rec -> Arbnum.num -> term

  (* Similar to contructing the label, we need an equality of this label with
     the label of the PC, this then simplifies to the PC having a certain value. *)
  val bmr_rec_mk_label_of_num_eq_pc : bmr_rec -> (term * Arbnum.num) -> term

end
