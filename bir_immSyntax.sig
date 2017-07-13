signature bir_immSyntax =
sig
   include Abbrev

   (*****************)
   (* bir_immtype_t *)
   (*****************)

   (* The type itself *)
   val bir_immtype_t_ty : hol_type

   (* list of all immtype constants *)
   val bir_immtype_t_list : term list;

   (* The constants *)
   val Bit1_tm : term
   val Bit8_tm : term
   val Bit16_tm : term
   val Bit32_tm : term
   val Bit64_tm : term

   (* And checkers *)
   val is_Bit1  : term -> bool
   val is_Bit8  : term -> bool
   val is_Bit16 : term -> bool
   val is_Bit32 : term -> bool
   val is_Bit64 : term -> bool


   (*****************)
   (* bir_imm_t     *)
   (*****************)

   (* The type itself *)
   val bir_imm_t_ty : hol_type

   (* list of all immtype constants *)
   val bir_imm_t_list : term list;

   (* The constants *)
   val Imm1_tm : term
   val Imm8_tm : term
   val Imm16_tm : term
   val Imm32_tm : term
   val Imm64_tm : term

   (* make functions *)
   val mk_Imm1  : term -> term
   val mk_Imm8  : term -> term
   val mk_Imm16 : term -> term
   val mk_Imm32 : term -> term
   val mk_Imm64 : term -> term

   (* dest functions *)
   val dest_Imm1  : term -> term
   val dest_Imm8  : term -> term
   val dest_Imm16 : term -> term
   val dest_Imm32 : term -> term
   val dest_Imm64 : term -> term

   (* And checkers *)
   val is_Imm1  : term -> bool
   val is_Imm8  : term -> bool
   val is_Imm16 : term -> bool
   val is_Imm32 : term -> bool
   val is_Imm64 : term -> bool



   (******************************)
   (* generalised size functions *)
   (******************************)

   (* A list of all known, i.e. supported sizes *)
   val known_imm_sizes : int list;

   (* checks whether a size or a word-type are supported *)
   val is_known_imm_size : int -> bool;
   val is_known_word_ty : hol_type -> bool;

   (* getting the type of a size, e.g. bir_imm_type_t_of_size 8 = ``Bit8`` *)
   val bir_imm_type_t_of_size : int -> term

   (* and the inverse, e.g. size_of_bir_imm_type_t ``Bit8`` = 8 *)
   val size_of_bir_imm_type_t : term -> int

   (* Same with words, e.g.

      bir_imm_type_t_of_word_ty ``:word8`` = ``Bit8``
      word_ty_of_bir_imm_type_t ``Bit8`` = ``:word8``
    *)
   val bir_imm_type_t_of_word_ty : hol_type -> term
   val word_ty_of_bir_imm_type_t : term -> hol_type

   (* Generalised mkImm. Given a word of a valid size,
      a boolean or a list of booleans of supported length,
      a corresponding bir_imm_t value is returned. *)
   val gen_mk_Imm : term -> term

   (* generalised destruction, returns the size and the argument, e.g.
      gen_dest_Imm ``Imm8 w`` = (8, ``w``) *)
   val gen_dest_Imm : term -> (int * term)

   (* Is the term any type of Imm constant *)
   val gen_is_Imm : term -> bool

   (* making Imm from numbers, first argument is size, second the value *)
   val mk_Imm_of_num : int -> Arbnum.num -> term;

   (* making Imm from integers instead of nums *)
   val mk_Imm_of_int : int -> int -> term;


   (***************************)
   (* various functions       *)
   (***************************)

   val type_of_bir_imm_tm   : term;
   val mk_type_of_bir_imm   : term -> term;
   val dest_type_of_bir_imm : term -> term;
   val is_type_of_bir_imm   : term -> bool;

   val size_of_bir_immtype_tm   : term;
   val mk_size_of_bir_immtype   : term -> term;
   val dest_size_of_bir_immtype : term -> term;
   val is_size_of_bir_immtype   : term -> bool;

   val bir_immtype_of_size_tm   : term;
   val mk_bir_immtype_of_size   : term -> term;
   val dest_bir_immtype_of_size : term -> term;
   val is_bir_immtype_of_size   : term -> bool;

   val b2w_tm   : term;
   val mk_b2w   : term -> term;
   val dest_b2w : term -> term;
   val is_b2w   : term -> bool;

   val w2bs_tm   : term;
   val mk_w2bs   : (term * term) -> term;
   val dest_w2bs : term -> (term * term);
   val is_w2bs   : term -> bool;

   val bool2b_tm   : term;
   val mk_bool2b   : term -> term;
   val dest_bool2b : term -> term;
   val is_bool2b   : term -> bool;

   val n2bs_tm   : term;
   val mk_n2bs   : (term * term) -> term;
   val dest_n2bs : term -> (term * term);
   val is_n2bs   : term -> bool;

   val b2n_tm   : term;
   val mk_b2n   : term -> term;
   val dest_b2n : term -> term;
   val is_b2n   : term -> bool;

   val b2v_tm   : term;
   val mk_b2v   : term -> term;
   val dest_b2v : term -> term;
   val is_b2v   : term -> bool;

   val v2bs_tm   : term;
   val mk_v2bs   : (term * term) -> term;
   val dest_v2bs : term -> (term * term);
   val is_v2bs   : term -> bool;

end
