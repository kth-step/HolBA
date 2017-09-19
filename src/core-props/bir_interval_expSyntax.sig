signature bir_interval_expSyntax =
sig
   include Abbrev

   (*******************)
   (* word_interval_t *)
   (*******************)

   val mk_word_interval_t_ty   : hol_type -> hol_type
   val dest_word_interval_t_ty : hol_type -> hol_type
   val is_word_interval_t_ty   : hol_type -> bool


   (******************************)
   (* Constructor like functions *)
   (******************************)

   val WI_end_tm   : term
   val dest_WI_end : term -> term * term
   val is_WI_end   : term -> bool
   val mk_WI_end   : term * term -> term

   val WI_size_tm   : term
   val dest_WI_size : term -> term * term
   val is_WI_size   : term -> bool
   val mk_WI_size   : term * term -> term


   (********************)
   (* Common functions *)
   (********************)

   val WI_wf_tm          : term
   val dest_WI_wf        : term -> term
   val is_WI_wf          : term -> bool
   val mk_WI_wf          : term -> term

   val WI_wfe_tm         : term
   val dest_WI_wfe       : term -> term
   val is_WI_wfe         : term -> bool
   val mk_WI_wfe         : term -> term

   val WI_MEM_tm         : term
   val dest_WI_MEM       : term -> term * term
   val is_WI_MEM         : term -> bool
   val mk_WI_MEM         : term * term -> term

   val WI_ELEM_LIST_tm   : term
   val dest_WI_ELEM_LIST : term -> term * term
   val is_WI_ELEM_LIST   : term -> bool
   val mk_WI_ELEM_LIST   : term * term -> term

   val WI_is_empty_tm    : term
   val dest_WI_is_empty  : term -> term
   val is_WI_is_empty    : term -> bool
   val mk_WI_is_empty    : term -> term

   val WI_is_sub_tm      : term
   val dest_WI_is_sub    : term -> term * term
   val is_WI_is_sub      : term -> bool
   val mk_WI_is_sub      : term * term -> term

   val WI_overlap_tm     : term
   val dest_WI_overlap   : term -> term * term
   val is_WI_overlap     : term -> bool
   val mk_WI_overlap     : term * term -> term

   val WI_distinct_tm    : term
   val dest_WI_distinct  : term -> term * term
   val is_WI_distinct    : term -> bool
   val mk_WI_distinct    : term * term -> term


   (*****************************)
   (* Constructing from numbers *)
   (*****************************)

   (* Often we want to construct fixed intervals from given numbers.
      For this we need to provide the type of the words used, e.g. ``:32``
      as well as two numbers. In these cases it is simple to show well-formedness
      theorems. So, there is a version proving a WI_wfe theorem automatically. *)

   val mk_WI_end_of_nums      : hol_type -> Arbnum.num -> Arbnum.num -> term
   val mk_WI_size_of_nums     : hol_type -> Arbnum.num -> Arbnum.num -> term
   val mk_WI_end_of_nums_WFE  : hol_type -> Arbnum.num -> Arbnum.num -> term * thm
   val mk_WI_size_of_nums_WFE : hol_type -> Arbnum.num -> Arbnum.num -> term * thm

end
