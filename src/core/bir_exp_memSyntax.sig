signature bir_mem_expSyntax =
sig
   include Abbrev


   (*************************)
   (* bir_endian_t          *)
   (*************************)

   val bir_endian_t_ty : hol_type

   val BEnd_BigEndian_tm    : term
   val BEnd_LittleEndian_tm : term
   val BEnd_NoEndian_tm     : term

   val is_BEnd_BigEndian    : term -> bool
   val is_BEnd_LittleEndian : term -> bool
   val is_BEnd_NoEndian     : term -> bool


end
