signature bir_valuesSyntax =
sig
   include Abbrev

   (*************)
   (* bir_val_t *)
   (*************)

   (* The type itself *)
   val bir_val_t_ty : hol_type

   (* BVal_Unknown *)
   val BVal_Unknown_tm : term
   val is_BVal_Unknown : term -> bool

   (* BVal_Imm *)
   val BVal_Imm_tm   : term
   val dest_BVal_Imm : term -> term
   val is_BVal_Imm   : term -> bool
   val mk_BVal_Imm   : term -> term

   (* BVal_Mem *)
   val BVal_Mem_tm   : term
   val dest_BVal_Mem : term -> term * term * term
   val is_BVal_Mem   : term -> bool
   val mk_BVal_Mem   : term * term * term -> term

   (* BVal_Imm for concrete sizes *)
   val dest_BVal_Imm1    : term -> term
   val dest_BVal_Imm8    : term -> term
   val dest_BVal_Imm16   : term -> term
   val dest_BVal_Imm32   : term -> term
   val dest_BVal_Imm64   : term -> term
   val gen_dest_BVal_Imm : term -> int * term

   val is_BVal_Imm1    : term -> bool
   val is_BVal_Imm8    : term -> bool
   val is_BVal_Imm16   : term -> bool
   val is_BVal_Imm32   : term -> bool
   val is_BVal_Imm64   : term -> bool
   val gen_is_BVal_Imm : int -> term -> bool


   (* Memory that stores bytes is common, common
      adderess sizes are 32 or 64 bit.
      So let's provide special functions *)
   val mk_BVal_MemByte   : term * term -> term
   val dest_BVal_MemByte : term -> term * term
   val is_BVal_MemByte   : term -> bool

   val mk_BVal_MemByte_32   : term -> term
   val dest_BVal_MemByte_32 : term -> term
   val is_BVal_MemByte_32   : term -> bool

   val mk_BVal_MemByte_64   : term -> term
   val dest_BVal_MemByte_64 : term -> term
   val is_BVal_MemByte_64   : term -> bool


   (*****************)
   (* bir_type_t    *)
   (*****************)

   (* The type itself *)
   val bir_type_t_ty  : hol_type

   (* BType_Imm *)
   val BType_Imm_tm   : term
   val dest_BType_Imm : term -> term
   val is_BType_Imm   : term -> bool
   val mk_BType_Imm   : term -> term

   (* BType_Mem *)
   val BType_Mem_tm   : term
   val dest_BType_Mem : term -> term * term
   val is_BType_Mem   : term -> bool
   val mk_BType_Mem   : term * term -> term

   (* BType_Imm special sizes *)
   val gen_mk_BType_Imm   : int -> term
   val gen_dest_BType_Imm : term -> int * term
   val gen_is_BType_Imm   : int -> term -> bool

   val BType_Imm1_tm  : term
   val BType_Imm8_tm  : term
   val BType_Imm16_tm : term
   val BType_Imm32_tm : term
   val BType_Imm64_tm : term

   val is_BType_Imm1  : term -> bool
   val is_BType_Imm8  : term -> bool
   val is_BType_Imm16 : term -> bool
   val is_BType_Imm32 : term -> bool
   val is_BType_Imm64 : term -> bool

   (* BType_Bool is defined as BType_Imm1, so let's have
      a checker that recognizes both *)
   val BType_Bool_tm  : term
   val is_BType_Bool  : term -> bool
   val is_BType_Bool_Imm1 : term -> bool


   (* special memory sizes *)
   val mk_BType_MemByte    : term -> term
   val dest_BType_MemByte  : term -> term
   val is_BType_MemByte    : term -> bool

   val BType_MemByte_32_tm : term
   val BType_MemByte_64_tm : term


   (***************************)
   (* various functions       *)
   (***************************)

   val type_of_bir_val_tm   : term;
   val mk_type_of_bir_val   : term -> term;
   val dest_type_of_bir_val : term -> term;
   val is_type_of_bir_val   : term -> bool;

end
