structure bir_valuesSyntax :> bir_valuesSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_valuesTheory;
open bir_immSyntax;


val ERR = mk_HOL_ERR "bir_valuesSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_values"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;



(* bir_val_t *)

val bir_val_t_ty = mk_type ("bir_val_t", []);

val (BVal_Unknown_tm,  is_BVal_Unknown)  = syntax_fns0 "BVal_Unknown";
val (BVal_Imm_tm,  mk_BVal_Imm, dest_BVal_Imm, is_BVal_Imm)  = syntax_fns1 "BVal_Imm";
val (BVal_Mem_tm,  mk_BVal_Mem, dest_BVal_Mem, is_BVal_Mem)  = syntax_fns3 "BVal_Mem";

val dest_BVal_Imm1  = dest_Imm1 o dest_BVal_Imm
val dest_BVal_Imm8  = dest_Imm8 o dest_BVal_Imm
val dest_BVal_Imm16 = dest_Imm16 o dest_BVal_Imm
val dest_BVal_Imm32 = dest_Imm32 o dest_BVal_Imm
val dest_BVal_Imm64 = dest_Imm64 o dest_BVal_Imm
val gen_dest_BVal_Imm = gen_dest_Imm o dest_BVal_Imm

val is_BVal_Imm1  = can dest_BVal_Imm1;
val is_BVal_Imm8  = can dest_BVal_Imm8;
val is_BVal_Imm16 = can dest_BVal_Imm16;
val is_BVal_Imm32 = can dest_BVal_Imm32;
val is_BVal_Imm64 = can dest_BVal_Imm64;
fun gen_is_BVal_Imm n t = (fst (gen_dest_BVal_Imm t) = n) handle HOL_ERR _ => false;


fun mk_BVal_MemByte (aty, mf) = mk_BVal_Mem (aty, Bit8_tm, mf);

fun dest_BVal_MemByte tm = let
  val (aty, vty, mf) = dest_BVal_Mem tm;
  val _ = if is_Bit8 vty then () else fail();
in (aty, mf) end handle HOL_ERR _ =>
  raise ERR "dest_BVal_MemByte" "???";

val is_BVal_MemByte = can dest_BVal_MemByte;

fun mk_BVal_MemByte_32 mf = mk_BVal_Mem (Bit32_tm, Bit8_tm, mf);

fun dest_BVal_MemByte_32 tm = let
  val (aty, mf) = dest_BVal_MemByte tm;
  val _ = if is_Bit32 aty then () else fail();
in mf end handle HOL_ERR _ =>
  raise ERR "dest_BVal_MemByte_32" "???";

val is_BVal_MemByte_32 = can dest_BVal_MemByte_32;

fun mk_BVal_MemByte_64 mf = mk_BVal_Mem (Bit64_tm, Bit8_tm, mf);
fun dest_BVal_MemByte_64 tm = let
  val (aty, mf) = dest_BVal_MemByte tm;
  val _ = if is_Bit64 aty then () else fail();
in mf end handle HOL_ERR _ =>
  raise ERR "dest_BVal_MemByte_32" "???";

val is_BVal_MemByte_64 = can dest_BVal_MemByte_64;


(* bir_type_t *)

val bir_type_t_ty = mk_type ("bir_type_t", []);

val (BType_Imm_tm,  mk_BType_Imm,  dest_BType_Imm,  is_BType_Imm)  = syntax_fns1 "BType_Imm";
val (BType_Mem_tm,  mk_BType_Mem,  dest_BType_Mem,  is_BType_Mem)  = syntax_fns2 "BType_Mem";
val (BType_Bool_tm, is_BType_Bool) = syntax_fns0 "BType_Bool";

fun gen_mk_BType_Imm n = mk_BType_Imm (bir_immtype_t_of_size n);
val gen_dest_BType_Imm = gen_dest_Imm o dest_BType_Imm
fun gen_is_BType_Imm n t = (fst (gen_dest_BType_Imm t) = n) handle HOL_ERR _ => false;

val BType_Imm1_tm  = mk_BType_Imm Bit1_tm;
val BType_Imm8_tm  = mk_BType_Imm Bit8_tm;
val BType_Imm16_tm = mk_BType_Imm Bit16_tm;
val BType_Imm32_tm = mk_BType_Imm Bit32_tm;
val BType_Imm64_tm = mk_BType_Imm Bit64_tm;

val is_BType_Imm1  = aconv BType_Imm1_tm;
fun is_BType_Bool_Imm1 tm = is_BType_Bool tm orelse is_BType_Imm1 tm
val is_BType_Imm8  = aconv BType_Imm8_tm;
val is_BType_Imm16 = aconv BType_Imm16_tm;
val is_BType_Imm32 = aconv BType_Imm32_tm;
val is_BType_Imm64 = aconv BType_Imm64_tm;

fun mk_BType_MemByte aty = mk_BType_Mem (aty, Bit8_tm);

fun dest_BType_MemByte tm = let
  val (aty, vty) = dest_BType_Mem tm;
  val _ = if is_Bit8 vty then () else fail();
in aty end handle HOL_ERR _ =>
  raise ERR "dest_BType_MemByte" "???";

val is_BType_MemByte = can dest_BType_MemByte;

val BType_MemByte_32_tm = mk_BType_Mem (Bit32_tm, Bit8_tm);
val BType_MemByte_64_tm = mk_BType_Mem (Bit64_tm, Bit8_tm);
val is_BType_MemByte_32 = mk_BType_Mem (Bit32_tm, Bit8_tm);
val is_BType_MemByte_64 = mk_BType_Mem (Bit64_tm, Bit8_tm);



(* various functions *)

val (type_of_bir_val_tm, mk_type_of_bir_val, dest_type_of_bir_val, is_type_of_bir_val)  = syntax_fns1 "type_of_bir_val";


end
