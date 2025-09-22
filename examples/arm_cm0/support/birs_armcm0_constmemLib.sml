structure birs_armcm0_constmemLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;

  (* error handling *)
  val libname = "birs_armcm0_constmemLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

fun gen_const_load_32_32_cheat_thm (a,b) =
  let
    fun bir_const32 v = ``BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(v, 32)))``;
    val thm_tm = ``
    !pcond.
      birs_simplification
        pcond
        (BExp_Load
          (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
          ^(bir_const32 a)
          BEnd_LittleEndian
          Bit32)
        ^(bir_const32 b)
    ``;
  in
    aux_moveawayLib.mk_oracle_preserve_tags [] "BIRS_CONST_LOAD" (thm_tm)
  end;
val gen_const_load_32_32_cheat_thms = List.map gen_const_load_32_32_cheat_thm;

fun gen_binaryValues progbin_tm =
  (List.map
    ((fn (s,l) => 
      ((Arbnum.toInt o wordsSyntax.dest_word_literal) s,
       (List.map (Arbnum.toInt o wordsSyntax.dest_word_literal) o fst o listSyntax.dest_list) l)) o pairSyntax.dest_pair) o
    fst o listSyntax.dest_list)
  progbin_tm;
val int_to_hexstr = (fn s => "0x" ^ s) o Arbnum.toHexString o Arbnum.fromInt;
fun print_binaryValues_range binaryValues = List.map (fn (start, mappings) =>
  let
    val len = List.length mappings;
  in
    print ("[" ^ (int_to_hexstr start) ^ ", " ^ (int_to_hexstr (start + len)) ^ ")\n")
  end
) binaryValues;

fun find_binval (start, mappings) ad =
  let
    val idx = ad - start;
  in
    if 0 <= idx andalso idx < List.length mappings then
      SOME (List.nth(mappings, idx))
    else
      NONE
  end;

fun get_binval_w8 binaryValues ad =
  let
    fun foldfun (m, acc) =
      case acc of
          SOME x => SOME x
        | NONE => find_binval m ad;
    val v_o = List.foldl foldfun NONE binaryValues;
  in
    case v_o of
        SOME x => x
      | NONE => raise ERR "get_binval_w8" ("couldn't get the binary value @" ^ (int_to_hexstr ad))
  end;

fun power (x : int) (n : int) : int =
  if n = 0 then 1
  else 
    if (n mod 2) = 0 then 
      let val r = power x (n div 2) in r * r end
    else
      let val r = power x (n div 2) in r * r * x end;
fun lshift x n =
  x * (power 2 n);
fun get_binval_w32_le binaryValues ad =
  (lshift (get_binval_w8 binaryValues (ad+0)) 0) +
  (lshift (get_binval_w8 binaryValues (ad+1)) 8) +
  (lshift (get_binval_w8 binaryValues (ad+2)) 16) +
  (lshift (get_binval_w8 binaryValues (ad+3)) 24);

(*gen_const_load_32_32_cheat_thms [(0x10000DA0, 0x10000DA8)]*)
(*
val _ = print ((int_to_hexstr (get_binval_w32_le 0x10000DA0)) ^ "\n");
val _ = List.app (fn i => print ((int_to_hexstr (get_binval_w8 (0x10000DA0+i))) ^ "\n")) (List.tabulate (20, fn i => i - 10));
*)

(*
val prog_thm = balrobTheory.bir_balrob_progbin_def;
val progbin_tm = (rhs o concl) prog_thm;
*)
fun const_load_32_32_fromprog progbin_tm (ad_start, n) =
  List.tabulate (n, fn i => let val ad = ad_start + (4 * i) in (ad, get_binval_w32_le (gen_binaryValues progbin_tm) ad) end);

fun const_load_32_32_cheat_thms_fromprog progbin_tm (ad_start, n) =
  gen_const_load_32_32_cheat_thms (const_load_32_32_fromprog progbin_tm (ad_start, n));

fun const_load_32_32_cheat_thms_fromprog_range progbin_tm (from, to) =
  const_load_32_32_cheat_thms_fromprog progbin_tm (from, (to-from) div 4);

end (* local *)

end (* struct *)