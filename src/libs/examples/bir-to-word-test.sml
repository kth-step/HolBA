open HolKernel Parse boolLib bossLib;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "../bir_exp_to_wordsLib"; (* ../ *)
  ()) else ();

open bir_exp_to_wordsLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = wordsLib.add_word_cast_printer ();
val _ = Globals.show_types := true;

(*
val _ = Globals.linewidth := 100;
val _ = Globals.show_assums := true;
val _ = Globals.show_tags := true;
*)

val bir_exprs = [
  ("32-bits constant", ``BExp_Const (Imm32 12345w)``),
  ("not equal", ``(BExp_UnaryExp BIExp_Not
                    (BExp_BinPred BIExp_Equal
                      (BExp_Den (BVar "x" (BType_Imm Bit32)))
                      (BExp_Const (Imm32 0w))))``),
  ("64-bits substraction", ``(BExp_BinExp BIExp_Minus
                               (BExp_Den (BVar "x" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 112w)))``),
  ("Less-than predicate", ``(BExp_BinPred BIExp_LessThan
                              (BExp_Den (BVar "x" (BType_Imm Bit128)))
                              (BExp_Const (Imm128 45867w)))``),
  ("If-then-else with less-than", ``(BExp_IfThenElse
                                      (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))
                                        (BExp_Const (Imm64 200w))
                                        (BExp_Const (Imm64 404w)))``),
  ("16-bit value store", ``(BExp_Store
                             (BExp_Den (BVar "memory" (BType_Mem Bit32 Bit8)))
                             (BExp_Den (BVar "address" (BType_Imm Bit32)))
                             BEnd_BigEndian
                             (BExp_Const (Imm16 (42w :word16))))``),
  ("128-bit value load", ``(BExp_Load
                             (BExp_Den (BVar "memory" (BType_Mem Bit64 Bit8)))
                             (BExp_Den (BVar "address" (BType_Imm Bit64)))
                             BEnd_LittleEndian
                             Bit128)``)
];

(* Simply prints all BIR expressions as words expressions. *)
val _ = List.foldr
  (fn ((name, bir_exp), _) => (print (name ^ ": "); Hol_pp.print_term (bir2w bir_exp); print "\n"))
  () bir_exprs;
