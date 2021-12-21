open HolKernel Parse boolLib bossLib;

open bir_angrLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

val _ = print "Parsing test cases\n";

val angr_exp_testcases = [
  ("<Bool (R27_3_64[7:0] & 7#8) == 0#8>",
   ``BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
         (BExp_CastMask Bit64 7 0 (BExp_Den (BVar "R27" (BType_Imm Bit64)))
            (THE (bir_immtype_of_size 8))) (BExp_Const (Imm8 7w)))
      (BExp_Const (Imm8 0w))``)
(*
  ,("<...>",
    ``T``)
*)
];

val _ = print "Running and checking test cases\n";

val fail_ref = ref false;
val num_success = ref 0;
val _ = List.map (fn (calripyexp, expectedterm) =>
  let
    val res = bir_angrLib.parse_guard calripyexp;
    val _ = if identical res expectedterm then (num_success := (!num_success + 1)) else (
            fail_ref := true;
            print ("--------------------------------------\n");
            print ("+++ test input: \n");
            PolyML.print calripyexp;
            print ("+++ have as result: \n");
            print_term res;
            print ("+++ expecting: \n");
            print_term expectedterm;
            print ("\n\n"));
  in () end) angr_exp_testcases;

val _ = print ("\n\n" ^ "number of successful test cases: " ^ (Int.toString (!num_success)) ^ "\n\n");

val _ = if not(!fail_ref) then () else
        raise Fail "some test case(s) failed";
