open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

(*
(* trace that also controls whether temporary z3 input files are preserved *)
val _ = HolBA_Library.trace := 100;
*)


val test_cases = [
  ("simple addition",
   ``
     (x:word32) + y = 10w
   ``,
   [("y", ``0w:word32``), ("x", ``10w:word32``)]),


  ("addition and simple memory constraint",
   ``
     (FAPPLY (mem0 : 32 word |-> 8 word) x = 0x45w) /\
     (x + y = 3w)
   ``,
   [("y", ``0w:word32``), ("x", ``3w:word32``),
    ("mem0", ``FUN_FMAP (K (69w) :word32 -> word8) UNIV``)]),


  ("addition and two simple memory constraints",
   ``
     (FAPPLY (mem0 : 32 word |-> 8 word) x = 0x45w) /\
     (FAPPLY (mem0 : 32 word |-> 8 word) y = 0x28w) /\
     (x + y = 188w)
   ``,
   [("mem0",``((FUN_FMAP (K (40w :word8)) UNIV)  :word32 |-> word8)
       |+ (0w,40w) |+ (188w,69w)``),
    ("y", ``0w:word32``), ("x", ``188w:word32``)]),


  ("slightly more involving constraints (translated from original debug input)",
   ``
    (mem_ = (mem0 : 32 word |-> 8 word)
             |+ (addr1  + 0w, (7 >< 0)  (42w:word32))
             |+ (addr1  + 1w, (15 >< 8) (42w:word32))) /\

    (FAPPLY mem_ (addr2  + 0w) = (7 >< 0)  (42w:word32)) /\
    (FAPPLY mem_ (addr2  + 1w) = (15 >< 8) (42w:word32)) /\

    (mem0 = FUN_FMAP (K (0w)) (UNIV)) /\

    (addr1 = addr2)
   ``,
   [("mem_", ``(FUN_FMAP (K 0w) UNIV :word32 |-> word8)
                |+ (0w,42w) |+ (1w,0w)``),
    ("mem0", ``FUN_FMAP (K 0w) UNIV  :word32 |-> word8``),
    ("addr2", “(0w :word32)”), ("addr1", “(0w :word32)”)])
];



(*
val (name, query, expected) = hd test_cases;
*)

val _ = List.map (fn (name, query, expected) =>
    let
      val _ = print ("\n\n=============== >>> RUNNING TEST CASE '" ^ name ^ "'\n");

      val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL query;

      (* TODO: improve comparison to not be order sensitive *)
      val eq_fun = Portable.list_eq (pair_eq (fn (a:string) => fn b => a = b) identical);

      val _ = if eq_fun model expected then () else (
            print "=============== >>> TEST CASE FAILED\n";
            print ("have: \n");
            PolyML.print model;
            print ("expecting: \n");
            PolyML.print expected;
            raise Fail ("unexpected result: " ^ name));

      val _ = print ("=============== >>> SUCCESS\n");
    in () end
  ) test_cases;


(* test of real input, comparison. it is quite rigid in terms of output requirement *)
open bir_fileLib;

val filename = "z3_wrapper_test/z3_wrapper_input_z3_T5bnC5_sat";
val _ = print ("\n\n=============== >>> RUNNING TEST CASE FILE '" ^ filename ^ "'\n");

val expected_output = read_from_file (filename ^ "_expectedoutput");

val output = bir_exec_wrapLib.get_exec_output ("../z3_wrapper.py " ^ filename);

val _ = if output = expected_output then () else (
            print "=============== >>> TEST CASE FAILED\n";
            raise Fail ("unexpected result. check the test case"));
val _ = print ("=============== >>> SUCCESS\n");
        
