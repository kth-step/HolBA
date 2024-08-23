open HolKernel Parse boolLib bossLib;

open wordsTheory;
open finite_mapTheory;

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
   ``),


  ("addition and simple memory constraint",
   ``
     (FAPPLY (mem0 : 32 word |-> 8 word) x = 0x45w) /\
     (x + y = 3w)
   ``),


  ("addition and two simple memory constraints",
   ``
     (FAPPLY (mem0 : 32 word |-> 8 word) x = 0x45w) /\
     (FAPPLY (mem0 : 32 word |-> 8 word) y = 0x28w) /\
     (x + y = 188w)
   ``),


  ("slightly more involving constraints (translated from original debug input)",
   ``
    (mem_ = (mem0 : 32 word |-> 8 word)
             |+ (addr1  + 0w, (7 >< 0)  (42w:word32))
             |+ (addr1  + 1w, (15 >< 8) (42w:word32))) /\

    (FAPPLY mem_ (addr2  + 0w) = (7 >< 0)  (42w:word32)) /\
    (FAPPLY mem_ (addr2  + 1w) = (15 >< 8) (42w:word32)) /\

    (mem0 = FUN_FMAP (K (0w)) (UNIV)) /\

    (addr1 = addr2)
   ``)
];



(*
val (name, query) = hd test_cases;
val test_cases = tl test_cases;
*)

(* check that all elements of l1 appear in l2 *)
fun list_inclusion eq_fun l1 l2 =
  foldl (fn (x, acc) => acc andalso (exists (fn y => eq_fun x y) l2)) true l1;

(* better than Portable.list_eq, because not order sensitive *)
fun mutual_list_inclusion eq_fun l1 l2 =
  list_inclusion eq_fun l1 l2 andalso
  length l1 = length l2;


local
 fun map_in_model m s =
  case List.find (fn (x,_) => x = s) m of
     NONE => raise Fail "could not find variable in model"
   | SOME x => snd x;

 val finite_word32_thm = prove(``FINITE (UNIV:word32->bool)``, cheat);
 val fmap_rewr_thm = MATCH_MP finite_mapTheory.FUN_FMAP_DEF finite_word32_thm;
 val word32_conr_thm = prove(``!x. (x :word32) IN (UNIV:word32->bool)``, cheat);
 val fmap_rewr_thms = [finite_mapTheory.FUN_FMAP_DEF, finite_word32_thm, word32_conr_thm];
in
 fun check_model query model =
  let
     val fvs = free_vars query;
      val fv_insts = foldl (fn (x, acc) => ((x, (map_in_model model o fst o dest_var) x)::acc)) [] fvs;
      val s = foldl (fn ((x,y),acc) => ((x |-> y)::acc)) [] fv_insts;
      val inst_tm = subst s query;
      val eval_thm = (EVAL THENC SIMP_CONV std_ss fmap_rewr_thms THENC EVAL) inst_tm;
      val res = identical T ((snd o dest_eq o concl) eval_thm);
  in
    (res, eval_thm)
  end;
end;

val _ = List.map (fn (name, query) =>
    let
      val _ = print ("\n\n=============== >>> RUNNING TEST CASE '" ^ name ^ "'\n");

      val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL query;
      val (res, eval_thm) = check_model query model;

      val _ = if res then () else (
            print "=============== >>> TEST CASE FAILED\n";
            print ("have: \n");
            PolyML.print model;
            print ("does not eval to T: \n");
            PolyML.print eval_thm;
            raise Fail ("unexpected result: " ^ name));

      val _ = print ("=============== >>> SUCCESS\n");
    in () end
  ) test_cases;


(* test of real input, cannot compare the model as it changes for different z3 versions *)
open holba_fileLib;

val filename = "z3_wrapper_test/z3_wrapper_input_z3_T5bnC5_sat";
val _ = print ("\n\n=============== >>> RUNNING TEST CASE FILE '" ^ filename ^ "'\n");

val output = holba_exec_wrapLib.get_exec_output ("../smt/z3_wrapper.py " ^ filename);

val result = String.substring (output, 0, 4) = "sat\n" andalso
             size output > 40;

val _ = if result then () else (
            print "=============== >>> TEST CASE FAILED\n"(*;
            raise Fail ("unexpected result. check the test case")*));
val _ = print ("=============== >>> SUCCESS\n");
        
