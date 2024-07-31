(* ------------------------------------------------------------------------- *)
(*  Library for benchmarking mem_incr example                                *)
(* ------------------------------------------------------------------------- *)

structure ex_mem_incrLib :> ex_mem_incrLib =
struct

open HolKernel Parse bossLib boolLib;
open bir_basicTheory ;
open ex_mem_incrTheory ;
open bir_computeLib ;
open wordsTheory ;
open numSyntax ;


fun generate_bigger_inc (term:term) (n:int) : term =
  if n = 0 then term else 
    generate_bigger_inc 
    `` 
    BExp_Store (BExp_Den mem_var) (mem_addr (n2w ^(term_of_int (n-1)))) BEnd_BigEndian
      (BExp_BinExp BIExp_Plus 
        (BExp_Load (^term) (mem_addr (n2w ^(term_of_int n))) BEnd_BigEndian Bit8)
        (BExp_Load (^term) (mem_addr (n2w ^(term_of_int n))) BEnd_BigEndian Bit8))
    `` (n-1)

fun power (x : int) (n : int) : int =
  if n = 0 then 1
  else 
    if (n mod 2) = 0 then 
      let val r = power x (n div 2) in r * r end
    else
      let val r = power x (n div 2) in r * r * x end



fun benchmark () = 
let
  (* val n = power 2 4 ; *)
  val n = 12 ;
  val n_tm = term_of_int n ;
  val _ = print ("***** n : " ^ (Int.toString n) ^ " ***** \n") ;
  val unamed_term = rhs (concl (SPEC ``(n2w ^n_tm):word64`` mem_incr_exp_def)) ;

  val _ = print "Generating term...\n" ;
  val big_term = time (generate_bigger_inc unamed_term) n ;
  val _ = print "Finished generating !\n" ;
  val _ = print "Cleaning the term by EVALing...\n" ;
  val big_term_clean = rhs (concl (time EVAL big_term)) ;

  val _ = print "Creating big_term definition...\n" ;
  val exp_def = time (xDefine "big_term_clean") `big_term_clean = ^big_term_clean` ;
  val env = ``start_env ^n_tm 5`` ;

  val _ = print "Starting measurements...\n" ;
  val _ = print "EVAL measurement...\n" ;
  val eval_value = time (compute_exp_EVAL ``big_term_clean``) env ;

  val _ = print "cv measurement...\n" ;
  val _ = translate_exp_cv exp_def ;
  val cv_value = time (compute_exp_cv exp_def) env ;

  val _ = assert (fn x => (Term.compare (x, (rhs (concl cv_value))) = EQUAL)) (rhs (concl eval_value ))
in 
  ()
end




end
