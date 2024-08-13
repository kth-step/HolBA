structure ex_sum_listLib :> ex_sum_listLib =
struct

open HolKernel Parse bossLib boolLib ;
open ex_sum_listTheory ;
open bir_computeLib ;
open numSyntax ;

(* Create an initial state *)
fun create_state (n : int) : term =
  rhs (concl (EVAL ``start_state ^(term_of_int n)``)) ;

fun power (x : int) (n : int) : int =
  if n = 0 then 1
  else 
    if (n mod 2) = 0 then 
      let val r = power x (n div 2) in r * r end
    else
      let val r = power x (n div 2) in r * r * x end

fun benchmark_one_step () = 
let
  val n = power 2 10 ;
  val _ = print ("***** n : " ^ (Int.toString n) ^ " ***** \n") ;
  val _ = print "Creating initial state...\n" ;
  val start_state_tm = time create_state n ;
  
  val program_tm = lhs (concl sum_list_program_def) ; 
  (* We EVAL the program to have it in « canonical » form, 
  * that is without any variables / definition in it *)
  val program_evaled_thm = EVAL program_tm

  val _ = print "Starting measurements...\n" ;
  val _ = print "EVAL measurement...\n" ;
  val eval_value = time (compute_step_EVAL program_tm) start_state_tm ;

  val _ = print "cv measurement...\n" ;
  val _ = translate_program_cv program_evaled_thm ;
  val cv_value = time (compute_step_cv program_evaled_thm) start_state_tm ;

  (* val _ = assert (fn x => (Term.compare (x, (rhs (concl cv_value))) = EQUAL)) (rhs (concl eval_value)) *)
in 
  ()
end





end

