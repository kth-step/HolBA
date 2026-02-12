structure ex_cv_sum_listLib :> ex_cv_sum_listLib =
struct

open HolKernel Parse bossLib boolLib;
open ex_cv_sum_listTheory;
open bir_computeLib;
open numSyntax;
open cv_transLib;

(* Create an initial state *)
fun create_state (n : int) : term =
  rhs (concl (EVAL ``cv_start_state ^(term_of_int n)``));

fun power (x : int) (n : int) : int =
  if n = 0 then 1
  else 
    if (n mod 2) = 0 then 
      let val r = power x (n div 2) in r * r end
    else
      let val r = power x (n div 2) in r * r * x end;

fun benchmark_one_step () = 
let
  val n = power 2 15;
  val _ = print ("***** n : " ^ (Int.toString n) ^ " ***** \n");
  val _ = print "Creating initial state...\n";
  val start_state_tm = time create_state n;
  
  val program_tm = lhs (concl cv_sum_list_program_def); 
  (* We EVAL the program to have it in « canonical » form, 
  * that is without any variables / definition in it *)
  val program_evaled_thm = EVAL program_tm;
  val program_evaled_tm = rhs (concl program_evaled_thm);

  val _ = print "Starting measurements...\n";
  val _ = print "EVAL measurement...\n";
  val eval_value = time EVAL ``bir_cv_compute_step ^program_tm ^start_state_tm``;


  val _ = print "cv measurement...\n";
  val embed_program_def = deep_embed_program "cv_sum_list" program_evaled_tm;
  val embed_program_tm = rhs (concl embed_program_def);

  val embed_state_def = deep_embed_state "cv_sum_list" start_state_tm;
  val embed_state_tm = lhs (concl embed_state_def);

  val _ = print "Using cv_eval...\n";
  val cv_value = time cv_eval ``bir_cv_compute_step ^embed_program_tm ^embed_state_tm``;

  val _ = assert (fn x => (Term.compare (x, (rhs (concl cv_value))) = EQUAL)) (rhs (concl eval_value))
in 
  ()
end;





end

