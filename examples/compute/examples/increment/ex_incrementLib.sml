(* ------------------------------------------------------------------------- *)
(*  Library for benchmarking increment example                               *)
(* ------------------------------------------------------------------------- *)

structure ex_incrementLib :> ex_incrementLib =
struct

open HolKernel Parse bossLib boolLib;
open bir_basicTheory;
open ex_incrementTheory;
open bir_computeLib;


fun generate_bigger_inc (term:term) (n:int) : term =
  if n = 0 then term else 
    generate_bigger_inc ``BExp_BinExp BIExp_Plus (^term) (^term)`` (n-1);

fun power (x : int) (n : int) : int =
  if n = 0 then 1
  else 
    if (n mod 2) = 0 then 
      let val r = power x (n div 2) in r * r end
    else
      let val r = power x (n div 2) in r * r * x end;



fun benchmark () = 
let
  (* val n = power 2 4; *)
  val n = 14;
  val _ = print ("***** n : " ^ (Int.toString n) ^ " ***** \n");
  val unamed_term = rhs (concl increment_exp_def);

  val _ = print "Generating term...\n";
  val big_term = time (generate_bigger_inc unamed_term) n;
  val _ = print "Finished generating !\n";

  val _ = print "Creating big_term definition...\n";
  val exp_def = time (xDefine "big_term") `big_term = ^big_term`;
  val env = ``start_env 3w``;

  val _ = print "Starting measurements...\n";
  val _ = print "EVAL measurement...\n";
  val eval_value = time (compute_exp_EVAL ``big_term``) env;

  val _ = print "cv measurement...\n";
  val _ = translate_exp_cv exp_def;
  val cv_value = compute_exp_cv exp_def env;

  val _ = assert (fn x => (Term.compare (x, (rhs (concl cv_value))) = EQUAL)) (rhs (concl eval_value ))
in 
  ()
end;




end
