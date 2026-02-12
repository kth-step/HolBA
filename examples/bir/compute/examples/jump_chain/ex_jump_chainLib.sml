(* ------------------------------------------------------------------------- *)
(*  Example where the program is a long chain of jumps                       *)
(* ------------------------------------------------------------------------- *)


structure ex_jump_chainLib :> ex_jump_chainLib =
struct

open HolKernel Parse bossLib boolLib;
open bir_programTheory bir_programSyntax;
open stringSyntax;
open bir_computeLib;

fun create_block (n : int) : term = 
let val name = "block_" ^ (Int.toString n);
  val label_name = stringSyntax.fromMLstring name;
  val next_name = "block_" ^ (Int.toString (n + 1));
  val next_label_name = fromMLstring next_name;
in ``<|bb_label := BL_Label (^label_name); bb_statements := [];
  bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label (^next_label_name)))|> ``
end;

fun generate_big_program (n : int) = 
let fun aux n k blist = if n = 0 then blist else aux (n-1) (k+1) ((create_block k)::blist)
  val blist = rev $ aux n 0 [];
  val blist_tm = listSyntax.mk_list (blist, ``:bir_block_t``);
in bir_programSyntax.mk_program blist_tm end;


val init_state_tm = ``<|bst_pc := <| bpc_label := BL_Label "block_0"; 
  bpc_index := 0 |>; bst_environ := bir_empty_env; bst_status := BST_Running |>``;

fun power (x : int) (n : int) : int =
  if n = 0 then 1
  else 
    if (n mod 2) = 0 then 
      let val r = power x (n div 2) in r * r end
    else
      let val r = power x (n div 2) in r * r * x end;



fun benchmark_one_step () =
let
  val n = power 2 10;

  val program_tm = generate_big_program n;
  val program_def = Define `big_program = ^program_tm`;

  val _ = print "Starting measurements...\n";
  val _ = print "EVAL measurement...\n";
  val eval_value = time (compute_step_EVAL program_tm) init_state_tm;

  val _ = print "cv measurement...\n";
  val _ = print "Starting cv translation...\n";
  val _ = time translate_program_cv program_def;
  val cv_value = compute_step_cv program_def init_state_tm;

  val _ = assert (fn x => (Term.compare (x, (rhs (concl cv_value))) = EQUAL)) (rhs (concl eval_value))
in () end;

end
