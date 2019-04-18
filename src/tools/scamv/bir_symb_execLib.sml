(* 
app load ["bir_symb_execTheory", "bir_symb_envTheory", "bir_symb_init_envLib"];
*)


open HolKernel
open bir_symb_execTheory;
open bir_symb_envTheory;
open bir_symb_init_envLib;
open listSyntax bir_programSyntax;

structure bir_symb_execLib = 
struct



(* In order to decide when we want to stop execution, we need 
 * to destruct the symbolic state 
 * Use method "is_BST_Running to decide wether we want to stop
 *)

(* -------------------- syntax functions ----------------------------- *)
val bir_symb_state_t_ty = mk_type ("bir_symb_state_t", []);
fun dest_bir_symb_state tm =
  let 
    val (ty, l) = TypeBase.dest_record tm 
    val _ = if ty = bir_symb_state_t_ty then () else fail()
    val pc = Lib.assoc "bsst_pc" l
    val env = Lib.assoc "bsst_environ" l
    val pred = Lib.assoc "bsst_pred" l
    val status = Lib.assoc "bsst_status" l
    val obs = Lib.assoc "bsst_obs" l
  in 
    (pc, env, pred, status, obs)
  end handle HOL_ERR _ => raise ERR "dest_bir_symb_state" ("cannot destruct term \"" ^ (term_to_string tm) ^ "\"");

val bir_symb_obs_t_ty = mk_type ("bir_symb_obs_t", []);
fun dest_bir_symb_obs tm =
  let 
    val (ty, l) = TypeBase.dest_record tm 
    val _ = if ty = bir_symb_obs_t_ty then () else fail()
    val obs_cond = Lib.assoc "obs_cond" l
    val obs = Lib.assoc "obs" l
  in 
    (obs_cond, obs)
  end handle HOL_ERR _ => raise ERR "dest_bir_symb_obs" ("cannot destruct term \"" ^ (term_to_string tm) ^ "\"");
(* ------------------------------------------------------------------- *)

(* Destruct symbolic state to decide wheter branch is still running *)
fun symb_is_BST_Running state = 
  let 
    val (pc, env, pres, status, obs) = dest_bir_symb_state state;
  in
    is_BST_Running status
  end;

(* We represent an Execution as a binary tree, where branches
 * in the Tree represent the Branches in the CFG *)
datatype 'a symb_tree_t = Symb_Empty | Symb_Node of ('a * 'a symb_tree_t * 'a symb_tree_t);

fun symb_exec_run bir_program tree =
    case tree of 
       (* Empty Tree: Nothing to execute *)
       Symb_Empty => let val _ = print ("Empty\n") in Symb_Empty end
     | Symb_Node (state, Symb_Empty, Symb_Empty) => 
         (if (symb_is_BST_Running state) then 
            (let 
                val _ = print ("Running!\n");
                val st_lst =  
                ((rhs o concl o EVAL) ``bir_symb_exec_label_block ^bir_program ^state``)
             in
                case (#1 (dest_list st_lst)) of 
                (* Only one follow-up state: Simply update the state *)
                [st] => 
                    (symb_exec_run bir_program (Symb_Node (st, Symb_Empty, Symb_Empty)))
                (* Two follow up states: "Fork" and execute both conditional
                 * branches *)
              | [st_l, st_r] => 
                    (Symb_Node (state, 
                        (symb_exec_run bir_program (Symb_Node (st_l, Symb_Empty, Symb_Empty))),
                        (symb_exec_run bir_program (Symb_Node (st_r, Symb_Empty, Symb_Empty)))))
              | _ => raise ERR "symb_exec_run" "More than two states" end)
        else 
          let val _ = print ("Branch stopped Running\n") in tree end)
     | _ => raise ERR "symb_exec_run" "Wrong Tree format";

(* Given a Program, exec until every branch halts *)
fun symb_exec_program bir_program =
  let 
    val env = init_env ();
    val state = 
        (rhs o concl o EVAL) ``bir_symb_state_init ^bir_program ^env``;
    val tree = 
        symb_exec_run bir_program (Symb_Node (state, Symb_Empty, Symb_Empty))
  in 
    let val _ = print ("Execution: Done!\n") in 
    tree end
  end;


fun symb_exec_leaflist Symb_Empty = raise ERR "symb_exec_leaflist" "this should not happen"
  | symb_exec_leaflist (Symb_Node (s, Symb_Empty, Symb_Empty)) = [s]
  | symb_exec_leaflist (Symb_Node (_, n1, Symb_Empty)) = symb_exec_leaflist n1
  | symb_exec_leaflist (Symb_Node (_, Symb_Empty, n2)) = symb_exec_leaflist n2
  | symb_exec_leaflist (Symb_Node (_, n1, n2)) = (symb_exec_leaflist n1)@(symb_exec_leaflist n2);

  
(*
In order to Execute a Program: 

val prog = (snd o dest_comb o concl) toy_arm8_THM; <-- replace program
val tree = symb_exec_program prog;
val tree = symb_exec_program prog_w_obs;
 *)
end
