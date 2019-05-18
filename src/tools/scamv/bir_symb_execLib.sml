structure bir_symb_execLib :> bir_symb_execLib = 
struct

local
(* 
app load ["bir_symb_execTheory", "bir_symb_envTheory", "bir_symb_init_envLib"];
*)

open HolKernel
open pairLib
open bir_symb_execTheory;
open bir_symb_envTheory;
open bir_symb_init_envLib;
open listSyntax bir_programSyntax;

open bir_immSyntax;
open bir_expSyntax;
open bir_envSyntax;

in

(* In order to decide when we want to stop execution, we need 
 * to destruct the symbolic state 
 * Use method "is_BST_Running to decide wether we want to stop
 *)

(* -------------------- syntax functions ----------------------------- *)
(* val bir_symb_state_t_ty = mk_type ("bir_symb_state_t", []); *)
fun dest_bir_symb_state tm =
  let 
    val (ty, l) = TypeBase.dest_record tm 
    val _ = if is_type ty andalso
               (fst o dest_type) ty = "bir_symb_state_t" andalso
               (length o snd o dest_type) ty = 1
            then () else fail()
    val pc = Lib.assoc "bsst_pc" l
    val env = Lib.assoc "bsst_environ" l
    val pred = Lib.assoc "bsst_pred" l
    val status = Lib.assoc "bsst_status" l
    val obs = Lib.assoc "bsst_obs" l
  in 
    (pc, env, pred, status, obs)
  end handle HOL_ERR _ => raise ERR "dest_bir_symb_state" ("cannot destruct term \"" ^ (term_to_string tm) ^ "\"");

(*val bir_symb_obs_t_ty = mk_type ("bir_symb_obs_t", []);*)
fun dest_bir_symb_obs tm =
  let 
    val (ty, l) = TypeBase.dest_record tm 
    val _ = if is_type ty andalso
               (fst o dest_type) ty = "bir_symb_obs_t" andalso
               (length o snd o dest_type) ty = 1
            then () else fail()
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
datatype 'a symb_tree_t =
        Symb_Empty 
      | Symb_Node of ('a  * 'a symb_tree_t * 'a symb_tree_t);


(* The main function to execute a BIR Program:
 * Builds an Execution Tree and additionally 
 * returns a list with state of AssertionViolated states *)
fun symb_exec_run bir_program tree assert_list_ref = 
  case tree of
      (* Nothing to do here. *)
      Symb_Empty => (Symb_Empty, !assert_list_ref)
      (* Continue Execution. *)
    | Symb_Node (state, Symb_Empty, Symb_Empty) => 
        if (symb_is_BST_Running state) then 
          let 
            val (st_assert_lst, st_running_lst) = 
              ((dest_pair o  rhs o concl o EVAL) ``bir_symb_exec_label_block ^bir_program ^state``);
            val st_assert_lst_dest = (#1 (dest_list st_assert_lst));
          in 
            (* Collect the AssertionViolated States *)
            assert_list_ref := !assert_list_ref @ st_assert_lst_dest;
            case (#1 (dest_list st_running_lst)) of 
                (* If only one follow-up state: Simply continue with this State *)
                [st] => 
                  (symb_exec_run bir_program (Symb_Node (st, Symb_Empty,
                   Symb_Empty)) assert_list_ref)
                (* If two states: Continue with both *)
              | [st_l, st_r] => 
                  let 
                  val (node_l, _)  = 
                    symb_exec_run bir_program (Symb_Node (st_l, Symb_Empty, Symb_Empty)) assert_list_ref;
                  val (node_r, _) =
                    symb_exec_run bir_program (Symb_Node (st_r, Symb_Empty, Symb_Empty)) assert_list_ref;
                  in
                    (Symb_Node (state, node_l, node_r), !assert_list_ref)
                   end
              | _ => raise ERR "symb_exec_run" "Too many states after executing  BB."
          end 
        else
          (tree, !assert_list_ref)
    | _ => raise ERR "symb_exec_run" "Wrong Tree Format.";

   
(* Given a Program, exec until every branch halts *)
(*
val bir_program = ``BirProgram [] : 'observation_type bir_program_t``;
*)
fun symb_exec_program bir_program =
  let 
    val env = init_env ();
    val state = 
        (rhs o concl o EVAL) ``bir_symb_state_init ^bir_program ^env``;
    val st_assert_lst_ref = ref [];
    val (tree, st_assert_lst)  = 
        symb_exec_run bir_program (Symb_Node (state, Symb_Empty, Symb_Empty))
        st_assert_lst_ref;
   in 
    let val _ = print ("Execution: Done!\n") in 
    (tree, st_assert_lst)  end
  end;


fun symb_exec_leaflist Symb_Empty = raise ERR "symb_exec_leaflist" "this should not happen"
  | symb_exec_leaflist (Symb_Node (s, Symb_Empty, Symb_Empty))  = [s]
  | symb_exec_leaflist (Symb_Node (_, n1, Symb_Empty)) = symb_exec_leaflist n1
  | symb_exec_leaflist (Symb_Node (_, Symb_Empty, n2)) = symb_exec_leaflist n2
  | symb_exec_leaflist (Symb_Node (_, n1, n2)) = (symb_exec_leaflist n1)@(symb_exec_leaflist n2);

fun symb_exec_leaflist_complete tree st_assert_lst = 
    (symb_exec_leaflist tree) @ st_assert_lst;

(* TODO: move this to lib and possibly merge to bir_expLib *)
  fun bir_exp_rewrite rwf exp =
      if is_BExp_Const exp then
        rwf exp

      else if is_BExp_Den exp then
        rwf exp

      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val exp_rw = bir_exp_rewrite rwf exp;
        in
          rwf (mk_BExp_Cast (castt, exp_rw, sz))
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val exp_rw = bir_exp_rewrite rwf exp;
        in
          rwf (mk_BExp_UnaryExp (uop, exp_rw))
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val exp1_rw = bir_exp_rewrite rwf exp1;
          val exp2_rw = bir_exp_rewrite rwf exp2;
        in
          rwf (mk_BExp_BinExp (bop, exp1_rw, exp2_rw))
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val exp1_rw = bir_exp_rewrite rwf exp1;
          val exp2_rw = bir_exp_rewrite rwf exp2;
        in
          rwf (mk_BExp_BinPred (bpredop, exp1_rw, exp2_rw))
        end

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
          val expc_rw = bir_exp_rewrite rwf expc;
          val expt_rw = bir_exp_rewrite rwf expt;
          val expf_rw = bir_exp_rewrite rwf expf;
        in
          rwf (mk_BExp_IfThenElse (expc_rw, expt_rw, expf_rw))
        end

      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val expm_rw = bir_exp_rewrite rwf expm;
          val expad_rw = bir_exp_rewrite rwf expad;
        in
          rwf (mk_BExp_Load (expm_rw, expad_rw, endi, sz))
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val expm_rw = bir_exp_rewrite rwf expm;
          val expad_rw = bir_exp_rewrite rwf expad;
          val expv_rw = bir_exp_rewrite rwf expv;
        in
          rwf (mk_BExp_Store (expm_rw, expad_rw, endi, expv_rw))
        end

      else
        raise (ERR "bir_exp_rewrite" ("don't know BIR expression: \"" ^ (term_to_string exp) ^ "\""))
      ;

local
  open bir_valuesSyntax;
in
(*
val exp = ``BExp_Const (Imm32 r1)``;
*)
  val bir_exp_hvar_to_bvar_bexp = bir_exp_rewrite (fn exp => if not (is_BExp_Const exp) then exp else
        let val (imm_t_i, w) = (gen_dest_Imm o dest_BExp_Const) exp in
          if not (is_var w) then exp else
          let val (v_n, v_t) = dest_var w in
            (mk_BExp_Den o mk_BVar_string) (v_n, mk_BType_Imm(bir_immtype_t_of_word_ty v_t))
          end
        end);

(*
 this function tolerates lists and maps bir_exp_hvar_to_bvar_bexp
   to the list elements, or applies it directly
 *)
  fun bir_exp_hvar_to_bvar t =
    if is_list t then
      let
        val (t_l, t_t) = dest_list t;
      in
        mk_list (List.map bir_exp_hvar_to_bvar_bexp t_l, t_t)
      end
    else
      bir_exp_hvar_to_bvar_bexp t;

end

  
(*
In order to Execute a Program: 

val prog = (snd o dest_comb o concl) toy_arm8_THM; <-- replace program
val (tree, st_assert_lst) = symb_exec_program prog_w_obs;
val sts = symb_exec_leaflist_complete tree st_assert_lst;
 *)
end (* local *)

end (* struct *)
