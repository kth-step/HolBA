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

val debug_on = false;

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
    val obs_id = Lib.assoc "obs_id" l
    val obs_cond = Lib.assoc "obs_cond" l
    val obs = Lib.assoc "obs" l
    val obs_fun = Lib.assoc "obs_fun" l
  in 
    (obs_id, obs_cond, obs, obs_fun)
  end handle HOL_ERR _ => raise ERR "dest_bir_symb_obs" ("cannot destruct term \"" ^ (term_to_string tm) ^ "\"");
(* ------------------------------------------------------------------- *)

(* Destruct symbolic state to decide wheter branch is still running *)
fun symb_is_BST_Running state = 
  let 
    val (pc, env, pres, status, obs) = dest_bir_symb_state state;
  in
    is_BST_Running status
  end;

fun symb_is_BST_Halted state = 
  let 
    val (pc, env, pres, status, obs) = dest_bir_symb_state state;
  in
    is_BST_Halted status
  end;

fun symb_is_BST_AssertionViolated state = 
  let 
    val (pc, env, pres, status, obs) = dest_bir_symb_state state;
  in
    status = ``BST_AssertionViolated``
  end;

(* We represent an Execution as a tree, where branches
 * in the Tree represent the Branches in the CFG *)
datatype 'a symb_tree_t = Symb_Node  of ('a  * 'a symb_tree_t list);

fun decide_pred pd s =
  let 
    val (pc, env, pred, status, obs) = dest_bir_symb_state s;
  in
    pd pred
  end;


(* The main function to execute a BIR Program:
 * Builds an Execution Tree  *)
(*
 val bp = bir_program;
 val st = state;
 *)
fun symb_exec_run max bp pd st = 
  if (not (symb_is_BST_Running st)) orelse (max = 0) then
    Symb_Node (st, [])
  else
    let
      val max_new = if max < 0 then max else (max-1);
      val (sts_running, sts_terminated) = 
              ((dest_pair o  rhs o concl o EVAL) ``bir_symb_exec_label_block ^bp ^st``);
      val sts_ter = (#1 (dest_list sts_terminated));
      val sts_run = (#1 (dest_list sts_running));
      val sts = (sts_ter @ sts_run);
      val sts_filtered = List.filter (decide_pred pd) sts;
      val _ = if not debug_on then () else
        let
	  val _ = print "=========================================\n";
	  val _ = print (Int.toString max);
	  val _ = print "\n=========================================\n";
        in () end;
      val sts_rec = List.map (symb_exec_run max_new bp pd) sts_filtered;
    in
      Symb_Node (st, sts_rec)
(*
      Symb_Node (st, (List.map (fn st' => Symb_Node (st', [])) (sts_ter @ sts_run)))
*)
    end;
   
(* Given a Program, exec until every branch halts *)
(*
val bir_program = ``BirProgram [] : 'observation_type bir_program_t``;

val bir_program = ``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
         bb_statements :=
         [BStmt_Assert
              (BExp_Const (Imm1 abc));
	   BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))])
                          (\x. x)];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm64 4w))|>]``;
*)
fun symb_exec_program depth precond bir_program rso pd envupdate_o =
  let 
    val env_ = init_env bir_program rso;
    val env = case envupdate_o of
                 NONE   => env_
               | SOME f => f env_;
    val state = (rhs o concl o EVAL)
                  ``bir_symb_state_init ^bir_program ^env ^precond``;
    val tree  = symb_exec_run depth bir_program pd state;
    val _ = print ("Execution: Done!\n");
   in 
     tree
   end;


fun symb_exec_leaflist (Symb_Node (s, [])) = [s]
  | symb_exec_leaflist (Symb_Node (_, l )) = List.concat (List.map symb_exec_leaflist l)
(*  | symb_exec_leaflist _  = raise ERR "symb_exec_leaflist" "this should not happen"*)
  ;

(* TODO: move this to lib and possibly merge to bir_expLib *)
  fun bir_exp_rewrite rwf exp =
      if is_BExp_Const exp then
        rwf exp
      else if is_BExp_MemConst exp then
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
