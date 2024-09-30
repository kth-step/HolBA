structure birsSyntax =
struct

local

open HolKernel Parse boolLib bossLib;

open symb_recordTheory;
open birs_auxTheory;

  (* error handling *)
  val libname = "birSyntax"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "option"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
in
 val (OPTION_BIND_tm,  mk_OPTION_BIND, dest_OPTION_BIND, is_OPTION_BIND)  = syntax_fns2 "OPTION_BIND";
end;

local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
 open bir_programTheory;
in
 val (bir_get_current_statement_tm,  mk_bir_get_current_statement, dest_bir_get_current_statement, is_bir_get_current_statement)  = syntax_fns2 "bir_get_current_statement";
end;

(*
local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "symb_record"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
in
 val (symb_hl_step_in_L_sound_tm,  mk_symb_hl_step_in_L_sound, dest_symb_hl_step_in_L_sound, is_symb_hl_step_in_L_sound)  = syntax_fns2 "symb_hl_step_in_L_sound";
end;
*)

local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "birs_aux"
  val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
  val syntax_fns1_env = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
  val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
in
  val (birs_gen_env_tm,  mk_birs_gen_env, dest_birs_gen_env, is_birs_gen_env)  = syntax_fns1_env "birs_gen_env";
  val (birs_exps_of_senv_tm,  mk_birs_exps_of_senv, dest_birs_exps_of_senv, is_birs_exps_of_senv)  = syntax_fns1_set "birs_exps_of_senv";
end;

local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "birs_rules"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
  val syntax_fns2_set = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop;
in
  val (birs_symb_exec_tm,  mk_birs_symb_exec, dest_birs_symb_exec, is_birs_symb_exec)  = syntax_fns2 "birs_symb_exec";
  val (birs_symb_symbols_set_tm,  mk_birs_symb_symbols_set, dest_birs_symb_symbols_set, is_birs_symb_symbols_set)  = syntax_fns1_set "birs_symb_symbols_set";
  val (birs_freesymbs_tm,  mk_birs_freesymbs, dest_birs_freesymbs, is_birs_freesymbs)  = syntax_fns2_set "birs_freesymbs";
end;

local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb";
  val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns2_env = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns2_set = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val syntax_fns3_set = syntax_fns 4 HolKernel.dest_triop HolKernel.mk_triop;
in
 val (birs_senv_typecheck_tm,  mk_birs_senv_typecheck, dest_birs_senv_typecheck, is_birs_senv_typecheck)  = syntax_fns2 "birs_senv_typecheck";
 
 val (birs_update_env_tm,  mk_birs_update_env, dest_birs_update_env, is_birs_update_env)  = syntax_fns2_env "birs_update_env";
 
 val (birs_exec_step_tm,  mk_birs_exec_step, dest_birs_exec_step, is_birs_exec_step)  = syntax_fns2_set "birs_exec_step";
 
 val (birs_symb_to_symbst_tm,  mk_birs_symb_to_symbst, dest_birs_symb_to_symbst, is_birs_symb_to_symbst)  = syntax_fns1 "birs_symb_to_symbst";
 
 val (birs_symbval_concretizations_tm,  mk_birs_symbval_concretizations, dest_birs_symbval_concretizations, is_birs_symbval_concretizations)  = syntax_fns2_set "birs_symbval_concretizations";

 val (birs_eval_label_exp_tm,  mk_birs_eval_label_exp, dest_birs_eval_label_exp, is_birs_eval_label_exp)  = syntax_fns3 "birs_eval_label_exp";

 val (birs_eval_exp_tm,  mk_birs_eval_exp, dest_birs_eval_exp, is_birs_eval_exp)  = syntax_fns2 "birs_eval_exp";

 val (birs_exec_stmt_jmp_tm,  mk_birs_exec_stmt_jmp, dest_birs_exec_stmt_jmp, is_birs_exec_stmt_jmp)  = syntax_fns3_set "birs_exec_stmt_jmp";
 val (birs_exec_stmt_tm,  mk_birs_exec_stmt, dest_birs_exec_stmt, is_birs_exec_stmt)  = syntax_fns3_set "birs_exec_stmt";

 val birs_state_t_ty = mk_type ("birs_state_t", []);
 fun dest_birs_state tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if ty = birs_state_t_ty then () else fail()
  val pc = Lib.assoc "bsst_pc" l
  val env = Lib.assoc "bsst_environ" l
  val status = Lib.assoc "bsst_status" l
  val pcond = Lib.assoc "bsst_pcond" l
 in
  (pc, env, status, pcond)
 end handle e => (print_term tm; raise wrap_exn "dest_bir_state" e);

 val is_birs_state = can dest_birs_state;

 fun mk_birs_state (pc, env, status, pcond) = let
  val l = [("bsst_pc", pc),
           ("bsst_environ", env),
           ("bsst_status", status),
           ("bsst_pcond", pcond)];
 in
  TypeBase.mk_record (birs_state_t_ty, l)
 end handle e => raise wrap_exn "mk_birs_state" e;

 (* val (_tm,  mk_, dest_, is_)  = syntax_fns2_set "";*)
end

local
  open bir_symb_sound_coreTheory;
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb_sound_core";
  val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
in
  val (birs_symb_symbols_tm,  mk_birs_symb_symbols, dest_birs_symb_symbols, is_birs_symb_symbols)  = syntax_fns1_set "birs_symb_symbols";
end

local
  open bir_symb_simpTheory;
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb_simp";
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
in
  val (birs_simplification_tm,  mk_birs_simplification, dest_birs_simplification, is_birs_simplification)  = syntax_fns3 "birs_simplification";
  val (birs_exp_imp_tm,  mk_birs_exp_imp, dest_birs_exp_imp, is_birs_exp_imp)  = syntax_fns2 "birs_exp_imp";
end

(*
fun is_IMAGE_birs_symb_to_symbst Pi = pred_setSyntax.is_image Pi andalso (identical birs_symb_to_symbst_tm o fst o pred_setSyntax.dest_image) Pi;
fun dest_IMAGE_birs_symb_to_symbst Pi =
  let
    val (im_fun_tm, im_set_tm) = (pred_setSyntax.dest_image) Pi;
    val _ = if identical birs_symb_to_symbst_tm im_fun_tm then () else
            raise ERR "dest_IMAGE_birs_symb_to_symbst" "image function has to be birs_symb_to_symbst";
  in
    im_set_tm
  end;
  *)

(* ====================================================================================== *)

(* helpers to check if sound structure terms (and subterms) are in normalform *)
(* ----------------------------------------------- *)
    (*
    val bir_state_init = ``<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>;
      bsst_environ :=
                 birs_gen_env
                    [("x15",BExp_Den (BVar "sy_x15" (BType_Imm Bit64)));
                     ("x13",BExp_Den (BVar "sy_x13" (BType_Imm Bit64)));
                     ("x14",BExp_Den (BVar "sy_x14" (BType_Imm Bit64)));
                     ("x10",BExp_Den (BVar "sy_x10" (BType_Imm Bit64)));
                     ("MEM8",
                      BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)));
                     ("x2",BExp_Den (BVar "sy_x2" (BType_Imm Bit64)));
                     ("x1",BExp_Den (BVar "sy_x1" (BType_Imm Bit64)))];
      bsst_status := BST_Running;
      bsst_pcond :=
        BExp_BinExp BIExp_And
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0xFFFFFFw))
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
             (BExp_Aligned Bit32 2
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
          (BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>``;
    *)
    fun birs_state_is_normform tm =
      is_birs_state tm andalso
      let
        val (_, env, _, _) = dest_birs_state tm;
      in
        is_birs_gen_env env
      end;

    fun is_a_normform_set tm =
      can pred_setSyntax.strip_set tm;

    fun birs_states_are_normform tm =
      is_a_normform_set tm andalso
      (List.all birs_state_is_normform o pred_setSyntax.strip_set) tm;


    fun birs_state_is_normform_CONV sfun bstate_tm =
      (if (birs_state_is_normform) bstate_tm then () else
            (print_term bstate_tm;
             raise ERR (sfun^"::birs_state_is_normform_CONV") "something is not right, the input state is not as expected");
       REFL bstate_tm);

    fun birs_states_are_normform_CONV sfun bstates_tm =
      (if (birs_states_are_normform) bstates_tm then () else
            (print_term bstates_tm;
             raise ERR (sfun^"::birs_states_are_normform_CONV") "something is not right, the produced theorem is not evaluated enough");
       REFL bstates_tm);

    fun birs_states_are_normform_CONV_with_start sfun bstate_tm bstates_tm =
        birs_states_are_normform_CONV sfun bstates_tm
	handle e => (print "\n[[[[\n"; print_term bstate_tm; print "\n]]]]\n"; raise e);



(* extract information from a sound structure *)
(* ----------------------------------------------- *)
fun symb_sound_struct_get_sysLPi_fun tm =
  let
    val sysLPi_tm =
      (snd o dest_birs_symb_exec) tm;
    val res =
      case pairSyntax.strip_pair sysLPi_tm of
         [sys_tm, L_tm, Pi_tm] => (sys_tm, L_tm, Pi_tm)
       | _ => raise ERR "symb_sound_struct_get_sysLPi_fun" "unexpected structure triple";
  in
    res
  end;
  
(*
val Pi_tm = Pi_A_tm;
*)
fun symb_sound_struct_Pi_to_birstatelist_fun Pi_tm =
  pred_setSyntax.strip_set Pi_tm;

(* check if sound structure term is in normalform *)
(* ----------------------------------------------- *)
fun symb_sound_struct_is_normform tm =
  let
    val (sys, L, Pi) = symb_sound_struct_get_sysLPi_fun tm
                       handle _ => raise ERR "symb_sound_struct_is_normform" "unexpected term, should be a birs_symb_exec with a triple as structure";

    val sys_ok = birs_state_is_normform sys;
    val L_ok = is_a_normform_set L;
    val Pi_ok = birs_states_are_normform Pi;
  in
    sys_ok andalso L_ok andalso Pi_ok
  end;




end (* local *)

end (* struct *)
