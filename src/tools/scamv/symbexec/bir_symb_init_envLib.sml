(********************************************************)
(* Functions definied within this file are use to       *)
(* initialize the environment / memory                  *)
(* This is mostly SML -- not HOL definitions!           *)
(********************************************************)

(* 
app load ["bir_symb_envTheory", "bir_symb_execTheory", "stringLib"]
*)

structure bir_symb_init_envLib :> bir_symb_init_envLib = 
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

local

open HolKernel;
open bir_expTheory;
open bir_symb_execTheory 
open bir_symb_envTheory;
open bir_valuesTheory;
open bir_immTheory;
open finite_mapTheory;
open bitstringTheory;
open stringLib;
open bir_exp_memTheory;


open bir_exec_typingLib;
open stringSyntax;

open bir_immSyntax;
open bir_valuesSyntax;
open bir_expSyntax;
open wordsSyntax;

  (* error handling *)
  val libname  = "bir_symb_init_envLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

fun update_env_ultimate ((name_hol, bexp, bty), env) =
    (rhs o concl o EVAL) ``bir_symb_env_update ^name_hol ^bexp ^bty ^env``;

fun genf_ultimate (name_hol, bty) =
  if is_BType_Imm bty then
    let
      val n = size_of_bir_immtype_t (dest_BType_Imm bty);

      val r = mk_var(fromHOLstring name_hol, mk_int_word_type n);
      val tva = mk_BExp_Const (gen_mk_Imm r);
    in
      (name_hol, tva, bty)
    end
  else if is_BType_Mem bty then
    let
      val (tybba, tybbn) = dest_BType_Mem bty;
      (*
      val a = size_of_bir_immtype_t tybba;
      val n = size_of_bir_immtype_t tybbn;
      *)
      val mem = mk_var ("MEM",Type`:num |-> num`); (* TODO: this is hard coded... *)
      val tva = mk_BExp_MemConst (tybba, tybbn, mem);
    in
      (name_hol, tva, bty)
    end
  else
    raise ERR "genf_ultimate" "unexpected hol term";

val env_empty = ``BSEnv FEMPTY``;

fun init_env bir_program =
  let
    val updates = List.map (genf_ultimate o dest_BVar) (gen_vars_of_prog bir_program);
    val env = List.foldl update_env_ultimate env_empty updates;
  in
    env
  end;

end (* local *)

end (* struct *)
