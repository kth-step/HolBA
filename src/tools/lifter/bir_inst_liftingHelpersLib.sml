structure bir_inst_liftingHelpersLib =
struct

local

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingLibTypes
open PPBackEnd Parse

in

(**********)
(* Syntax *)
(**********)

(* a function with the old behavior of print_with_style (no implicit newline at the end) *)
fun print_with_style_ sty = print o (add_style_to_string sty);

val ERR = mk_HOL_ERR "bir_inst_liftingLib"
fun failwith s = raise (ERR "???" s)

fun dest_quinop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e

fun list_of_quintuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_quinop tm = HolKernel.list_mk_icomb tm o list_of_quintuple

fun dest_sexop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6) else raise e
    | _ => raise e

fun list_of_sextuple (a, b, c, d, e, f) = [a, b, c, d, e, f];
fun mk_sexop tm = HolKernel.list_mk_icomb tm o list_of_sextuple

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_inst_lifting"

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;
val syntax_fns5 = syntax_fns 5 dest_quinop mk_quinop;
val syntax_fns6 = syntax_fns 6 dest_sexop mk_sexop;

fun get_const name = prim_mk_const{Name=name,        Thy="bir_inst_lifting"}

val bir_assert_desc_t_ty =
   Type.mk_thy_type {Tyop = "bir_assert_desc_t", Thy = "bir_update_block", Args = []};


val bir_updateE_desc_exp_tm = prim_mk_const{Name="bir_updateE_desc_exp", Thy="bir_update_block"}

val block_observe_ty = mk_vartype "'observation_type"

val bir_is_lifted_inst_block_COMPUTE_block_tm =
   inst [Type.alpha |-> block_observe_ty] (get_const "bir_is_lifted_inst_block_COMPUTE_block")

val bir_is_lifted_inst_block_COMPUTE_precond_tm =
    inst [Type.delta |-> block_observe_ty] (get_const "bir_is_lifted_inst_block_COMPUTE_precond")

val bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_tm =
  get_const "bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK";

val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_tm =
  get_const "bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES";

val bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_tm =
  get_const "bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES";

val PROTECTED_COND_tm =
  prim_mk_const{Name="PROTECTED_COND", Thy="bir_lifter_general_aux"}


val (bir_is_lifted_prog_LABELS_DISTINCT_tm,  mk_bir_is_lifted_prog_LABELS_DISTINCT, dest_bir_is_lifted_prog_LABELS_DISTINCT, is_bir_is_lifted_prog_LABELS_DISTINCT)  = syntax_fns4 "bir_is_lifted_prog_LABELS_DISTINCT";

val (bir_is_lifted_prog_tm,  mk_bir_is_lifted_prog, dest_bir_is_lifted_prog, is_bir_is_lifted_prog)  = syntax_fns4 "bir_is_lifted_prog";

val (bir_is_lifted_inst_prog_tm,  mk_bir_is_lifted_inst_prog, dest_bir_is_lifted_inst_prog, is_bir_is_lifted_inst_prog) = syntax_fns5 "bir_is_lifted_inst_prog";

val (bir_is_lifted_inst_block_tm,  mk_bir_is_lifted_inst_block, dest_bir_is_lifted_inst_block, is_bir_is_lifted_inst_block) = syntax_fns6 "bir_is_lifted_inst_block";


(*******************)
(* Auxiliary stuff *)
(*******************)

exception bir_inst_liftingAuxExn of bir_inst_liftingExn_data;

val debug_trace = ref (1:int)
val _ = register_trace ("bir_inst_lifting.DEBUG_LEVEL", debug_trace, 2)

val sty_OK    = [FG Green];
val sty_CACHE = [FG Yellow];
val sty_FAIL  = [FG OrangeRed];

end (* outermost local *)

end (* struct *)
