structure bir_lifting_machinesLib :> bir_lifting_machinesLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_exp_liftingLib bir_lifting_machinesTheory
open arm8_stepLib

(**********)
(* SYNTAX *)
(**********)

val ERR = mk_HOL_ERR "bir_lifting_machinesLib"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_lifting_machines"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;



fun mk_bir_lifting_machine_rec_t_ty (ty_ms, ty_m_addr, ty_m_val) =
  mk_type ("bir_lifting_machine_rec_t", [ty_m_addr, ty_m_val, ty_ms]);


fun dest_bir_lifting_machine_rec_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="bir_lifting_machine_rec_t", Thy="bir_lifting_machines", Args=[ty_ma, ty_mv, ty_ms]} => (ty_ms, ty_ma, ty_mv)
     | other => raise ERR "dest_bir_lifting_machine_rec_t_ty" ""


val is_bir_lift_machine_rec_t_ty = can dest_bir_lifting_machine_rec_t_ty


val (bmr_ok_tm,  mk_bmr_ok, dest_bmr_ok, is_bmr_ok)  = syntax_fns1 "bmr_ok";
val (bmr_rel_tm,  mk_bmr_rel, dest_bmr_rel, is_bmr_rel)  = syntax_fns3 "bmr_rel";
val (bmr_vars_tm,  mk_bmr_vars, dest_bmr_vars, is_bmr_vars)  = syntax_fns1 "bmr_vars";
val (bmr_temp_vars_tm,  mk_bmr_temp_vars, dest_bmr_temp_vars, is_bmr_temp_vars)  = syntax_fns1 "bmr_temp_vars";




(* the main part of bir_lifting_machinesTheory is the record
   type bir_lifting_machine_rec_t. To work with it and related types,
   some rewrites are needed. *)

val bmr_REWRS = (
   (type_rws ``:('a, 'b, 'c) bir_lifting_machine_rec_t``) @
   (type_rws ``:'a bir_machine_lifted_pc_t``) @
   (type_rws ``:'a bir_machine_lifted_imm_t``) @
   (type_rws ``:('a, 'b, 'c) bir_machine_lifted_mem_t``)
)
;

val bmr_ss = rewrites bmr_REWRS



(************************)
(* The main record type *)
(************************)


type bmr_rec = {bmr_const              : term,
                bmr_ok_thm             : thm,
                bmr_eval_thm           : thm,
                bmr_eval_rel_thm       : thm,
                bmr_eval_vars_thm      : thm,
                bmr_eval_temp_vars_thm : thm,
                bmr_extra_lifted_thms  : thm list,
                bmr_extra_ss           : simpLib.ssfrag,
                bmr_lifted_thm         : thm,
                bmr_step_hex           : string -> thm list};


(* Some sanity checks to ensure everything is as expected. *)
val brm_rec_sanity_check = let

  fun check_const t = is_bir_lift_machine_rec_t_ty (type_of t) andalso
                      is_const t

  fun check_ok_thm t thm = aconv (concl thm) (mk_bmr_ok t)
  fun check_vars_thm (r:bmr_rec) = let
     val thm = (#bmr_eval_vars_thm r);
     val lhs_t = mk_bmr_vars (#bmr_const r)
     val lhs_thm = lhs (concl thm);
     val rhs_thm = rhs (concl thm);
     val (vs, _) = listSyntax.dest_list rhs_thm
  in
    (aconv lhs_t lhs_thm) andalso List.all bir_envSyntax.is_BVar vs
  end handle HOL_ERR _ => false;

  fun check_temp_vars_thm (r:bmr_rec) = let
     val thm = (#bmr_eval_temp_vars_thm r);
     val lhs_t = mk_bmr_temp_vars (#bmr_const r)
     val lhs_thm = lhs (concl thm);
     val rhs_thm = rhs (concl thm);
     val (vs, _) = listSyntax.dest_list rhs_thm
  in
    (aconv lhs_t lhs_thm) andalso List.all bir_envSyntax.is_BVar vs
  end handle HOL_ERR _ => false;

  fun check_lifted_thm (r:bmr_rec) = let
     val thm = (#bmr_lifted_thm r);
     val (vl, b) = strip_forall (concl thm)
     val _ = assert (fn l => length l = 2) vl
     val (bs_t, ms_t) = (el 1 vl, el 2 vl)

     val (l_t, r_t) = dest_imp_only b
     val _ = assert (aconv (mk_bmr_rel (#bmr_const r, bs_t, ms_t))) l_t

     val tl = strip_conj r_t
  in
    List.all bir_exp_liftingLib.is_bir_is_lifted_exp tl
  end handle HOL_ERR _ => false;

in
  fn r => (
     (check_const (#bmr_const r))
     andalso
     (check_ok_thm (#bmr_const r) (#bmr_ok_thm r))
     andalso
     (check_vars_thm r)
     andalso
     (check_temp_vars_thm r)
     andalso
     (check_lifted_thm r)
  )
end



val arm8_bmr_rec : bmr_rec = {
  bmr_const              = prim_mk_const{Name="arm8_bmr", Thy="bir_lifting_machines"},
  bmr_ok_thm             = arm8_bmr_OK,
  bmr_lifted_thm         = arm8_brm_LIFTED,
  bmr_extra_lifted_thms  = [],
  bmr_eval_thm           = arm8_bmr_EVAL,
  bmr_eval_vars_thm      = arm8_brm_vars_EVAL,
  bmr_eval_temp_vars_thm = arm8_brm_temp_vars_EVAL,
  bmr_eval_rel_thm       = arm8_bmr_rel_EVAL,
  bmr_extra_ss           = rewrites [],
  bmr_step_hex           = arm8_step_hex
};

val _ = assert brm_rec_sanity_check arm8_bmr_rec

end;
