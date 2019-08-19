structure bir_lifting_machinesLib :> bir_lifting_machinesLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_exp_liftingLib bir_lifting_machinesTheory


(**********)
(* SYNTAX *)
(**********)

val ERR = mk_HOL_ERR "bir_lifting_machinesLib"
val wrap_exn = Feedback.wrap_exn "bir_lifting_machinesLib"

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

val (bmr_ms_mem_contains_tm,  mk_bmr_ms_mem_contains, dest_bmr_ms_mem_contains, is_bmr_ms_mem_contains)  = syntax_fns3 "bmr_ms_mem_contains";


fun get_const name = prim_mk_const{Name=name,        Thy="bir_lifting_machines"}

val bmr_pc_lf_tm       =   get_const "bmr_pc_lf";
val bmr_pc_var_tm      =   get_const "bmr_pc_var";
val bmr_pc_var_cond_tm =   get_const "bmr_pc_var_cond";
val bmr_mem_lf_tm      =   get_const "bmr_mem_lf";
val bmr_mem_var_tm     =   get_const "bmr_mem_var";


val (BMLI_tm,  mk_BMLI, dest_BMLI, is_BMLI)  = syntax_fns2 "BMLI";
val (BMLM_tm,  mk_BMLM, dest_BMLM, is_BMLM)  = syntax_fns2 "BMLM";
val (BMLPC_tm,  mk_BMLPC, dest_BMLPC, is_BMLPC)  = syntax_fns3 "BMLPC";

fun dest_bir_lifting_machine_rec tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if is_bir_lift_machine_rec_t_ty ty then () else fail()
  val (imms, _) = listSyntax.dest_list (Lib.assoc "bmr_imms" l)
  val mem = Lib.assoc "bmr_mem" l
  val pc = Lib.assoc "bmr_pc" l
  val extra = Lib.assoc "bmr_extra" l
  val step_fun = Lib.assoc "bmr_step_fun" l
in
  (imms, mem, pc, extra, step_fun)
end handle e => raise wrap_exn "dest_bir_lifting_machine_rec" e;


(* Array fields *)

val (bmr_field_extra_tm,  mk_bmr_field_extra, dest_bmr_field_extra, is_bmr_field_extra)  = syntax_fns2 "bir_lifting_machine_rec_t_bmr_extra";

val (bmr_field_imms_tm,  mk_bmr_field_imms, dest_bmr_field_imms, is_bmr_field_imms)  = syntax_fns1 "bir_lifting_machine_rec_t_bmr_imms";

val (bmr_field_pc_tm,  mk_bmr_field_pc, dest_bmr_field_pc, is_bmr_field_pc)  = syntax_fns1 "bir_lifting_machine_rec_t_bmr_pc";

val (bmr_field_mem_tm,  mk_bmr_field_mem, dest_bmr_field_mem, is_bmr_field_mem)  = syntax_fns1 "bir_lifting_machine_rec_t_bmr_mem";

val (bmr_field_step_fun_tm,  mk_bmr_field_step_fun, dest_bmr_field_step_fun, is_bmr_field_step_fun)  = syntax_fns2 "bir_lifting_machine_rec_t_bmr_step_fun";


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


type bmr_rec = {bmr_const                : term,
                bmr_ok_thm               : thm,
                bmr_eval_thm             : thm,
                bmr_extra_lifted_thms    : thm list,
                bmr_change_interval_thms : thm list,
                bmr_extra_ss             : simpLib.ssfrag,
                bmr_label_thm            : thm,
                bmr_dest_mem             : term -> term * term,
                bmr_lifted_thm           : thm,
                bmr_step_hex             : term -> string -> thm list,
                bmr_mk_data_mm           : Arbnum.num -> string -> term,
                bmr_hex_code_size        : string -> Arbnum.num,
                bmr_ihex_param           : (int * bool) option};


(* Some sanity checks to ensure everything is as expected. *)
val bmr_rec_sanity_check_basic = let

  fun check_const t = is_bir_lift_machine_rec_t_ty (type_of t)

  fun check_ok_thm t thm = aconv (concl thm) (mk_bmr_ok t)

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

  fun check_change_interval_thms (r:bmr_rec) = let
     val thms = flatten (map BODY_CONJUNCTS (#bmr_change_interval_thms r));

     fun entry_ok thm = let
        val (va_tm, sz_tm, f1_tm, f2_tm) = bir_interval_expSyntax.dest_FUNS_EQ_OUTSIDE_WI_size (concl thm)

        val _ = assert numSyntax.is_numeral sz_tm
        val f1_vs = FVL [f1_tm] empty_tmset
        val rest_vs = FVL [f2_tm, va_tm] empty_tmset
        val _ = assert (fn rest_vs => HOLset.isSubset (rest_vs, f1_vs)) rest_vs
     in
       true
     end

     val _ = map entry_ok thms
  in
    true
  end handle HOL_ERR _ => false;

  fun check_label_thm (r:bmr_rec) = let
     val thm = (#bmr_label_thm r);
     val (vl, b) = strip_forall (concl thm)
     val _ = assert (fn l => length l = 3) vl
     val _ = assert (fn n => (type_of n = numSyntax.num)) (el 2 vl)
     val _ = assert (fn n => (type_of n = stringSyntax.string_ty)) (el 3 vl)

     val (lhs_t, rhs_t) = dest_imp_only b
     val _ = assert is_eq lhs_t
     val _ = assert is_eq rhs_t
  in
     true
  end handle HOL_ERR _ => false;

in
  fn r => (
     (check_const (#bmr_const r))
     andalso
     (check_ok_thm (#bmr_const r) (#bmr_ok_thm r))
     andalso
     (check_lifted_thm r)
     andalso
     (check_change_interval_thms r)
     andalso
     (check_label_thm r)
  )
end



(* extract the fields of the record *)
fun bmr_rec_extract_fields (r:bmr_rec) =
  dest_bir_lifting_machine_rec (rhs (concl (#bmr_eval_thm r)))

fun bmr_rec_mk_pc_of_term (r:bmr_rec) = let
  val (ms_ty, _, _)  = dest_bir_lifting_machine_rec_t_ty (type_of (#bmr_const r))
  val ms_v = mk_var ("ms", ms_ty);

  val (_, _, r_pc, _, _) = bmr_rec_extract_fields r;
  val (_, _, mk_lbl) = dest_BMLPC r_pc;
  val tm0 = mk_comb (mk_lbl, ms_v);
  val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
  val (sz, tm2) = bir_immSyntax.gen_dest_Imm tm1
in
  (sz, (fn t => subst [ms_v |-> t] tm2))
end

fun bmr_rec_mk_label_of_num (r:bmr_rec) = let
  val (sz, _) = bmr_rec_mk_pc_of_term r;
in fn pc =>
  bir_programSyntax.mk_BL_Address (bir_immSyntax.mk_Imm_of_num sz pc)
end

fun bmr_rec_mk_label_of_num_eq_pc (r:bmr_rec) = let
  val (sz, pc_tm) = bmr_rec_mk_pc_of_term r;
in fn (ms, pc) =>
  mk_eq (bir_programSyntax.mk_BL_Address (bir_immSyntax.gen_mk_Imm (pc_tm ms)),
         bir_programSyntax.mk_BL_Address (bir_immSyntax.mk_Imm_of_num sz pc))
end

fun bmr_rec_sanity_check r =
  (bmr_rec_sanity_check_basic r) andalso
  (can bmr_rec_extract_fields r) andalso
  (can bmr_rec_mk_label_of_num r) andalso
  (can bmr_rec_mk_label_of_num_eq_pc r) andalso
  (can bmr_rec_mk_pc_of_term r);


end;
