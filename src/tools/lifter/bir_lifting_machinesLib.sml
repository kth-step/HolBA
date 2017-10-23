structure bir_lifting_machinesLib :> bir_lifting_machinesLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_exp_liftingLib bir_lifting_machinesTheory
open bir_nzcv_introsTheory bir_arm8_extrasTheory bir_m0_extrasTheory
open arm8_stepLib m0_stepLib

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
end handle HOL_ERR _ => raise ERR "dest_bir_lifting_machine_rec" "";


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

val asm = `bl   48`
   fun hex_code_of_asm asm = hd (m0AssemblerLib.m0_disassemble `str     r3, [r2, #0]`)
   fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)

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


(**************************)
(* Instantiation for ARM8 *)
(**************************)

(* This performs some common normalisations which are many architectures. It
   checks whether the resulting theorem is of the form

   (NEXT_STEP_FUN var = SOME ...)

   and renames the variable into the given one. *)
fun bmr_normalise_step_thm (r_step_rel:term) vn thm =
   (* check whether thm is of expected form and normalise the state variable name *)
   let
      val (t_lhs, t_rhs) = dest_eq (concl thm)
      val _ = optionSyntax.dest_some t_rhs
      val (t_rel, v) = dest_comb t_lhs
      val _ = if (aconv t_rel r_step_rel) then () else fail ()
   in INST [v |-> vn] thm end;



(* DEBUG
  val vn = ``ms:arm8_state``
  val hex_code = "B90033E0";
  val hex_code = "79000001"
  val hex_code = "D345FC41"
  val hex_code = "A9B97BFD"
  val hex_code = "90000000"
  val hex_code = "BA020000"
  val hex_code = "BA000000"
  val hex_code = "FA010000"
  val hex_code = "FA000000"
  val hex_code = "7100001F"

  val thms = arm8_step_hex hex_code
*)

fun bytes_of_hex_code hex_code = let
   val _ = if (String.size hex_code mod 2 = 0) then () else failwith "invalid hex_code";

   fun prepare_word8_of_substring i =
     wordsSyntax.mk_wordi (Arbnum.fromHexString (String.substring (hex_code, i+i, 2)), 8);

in
   List.tabulate (String.size hex_code div 2, prepare_word8_of_substring)
end;


local
  val next_state_tm = (prim_mk_const{Name="NextStateARM8", Thy="arm8_step"});


  val simp_rule = (SIMP_RULE std_ss [nzcv_FOLDS_ARM8, arm8_stepTheory.ExtendValue_0,
      arm8_extra_FOLDS]);
  val simp_conv2 = (SIMP_CONV (arith_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_LOGIC_ss) []) THENC
                   (SIMP_CONV std_ss [word_add_to_sub_TYPES, alignmentTheory.aligned_numeric]);

  fun arm8_extra_THMS vn = let
     val thm0  = SPEC vn bmr_extra_ARM8
     val thm1a = ASSUME (lhs (concl thm0))
     val thm1 = CONV_RULE (K thm0) thm1a
  in
     CONJUNCTS thm1
  end;

  fun prepare_mem_contains_thms vn hex_code =
  let
    val bytes = bytes_of_hex_code hex_code
    val _ = if length bytes = 4 then () else failwith "invalid hex-code";

    val thm0 = SPECL (vn :: (List.rev bytes)) bmr_ms_mem_contains_ARM8

    val thm1a = ASSUME (lhs (concl thm0))
    val thm2 = CONV_RULE (K thm0) thm1a
  in
    CONJUNCTS thm2
  end;

  (* check for hyp (SOME _ = SOME vars) which can be discared via instantiating it *)
  fun instantiate_arm8_thm thm = let
       fun process_hyp (tm, thm) =
       let
          val (l_tm, r_tm) = dest_eq tm;
          val l_tm' = optionSyntax.dest_some l_tm;
          val r_tm' = optionSyntax.dest_some r_tm;
          val (s, _) = match_term r_tm' l_tm'

          val thm0a = INST s thm
          val thm0b = PROVE_HYP (REFL l_tm) thm0a
       in
          thm0b
       end handle HOL_ERR _ => thm;
   in
     foldl process_hyp thm (hyp thm)
   end;

(* val thm = hd step_thms0  *)
   fun process_arm8_thm vn pc_mem_thms thm = let
     val thm0 = bmr_normalise_step_thm next_state_tm vn thm
     val thm1 = instantiate_arm8_thm thm0
     val thm2 = foldl (fn (pre_thm, thm) => PROVE_HYP pre_thm thm) thm1
       (pc_mem_thms @ (arm8_extra_THMS vn))

     val thm3 = simp_rule thm2
     val thm4 = HYP_CONV_RULE (K true) (simp_conv2) (CONV_RULE simp_conv2 thm3)
   in
     thm4
   end;

in
  fun arm8_step_hex' vn hex_code = let
    val pc_mem_thms = prepare_mem_contains_thms vn hex_code;

    val step_thms0 = arm8_step_hex hex_code
    val step_thms1 = List.map (process_arm8_thm vn pc_mem_thms) step_thms0;
  in
    step_thms1
  end
end;

local
  val addr_ty = fcpLib.index_type (Arbnum.fromInt 64);
  val val_ty = fcpLib.index_type (Arbnum.fromInt 8);
  val val_word_ty = wordsSyntax.mk_word_type val_ty
in

fun arm8_mk_data_mm mem_loc hex_code = let
  val ml_tm = wordsSyntax.mk_n2w (numSyntax.mk_numeral mem_loc, addr_ty)
  val bytes = List.rev (bytes_of_hex_code hex_code)
  val _ = if length bytes = 4 then () else failwith "invalid hex-code";
  val bytes_tm = listSyntax.mk_list (bytes, val_word_ty)
in
  pairSyntax.mk_pair (ml_tm, bytes_tm)
end;

end;

val arm8_state_mem_tm = prim_mk_const{Name="arm8_state_MEM", Thy="arm8"};
val arm8_dest_mem = HolKernel.dest_binop arm8_state_mem_tm (ERR "arm8_dest_mem" "");

val arm8_REWRS = (
   (type_rws ``:arm8_state``) @
   (type_rws ``:ProcState``)
)
;

val arm8_extra_ss = rewrites arm8_REWRS

val arm8_bmr_rec : bmr_rec = {
  bmr_const                = prim_mk_const{Name="arm8_bmr", Thy="bir_lifting_machines"},
  bmr_ok_thm               = arm8_bmr_OK,
  bmr_lifted_thm           = arm8_bmr_LIFTED,
  bmr_extra_lifted_thms    = [arm8_extra_LIFTS],
  bmr_change_interval_thms = [arm8_CHANGE_INTERVAL_THMS],
  bmr_eval_thm             = arm8_bmr_EVAL,
  bmr_label_thm            = arm8_bmr_label_thm,
  bmr_dest_mem             = arm8_dest_mem,
  bmr_extra_ss             = arm8_extra_ss,
  bmr_step_hex             = arm8_step_hex',
  bmr_mk_data_mm           = arm8_mk_data_mm,
  bmr_hex_code_size        = K (Arbnum.fromInt 4),
  bmr_ihex_param           = SOME (4, true)
};

val _ = assert bmr_rec_sanity_check arm8_bmr_rec


(************************)
(* Instantiation for M0 *)
(************************)

(* DEBUG
  val vn = ``ms:m0_state``
  val endian_fl = true
  val sel_fl = true

  val hex_code = "b510"
  val hex_code = "f000f858"
  val hex_code = "3202"
  val hex_code = "4A15"

  val hex_code = "635C"
  val hex_code = "70E8"
  val hex_code = "B570"
  val hex_code = "BD70"
  val hex_code = "B510"
  val hex_code = "4770"
  val hex_code = "0100"

  val hex_code = "B285"
  val hex_code = "8028"
  val hex_code = "4182"
  val hex_code = "4088";
  val hex_code = "BA18";
  val hex_code = "BDF7";
  val hex_code = "B5F7"

  val thms = thumb_step_hex (true, true) hex_code
  val thms = thumb_step_hex (false, true) hex_code
  val thms = thumb_step_hex (true, true) hex_code

*)


fun m0_reorder_bytes false (b1::b2::bs) =
    b2::b1::(m0_reorder_bytes false bs)
  | m0_reorder_bytes _ l = l

local
  val addr_ty = fcpLib.index_type (Arbnum.fromInt 32);
  val val_ty = fcpLib.index_type (Arbnum.fromInt 8);
  val val_word_ty = wordsSyntax.mk_word_type val_ty
in

fun m0_mk_data_mm ef mem_loc hex_code = let
  val ml_tm = wordsSyntax.mk_n2w (numSyntax.mk_numeral mem_loc, addr_ty)
  val bytes = m0_reorder_bytes ef (bytes_of_hex_code hex_code)
  val _ = if (length bytes = 2) orelse (length bytes = 4) then () else failwith "invalid hex-code";
  val bytes_tm = listSyntax.mk_list (bytes, val_word_ty)
in
  pairSyntax.mk_pair (ml_tm, bytes_tm)
end;

end;

val m0_state_mem_tm = prim_mk_const{Name="m0_state_MEM", Thy="m0"};
val m0_dest_mem = HolKernel.dest_binop m0_state_mem_tm (ERR "m0_dest_mem" "");

val m0_REWRS = (RName_distinct :: (
   (type_rws ``:m0_state``) @
   (type_rws ``:PSR``) @
   (type_rws ``:RName``) @
   (type_rws ``:Mode``)
));

val m0_extra_ss = rewrites m0_REWRS;

(* DEBUG

  val endian_fl = false
  val sel_fl = true

  val res = m0_step_hex' (endian_fl, sel_fl) vn hex_code

*)

fun m0_step_hex' (endian_fl, sel_fl) = let
  val endian_fl_tm = if endian_fl then T else F;
  val sel_fl_tm = if sel_fl then T else F;

  val m0_step_hex = m0_stepLib.thumb_step_hex (endian_fl, sel_fl);

  val next_state_tm = (prim_mk_const{Name="NextStateM0", Thy="m0_step"});

  val simp_conv = (SIMP_CONV (arith_ss++bitstringLib.v2w_n2w_ss)
     ((if endian_fl then m0_extra_FOLDS_BE else m0_extra_FOLDS_LE)::[nzcv_FOLDS_M0,
     EQ_13w_EVAL, EQ_15w_EVAL, R_name_EVAL, bir_auxiliaryTheory.w2w_n2w,
     m0_extra_FOLDS_GEN, Mode_Handler_INTRO, bir_auxiliaryTheory.align_aligned_add,
     bir_auxiliaryTheory.align_aligned_sub, LowestSetBit_n2w, numeral_bitTheory.LOWEST_SET_BIT,
     alignmentTheory.aligned_numeric, alignmentTheory.align_aligned]));

  val simp_conv2 = (SIMP_CONV (arith_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_LOGIC_ss++wordsLib.SIZES_ss) [wordsTheory.n2w_11, m0_extra_FOLDS_GEN, wordsTheory.word_msb]) THENC
                   (SIMP_CONV std_ss [word_add_to_sub_TYPES, alignmentTheory.aligned_numeric]);

  val bmr_extra_M0' = REWRITE_RULE [] (SPECL [endian_fl_tm, sel_fl_tm] bmr_extra_M0)
  fun m0_extra_THMS vn = let
     val thm0  = SPEC vn bmr_extra_M0'
     val thm1a = ASSUME (lhs (concl thm0))
     val thm1 = CONV_RULE (K thm0) thm1a
  in
     CONJUNCTS thm1
  end;


  val bmr_ms_mem_contains_M0_2' = SPECL [endian_fl_tm, sel_fl_tm] bmr_ms_mem_contains_M0_2
  val bmr_ms_mem_contains_M0_4' = SPECL [endian_fl_tm, sel_fl_tm] bmr_ms_mem_contains_M0_4

  fun prepare_mem_contains_thms vn hex_code =
  let
    val bytes = m0_reorder_bytes endian_fl (bytes_of_hex_code hex_code)
    val ms_thm = if (length bytes = 2) then
                    bmr_ms_mem_contains_M0_2'
                 else if (length bytes = 4) then
                    bmr_ms_mem_contains_M0_4'
                 else failwith "invalid hex-code";

    val thm0 = SPECL (vn :: bytes) ms_thm

    val thm1a = ASSUME (lhs (concl thm0))
    val thm2 = CONV_RULE (K thm0) thm1a
  in
    CONJUNCTS thm2
  end;

(* val thm = hd step_thms0  *)
   fun process_m0_thm vn pc_mem_thms thm = let
     val thm0 = bmr_normalise_step_thm next_state_tm vn thm
     val thm1 = HYP_CONV_RULE (K true) simp_conv thm0
     val thm2 = foldl (fn (pre_thm, thm) => PROVE_HYP pre_thm thm) thm1
       (pc_mem_thms @ (m0_extra_THMS vn))

     val thm3 = DISCH_ALL thm2
     val thm4 = CONV_RULE (simp_conv THENC simp_conv2) thm3
     val thm5 = UNDISCH_ALL thm4

     (* check that theorem structure did not get destroyed by e.g.
        contradicting assumptions. *)
     val _ = dest_eq (concl thm5) handle HOL_ERR _ => failwith "m0_step_hex': unexpected resulting theorem"
   in
     thm5
   end;

in

  fn vn => fn hex_code => let
    val pc_mem_thms = prepare_mem_contains_thms vn hex_code;

    val step_thms0 = m0_step_hex hex_code
    val step_thms1 = List.map (process_m0_thm vn pc_mem_thms) step_thms0;
  in
    step_thms1
  end
end;


fun m0_bmr_rec endian_fl sel_fl =
let
  val endian_fl_tm = if endian_fl then T else F;
  val sel_fl_tm = if sel_fl then T else F;

  val const_tm0 = prim_mk_const{Name="m0_bmr", Thy="bir_lifting_machines"};
  val const_tm = mk_comb (const_tm0, pairSyntax.mk_pair (endian_fl_tm, sel_fl_tm))

in
{
  bmr_const                = const_tm,
  bmr_ok_thm               = SPECL [endian_fl_tm, sel_fl_tm] m0_bmr_OK,
  bmr_lifted_thm           = SPECL [endian_fl_tm, sel_fl_tm] m0_bmr_LIFTED,
  bmr_extra_lifted_thms    = [if endian_fl then m0_extra_LIFTS_BE else m0_extra_LIFTS_LE],
  bmr_change_interval_thms = [m0_CHANGE_INTERVAL_THMS],
  bmr_eval_thm             = REWRITE_RULE [] (SPECL [endian_fl_tm, sel_fl_tm] m0_bmr_EVAL),
  bmr_label_thm            = SPECL [endian_fl_tm, sel_fl_tm] m0_bmr_label_thm,
  bmr_dest_mem             = m0_dest_mem,
  bmr_extra_ss             = m0_extra_ss,
  bmr_step_hex             = m0_step_hex' (endian_fl, sel_fl),
  bmr_mk_data_mm           = m0_mk_data_mm endian_fl,
  bmr_hex_code_size        = (fn hc => if String.size hc = 8 then Arbnum.fromInt 4 else Arbnum.fromInt 2),
  bmr_ihex_param           = NONE
}: bmr_rec
end;

val m0_bmr_rec_LittleEnd_Main    = m0_bmr_rec false false
val m0_bmr_rec_BigEnd_Main       = m0_bmr_rec true  false
val m0_bmr_rec_LittleEnd_Process = m0_bmr_rec false true
val m0_bmr_rec_BigEnd_Process    = m0_bmr_rec true  true

val _ = assert bmr_rec_sanity_check (m0_bmr_rec_BigEnd_Process)
val _ = assert bmr_rec_sanity_check (m0_bmr_rec_LittleEnd_Process)
val _ = assert bmr_rec_sanity_check (m0_bmr_rec_BigEnd_Main)
val _ = assert bmr_rec_sanity_check (m0_bmr_rec_LittleEnd_Main)


end;
