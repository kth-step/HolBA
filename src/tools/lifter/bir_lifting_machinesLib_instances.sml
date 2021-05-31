structure bir_lifting_machinesLib_instances :>
  bir_lifting_machinesLib_instances =
struct
(* For compilation: *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
(* Local theories: *)
open bir_lifting_machinesTheory
     bir_nzcv_introsTheory bir_arm8_extrasTheory bir_m0_extrasTheory
     bir_riscv_extrasTheory;
open bslSyntax;
open bir_program_labelsSyntax bir_programSyntax
     bir_valuesSyntax bir_immSyntax bir_exp_immSyntax
     bir_interval_expSyntax;
(* Local function libraries: *)
open bir_lifting_machinesLib bir_inst_liftingHelpersLib
     bir_exp_liftingLib;
(* Function libraries from examples/l3-machine-code: *)
open arm8_stepLib m0_stepLib riscv_stepLib;

(* Abbreviations used in this file:
 * BMR: BIR machine record. *)

val ERR = mk_HOL_ERR "bir_lifting_machinesLib_instances"

(**************************)
(* Instantiation for ARM8 *)
(**************************)

(* This performs some normalisations which are shared across many
 * architectures. It
 * checks whether the resulting theorem thm is of the form

     r_step_rel var = SOME ...

 * and instantiates the variable var to the variable
 * supplied in var_name, thus renaming it. *)
fun bmr_normalise_step_thm (r_step_rel:term) var_name thm =
  let
    val (thm_lhs, thm_rhs) = dest_eq (concl thm)
    (* The below line checks whether the RHS of thm has
     * option type SOME. If that is not the case, then
     * an exception will be thrown, which alerts the user
     * to the error in lifting. *)
    val _ = optionSyntax.dest_some thm_rhs
    val (thm_rel, var) = dest_comb thm_lhs
    val _ = if (aconv thm_rel r_step_rel) then () else fail ()
  in
    INST [var |-> var_name] thm
  end;



(* DEBUG
  fun arm8_hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code [QUOTE asm])

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
  val hex_code = arm8_hex_code_of_asm "rev16 x1, x2";
  val hex_code = arm8_hex_code_of_asm "rev16 w1, w2";
  val hex_code = arm8_hex_code_of_asm "rev32 x1, x2";
  val hex_code = arm8_hex_code_of_asm "ngc x1, x2"
  val hex_code = arm8_hex_code_of_asm "ngc w1, w2"
  val hex_code = arm8_hex_code_of_asm "ngcs x1, x2"
  val hex_code = arm8_hex_code_of_asm "ngc w1, w2"
  val hex_code = arm8_hex_code_of_asm "rbit w1, w2"
  val hex_code = arm8_hex_code_of_asm "ror x1, x2, x3"
  val hex_code = arm8_hex_code_of_asm "ror x1, x2, #2"
  val hex_code = arm8_hex_code_of_asm "ror w1, w2, #2"
  val hex_code = arm8_hex_code_of_asm "extr w1, w2, w3, #2"
  val hex_code = arm8_hex_code_of_asm "extr x1, x2, x3, #2"
  val hex_code = arm8_hex_code_of_asm "movk x1, #2"
  val hex_code = arm8_hex_code_of_asm "movk w1, #2"
  val hex_code = arm8_hex_code_of_asm "ngc w0, w1"
  val hex_code = arm8_hex_code_of_asm "ngcs w0, w1"
  val hex_code = arm8_hex_code_of_asm "adcs w0, w1, w2"
  val hex_code = arm8_hex_code_of_asm "sbcs w0, w1, w2"

  val thms = arm8_step_hex hex_code
  val thms' = arm8_step_hex' vn hex_code
*)

(* TODO: Document this function. *)
fun bytes_of_hex_code hex_code = let
  val _ = if (String.size hex_code mod 2 = 0)
          then ()
          else failwith "invalid hex_code";

  fun prepare_word8_of_substring i =
    wordsSyntax.mk_wordi (
      Arbnum.fromHexString (String.substring (hex_code, i+i, 2)),
      8
    );

in
  List.tabulate (String.size hex_code div 2,
                 prepare_word8_of_substring)
end;


local
  val next_state_tm = (prim_mk_const{Name="NextStateARM8", Thy="arm8_step"});

  val simp_conv = (SIMP_CONV std_ss [nzcv_FOLDS_ARM8] THENC
                   SIMP_CONV std_ss [arm8_stepTheory.ExtendValue_0, arm8_extra_FOLDS]);

  val simp_conv2 = (SIMP_CONV (arith_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_LOGIC_ss) []) THENC
                   (SIMP_CONV std_ss [word_add_to_sub_TYPES, alignmentTheory.aligned_numeric,
                        wordsTheory.WORD_SUB_INTRO, wordsTheory.WORD_MULT_CLAUSES]);

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

     val thm3 = DISCH_ALL thm2
     val thm4 = CONV_RULE (simp_conv THENC simp_conv2) thm3
     val thm5 = UNDISCH_ALL thm4
   in
     thm5
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
  bmr_mc_lift_instr           = NONE,
  bmr_mk_data_mm           = arm8_mk_data_mm,
  bmr_hex_code_size        = (fn hc => Arbnum.fromInt ((String.size hc) div 2)),
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
  val hex_code = "2200";
  val hex_code = "2204";
  val hex_code = "4084"
  val hex_code = "40C4"
  val hex_code = "1ACC";
  val hex_code = "1E08"
  val hex_code = "4251"
  val hex_code = "40C4"
  val hex_code = "4088"
  val hex_code = "BA51";
  val hex_code = "BAD1"
  val hex_code = "41C8"

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
fun m0_mk_data_mm ef mem_loc hex_code =
  let
    val ml_tm =
      wordsSyntax.mk_n2w (numSyntax.mk_numeral mem_loc, addr_ty)
    val bytes = m0_reorder_bytes ef (bytes_of_hex_code hex_code)
    val _ = if (length bytes = 2) orelse (length bytes = 4)
            then ()
            else failwith "invalid hex-code";
    val bytes_tm = listSyntax.mk_list (bytes, val_word_ty)
  in
    pairSyntax.mk_pair (ml_tm, bytes_tm)
  end
end;

val m0_state_mem_tm = prim_mk_const{Name="m0_state_MEM", Thy="m0"};
val m0_dest_mem = HolKernel.dest_binop m0_state_mem_tm
                                       (ERR "m0_dest_mem" "");

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

  val vn = ``ms:m0_state``

  val hex_code = "D001";

  val res = m0_step_hex' (endian_fl, sel_fl) vn hex_code

*)

fun m0_step_hex' (endian_fl, sel_fl) = let
  val endian_fl_tm = if endian_fl then T else F;
  val sel_fl_tm = if sel_fl then T else F;

  val m0_step_hex = m0_stepLib.thumb_step_hex (endian_fl, sel_fl);

  val next_state_tm = (prim_mk_const{Name="NextStateM0", Thy="m0_step"});

  val simp_conv = (SIMP_CONV (arith_ss++bitstringLib.v2w_n2w_ss++wordsLib.SIZES_ss)
     ((if endian_fl then m0_extra_FOLDS_BE else m0_extra_FOLDS_LE)::[nzcv_FOLDS_M0,
     EQ_13w_EVAL, EQ_15w_EVAL, R_name_EVAL, bir_auxiliaryTheory.w2w_n2w,
     m0_extra_FOLDS_GEN, Mode_Handler_INTRO, bir_auxiliaryTheory.align_aligned_add,
     bir_auxiliaryTheory.align_aligned_sub, LowestSetBit_n2w, numeral_bitTheory.LOWEST_SET_BIT,
     alignmentTheory.aligned_numeric, alignmentTheory.align_aligned, wordsTheory.word_bit_n2w]));

  val compset_2 = reduceLib.num_compset ();
  val _ = bitLib.add_bit_compset compset_2

  val simp_conv2 = SIMP_CONV (arith_ss++wordsLib.WORD_ARITH_ss ++ wordsLib.WORD_LOGIC_ss++wordsLib.SIZES_ss) [wordsTheory.n2w_11, m0_extra_FOLDS_GEN, wordsTheory.word_msb, wordsTheory.word_bit_n2w] THENC
                   (SIMP_CONV std_ss [word_add_to_sub_TYPES, wordsTheory.WORD_SUB_INTRO, alignmentTheory.aligned_numeric, wordsTheory.WORD_MULT_CLAUSES] THENC
                    computeLib.CBV_CONV compset_2);

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
  bmr_mc_lift_instr           = NONE,
  bmr_mk_data_mm           = m0_mk_data_mm endian_fl,
  bmr_hex_code_size        = (fn hc => Arbnum.fromInt ((String.size hc) div 2)),
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


(************************)
(* Instantiation for M0_mod (modified to include countw and old base) *)
(************************)


fun m0_mod_reorder_bytes false (b1::b2::bs) =
    b2::b1::(m0_mod_reorder_bytes false bs)
  | m0_mod_reorder_bytes _ l = l

local
  val addr_ty = fcpLib.index_type (Arbnum.fromInt 32);
  val val_ty = fcpLib.index_type (Arbnum.fromInt 8);
  val val_word_ty = wordsSyntax.mk_word_type val_ty
in

fun m0_mod_mk_data_mm ef mem_loc hex_code = let
  val ml_tm = wordsSyntax.mk_n2w (numSyntax.mk_numeral mem_loc, addr_ty)
  val bytes = m0_mod_reorder_bytes ef (bytes_of_hex_code hex_code)
  val _ = if (length bytes = 2) orelse (length bytes = 4) then () else failwith "invalid hex-code";
  val bytes_tm = listSyntax.mk_list (bytes, val_word_ty)
in
  pairSyntax.mk_pair (ml_tm, bytes_tm)
end;

end;

val m0_mod_REWRS = (RName_distinct :: (
   (type_rws ``:m0_state``) @
   (type_rws ``:m0_mod_state``) @
   (type_rws ``:PSR``) @
   (type_rws ``:RName``) @
   (type_rws ``:Mode``)
));

val m0_mod_extra_ss = rewrites m0_mod_REWRS;

(* DEBUG

  val endian_fl = false
  val sel_fl = true

  val vn = ``ms:m0_mod_state``
  val hex_code = "41C8"
  val hex_code = "D001";

  val res = m0_mod_step_hex' (endian_fl, sel_fl) vn hex_code

*)

fun m0_mod_step_hex' (endian_fl, sel_fl) = let
  val endian_fl_tm = if endian_fl then T else F;
  val sel_fl_tm = if sel_fl then T else F;

  val m0_mod_step_hex = m0_mod_stepLib.thumb_mod_step_hex (endian_fl, sel_fl);

  val next_state_tm = (prim_mk_const{Name="NextStateM0_mod", Thy="m0_mod_step"});

  val simp_conv = (SIMP_CONV (arith_ss++bitstringLib.v2w_n2w_ss++wordsLib.SIZES_ss)
     ((if endian_fl then m0_extra_FOLDS_BE else m0_extra_FOLDS_LE)::[nzcv_FOLDS_M0,
     EQ_13w_EVAL, EQ_15w_EVAL, R_name_EVAL, bir_auxiliaryTheory.w2w_n2w,
     m0_extra_FOLDS_GEN, Mode_Handler_INTRO, bir_auxiliaryTheory.align_aligned_add,
     bir_auxiliaryTheory.align_aligned_sub, LowestSetBit_n2w, numeral_bitTheory.LOWEST_SET_BIT,
     alignmentTheory.aligned_numeric, alignmentTheory.align_aligned, wordsTheory.word_bit_n2w]));

  val compset_2 = reduceLib.num_compset ();
  val _ = bitLib.add_bit_compset compset_2

  val simp_conv2 = SIMP_CONV (arith_ss++wordsLib.WORD_ARITH_ss ++ wordsLib.WORD_LOGIC_ss++wordsLib.SIZES_ss) [wordsTheory.n2w_11, m0_extra_FOLDS_GEN, wordsTheory.word_msb, wordsTheory.word_bit_n2w] THENC
                   (SIMP_CONV std_ss [word_add_to_sub_TYPES, wordsTheory.WORD_SUB_INTRO, alignmentTheory.aligned_numeric, wordsTheory.WORD_MULT_CLAUSES] THENC
                    computeLib.CBV_CONV compset_2);

  val bmr_extra_M0_mod' = REWRITE_RULE [] (SPECL [endian_fl_tm, sel_fl_tm] bmr_extra_M0_mod)
  fun m0_mod_extra_THMS vn = let
     val thm0  = SPEC vn bmr_extra_M0_mod'
     val thm1a = ASSUME (lhs (concl thm0))
     val thm1 = CONV_RULE (K thm0) thm1a
  in
     CONJUNCTS thm1
  end;


  val bmr_ms_mem_contains_M0_mod_2' = SPECL [endian_fl_tm, sel_fl_tm] bmr_ms_mem_contains_M0_mod_2
  val bmr_ms_mem_contains_M0_mod_4' = SPECL [endian_fl_tm, sel_fl_tm] bmr_ms_mem_contains_M0_mod_4

  fun prepare_mem_contains_thms vn hex_code =
  let
    val bytes = m0_mod_reorder_bytes endian_fl (bytes_of_hex_code hex_code)
    val ms_thm = if (length bytes = 2) then
                    bmr_ms_mem_contains_M0_mod_2'
                 else if (length bytes = 4) then
                    bmr_ms_mem_contains_M0_mod_4'
                 else failwith "invalid hex-code";

    val thm0 = SPECL (vn :: bytes) ms_thm

    val thm1a = ASSUME (lhs (concl thm0))
    val thm2 = CONV_RULE (K thm0) thm1a
  in
    CONJUNCTS thm2
  end;

(* val thm = hd step_thms0  *)
   fun process_m0_mod_thm vn pc_mem_thms thm = let
     val thm0 = bmr_normalise_step_thm next_state_tm vn thm
     val thm1 = HYP_CONV_RULE (K true) simp_conv thm0
     val thm2 = foldl (fn (pre_thm, thm) => PROVE_HYP pre_thm thm) thm1
       (pc_mem_thms @ (m0_mod_extra_THMS vn))

     val thm3 = DISCH_ALL thm2
     val thm4 = CONV_RULE (simp_conv THENC simp_conv2) thm3
     val thm5 = UNDISCH_ALL thm4

     (* check that theorem structure did not get destroyed by e.g.
        contradicting assumptions. *)
     val _ = dest_eq (concl thm5) handle HOL_ERR _ => failwith "m0_mod_step_hex': unexpected resulting theorem"
   in
     thm5
   end;

in

  fn vn => fn hex_code => let
    val pc_mem_thms = prepare_mem_contains_thms vn hex_code;

    val step_thms0 = m0_mod_step_hex hex_code
    val step_thms1 = List.map (process_m0_mod_thm vn pc_mem_thms) step_thms0;
  in
    step_thms1
  end
end;


fun m0_mod_bmr_rec endian_fl sel_fl =
let
  val endian_fl_tm = if endian_fl then T else F;
  val sel_fl_tm = if sel_fl then T else F;

  val const_tm0 = prim_mk_const{Name="m0_mod_bmr", Thy="bir_lifting_machines"};
  val const_tm = mk_comb (const_tm0, pairSyntax.mk_pair (endian_fl_tm, sel_fl_tm))

in
{
  bmr_const                = const_tm,
  bmr_ok_thm               = SPECL [endian_fl_tm, sel_fl_tm] m0_mod_bmr_OK,
  bmr_lifted_thm           = SPECL [endian_fl_tm, sel_fl_tm] m0_mod_bmr_LIFTED,
  bmr_extra_lifted_thms    = [if endian_fl then m0_extra_LIFTS_BE else m0_extra_LIFTS_LE],
  bmr_change_interval_thms = [m0_CHANGE_INTERVAL_THMS],
  bmr_eval_thm             = REWRITE_RULE [] (SPECL [endian_fl_tm, sel_fl_tm] m0_mod_bmr_EVAL),
  bmr_label_thm            = SPECL [endian_fl_tm, sel_fl_tm] m0_mod_bmr_label_thm,
  bmr_dest_mem             = m0_dest_mem,
  bmr_extra_ss             = m0_mod_extra_ss,
  bmr_step_hex             = m0_mod_step_hex' (endian_fl, sel_fl),
  bmr_mc_lift_instr           = NONE,
  bmr_mk_data_mm           = m0_mod_mk_data_mm endian_fl,
  bmr_hex_code_size        = (fn hc => Arbnum.fromInt ((String.size hc) div 2)),
  bmr_ihex_param           = NONE
}: bmr_rec
end;

val m0_mod_bmr_rec_LittleEnd_Main    = m0_mod_bmr_rec false false
val m0_mod_bmr_rec_BigEnd_Main       = m0_mod_bmr_rec true  false
val m0_mod_bmr_rec_LittleEnd_Process = m0_mod_bmr_rec false true
val m0_mod_bmr_rec_BigEnd_Process    = m0_mod_bmr_rec true  true

val _ = assert bmr_rec_sanity_check (m0_mod_bmr_rec_BigEnd_Process)
val _ = assert bmr_rec_sanity_check (m0_mod_bmr_rec_LittleEnd_Process)
val _ = assert bmr_rec_sanity_check (m0_mod_bmr_rec_BigEnd_Main)
val _ = assert bmr_rec_sanity_check (m0_mod_bmr_rec_LittleEnd_Main)


(****************************)
(* Instantiation for RISC-V *)
(****************************)
(* TODO: bmr_normalise_step_thm and bytes_of_hex_code are defined
 * above - make separate variants for RISC-V? *)

(* Type rewrites as a list of theorems (ARM8 also had rewrites
 * for ``:ProcState``)... *)
val riscv_REWRS = (
  (type_rws ``:riscv_state``)
);

(* ... and as a simplification set. *)
val riscv_extra_ss = rewrites (riscv_REWRS@[combinTheory.APPLY_UPDATE_THM])

local
  (* The naming convention for this is slightly different in the
   * RISC-V version of the HOL4 model. *)
  val next_state_tm =
    prim_mk_const{Name="NextRISCV", Thy="riscv_step"}

  val simp_conv = SIMP_CONV std_ss [riscv_extra_FOLDS]

  val simp_conv2 =
    (SIMP_CONV (arith_ss++wordsLib.WORD_ARITH_ss++
                wordsLib.WORD_LOGIC_ss) []
    ) THENC
    (SIMP_CONV std_ss
               [bir_riscv_extrasTheory.word_add_to_sub_TYPES,
                alignmentTheory.aligned_numeric,
                wordsTheory.WORD_SUB_INTRO,
                wordsTheory.WORD_MULT_CLAUSES]
    )

  fun riscv_extra_THMS vn = let
     val thm0  = SPEC vn bmr_extra_RISCV
     val thm1a = ASSUME (lhs (concl thm0))
     val thm1 = CONV_RULE (K thm0) thm1a
  in
     CONJUNCTS thm1
  end

  fun prepare_mem_contains_thms vn hex_code =
    let
      val bytes = bytes_of_hex_code hex_code
      val _ = if length bytes = 4
              then ()
              else failwith "invalid hex-code";

      val thm0 = SPECL (vn::(List.rev bytes))
                       bmr_ms_mem_contains_RISCV

      val thm1a = ASSUME (lhs (concl thm0))
      val thm2 = CONV_RULE (K thm0) thm1a
    in
      CONJUNCTS thm2
    end

  (* instantiate_riscv_thm checks for hyp (SOME _ = SOME vars)
   * which can be discarded via instantiating it. *)
  fun instantiate_riscv_thm thm =
    let
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

  (* process_riscv_thm uses all of the above locally defined
   * functions to process the theorem obtained by riscv_step_hex
   * into a more manageable format. *)
  (* DEBUG (when called from riscv_step_hex')
   
     val thm = hd step_thms0 

  *)
  fun process_riscv_thm vn pc_mem_thms thm = let
    val thm0 = bmr_normalise_step_thm next_state_tm vn thm
    val thm1 =
	UNDISCH_ALL (SIMP_RULE (empty_ss++bitstringLib.v2w_n2w_ss++bitstringLib.BITSTRING_GROUND_ss) [] (DISCH_ALL thm0))
          handle UNCHANGED => thm0
    val thm2 =
	SIMP_RULE (std_ss++riscv_extra_ss) [riscvTheory.Skip_def] thm1
          handle UNCHANGED => thm1
    val thm3 = instantiate_riscv_thm thm2
    val thm4 = foldl (fn (pre_thm, thm) => PROVE_HYP pre_thm thm)
                     thm3
                     (pc_mem_thms @ (riscv_extra_THMS vn))

    val thm5 = DISCH_ALL thm4
    (* TODO: Simplifying with riscv_extra_THMS is useful when things like 32-bit mode comes up in
     * expressions. This doesn't need to be handled using the explicit assumptions in
     * riscv_extra_THMS, but could be lifted along with the MCSR and treated dynamically as part of
     * the program. In other words, remove the last conversion when you start lifting system
     * registers. *)
    val thm6 =
      CONV_RULE (simp_conv THENC simp_conv2 THENC (SIMP_CONV std_ss (riscv_extra_THMS vn))) thm5
    val thm7 = UNDISCH_ALL thm6
  in
    thm7
  end;

in
(* Debugging RISC-V:

  val (ms_ty, addr_sz_ty, mem_val_sz_ty)  = dest_bir_lifting_machine_rec_t_ty (type_of (prim_mk_const{Name="riscv_bmr", Thy="bir_lifting_machines"}))
  val vn = mk_var ("ms", ms_ty);
  val hex_code = "FCE14083" (* "lbu x1,x2,-50" *)

  val hex_code = "340090F3" (* "csrrw x1,mscratch, x1" *)

*)
  fun riscv_step_hex' vn hex_code = let
    val pc_mem_thms = prepare_mem_contains_thms vn hex_code

    val step_thms0 = [riscv_step_hex hex_code]
    val step_thms1 =
      List.map (process_riscv_thm vn pc_mem_thms) step_thms0
  in
    step_thms1
  end
end;

(* RISC-V Multicore wrapper *)
local

(* Auxiliary function to obtain a padded binary string from a hex instruction. *)
local
fun pad_zero' 0   str = str
  | pad_zero' len str = pad_zero' (len-1) ("0"^str)
in
fun hex_to_bin_pad_zero len str =
  let
    val str' = (Arbnum.toBinString (Arbnum.fromHexString str))
  in
    pad_zero' (len - (size str')) str'
  end
end

(* Takes a hex-format string instruction and returns a representation of it using
 * a list with 4 bytes. *)
val word8_tm = wordsSyntax.mk_word_type (fcpSyntax.mk_numeric_type (Arbnum.fromInt 8))

(* Takes a SML "0" or "1" string and converts it into a HOL4 bool *)
fun str_to_bool str =
  if str = "1"
  then true
  else if str = "0"
  then false
  else raise ERR "str_to_bool" ("String "^str^" is not 0 or 1, and could not be converted to a bool term")

fun get_byte_word_l hex =
  let
    val bin = hex_to_bin_pad_zero 32 hex
    val byte1 = substring (bin, 0, 8)
    val byte2 = substring (bin, 8, 8)
    val byte3 = substring (bin, 16, 8)
    val byte4 = substring (bin, 24, 8)
    val byte_to_word8 = (fn byte => (wordsSyntax.mk_wordi (Arbnum.fromBinString byte, 8)))
  in
    listSyntax.mk_list ((map byte_to_word8 [byte1, byte2, byte3, byte4]), word8_tm)
  end

(* Parses the hex-format fence instruction into its fields. *)
fun parse_fence hex_code =
  let
    val bin = hex_to_bin_pad_zero 32 hex_code
    val fm = substring (bin, 0, 4)
    val pi = substring (bin, 4, 1)
    val po = substring (bin, 5, 1)
    val pr = substring (bin, 6, 1)
    val pw = substring (bin, 7, 1)
    val si = substring (bin, 8, 1)
    val so = substring (bin, 9, 1)
    val sr = substring (bin, 10, 1)
    val sw = substring (bin, 11, 1)
    val rs1 = substring (bin, 12, 5)
    val funct3 = substring (bin, 17, 3)
    val rd = substring (bin, 20, 5)
    val opcode = substring (bin, 25, 7)
  in
    (fm, pi, po, pr, pw, si, so, sr, sw, rs1, funct3, rd, opcode)
  end

(* Parses hex-format instructions with opcode AMO into its fields. *)
fun parse_amo hex_code =
  let
    val bin = hex_to_bin_pad_zero 32 hex_code
    val funct5 = substring (bin, 0, 5)
    val aq = substring (bin, 5, 1)
    val rl = substring (bin, 6, 1)
    val rs2 = substring (bin, 7, 5)
    val rs1 = substring (bin, 12, 5)
    val funct3 = substring (bin, 17, 3)
    val rd = substring (bin, 20, 5)
    val opcode = substring (bin, 25, 7)
  in
    (funct5, aq, rl, rs2, rs1, funct3, rd, opcode)
  end

(* Checks if hex-format instruction is a fence. *)
fun is_fence hex_code =
  let
    val (fm, pi, po, pr, pw, si, so, sr, sw, rs1, funct3, rd, opcode) = parse_fence hex_code
  in
    if opcode = "0001111" (* opcode MISC-MEM *)
    then
      if (fm = "0000") orelse ((fm = "1000") andalso
                               (pr = "1") andalso
                               (pw = "1") andalso
                               (sr = "1") andalso
                               (sw = "1"))
      then true
      else if (funct3 = "001")
      then raise ERR "is_fence" ("Fence instruction "^hex_code^" is unsupported FENCE.I")
      else raise ERR "is_fence" ("Fence instruction "^hex_code^" is unknown fence type")
    else false
  end

(* List of possible funct5-values for AMO-type instructions. *)
val amo_funct5 =
  ["00001",
   "00000",
   "00100",
   "01100",
   "01000",
   "10000",
   "10100",
   "11000",
   "11100"
  ];

(* Checks if hex-format instruction is a non-LR/SC AMO-type instruction. *)
fun is_amo hex_code =
  let
    val (funct5, _, _, _, _, _, _, opcode) = parse_amo hex_code
  in
    if opcode = "0101111" (* opcode AMO *)
    then
      (* Rule out LR and SC, which are treated separately *)
      (exists (fn f5 => f5 = funct5) amo_funct5)
    else false
  end
;

(* List of possible funct5-values for LR/SC AMO-type instructions. *)
val lrsc_funct5 =
  ["00010",
   "00011"
  ];

(* Checks if hex-format instruction is a LR/SC AMO-type instruction. *)
fun is_lrsc hex_code =
  let
    val (funct5, _, _, _, _, _, _, opcode) = parse_amo hex_code
  in
    if opcode = "0101111" (* opcode AMO *)
    then
      (exists (fn f5 => f5 = funct5) lrsc_funct5)
    else false
  end
;

(* Gets the Fence bstmts from hex-format instruction. *)
fun get_fence_bstmts hex_code =
  let
    val (fm, pi, po, pr, pw, si, so, sr, sw, _, _, _, _) = parse_fence hex_code
  in
    if (fm = "0000")
    then
      [mk_BStmt_Fence
	 (if pr = "1"
	  then if pw = "1"
	       then BM_ReadWrite_tm
	       else BM_Read_tm
	  else if pw = "1"
	       then BM_Write_tm
	       else raise ERR "get_fence_args" ("Fence instruction "^hex_code^" has no predecessor R/W bits set"),
	  if sr = "1"
	  then if sw = "1"
	       then BM_ReadWrite_tm
	       else BM_Read_tm
	  else if sw = "1"
	       then BM_Write_tm
	       else raise ERR "get_fence_args" ("Fence instruction "^hex_code^" has no successor R/W bits set")
	    )]
    else if (fm = "1000")
    then (* TSO fence *)
      [mk_BStmt_Fence (BM_Read_tm, BM_ReadWrite_tm), mk_BStmt_Fence (BM_Write_tm, BM_Write_tm)]
    else raise ERR "get_fence_args" ("Fence instruction "^hex_code^" has unknown fm bits: "^fm)
  end

(* Construct the name of a RISC-V GPR (see bir_lifting_machinesLib_instances) *)
fun mk_gpr_var_name bit_code =
  ("x"^(Arbnum.toString (Arbnum.fromBinString bit_code)))

(*
val ity = Bit64_tm
val rd = "00001"
val rs1 = "00011"
val rs2 = "00111"

 1. Load data value from address in rs1, place value into rd,
 2. apply binary operator to the loaded value and the original value in rs2,
 3. then store the result back to the address in rs1.

open bslSyntax;

val brd = mk_gpr_var_name rd
val brs1 = mk_gpr_var_name rs1
val brs2 = mk_gpr_var_name rs2

val bvar_rd = bvarimm64 brd
val bvar_rs1 = bvarimm64 brs1
val bvar_rs2 = bvarimm64 brs2

LOAD 32-BIT:

  BStmt_Assert
    (BExp_Aligned Bit64 2
	  (BExp_Den (BVar "rs1" (BType_Imm Bit64))));
  BStmt_Assign (BVar "rd" (BType_Imm Bit64))
    (BExp_Cast BIExp_SignedCast
       (BExp_Load
	  (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
	  (BExp_Den (BVar "rs1" (BType_Imm Bit64)))
          BEnd_LittleEndian
	  Bit32) Bit64)

  Abbreviate Load ops (32-bit):

    bassert (baligned Bit64_tm (numSyntax.term_of_int 2, bden bvar_rs1))

    bassign (bvarimm64 brd, bscast64 (bload32_le (bden (bvarmem64_8 "MEM8")) (bden (bvar_rs1))))

    Done! (inspired by lifting of "LW x1,x2,0")

LOAD 64-BIT:

  BStmt_Assert
    (BExp_Aligned Bit64 3
       (BExp_Den (BVar "rs1" (BType_Imm Bit64))));
  BStmt_Assign (BVar "x1" (BType_Imm Bit64))
    (BExp_Load
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "x2" (BType_Imm Bit64)))
       BEnd_LittleEndian Bit64)

  Abbreviate Load ops (64-bit):

    bassert (baligned Bit64_tm (numSyntax.term_of_int 3, bden bvar_rs1))

    bassign (bvarimm64 brd, bload64_le (bden (bvarmem64_8 "MEM8")) (bden (bvar_rs1)))

    Done! (inspired by lifting of "LD x1,x2,0")

STORE 32-BIT:

  BStmt_Assert
    (BExp_Aligned Bit64 2
       (BExp_Den (BVar "rs1" (BType_Imm Bit64))));

  bassert (baligned Bit64_tm (numSyntax.term_of_int 2, bden bvar_rs1))

  BStmt_Assert
    (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
       (BExp_BinExp BIExp_Plus
	  (BExp_Den (BVar "rs1" (BType_Imm Bit64)))
	  (BExp_Const (Imm64 8w))) 4);

  bassert (mk_BExp_unchanged_mem_interval_distinct (Bit64_tm, numSyntax.term_of_int 0, numSyntax.term_of_int 16777216, bden bvar_rs1, numSyntax.term_of_int 4))

  BStmt_Assign (BVar "MEM8" (BType_Mem Bit64 Bit8))
    (BExp_Store
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "rs1" (BType_Imm Bit64)))
       BEnd_LittleEndian
       (BExp_Cast BIExp_LowCast
	  (BExp_Den (BVar "result" (BType_Imm Bit64))) Bit32))

val atomic_op_res = bplus (bden (bvarimm64 brd), bden (bvarimm64 brs2))

    bassign (bvarmem64_8 "MEM8", bstore_le (bden (bvarmem64_8 "MEM8"))
                                           (bden bvar_rs1)
                                           (blowcast32 atomic_op_res))

STORE 64-BIT:

  BStmt_Assert
    (BExp_Aligned Bit64 3
      (BExp_Den (BVar "rs1" (BType_Imm Bit64))));

  bassert (baligned Bit64_tm (numSyntax.term_of_int 3, bden bvar_rs1))

  BStmt_Assert
    (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
      (BExp_Den (BVar "rs1" (BType_Imm Bit64))) 8);

  bassert (mk_BExp_unchanged_mem_interval_distinct (Bit64_tm, numSyntax.mk_numeral mu_b, numSyntax.mk_numeral mu_e, bden bvar_rs1, numSyntax.term_of_int 8))

  BStmt_Assign (BVar "MEM8" (BType_Mem Bit64 Bit8))
    (BExp_Store
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "rs1" (BType_Imm Bit64)))
       BEnd_LittleEndian
       (BExp_Den (BVar "x14" (BType_Imm Bit64))))

val atomic_op_res = bplus (bden (bvarimm64 brd), bden (bvarimm64 brs2))

    bassign (bvarmem64_8 "MEM8", bstore_le (bden (bvarmem64_8 "MEM8"))
                                           (bden bvar_rs1)
                                           atomic_op_res)

*)

fun mk_atomic_binop bvar_rd bvar_rs2 funct5 =
  if funct5 = "00001"
  then (bden bvar_rs2)
  else if funct5 = "00000"
  then bplus (bden bvar_rd, bden bvar_rs2)
  else if funct5 = "00100"
  then bxor (bden bvar_rd, bden bvar_rs2)
  else if funct5 = "01100"
  then band (bden bvar_rd, bden bvar_rs2)
  else if funct5 = "01000"
  then bor (bden bvar_rd, bden bvar_rs2)
  else if funct5 = "10000"
  then bite (bslt (bden bvar_rd, bden bvar_rs2), bden bvar_rd, bden bvar_rs2)
  else if funct5 = "10100"
  then bite (bslt (bden bvar_rd, bden bvar_rs2), bden bvar_rs2, bden bvar_rd)
  else if funct5 = "11000"
  then bite (blt (bden bvar_rd, bden bvar_rs2), bden bvar_rd, bden bvar_rs2)
  else if funct5 = "11100"
  then bite (blt (bden bvar_rd, bden bvar_rs2), bden bvar_rs2, bden bvar_rd)
  else  raise ERR "mk_atomic_binop" ("Unsupported funct5 bits: "^funct5)

(* Dummy assignment to shadow memory for .aq and .rl flags *)
val mem_aqrl_bstmtl =
  [bassign (bvarmem (1,1) "MEM_aqrl",
           bstore_le (bden (bvarmem (1,1) "MEM_aqrl")) (bconst1 1) (bconst1 1))];

(* Adds effects of eventual acquire/release flags *)
fun add_aqrl bir_block_base is_aq is_rl =
  (* Case 1: .aq.rl: instruction is sequentially consistent *)
  if is_aq andalso is_rl
  then ([mk_BStmt_Fence (BM_ReadWrite_tm, BM_ReadWrite_tm)]@
	bir_block_base@mem_aqrl_bstmtl@
	[mk_BStmt_Fence (BM_ReadWrite_tm, BM_ReadWrite_tm)])
  (* Case 2: .rl: flush r/w before executing *)
  else if is_rl
  then ([mk_BStmt_Fence (BM_ReadWrite_tm, BM_Write_tm)]@
	bir_block_base@mem_aqrl_bstmtl)
  (* Case 3: .aq: prevent early r/w after *)
  else if is_aq
  then (bir_block_base@mem_aqrl_bstmtl@
	[mk_BStmt_Fence (BM_Read_tm, BM_ReadWrite_tm)])
  (* Case 3: No flags *)
  else bir_block_base
;

fun get_amo_bstmts mu_b mu_e hex_code =
  let
    val (funct5, aq, rl, rs2, rs1, funct3, rd, _) = parse_amo hex_code
    val bvar_rd = bvarimm64 (mk_gpr_var_name rd)
    val bvar_rs1 = bvarimm64 (mk_gpr_var_name rs1)
    val bvar_rs2 = bvarimm64 (mk_gpr_var_name rs2)
    val is_rl = str_to_bool rl
    val is_aq = str_to_bool aq
    val atomic_op_res = mk_atomic_binop bvar_rd bvar_rs2 funct5
    (* Stores the base functionality of the atomic instructions, sans effect of .aq and .rl flags *)
    val bir_block_base =
      (* Check if atomic instruction is 32- or 64-bit (.W or .D) *)
      if funct3 = "010" (* .W (RV32) *)
      then
	[(* 1. Load data value from address in rs1, place value into rd *)
	 bassert (baligned Bit64_tm (numSyntax.term_of_int 2, bden bvar_rs1)),

	 bassign (bvar_rd, bscast64 (bload32_le (bden (bvarmem64_8 "MEM8")) (bden (bvar_rs1)))),
	 (* 2. Apply binary operation to the loaded value and the original value in rs2,
	       then store the result back to the address in rs1 *)
	 bassert (mk_BExp_unchanged_mem_interval_distinct (Bit64_tm, numSyntax.mk_numeral mu_b, numSyntax.mk_numeral mu_e, bden bvar_rs1, numSyntax.term_of_int 4)),
	 bassign (bvarmem64_8 "MEM8", bstore_le (bden (bvarmem64_8 "MEM8"))
						(bden bvar_rs1)
						(blowcast32 atomic_op_res))
	]
      else if funct3 = "011" (* .D (RV64) *)
      then
	[(* 1. Load data value from address in rs1, place value into rd *)
	 bassert (baligned Bit64_tm (numSyntax.term_of_int 3, bden bvar_rs1)),

	 bassign (bvar_rd, bload64_le (bden (bvarmem64_8 "MEM8")) (bden (bvar_rs1))),
	 (* 2. Apply binary operation to the loaded value and the original value in rs2,
	       then store the result back to the address in rs1 *)
	 bassert (mk_BExp_unchanged_mem_interval_distinct (Bit64_tm, numSyntax.mk_numeral mu_b, numSyntax.mk_numeral mu_e, bden bvar_rs1, numSyntax.term_of_int 8)),
	 bassign (bvarmem64_8 "MEM8", bstore_le (bden (bvarmem64_8 "MEM8"))
						(bden bvar_rs1)
						atomic_op_res)
	]
      else raise ERR "get_amo_bstmts" ("Atomic instruction "^hex_code^" has unsupported funct3 bits: "^funct3)
  in
    (add_aqrl bir_block_base is_aq is_rl)
  end

fun get_lrsc_bstmts mu_b mu_e hex_code =
  let
    val (funct5, aq, rl, rs2, rs1, funct3, rd, _) = parse_amo hex_code
    val bvar_rd = bvarimm64 (mk_gpr_var_name rd)
    val bvar_rs1 = bvarimm64 (mk_gpr_var_name rs1)
    (* TODO: rs2 in LR *)
    val bvar_rs2 = bvarimm64 (mk_gpr_var_name rs2)
    val is_rl = str_to_bool rl
    val is_aq = str_to_bool aq
    (* "01010101" in hex *)
    val ones_32 = bconst32 16843009
    val ones_64 = bconst64 72340172838076673
    (* Empty memory *)
    val mem_zero = bden (bvarmem64_8 "MEM8_Z")
    (* Memory holding reserved addresses *)
    val mem_reserved = bden (bvarmem64_8 "MEM8_R")
    val (al, load_exp, ones, bytes, res_load_exp, cast) =
      if funct3 = "010" (* .W (RV32) *)
      then (2, (fn m => fn a => bscast64 (bload32_le m a)), ones_32, 4, bload64_le, blowcast32)
      else if funct3 = "011" (* .D (RV64) *)
      then (3, bload64_le, ones_64, 8, bload32_le, fn v => v)
      else raise ERR "get_lrsc_bstmts" ("LR/SC instruction "^hex_code^" has unsupported funct3 bits: "^funct3)
    val bir_block_base =
      if funct5 = "00010" (* LR *)
      then if rs2 = "00000"
	then
	  [(* 1. Load data value from address in rs1, place value into rd *)
	   bassert (baligned Bit64_tm (numSyntax.term_of_int al, bden bvar_rs1)),
	   bassign (bvar_rd, load_exp (bden (bvarmem64_8 "MEM8")) (bden (bvar_rs1))),
	   (* 2. Set reservation of memory *)
	   bassign (bvarmem64_8 "MEM8_R", bstore_le mem_zero (bden (bvar_rs1)) ones)
	  ]
	else raise ERR "get_lrsc_bstmts" ("LR instruction "^hex_code^" has non-zero rs2 bits: "^rs2)
      else if funct5 = "00011" (* SC *)
      then
	  [(* 1. Store value in rs2 into address in rs1 *)
	   bassert (baligned Bit64_tm (numSyntax.term_of_int al, bden bvar_rs1)),
	   bassert (mk_BExp_unchanged_mem_interval_distinct (Bit64_tm, numSyntax.mk_numeral mu_b, numSyntax.mk_numeral mu_e, bden bvar_rs1, numSyntax.term_of_int bytes)),
	   bassign (bvarmem64_8 "MEM8", 
		    bite (beq (res_load_exp mem_reserved (bden (bvar_rs1)),
			       ones),
			  bstore_le (bden (bvarmem64_8 "MEM8")) (bden bvar_rs1) (cast (bden bvar_rs2)),
			  bden (bvarmem64_8 "MEM8")
			 )
	   ),
	   (* 2. Reset reservation of memory *)
	   bassign (bvarmem64_8 "MEM8_R", mem_zero)
	  ]
      else raise ERR "get_lrsc_bstmts" ("LR/SC instruction "^hex_code^" has unsupported funct5 bits: "^funct5)
  in
    (add_aqrl bir_block_base is_aq is_rl)
  end
;

(* Generic function for lifting an instruction to custom BIR basic statement list using cheat *)
fun lift_by_cheat mu_b mu_e pc hex_code is_atomic_tm bstmt_list =
  let
    val riscv_bmr_tm = ``riscv_bmr``; (* TODO: Obtain this in a smarter way *)
    val pc_word = wordsSyntax.mk_wordi (pc, 64)
    val pc_imm = bir_immSyntax.gen_mk_Imm pc_word
    val pc_next_imm = bir_immSyntax.gen_mk_Imm (wordsSyntax.mk_wordii ((Arbnum.toInt pc)+4, 64))
    val wi_end =
      bir_interval_expSyntax.mk_WI_end (wordsSyntax.mk_wordii (Arbnum.toInt mu_b, 64),
                                        wordsSyntax.mk_wordii (Arbnum.toInt mu_e, 64))
    val byte_instruction = get_byte_word_l hex_code
    val prog =
      mk_BirProgram_list (Type.alpha,
	[mk_bir_block_list (Type.alpha,
			    mk_BL_Address_HC (pc_imm, stringSyntax.fromMLstring hex_code),
                            is_atomic_tm,
			    bstmt_list,
			    mk_BStmt_Jmp (mk_BLE_Label (mk_BL_Address pc_next_imm))
	)]
      )
    val lifted_tm =
      mk_bir_is_lifted_inst_prog (riscv_bmr_tm,
                                  pc_imm,
                                  wi_end,
                                  pairSyntax.mk_pair (pc_word, byte_instruction),
                                  prog
      )
    val lifted_thm = add_tag (Tag.read "multicore", prove(lifted_tm, cheat))
  in
    lifted_thm
  end

(* Lifts a fence instruction by producing a cheat. *)
fun lift_fence mu_b mu_e pc hex_code =
  let
    val bstmt_list = get_fence_bstmts hex_code
  in
    lift_by_cheat mu_b mu_e pc hex_code T bstmt_list
  end

(* Lifts an atomic memory operation instruction by producing a cheat. *)
fun lift_amo mu_b mu_e pc hex_code =
  let
    val bstmt_list = get_amo_bstmts mu_b mu_e hex_code
  in
    lift_by_cheat mu_b mu_e pc hex_code T bstmt_list
  end

(* Lifts a load-reserve or store-conditional by producing a cheat. *)
fun lift_lrsc mu_b mu_e pc hex_code =
  let
    val bstmt_list = get_lrsc_bstmts mu_b mu_e hex_code
  in
    lift_by_cheat mu_b mu_e pc hex_code T bstmt_list
  end

in
fun riscv_mc_lift_instr (mu_b, mu_e) pc hex_code =
  if is_fence hex_code
  then SOME (lift_fence mu_b mu_e pc hex_code)
  else if is_amo hex_code
  then SOME (lift_amo mu_b mu_e pc hex_code)
  (* LR/SC are instructions with opcode AMO, but are treated separately *)
  else if is_lrsc hex_code
  then SOME (lift_lrsc mu_b mu_e pc hex_code)
  else NONE
end
;

local
  (* M0 has address type 32, where this is 64. *)
  val addr_ty = fcpLib.index_type (Arbnum.fromInt 64);
  val val_ty = fcpLib.index_type (Arbnum.fromInt 8);
  val val_word_ty = wordsSyntax.mk_word_type val_ty
in
fun riscv_mk_data_mm mem_loc hex_code =
  let
    val ml_tm =
      wordsSyntax.mk_n2w ((numSyntax.mk_numeral mem_loc), addr_ty)
    val bytes = List.rev (bytes_of_hex_code hex_code)

    val _ =
      if length bytes = 4 then () else failwith "invalid hex-code";

    val bytes_tm = listSyntax.mk_list (bytes, val_word_ty)
  in
    pairSyntax.mk_pair (ml_tm, bytes_tm)
  end
end;

(* Note: In the ARM8 version, this constant is called
 * arm8_state_MEM. This is since the arm8_state record has an entry
 * called MEM, RISC-V seems to have a corresponding one called MEM8
 * of the same type. *)
val riscv_state_mem_tm =
  prim_mk_const{Name="riscv_state_MEM8", Thy="riscv"};
val riscv_dest_mem =
  HolKernel.dest_binop riscv_state_mem_tm (ERR "riscv_dest_mem" "");


val riscv_bmr_rec : bmr_rec = {
  bmr_const                =
    prim_mk_const{Name="riscv_bmr", Thy="bir_lifting_machines"},
  bmr_ok_thm               = riscv_bmr_OK,
  bmr_lifted_thm           = riscv_bmr_LIFTED,
  bmr_extra_lifted_thms    = [riscv_extra_LIFTS],
  bmr_change_interval_thms = [riscv_CHANGE_INTERVAL_THMS],
  bmr_eval_thm             = riscv_bmr_EVAL,
  bmr_label_thm            = riscv_bmr_label_thm,
  bmr_dest_mem             = riscv_dest_mem,
  bmr_extra_ss             = riscv_extra_ss,
  bmr_step_hex             = riscv_step_hex',
  bmr_mc_lift_instr        = SOME riscv_mc_lift_instr,
  bmr_mk_data_mm           = riscv_mk_data_mm,
  bmr_hex_code_size        =
    (fn hc => Arbnum.fromInt ((String.size hc) div 2)),
  bmr_ihex_param           = NONE
};

val _ = assert bmr_rec_sanity_check riscv_bmr_rec;

end;
