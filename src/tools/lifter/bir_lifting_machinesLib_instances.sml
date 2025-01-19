structure bir_lifting_machinesLib_instances :>
  bir_lifting_machinesLib_instances =
struct
(* For compilation: *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
(* Local theories: *)
open bir_exp_liftingLib bir_lifting_machinesTheory
     bir_nzcv_introsTheory bir_arm8_extrasTheory bir_m0_extrasTheory
     bir_riscv_extrasTheory
(* Local function libraries: *)
open bir_lifting_machinesLib;
(* Function libraries from examples/l3-machine-code: *)
open arm8_stepLib m0_stepLib riscv_stepLib

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

val arm8_state_mem_tm = prim_mk_const {Thy="arm8",
 Name = TypeBasePure.mk_recordtype_fieldsel {tyname = "arm8_state", fieldname = "MEM"}};
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
fun m0_reorder_bytes_data ef = if ef then I else List.rev;

local
  val addr_ty = fcpLib.index_type (Arbnum.fromInt 32);
  val val_ty = fcpLib.index_type (Arbnum.fromInt 8);
  val val_word_ty = wordsSyntax.mk_word_type val_ty
in
fun m0_mk_data_mm ef mem_loc hex_code =
  let
    val ml_tm =
      wordsSyntax.mk_n2w (numSyntax.mk_numeral mem_loc, addr_ty)
    val bytes = m0_reorder_bytes_data ef (bytes_of_hex_code hex_code)
    val _ = if (length bytes = 2) orelse (length bytes = 4)
            then ()
            else failwith "invalid hex-code";
    val bytes_tm = listSyntax.mk_list (bytes, val_word_ty)
  in
    pairSyntax.mk_pair (ml_tm, bytes_tm)
  end
end;

val m0_state_mem_tm = prim_mk_const {Thy="m0",
 Name = TypeBasePure.mk_recordtype_fieldsel {tyname = "m0_state", fieldname = "MEM"}};
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
     EQ_13w_EVAL, EQ_15w_EVAL, R_name_EVAL, holba_auxiliaryTheory.w2w_n2w,
     m0_extra_FOLDS_GEN, Mode_Handler_INTRO, holba_auxiliaryTheory.align_aligned_add,
     holba_auxiliaryTheory.align_aligned_sub, LowestSetBit_n2w, numeral_bitTheory.LOWEST_SET_BIT,
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
fun m0_mod_reorder_bytes_data ef = if ef then I else List.rev;

local
  val addr_ty = fcpLib.index_type (Arbnum.fromInt 32);
  val val_ty = fcpLib.index_type (Arbnum.fromInt 8);
  val val_word_ty = wordsSyntax.mk_word_type val_ty
in

fun m0_mod_mk_data_mm ef mem_loc hex_code = let
  val ml_tm = wordsSyntax.mk_n2w (numSyntax.mk_numeral mem_loc, addr_ty)
  val bytes = m0_mod_reorder_bytes_data ef (bytes_of_hex_code hex_code)
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
     EQ_13w_EVAL, EQ_15w_EVAL, R_name_EVAL, holba_auxiliaryTheory.w2w_n2w,
     m0_extra_FOLDS_GEN, Mode_Handler_INTRO, holba_auxiliaryTheory.align_aligned_add,
     holba_auxiliaryTheory.align_aligned_sub, LowestSetBit_n2w, numeral_bitTheory.LOWEST_SET_BIT,
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
  (type_rws ``:riscv_state``)@
  (type_rws ``:MachineCSR``)
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
val riscv_state_mem_tm = prim_mk_const { Thy="riscv",
 Name = TypeBasePure.mk_recordtype_fieldsel {tyname = "riscv_state", fieldname = "MEM8"}};
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
  bmr_mk_data_mm           = riscv_mk_data_mm,
  bmr_hex_code_size        =
    (fn hc => Arbnum.fromInt ((String.size hc) div 2)),
  bmr_ihex_param           = NONE
};

val _ = assert bmr_rec_sanity_check riscv_bmr_rec;

end;
