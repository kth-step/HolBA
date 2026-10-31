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
 * for ``:ProcState``), with reg'mstatus (rec'mstatus w) = w and so on for
 * the CSRs that are lifted as the words of their registers... *)
val riscv_REWRS = (
  (type_rws ``:riscv_state``)@
  (type_rws ``:MachineCSR``)@
  (type_rws ``:SupervisorCSR``)@
  [riscv_stepTheory.reg_rec_id]
);

(* The cast to 8 bits of a 2-bit word, which is what the lifted privilege
 * (BIR variable "priv", the 8-bit immediate w2w (ms.c_privilege
 * ms.procID)) is after an instruction that writes the privilege, as a BIR
 * expression: the cast of a literal, such as the w2w (3w:word2) after a
 * trap, is evaluated, the cast is pushed into a conditional, and the cast
 * of a field of a word, such as the w2w ((12 >< 11) mstatus) after MRET
 * (the privilege becomes mstatus.MPP), becomes a shift, a cast and a mask.
 * The privilege itself, w2w (ms.c_privilege ms.procID), is left as it
 * is. *)
local
  val word2_ty = ``:word2``
  val word8_ty = ``:word8``
  val cond_rand = ISPEC ``w2w : word2 -> word8`` boolTheory.COND_RAND
  fun num_of tm = Arbnum.toInt (numSyntax.dest_numeral tm)
in
  fun riscv_w2w_word2_conv tm =
    let
      val (x, _) = wordsSyntax.dest_w2w tm
      val _ = if type_of x = word2_ty andalso type_of tm = word8_ty then ()
              else raise UNCHANGED
    in
      if wordsSyntax.is_word_literal x then wordsLib.WORD_EVAL_CONV tm
      else if is_cond x then REWR_CONV cond_rand tm
      else if wordsSyntax.is_word_extract x then
        let
          val (h, l, w, _) = wordsSyntax.dest_word_extract x
          val (hn, ln) = (num_of h, num_of l)
          (* the number of bits of w in the 2-bit field *)
          val k = Int.min (hn, ln + 1) - ln + 1
          val _ = if k > 0 then () else raise UNCHANGED
          val shifted =
            if ln = 0 then w else wordsSyntax.mk_word_lsr (w, l)
          val cast =
            if type_of shifted = word8_ty then shifted
            else wordsSyntax.mk_w2w (shifted, ``:8``)
          val mask = wordsSyntax.mk_wordii (if k = 1 then 1 else 3, 8)
        in
          blastLib.BBLAST_PROVE
            (mk_eq (tm, wordsSyntax.mk_word_and (cast, mask)))
        end
      else raise UNCHANGED
    end
    handle HOL_ERR _ => raise UNCHANGED
end

(* ... and as a simplification set, with the casts of 2-bit words to 8 bits
 * above. *)
val riscv_extra_ss =
  simpLib.merge_ss
    [rewrites (riscv_REWRS@[combinTheory.APPLY_UPDATE_THM]),
     simpLib.std_conv_ss
       {name = "riscv_w2w_word2", conv = riscv_w2w_word2_conv,
        pats = [``(w2w (x : word2)) : word8``]}]

(* The CSRs that are lifted as the words of their registers (mstatus, mie,
 * mcause and mip; see riscv_sysregs_lifted_imms_LIST in
 * bir_lifting_machinesScript.sml) in a step theorem of the hart of the
 * machine state vn, as expressions on these words:
 *
 *   - a field of a stored register, (vn.c_MCSR vn.procID).mstatus.MIE,
 *     becomes bits of the lifted word,
 *     word_bit 3 (reg'mstatus (vn.c_MCSR vn.procID).mstatus);
 *   - a register written by the instruction becomes rec' of a word, so
 *     that the lifter finds the word of the BIR variable after the
 *     instruction, by reg'mstatus (rec'mstatus w) = w;
 *   - bit fields of words are stated with masks, shifts and casts to 8 and
 *     64 bits, which BIR expressions have.  Each such step is an instance
 *     of an equation of words that is proved by bit-blasting when it is
 *     made.  In the values written to CSRs every bit field is rewritten;
 *     elsewhere (hypotheses, values written to registers) only bit fields
 *     of the words of the lifted CSRs, so that other instructions are
 *     lifted as before. *)
local
  val csr_tys = [``:mstatus``, ``:mie``, ``:mcause``, ``:mip``]
  val record_rwts = List.concat (List.map type_rws csr_tys)
  val rec_fields = bir_riscv_extrasTheory.riscv_csr_rec_fields
  val reg_fields = CONJUNCTS bir_riscv_extrasTheory.riscv_csr_reg_fields
  val rec_reg_id = CONJUNCTS bir_riscv_extrasTheory.riscv_csr_rec_reg_id
  val word_rwts =
    [riscv_stepTheory.reg_rec_id,
     bir_riscv_extrasTheory.riscv_csr_reg_updates,
     bir_riscv_extrasTheory.riscv_csr_cond_rand,
     bir_riscv_extrasTheory.riscv_csr_rec_fields]

  val word64_ty = ``:word64``
  val word2_ty = ``:word2``
  fun closed tm = List.null (free_vars tm)
  fun num_of tm = Arbnum.toInt (numSyntax.dest_numeral tm)
  fun pow2 k = Arbnum.pow (Arbnum.two, Arbnum.fromInt k)
  fun mask (h, l) = Arbnum.- (pow2 (h + 1), pow2 l)
  fun low_mask k = Arbnum.- (pow2 k, Arbnum.one)
  (* the word of the word type wty with value n *)
  fun word_of wty n =
    wordsSyntax.mk_n2w (numSyntax.mk_numeral n, wordsSyntax.dest_word_type wty)
  (* the width of the words with index type ity *)
  fun width ity = Arbnum.toInt (fcpSyntax.dest_numeric_type ity)
  fun prove_eq tm1 tm2 =
    blastLib.BBLAST_PROVE (mk_eq (tm1, tm2))
    handle HOL_ERR _ => raise UNCHANGED
  (* (h >< l) w, with the bits of w that it takes, if it is an extract of a
     word w with ok w *)
  fun dest_extract ok tm =
    let
      val (h, l, w, ty) = wordsSyntax.dest_word_extract tm
      val (hn, ln) = (num_of h, num_of l)
      val hn' = Int.min (hn, ln + width ty - 1)
    in
      if ok w then (hn', ln, w) else raise UNCHANGED
    end
    handle HOL_ERR _ => raise UNCHANGED
  fun extract_conv ok tm =
    if boolSyntax.is_eq tm andalso
       wordsSyntax.is_word_extract (lhs tm) andalso
       wordsSyntax.is_word_literal (rhs tm) then
      (* (h >< l) w = c *)
      let
        val (h, l, w) = dest_extract ok (lhs tm)
        val c = Arbnum.* (wordsSyntax.dest_word_literal (rhs tm), pow2 l)
      in
        prove_eq tm
          (mk_eq (wordsSyntax.mk_word_and (w, word_of (type_of w) (mask (h, l))),
                  word_of (type_of w) c))
      end
    else if wordsSyntax.is_word_lo tm andalso
            wordsSyntax.is_word_extract (fst (wordsSyntax.dest_word_lo tm)) andalso
            wordsSyntax.is_word_literal (snd (wordsSyntax.dest_word_lo tm)) then
      (* (h >< 0) w <+ c *)
      let
        val (e, c) = wordsSyntax.dest_word_lo tm
        val (h, l, w) = dest_extract ok e
        val _ = if l = 0 then () else raise UNCHANGED
      in
        prove_eq tm
          (wordsSyntax.mk_word_lo
             (wordsSyntax.mk_word_and (w, word_of (type_of w) (mask (h, 0))),
              word_of (type_of w) (wordsSyntax.dest_word_literal c)))
      end
    else if wordsSyntax.is_word_lsl tm andalso
            wordsSyntax.is_w2w (fst (wordsSyntax.dest_word_lsl tm)) andalso
            wordsSyntax.is_word_extract
              (fst (wordsSyntax.dest_w2w (fst (wordsSyntax.dest_word_lsl tm)))) then
      (* w2w ((h >< l) w) << l, as wide as w *)
      let
        val (c, n) = wordsSyntax.dest_word_lsl tm
        val (h, l, w) = dest_extract ok (fst (wordsSyntax.dest_w2w c))
        val _ = if numSyntax.is_numeral n andalso num_of n = l andalso
                   type_of w = type_of tm then () else raise UNCHANGED
      in
        prove_eq tm (wordsSyntax.mk_word_and (w, word_of (type_of w) (mask (h, l))))
      end
    else if wordsSyntax.is_w2w tm andalso
            wordsSyntax.is_word_extract (fst (wordsSyntax.dest_w2w tm)) then
      (* w2w ((h >< l) w), with a shift and a mask *)
      let
        val (h, l, w) = dest_extract ok (fst (wordsSyntax.dest_w2w tm))
        val ty = type_of tm
        val wty = wordsSyntax.dest_word_type ty
        val k = h - l + 1
        val shifted =
          if l = 0 then w
          else wordsSyntax.mk_word_lsr (w, numSyntax.term_of_int l)
        val cast =
          if ty = type_of w then shifted else wordsSyntax.mk_w2w (shifted, wty)
      in
        if k < width wty then
          prove_eq tm (wordsSyntax.mk_word_and (cast, word_of ty (low_mask k)))
        else raise UNCHANGED
      end
    else if wordsSyntax.is_w2w tm andalso type_of tm = word64_ty andalso
            type_of (fst (wordsSyntax.dest_w2w tm)) = word2_ty andalso
            ok (fst (wordsSyntax.dest_w2w tm)) andalso
            not (wordsSyntax.is_word_literal (fst (wordsSyntax.dest_w2w tm))) then
      (* a 2-bit word, cast to 64 bits through the 8-bit immediate *)
      ISPEC (fst (wordsSyntax.dest_w2w tm))
        bir_riscv_extrasTheory.riscv_w2w_word2_word64
    else if wordsSyntax.is_word_concat tm andalso type_of tm = word64_ty then
      (* (63 >< l) a @@ (l - 1 >< 0) b *)
      let
        val (x, y) = wordsSyntax.dest_word_concat tm
        val (h1, l1, a) = dest_extract ok x
        val (h2, l2, b) = dest_extract ok y
        val _ = if h1 = 63 andalso l2 = 0 andalso h2 + 1 = l1 andalso
                   type_of a = word64_ty andalso type_of b = word64_ty
                then () else raise UNCHANGED
        val m = word_of word64_ty (low_mask l1)
      in
        prove_eq tm
          (wordsSyntax.mk_word_or
             (wordsSyntax.mk_word_and (a, wordsSyntax.mk_word_1comp m),
              wordsSyntax.mk_word_and (b, m)))
      end
    else raise UNCHANGED
  (* closed words and booleans that the rewrites leave, such as
     w2w (3w:word2) << 11 *)
  fun ground_conv tm =
    if closed tm andalso
       (type_of tm = bool orelse wordsSyntax.is_word_type (type_of tm)) andalso
       not (wordsSyntax.is_word_literal tm) andalso
       not (bitstringSyntax.is_v2w tm) andalso
       not (Teq tm) andalso not (Feq tm) then
      let
        val th = EVAL tm
      in
        if aconv (rhs (concl th)) tm then raise UNCHANGED else th
      end
    else raise UNCHANGED
  (* a value written to a CSR *)
  val value_conv =
    TOP_DEPTH_CONV (extract_conv (K true)) THENC DEPTH_CONV ground_conv
  val reg_value_conv =
    SIMP_CONV std_ss word_rwts THENC value_conv
  (* fails (HOL_ERR) on a term that is not an update of the field, so that
     FIRST_CONV tries the next field *)
  fun dest_fupd fupd_tm tm =
    let
      val (f, m) = dest_comb tm
      val (fupd, k) = dest_comb f
    in
      if same_const fupd fupd_tm then combinSyntax.dest_K_1 k
      else failwith "not an update of this field"
    end
  fun at_value conv = RATOR_CONV (RAND_CONV (RAND_CONV conv))
  (* the value written to a register-typed CSR: rec' of a word *)
  fun reg_fupd_conv (fupd_tm, reg_rec) tm =
    let
      val x = dest_fupd fupd_tm tm
      val (rec_tm, _) = strip_comb (lhs (snd (strip_forall (concl reg_rec))))
      val _ = if is_comb x andalso same_const (rator x) rec_tm
              then failwith "already a word" else ()
      (* x = rec' (reg' x) *)
      val th0 = SYM (ISPEC x reg_rec)
      val th1 = RAND_CONV reg_value_conv (rhs (concl th0))
    in
      at_value (K (TRANS th0 th1)) tm
    end
  (* the value written to a CSR that the model stores as a word *)
  fun word_fupd_conv fupd_tm tm =
    (dest_fupd fupd_tm tm; at_value value_conv tm)
  fun fupds ty = List.map (fn (n, {fupd, ...}) => (n, fupd)) (TypeBase.fields_of ty)
  val mcsr_fupds = fupds ``:MachineCSR``
  val reg_fields_names = ["mstatus", "mie", "mcause", "mip"]
  val value_convs =
    ListPair.map (fn (n, th) => reg_fupd_conv (Lib.assoc n mcsr_fupds, th))
      (reg_fields_names, rec_reg_id) @
    List.mapPartial
      (fn (n, fupd) =>
         if Lib.mem n reg_fields_names then NONE
         else SOME (word_fupd_conv fupd))
      (mcsr_fupds @ fupds ``:SupervisorCSR``)
  fun field_sel ty name =
    prim_mk_const {Thy = "riscv",
                   Name = TypeBasePure.mk_recordtype_fieldsel
                            {tyname = ty, fieldname = name}}
in
  fun riscv_csr_conv vn =
    let
      val mcsr = ``^vn.c_MCSR ^vn.procID``
      (* the registers of the hart, and their lifted words *)
      val regs =
        List.map (fn n => mk_comb (field_sel "MachineCSR" n, mcsr))
          reg_fields_names
      val images =
        List.map
          (fn r => mk_comb (prim_mk_const
                              {Thy = "riscv",
                               Name = "reg'" ^ fst (dest_type (type_of r))}, r))
          regs
      fun is_image w = List.exists (aconv w) images
      (* reg_fields instantiated to the registers of the hart *)
      val base_fields =
        List.map
          (fn th =>
             let
               val (r, _) = dest_forall (concl th)
               val n = fst (dest_type (type_of r))
             in
               ISPEC (mk_comb (field_sel "MachineCSR" n, mcsr)) th
             end) reg_fields
      val fields_conv =
        SIMP_CONV (std_ss ++ rewrites (record_rwts @ base_fields))
          [rec_fields]
    in
      fields_conv THENC
      DEPTH_CONV (FIRST_CONV value_convs) THENC
      TOP_DEPTH_CONV (extract_conv is_image)
    end
end

(* A load of 2, 4 or 8 bytes, m e1 @@ ... @@ m e0, as riscv_mem_load_half,
 * riscv_mem_load_word or riscv_mem_load_dword at the address e0 of its
 * lowest byte, which the lifter lifts to a BIR load.  riscv_extra_FOLDS
 * folds the loads whose addresses are e0 + 1w, e0 + 2w and so on; this
 * folds those whose addresses are written otherwise, such as the bytes of
 * mtimecmp in a read of mip, from 8w * w2w procID + 0x2004007w down to
 * 8w * w2w procID + 0x2004000w, and those of mtime, at constant addresses
 * (the step library adds the constants up).  Each address is shown to be
 * that of the definition by wordsLib.WORD_ARITH_CONV. *)
local
  val load_defs =
    [(2, bir_riscv_extrasTheory.riscv_mem_load_half_def),
     (4, bir_riscv_extrasTheory.riscv_mem_load_word_def),
     (8, bir_riscv_extrasTheory.riscv_mem_load_dword_def)]
  (* the bytes of a concatenation, the most significant first *)
  fun bytes tm =
    let
      val (a, b) = wordsSyntax.dest_word_concat tm
    in
      a :: bytes b
    end
    handle HOL_ERR _ => [tm]
  (* m d = m e, for the byte m d of the definition and the byte m e *)
  fun byte_eq (b1, b2) =
    if aconv b1 b2 then REFL b1
    else AP_TERM (rator b1)
           (EQT_ELIM (wordsLib.WORD_ARITH_CONV (mk_eq (rand b1, rand b2))))
  (* t1 = t2, for concatenations of bytes of the same shape *)
  fun chain_eq (t1, t2) =
    let
      val (a1, b1) = wordsSyntax.dest_word_concat t1
      val (a2, b2) = wordsSyntax.dest_word_concat t2
    in
      MK_COMB (AP_TERM (rator (rator t1)) (byte_eq (a1, a2)),
               chain_eq (b1, b2))
    end
    handle HOL_ERR _ => byte_eq (t1, t2)
in
  fun riscv_mem_load_fold_conv tm =
    let
      val bs = bytes tm
      val def = Lib.assoc (List.length bs) load_defs
      val m = rator (List.last bs)
      val _ = if List.all (fn b => is_comb b andalso aconv (rator b) m) bs
              then () else raise UNCHANGED
      (* riscv_mem_load_... m e0 = m (e0 + ...) @@ ... @@ m e0 *)
      val th0 = SPECL [m, rand (List.last bs)] def
      val th1 = TRANS th0 (chain_eq (rhs (concl th0), tm))
    in
      SYM th1
    end
    handle HOL_ERR _ => raise UNCHANGED
end

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

  (* ~word_bit 0 pc, the alignment of the pc in the step theorems, as
     aligned 1 pc, which the lifter discharges for a constant pc *)
  fun pc_aligned vn =
    ISPEC ``^vn.c_PC ^vn.procID`` bir_riscv_extrasTheory.riscv_word_bit_0_aligned

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
      val ms_thm = if (length bytes = 2) then
                      bmr_ms_mem_contains_RISCV_2
                   else if (length bytes = 4) then
                      bmr_ms_mem_contains_RISCV
                   else failwith "invalid hex-code";

      val thm0 = SPECL (vn::(List.rev bytes))
                       ms_thm

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
    (* The memory at the pc, and the conjuncts of riscv_state_is_OK (the
     * extra predicate of riscv_bmr), discharge the hypotheses that they
     * state. *)
    val thm4 = foldl (fn (pre_thm, thm) => PROVE_HYP pre_thm thm)
                     thm3
                     (pc_mem_thms @ (riscv_extra_THMS vn))

    val thm5 = DISCH_ALL thm4
    (* The remaining hypotheses are lifted to assertions: the contract of
     * the M-mode step theorems (H1 to H6, see bir_lifting_machinesScript),
     * alignment and the conditions of the instruction.  The conjuncts of
     * riscv_state_is_OK simplify the hypotheses that they do not state as
     * they are, such as ~word_bit 1 pc \/ misa.C, and the conclusion, such
     * as the value of mepc that a CSR instruction reads. *)
    val thm6 =
      CONV_RULE (simp_conv THENC TOP_DEPTH_CONV riscv_mem_load_fold_conv THENC
                 riscv_csr_conv vn THENC simp_conv2 THENC
                 (SIMP_CONV std_ss (riscv_extra_THMS vn)) THENC
                 PURE_REWRITE_CONV [pc_aligned vn]) thm5
    (* Minimum and maximum (from AMOMIN and similar) as comparisons *)
    val thm7 =
      PURE_REWRITE_RULE [wordsTheory.word_min_def, wordsTheory.word_max_def,
                         wordsTheory.word_smin_def, wordsTheory.word_smax_def] thm6
    val thm8 = UNDISCH_ALL thm7
  in
    thm8
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
      if (length bytes = 2) orelse (length bytes = 4) then ()
      else failwith "invalid hex-code";

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
