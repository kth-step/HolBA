
(****************)
(* Main functor *)
(****************)

functor bir_inst_liftingFunctor (MD : sig val mr : bir_lifting_machinesLib.bmr_rec end) : bir_inst_lifting = struct

(* dependencies *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
(* ================================================ *)

  open bir_inst_liftingHelpersLib;

  (* For debugging RISC-V:

    val mr = riscv_bmr_rec;

  *)

  (* For debugging
  structure MD = struct val mr = arm8_bmr_rec end;
  structure MD = struct val mr = m0_bmr_rec false true end;
  structure MD = struct val mr = m0_mod_bmr_rec false true end;
  structure MD = struct val mr = riscv_bmr_rec end;

  val pc = Arbnum.fromInt 0x10000
  val (mu_b, mu_e) = (Arbnum.fromInt 0x1000, Arbnum.fromInt 0x100000)
  val (_, mu_thm) = mk_WI_end_of_nums_WFE ``:64`` (Arbnum.fromInt 0x1000) (Arbnum.fromInt 0x100000)

  (* debug case for m0/m0_mod *)
  val pc = Arbnum.fromInt 0x3ee
  val (mu_b, mu_e) = (Arbnum.fromInt 0x00, Arbnum.fromInt 0x100000)
  val (_, mu_thm) = mk_WI_end_of_nums_WFE ``:64`` (Arbnum.fromInt 0x00) (Arbnum.fromInt 0x100000)
  val hex_code = "f002fecb"

  fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)

  (* ARM 8 *)
  val hex_code = hex_code_of_asm `adds x0, x1, #1`
  val hex_code = hex_code_of_asm `add x0, x1, x2`
  val hex_code = hex_code_of_asm `ldr x0, [x1, #8]`
  val hex_code = hex_code_of_asm `cmp x0, #0`
  val hex_code = hex_code_of_asm `lsl x0, x2, #8`
  val hex_code = hex_code_of_asm `add w0, w1, w2`
  val hex_code = hex_code_of_asm `adds w0, w1, w2`
  val hex_code = hex_code_of_asm `MOV x0 , x1`
  val hex_code = hex_code_of_asm `ADD X0, X1, W2, SXTW`
  val hex_code = hex_code_of_asm `LDRSW X0, [X1, #8]`
  val hex_code = hex_code_of_asm `lsl x0, x2, #8`
  val hex_code = hex_code_of_asm `ldr x0, [x2, #0]`
  val hex_code = hex_code_of_asm `adds x1, x1, #0`

  val hex_code = "B8617800"
  val hex_code = "94000000"
  val hex_code = "D65F03C0";
  val hex_code = "12001C00"
  val hex_code = "54000061";
  val hex_code = "79000001"
  val hex_code = "B4000040"
  val hex_code = "54000089"
  val hex_code = "90000000"
  val hex_code = "DA020000";
  val hex_code = "DAC01441";
  val hex_code = "DAC01041"

  (* M0 *)
  val hex_code = "3202"
  val hex_code = "C500"
  val hex_code = "B5F7"
  val hex_code = "448F"
  val hex_code = "D001"
  val hex_code = "a202"
  val hex_code = "466a"
  val hex_code = "aa02"

  val hex_code_desc = hex_code
*)

  open MD;

  (*****************)
  (* Preprocessing *)
  (*****************)

  (* The following code looks at the parameter of the functor and
     precomputes certain values that are needed later a lot. *)

  (* destruct the record to get the components easily *)
  val (mr_imms, mr_mem, mr_pc, _, mr_step_rel) = bmr_rec_extract_fields mr

  (* Some useful vars of the right type *)
  val (ms_ty, addr_sz_ty, mem_val_sz_ty)  = dest_bir_lifting_machine_rec_t_ty (type_of (#bmr_const mr))
  val ms_v = mk_var ("ms", ms_ty);
  val bs_v = mk_var ("bs", bir_state_t_ty);

  val addr_sz_immtype_t = bir_immSyntax.bir_immtype_t_of_word_ty (wordsSyntax.mk_word_type addr_sz_ty)

  val addr_sz_dimword_THM = SIMP_CONV (std_ss++wordsLib.SIZES_ss) [] (wordsSyntax.mk_dimword addr_sz_ty)

  val bmr_eval_REWRS = let
    val tms = [
       (mk_icomb (bmr_mem_lf_tm, (#bmr_const mr))),
       (mk_icomb (bmr_pc_lf_tm, (#bmr_const mr))),
       (mk_icomb (bmr_pc_var_tm, (#bmr_const mr))),
       (mk_icomb (bmr_pc_var_cond_tm, (#bmr_const mr))),
       (mk_icomb (bmr_mem_var_tm, (#bmr_const mr))),
       (mk_icomb (bmr_field_step_fun_tm, (#bmr_const mr))),
       (mk_icomb (bmr_field_extra_tm, (#bmr_const mr))),
       (mk_bmr_field_imms (#bmr_const mr)),
       (mk_bmr_field_pc (#bmr_const mr)),
       (mk_bmr_field_mem (#bmr_const mr))]
    val thms0 = map (SIMP_CONV (std_ss++bmr_ss) [(#bmr_eval_thm mr),
       bmr_mem_lf_def, bmr_pc_lf_def, bmr_pc_var_cond_def, bmr_pc_var_def,
       bmr_mem_var_def]) tms
    val thms1 = map GEN_ALL thms0
  in
    LIST_CONJ thms1
  end;


  fun mk_mem_addr_from_num (n:num) =
    wordsSyntax.mk_n2w (numSyntax.mk_numeral n, addr_sz_ty);

  (* Instantiate some useful syntax funs *)
  val (pc_sz, mk_pc_of_term) = bmr_rec_mk_pc_of_term mr
  val mk_label_of_num = bmr_rec_mk_label_of_num mr
  val mk_label_of_num_eq_pc = bmr_rec_mk_label_of_num_eq_pc mr;
  val pc_num_var = mk_var ("pc_n", numSyntax.num);

  fun inst_bmr_thm bmr_ok_flag thm = let
     val thm0 = INST_TYPE [mk_vartype "'o" |-> block_observe_ty] thm
     val thm1 = ISPEC (#bmr_const mr) thm0;
     val thm2 = if bmr_ok_flag then MP thm1 (#bmr_ok_thm mr) else thm1
  in
    thm2
  end;


  (* Instantiate the inst_lifting theorem with the record and types. *)
  val inst_lift_THM =
    inst_bmr_thm true bir_is_lifted_inst_block_COMPUTE_OPTIMISED;

  val inst_lift_THM_ex_vars = let
    val (_, t)  = dest_forall (concl inst_lift_THM)
    val (_, t)  = dest_imp_only t
    val (_, t)  = strip_forall t
    val (_, t)  = dest_imp_only t
    val (_, t)  = strip_forall t
    val (t, _)  = dest_imp_only t
    val (_, t)  = strip_forall t
    val (vs, _) = strip_exists t
  in vs end;


  (* Construct the extra thms *)
  val ms_extra_REWRS0 = let
     val thm0 = SPECL [bs_v, ms_v] (ISPEC (#bmr_const mr) bmr_rel_implies_extra)
     val thm1 = UNDISCH thm0
  in thm1 end;

  val ms_extra_REWRS =
     SIMP_RULE (std_ss) [bmr_eval_REWRS] ms_extra_REWRS0;

  (* precomputed imms_lifting *)
  val mr_imms_lf_of_ms = let
    fun do_it tm = let
      val (_, lf_tm) = dest_BMLI tm
      val tm0 = mk_comb (lf_tm, ms_v)
      val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
    in (tm, tm1) end
  in List.map do_it mr_imms end;

  (* precompute mem lifting *)
  val mr_mem_lf_of_ms = let
    val (_, lf_tm) = dest_BMLM mr_mem
    val tm0 = mk_comb (lf_tm, ms_v)
    val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
  in tm1 end;

  (* precompute pc lifting *)
  val (pc_var_t, pc_cond_var_t, mr_pc_lf_of_ms) = let
    val (pc_var_t, pc_cond_var_t, lf_tm) = dest_BMLPC mr_pc
    val tm0 = mk_comb (lf_tm, ms_v)
    val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
  in (pc_var_t, pc_cond_var_t, tm1) end;

  (* Build cond-lift theorems for all accessed fields *)
  (* RISC-V TODO: Some stuff here does not work as intended... *)
  val cond_lift_fields_thm = let
     val cond_tm = list_mk_icomb PROTECTED_COND_tm [
        mk_var ("c", bool),
        mk_var ("ms1", ms_ty),
        mk_var ("ms2", ms_ty)];

  (* RISC-V TODO: This changed to not loop in presence of process IDs, see if it still works... *)
     fun mk_lift_thm tm =
       GEN_ALL (QCONV (SIMP_CONV std_ss [PROTECTED_COND_RAND, Once PROTECTED_COND_RATOR])
                      (subst [ms_v |-> cond_tm] tm))


     fun mk_imm_thm (_, tm) =  mk_lift_thm ( (rand tm))

  in
    LIST_CONJ (
     (mk_lift_thm mr_mem_lf_of_ms) :: (* RISC-V TODO: OK. *)
     (mk_lift_thm (rand mr_pc_lf_of_ms)) ::
     map (mk_lift_thm o rand o snd) mr_imms_lf_of_ms)
  end;


  (* Constructing net for expression lifting. The _raw version does the lifting for
     the environment in a specially prepared net. Since we usually want the whole
     lifting to fail if some preconds remain, the wrapper exp_lift_fn checks for
     the existence of such preconds. Notice that this does not mean hypothesis, i.e.
     according to the implementation of bir_exp_lift only "bir_is_lifted_exp" terms. *)
  val exp_lift_fn_raw = let
     val eln0 = eln_default
     val eln1 = eln_add_thms eln0 [bs_v, ms_v] [SPECL [bs_v, ms_v] (#bmr_lifted_thm mr)]
     val eln2 = eln_add_thms eln1 [] (#bmr_extra_lifted_thms mr)
     val env_t = mk_bst_environ bs_v
  in
     bir_exp_lift env_t eln2
  end;

(* For debugging RISC-V:
  (* TODO: Make shortcuts for debugging other things than preconds *)

  val hex_code = String.map Char.toUpper "FCE0879B"; (* "addiw x15,x1,-50" *)

  val hex_code_desc = hex_code;
  val (next_thms, mm_tm, label_tm) = mk_inst_lifting_theorems hex_code hex_code_desc
  val (lb, ms_case_cond_t, next_thm) = el 1 (preprocess_next_thms label_tm next_thms)
  val next_thm0 = REWRITE_RULE [ASSUME ms_case_cond_t] next_thm
  val (preconds, next_tm) = strip_imp_only (concl next_thm0)
  val tm = (* Put term returned by exception here, don't forget type information... *)

val tm = ``Imm64
                (w2w ((riscv_mem_half ms.MEM8 (ms.c_gpr ms.procID 2w - 50w)):word16))``;

  (* In case of several preconds, continue with the following for 2, 3, 4, ...*)
  (* val tm = el 2 preconds *)

*)
  fun exp_lift_fn tm = let
     val res = exp_lift_fn_raw tm
     val _ = if is_imp_only (concl res) then failwith "exp_lift_fn: preconds present" else ()
     val exp_tm = rand (rator (concl res))
     val _ = if free_in ms_v exp_tm then failwith "exp_lift_fn: ms still present" else ()
  in
     res
  end handle HOL_ERR _ =>
    raise (bir_inst_liftingAuxExn (BILED_lifting_failed tm));


  (*******************************************************)
  (* Support for Intel Hex files                         *)
  (*******************************************************)


  fun read_hex_file file_name = case (#bmr_ihex_param mr) of
     NONE => failwith "No Intel HEX tools implemented for this architecture"
   | SOME p =>
      List.map (fn (pc, hcs) => mk_bir_inst_lifting_region pc hcs)
        (decode_ihex_list_hex p (read_from_ihex_file file_name))

  fun write_hex_file file_name data = case (#bmr_ihex_param mr) of
     NONE => failwith "No Intel HEX tools implemented for this architecture"
   | SOME p => write_to_ihex_file file_name true (encode_ihex_list_hex p
       (List.map (fn BILMR (pc, el) => (pc, List.map fst el)) data))


  (*******************************************************)
  (* patched step theorems                               *)
  (*******************************************************)

val oracletag = "BIR_step_patch";
val StepPatchThm = mk_oracle_thm oracletag;
val mk_patch_thms = List.map (fn tm => UNDISCH_ALL (StepPatchThm ([], tm)));

val patch_thms_m0modft_a202 = mk_patch_thms [
``(* copied an modified accordingly, based on "aa02" *)
  (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms
       (ms.base.REG RName_PC,[2w; 162w])) ==>
  (ms.countw <=+ 0xFFFFFFFFFFFFFFFEw) ==>
  ((m0_mod_bmr (F,T)).bmr_extra ms) ==>
  (aligned 1 (ms.base.REG RName_PC)) ==>
  (NextStateM0_mod ms =
      SOME
        <|base :=
          ms.base with
          <|REG :=
              (RName_PC =+ ms.base.REG RName_PC + 2w)
                ((RName_2 =+ ms.base.REG RName_PC + 8w) ms.base.REG);
            count := w2n ms.countw + 1; pcinc := 2w|>;
        countw := ms.countw + 1w|>)
``];


val is_mr_m0_mod_f_t = (identical (#bmr_const mr) (#bmr_const (m0_mod_bmr_rec false true)));

val patched_thms_ = [
    (is_mr_m0_mod_f_t, "a202", patch_thms_m0modft_a202)
  ];

val patched_thms = List.foldr (fn ((a, b, c), l) => if a then (b,c)::l else l) [] patched_thms_;

fun get_patched_step_hex ms_v hex_code =
  let
    val strToLower = implode o (List.map Char.toLower) o explode;
    val patch = List.find (fn (b, c) => strToLower b = strToLower hex_code) patched_thms;
  in
    if isSome patch then snd (valOf patch) else (#bmr_step_hex mr) ms_v hex_code
  end;

  (*******************************************************)
  (* Creating lifting theorems from a single instruction *)
  (*******************************************************)

  (* Given the hex-code of an instruction and a PC in form of a number
     to load it from, the first step is to create corresponding step theorems.

     These step theorems are instantiated with the concrete value of the PC,
     as many as possible preconditions are removed using the fact that the machine
     state is satisfying the extra predicate.

     In the remaining conditions, a memory region is searched that contains that
     instruction and these preconditions are transformed into the
     bmr_ms_mem_contains form.

     The list of resulting theorems, the computed memory mapping and the
     label corresponding to the given PC are returned. *)

  fun mk_inst_lifting_theorems hex_code hex_code_desc =
  let
     val lifted_thms_raw = let
       val res = get_patched_step_hex ms_v hex_code
       val _ = assert (not o List.null) res
       val _ = assert (List.all (fn thm => not (bir_eq_utilLib.mem_with (fn (a,b) => identical a b) F (hyp thm)))) res
     in res end handle HOL_ERR _ =>
       raise (bir_inst_liftingExn (hex_code, BILED_msg "bmr_step_hex failed"));

     (* instantiate pc and compute label *)
     val (label_tm, pc_thm) = let
        val thm0 = SPECL [ms_v, pc_num_var, stringSyntax.fromMLstring hex_code_desc] (#bmr_label_thm mr);
        val tm = rhs (#1 (dest_imp_only (concl thm0)))
     in (tm, UNDISCH thm0) end handle HOL_ERR _ =>
       raise (bir_inst_liftingExn (hex_code, BILED_msg "label thm failed"));

     (* Normalise all resulting theorems *)
     fun norm_thm thm = let
        val thm0 = HYP_CONV_RULE (K true) (PURE_REWRITE_CONV [pc_thm]) thm
        val thm1 = PROVE_HYP ms_extra_REWRS0 thm0
        fun disch_hyp_check tm =
          if (is_bmr_ms_mem_contains tm) then false else
          if (is_bmr_rel tm) then false else
          if (free_in pc_num_var tm) then false else true;

        val thm2 = foldl (uncurry DISCH) thm1 (List.filter disch_hyp_check (hyp thm1))
        val thm3 = REWRITE_RULE [pc_thm, wordsTheory.word_add_n2w, wordsTheory.word_and_n2w,
              wordsTheory.word_or_n2w, bir_auxiliaryTheory.word_sub_n2w,
              addressTheory.word_arith_lemma1,
              addressTheory.word_arith_lemma3,
              addressTheory.word_arith_lemma4,
              addr_sz_dimword_THM, bir_auxiliaryTheory.align_n2w] thm2 handle UNCHANGED => thm2
     in
        thm3
     end

     val lifted_thms = map norm_thm lifted_thms_raw;

     (* try to get bmr_ms_mem_contains *)
     val mm_tm = let
       val (_, _, mm_tm) = Lib.tryfind dest_bmr_ms_mem_contains (hyp (hd lifted_thms))
     in mm_tm end handle HOL_ERR _ =>
       raise (bir_inst_liftingExn (hex_code, BILED_msg "mem region search failed"));
  in
     (lifted_thms, mm_tm, label_tm)
  end handle HOL_ERR _ =>
    raise (bir_inst_liftingExn (hex_code, BILED_msg "mk_inst_lifting_theorems failed"));


  (******************************)
  (* Preprocessing next-theorem *)
  (******************************)

  (* If multiple theorems are produced by the step function, we might want to
     preprocess them. If there are exactly 2, one might want to merge them for example.
     Each theorem is accompanied by condition. The code generated around the theorems
     has to guarantee, that this condition is satisfied, once the block belonging to
     this theorem is executed. *)

  (* val [thm_a, thm_b] = next_thms *)
  fun preprocess_next_thms_simple_merge thm_a thm_b = let
    val thm0 = MATCH_MP COMBINE_TWO_STEP_THMS_SIMPLE thm_a
               handle HOL_ERR _ => MATCH_MP COMBINE_TWO_STEP_THMS_SIMPLE_2 thm_a
    val thm1 = MATCH_MP thm0 thm_b
    val (pre, _) = dest_imp_only (concl thm1);
    val pre_thm = SIMP_PROVE std_ss [] pre
    val thm2 = MP thm1 pre_thm
    val thm3 = REWRITE_RULE [PROTECTED_COND_NEG_COND, PROTECTED_COND_NEG_COND_CONJ] thm2
  in thm3 end

  fun preprocess_next_thms (lb:term) ([]:thm list) =
      raise bir_inst_liftingAuxExn (BILED_msg ("empty list of step theorems produced"))
    | preprocess_next_thms lb [thm] =
        [(lb, T, thm)]
    | preprocess_next_thms lb [thms1, thms2] =
      (
        [(lb, T, preprocess_next_thms_simple_merge thms1 thms2)]
        handle HOL_ERR _ =>
          raise bir_inst_liftingAuxExn (BILED_msg ("unknown error during merging of 2 next-theorems"))
      )
    | preprocess_next_thms _ _ =
        raise bir_inst_liftingAuxExn (BILED_msg ("more than 2 next-theorems cannot be merged currently: TODO"));



  (***********************************************)
  (* Lifting a single thm                        *)
  (***********************************************)

  (*----------------------*)
  (* Compute ms', al_step *)
  (*----------------------*)

  (* given a step theorem, compute the necessary preconditions and
     and lift them. This gives rise to al_step. Also extract the term ms'. *)
  local
    val conv2 = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++boolSimps.LIFT_COND_ss) ([
          PROTECTED_COND_def, ms_extra_REWRS])
   val bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_tm' = mk_icomb (bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_tm,
          (#bmr_const mr))
  in
(* For debugging RISC-V:

  val hex_code = String.map Char.toUpper "00E13423";
  val hex_code_desc = hex_code;
  val (next_thms, mm_tm, label_tm) = mk_inst_lifting_theorems hex_code hex_code_desc
  val (lb, ms_case_cond_t, next_thm) = el 1 (preprocess_next_thms label_tm next_thms)
  val next_thm0 = REWRITE_RULE [ASSUME ms_case_cond_t] next_thm

*)
  fun compute_al_step_ms' next_thm0 =
  let
    (* all possible simplifications of remaining conditions have been tried before,
       so let's just lift everything *)
    val (preconds, next_tm) = strip_imp_only (concl next_thm0)
    val ms'_t = rand (rhs (next_tm))

    (* lift all preconds *)
    (* TODO: Should the below be empty list? *)
    val lift_thms = map exp_lift_fn preconds
    val assert_ok_thms = map (MATCH_MP bir_assert_desc_OK_via_lifting) lift_thms
    val al_step_l = map (fn thm => (rand (concl thm))) assert_ok_thms
    val al_step = listSyntax.mk_list (al_step_l, bir_assert_desc_t_ty)

    (* Show that computed ms' and al_step really are ok *)
    val thm_tm = let
       val t0 = bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_tm'
       val t1 = list_mk_comb (t0, [bs_v, ms_v, al_step, ms'_t])

       val thm0 = SIMP_CONV (list_ss) (assert_ok_thms@[
          next_thm0,
          bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_def,
          bir_is_lifted_inst_block_COMPUTE_ms'_COND_def,
          bir_assert_desc_value_def,
          bmr_eval_REWRS]) t1
       val thm1 = CONV_RULE (RHS_CONV conv2) thm0

       val thm2 = EQT_ELIM thm1
    in thm2 end
  in
    (ms'_t, al_step, thm_tm)
  end;
  end;

  (*-----------------*)
  (* Compute imm_ups *)
  (*-----------------*)

  (* Given the new machine state as a term, figure out, which changes actually did
     happen. These are represented by the imm_ups list. We need this list as a term
     for later instantiating as well as only the changes as an SML datastructure for
     computing the block-updates later. Moreover, a theorem stating that the
     computed imm_ups list is correct is produced. *)
  local
    val compute_single_up_single_conv = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++wordsLib.SIZES_ss) [
         updateTheory.APPLY_UPDATE_THM, wordsTheory.n2w_11, cond_lift_fields_thm,
         PROTECTED_COND_ID];

    val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_tm' = mk_icomb (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_tm,
          (#bmr_const mr))
  in

  fun compute_imm_ups ms'_t =
  let
    fun compute_single_up lf_ms = let
      val lf_ms'_tm = subst [ms_v |-> ms'_t] lf_ms
      val lf_ms'_thm = compute_single_up_single_conv lf_ms'_tm handle UNCHANGED => REFL lf_ms'_tm

      val res = rhs (concl lf_ms'_thm)
      val (upd_tm, upd_tm_opt) = if (aconv res lf_ms) then (optionSyntax.mk_none (type_of res), NONE) else
                      (optionSyntax.mk_some res, SOME res)
    in
      (upd_tm, upd_tm_opt, lf_ms'_thm)
    end;

    (*
      val (bmli_tm, lf_ms) = el 3 mr_imms_lf_of_ms
    *)
    val (upds_tms, eval_thms) =
       foldl (fn ((bmli_tm, lf_ms), (resl, thmL)) =>
         let val (upd_tm, upd_opt, lf_ms'_thm) = compute_single_up lf_ms
             val resl' = pairSyntax.mk_pair (bmli_tm, upd_tm)::resl;
             val thml' = lf_ms'_thm :: thmL;
         in (resl', thml') end)
         ([], []) mr_imms_lf_of_ms

    val imm_ups_tm = listSyntax.mk_list (List.rev upds_tms, type_of (hd upds_tms))

    (* Show that computed imm_ups  is really are ok *)
    val thm_tm = let
       val t0 = bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_tm'
       val t1 = list_mk_comb (t0, [ms_v, ms'_t, imm_ups_tm])

       val thm1 = SIMP_CONV bool_ss ([
         bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_EVAL, bmr_eval_REWRS,
         bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def] @ eval_thms)
         t1
       val thm2 = EQT_ELIM thm1
    in thm2 end
  in
    (imm_ups_tm, thm_tm)
  end;
  end;


  (*-----------------*)
  (* Compute mem_up *)
  (*-----------------*)

  (* Given a new state, we compute whether updates to the memory happend. This
     is similar to computing updates to immediates via compute_imm_ups.
     The computed term, its SML representation and a correctness theorem are returned. *)
  local
    val lf_ms'_CONV = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++wordsLib.SIZES_ss) [cond_lift_fields_thm, PROTECTED_COND_ID]
   val bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_tm' = mk_icomb (bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_tm,
          (#bmr_const mr))
  in

  fun compute_mem_up ms'_t =
  let
     val lf_ms'_tm = subst [ms_v |-> ms'_t] mr_mem_lf_of_ms
     val lf_ms'_thm = lf_ms'_CONV  lf_ms'_tm handle UNCHANGED => REFL lf_ms'_tm

     val res = rhs (concl lf_ms'_thm)

     val (upd_tm, upd_tm_opt) = if (aconv res mr_mem_lf_of_ms) then (optionSyntax.mk_none (type_of res), NONE) else
                     (optionSyntax.mk_some res, SOME res)

     (* Show that computed imm_ups  is really are ok *)
     val thm_tm = let
       val t0 = bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_tm'
       val t1 = list_mk_comb (t0, [ms_v, ms'_t, upd_tm])

       val thm0 = SIMP_CONV bool_ss ([lf_ms'_thm, bmr_eval_REWRS,
           bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_EVAL])
           t1
       val thm1 = EQT_ELIM thm0
     in thm1 end
  in
    (upd_tm, upd_tm_opt, thm_tm, lf_ms'_thm)
  end;
  end;


  (*-----------------*)
  (* Compute al_mem  *)
  (*-----------------*)

  (* Given

     - the next machine state ms'_t as a term
     - the region of memory that needs to remain unchanged in the form of a theorem
         mu_thm :   |- WI_wfe (WI_end _ _)
     - the memory in ms'_t if it changed compared to mem_ms'_t as a term option
     - and a theorem "mem_up_thm" stating that "mem_ms'_t_opt" is indeed sound. This
       is the theorem produced by compute_mem_up.

    we need to compute a list for assertions that enforce that the memory does not
    change in the region specified bz mu_thm.
    This list of assertions is returned together with a theorem stating its validity.

    If the memory is not updated, finding such a list is trival, just return the
    empty list of assertions.

    More interestingly, if the memory is updated, we need to find out at which address.
    Usually this is a interval of addresses, seldomly multiple intervals. The start of the
    interval usually depends on the current state, e.g. on the value stored in a register.
    So, we need an assertion to enforce that the addresses computed at runtime are not
    inside the protected region.
  *)

  (* Trivial case: nothing changed. Just use preproved theorem. *)
  local
     val bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE' =
         ISPEC (#bmr_const mr) bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE
  in

  fun compute_al_mem_NONE (ms'_t:term) (mu_thm:thm) mem_up_thm = let
    val al_mem_thm = let
      val thm1 = SPECL [(rand (concl mu_thm)), bs_v, ms_v, ms'_t] bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE'
      val thm2 = MP thm1 mem_up_thm
    in thm2 end;

    val al_mem_t = rand (concl al_mem_thm)
  in
    (al_mem_t, al_mem_thm)
  end;
  end;



  (* The interesting case where we actually need to do something *)
  (*
     val (SOME mem_ms'_t) = real_mem_up_opt
  *)
  local

     val al_mem_INTRO_THM = let
       val thm0  = ISPEC (#bmr_const mr) bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO
       val thm1  = SPEC addr_sz_immtype_t thm0
       val (pre, _) = dest_imp_only (concl thm1)
       val pre_thm = SIMP_PROVE (std_ss++wordsLib.SIZES_ss++HolBACoreSimps.holBACore_ss) [
                  ] pre
       val thm2 = MP thm1 pre_thm
       val thm3 = SIMP_RULE std_ss [bmr_eval_REWRS] thm2
       val thm4 = SPECL [bs_v, ms_v] thm3
     in thm4 end;

     val al_mem_NIL_THM = let
       val thm0 = INST_TYPE [Type.alpha |-> addr_sz_ty, Type.beta |-> mem_val_sz_ty]
           bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_NIL
       val thm1 = SPECL [addr_sz_immtype_t, bs_v] thm0
     in thm1 end;

     val al_mem_CONS_THM = let
       val thm0 = INST_TYPE [Type.alpha |-> addr_sz_ty, Type.beta |-> mem_val_sz_ty]
           bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_CONS
       val thm1 = SPECL [addr_sz_immtype_t, bs_v] thm0
       val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss++HolBACoreSimps.holBACore_ss) [
          wordsTheory.w2w_id] thm1
     in thm2 end;

     val al_mem_MERGE_THM1 = let
       val thm0 = INST_TYPE [Type.alpha |-> addr_sz_ty, Type.beta |-> mem_val_sz_ty]
           bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_MERGE_1
       val thm1 = SPECL [addr_sz_immtype_t, bs_v] thm0
       val thm2 = REWRITE_RULE [addr_sz_dimword_THM] thm1
     in thm2 end;

     val al_mem_MERGE_THM2 = let
       val thm0 = INST_TYPE [Type.alpha |-> addr_sz_ty, Type.beta |-> mem_val_sz_ty]
           bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_MERGE_2
       val thm1 = SPECL [addr_sz_immtype_t, bs_v] thm0
       val thm2 = REWRITE_RULE [addr_sz_dimword_THM] thm1
     in thm2 end;


     val ch_thms = flatten (map BODY_CONJUNCTS (#bmr_change_interval_thms mr))
     (* val t = mem_ms'_t *)
     fun compute_next_interval t =
       Lib.tryfind (fn thm => PART_MATCH (rand o rator) thm t) ch_thms

     val merge_preconds_simp =  SIMP_CONV (std_ss++wordsLib.WORD_ss) []
  in

  fun compute_al_mem_SOME ms'_t mu_thm mem_ms'_t mem_ms'_thm = let
     fun merge_intervals_thm mthm intervals_thm = let
       val thm0 = MATCH_MP mthm intervals_thm
       val (pre, _) = dest_imp_only (concl thm0)
       val pre_thm = EQT_ELIM (merge_preconds_simp pre)
       val thm1 = MP thm0 pre_thm
     in
       thm1
     end

     fun merge_intervals intervals_thm =
       merge_intervals_thm al_mem_MERGE_THM1 intervals_thm
     handle HOL_ERR _ =>
       merge_intervals_thm al_mem_MERGE_THM2 intervals_thm
     handle HOL_ERR _ =>
       intervals_thm


     (* val current_thm = al_mem_NIL_THM *)
     fun compute_intervals_thm current_thm mem_t =
       if (aconv mem_t mr_mem_lf_of_ms) then current_thm else
       let
          val int_thm = compute_next_interval mem_t
          val (va_tm, sz_tm, _, mem_t') = bir_interval_expSyntax.dest_FUNS_EQ_OUTSIDE_WI_size
             (concl int_thm)
          val lift_thm = REWRITE_RULE [bir_exp_liftingTheory.bir_is_lifted_exp_def]
             (exp_lift_fn va_tm)
          val va_e_tm = rand (rator (concl lift_thm))

          val thm0 = MATCH_MP al_mem_CONS_THM current_thm
          val thm1 = SPECL [va_tm, sz_tm, mem_t, mem_t', va_e_tm] thm0
          val thm2 = MP thm1 int_thm
          val thm3 = MP thm2 lift_thm

          val (pre, _) = dest_imp_only (concl thm3)
          val thm4 = MP thm3 (DECIDE pre)

          val thm5 = merge_intervals thm4
       in
          compute_intervals_thm thm5 mem_t'
       end;

   val intervals_thm = compute_intervals_thm al_mem_NIL_THM mem_ms'_t

   val final_thm = let
     val thm0 = MATCH_MP al_mem_INTRO_THM mu_thm
     val thm1 = SPEC (rand (concl intervals_thm)) thm0
     val thm2 = MP thm1 intervals_thm
     val thm3 = SPEC ms'_t thm2
     val (pre, _) = dest_imp_only (concl thm3)
     val pre_thm = SIMP_PROVE list_ss [mem_ms'_thm] pre
     val thm4 = MP thm3 pre_thm
     val thm5 = SIMP_RULE list_ss [] thm4
   in thm5 end;

   val al_mem_t = rand (concl final_thm)
  in
    (al_mem_t, final_thm)
  end

  end;


  (* Combine both *)
  fun compute_al_mem ms'_t mu_thm real_mem_up_opt mem_up_thm mem_ms'_thm = (
    case (real_mem_up_opt) of
        NONE => compute_al_mem_NONE ms'_t mu_thm mem_up_thm
      | SOME mem_ms' => compute_al_mem_SOME ms'_t mu_thm mem_ms' mem_ms'_thm
  );


  (*-------------*)
  (* Compute eup *)
  (*-------------*)

  (* Given a next state as a term, we look at the PC of the state and
     compute an end statement update description that allows us to jump to
     that PC. *)
  local
    val comp_thm_eup_JMP = let
       val thm0 = ISPECL [#bmr_const mr, bs_v]
            bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___JMP
    in thm0 end;

    val comp_thm_eup_CJMP = let
       val thm0 = ISPECL [#bmr_const mr, bs_v, ms_v]
            bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___CJMP
       val thm1 = UNDISCH (MP thm0 (#bmr_ok_thm mr))
    in thm1 end;

    val comp_thm_eup_XJMP = let
       val thm0 = ISPECL [#bmr_const mr, bs_v, ms_v]
            bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___XJMP
       val thm1 = UNDISCH (MP thm0 (#bmr_ok_thm mr))
    in thm1 end;

    val lf_ms'_CONV = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++wordsLib.SIZES_ss) [bmr_eval_REWRS,
      cond_lift_fields_thm, PROTECTED_COND_ID, updateTheory.APPLY_UPDATE_THM] THENC
      PURE_REWRITE_CONV [PROTECTED_COND_def]
  in
  fun compute_eup ms'_t =
  let
     val lf_ms'_tm = list_mk_icomb bmr_pc_lf_tm [(#bmr_const mr), ms'_t];
     val lf_ms'_thm = lf_ms'_CONV lf_ms'_tm handle UNCHANGED => REFL lf_ms'_tm
     val res_imm = rhs (concl lf_ms'_thm)

     (* There are 3 cases supported:

        - simple unconditional jump : res is a literal word, e.g. 0x1000w
        - simple conditional jump : res is a conditional, with 2 literal words in the cases, e.g.
              if (some condition) then 0x1000w else 0x1008w
        - something fancy. res is an arbitrary, liftable word expression

        Just try them one after the other.
     *)

     fun compute_eup_JMP () = let
        (* Check we have a literal imm *)
        val (_, w) = bir_immSyntax.gen_dest_Imm res_imm
        val _ = if (wordsSyntax.is_n2w w) then () else fail ()

        val thm0 = SPEC ms'_t comp_thm_eup_JMP
        val thm1 = PURE_REWRITE_RULE [lf_ms'_thm] thm0
     in
        thm1
     end;

     (* DEBUG
        val expand_thm = prove (``Imm64 w = Imm64 (if T then w else w)``, SIMP_TAC std_ss [])
        val lf_ms'_thm = ONCE_REWRITE_RULE [expand_thm] lf_ms'_thm
        val res_imm = rhs (concl lf_ms'_thm)
      *)
     fun compute_eup_CJMP () = let
        val (sz, i) = bir_immSyntax.gen_dest_Imm res_imm
        val (c, w1, w2) = boolSyntax.dest_cond i
        val _ = if (wordsSyntax.is_n2w w1) then () else fail ()
        val _ = if (wordsSyntax.is_n2w w2) then () else fail ()

        val lf_ms'_thm' = CONV_RULE (RHS_CONV (REWR_CONV COND_RAND)) lf_ms'_thm
        val lift_thm = exp_lift_fn c

        val thm0 = SPECL [ms'_t, c, bir_immSyntax.gen_mk_Imm w1, bir_immSyntax.gen_mk_Imm w2] comp_thm_eup_CJMP
        val thm1 = MP thm0 lf_ms'_thm'
        val thm2 = MATCH_MP thm1 lift_thm
        val thm3 = PURE_REWRITE_RULE [bmr_eval_REWRS] thm2
     in
        thm3
     end;

     fun compute_eup_XJMP () = let
        val lift_thm = exp_lift_fn res_imm

        val thm0 = SPEC ms'_t comp_thm_eup_XJMP
        val thm1 = PURE_REWRITE_RULE [lf_ms'_thm] thm0
        val thm2 = MATCH_MP thm1 lift_thm
        val thm3 = PURE_REWRITE_RULE [bmr_eval_REWRS] thm2
     in
        thm3
     end;

     val eup_thm = compute_eup_JMP () handle HOL_ERR _ =>
                   compute_eup_CJMP () handle HOL_ERR _ =>
                   compute_eup_XJMP ();
     val eup_tm = rand (rator (concl eup_thm))
   in
     (eup_tm, eup_thm)
   end;
  end;

  (*-----------------*)
  (* Compute updates *)
  (*-----------------*)

  (* Given imm_ups, mem_up and the end description, the real updates,
     whether to use a temp var for the end description and theorem
     stating the correctness of the computed updates is derived.

     This mainly means lifting the values of imm_ups and mem_up and
     computing the flag whether to use temp vars by looking at which
     vars are still needed afterwards.
  *)
  local
     val comp_thm_updates_FULL_INTRO =
       ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO;

     val comp_thm_updates_ADD_IMM_UP =
       ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP;

     val comp_thm_updates_ADD_IMM_UP_NONE =
       ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP_NONE;

     val comp_thm_updates_INTRO_MEM =
       ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_MEM;

     val comp_thm_updates_INTRO_NO_MEM =
       ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_NO_MEM;

     val vn_set_empty = HOLset.empty String.compare;

     (* compute var names of expression. Return both a theorem and add them to the given
        string set. *)
     val comp_varnames_conv = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) ([
         pred_setTheory.INSERT_UNION_EQ,
         bir_temp_varsTheory.bir_temp_var_name_def]@
         HolBASimps.common_exp_defs)

     val comp_upd_imm_varname_conv = SIMP_CONV (list_ss++stringSimps.STRING_ss) [bir_temp_varsTheory.bir_temp_var_def, bir_envTheory.bir_var_name_def, bir_temp_varsTheory.bir_temp_var_name_def]

     val comp_upd_imm_nin_conv = SIMP_CONV (list_ss++pred_setSimps.PRED_SET_ss++stringSimps.STRING_ss) []

     val eval_updates_conv = SIMP_CONV list_ss [bmr_eval_REWRS]

     fun comp_varnames_thm e_tm = let
       val tm0 = pred_setSyntax.mk_image (bir_envSyntax.bir_var_name_tm,
                   (mk_bir_vars_of_exp e_tm))
       val thm0 = comp_varnames_conv tm0
     in
       thm0
     end handle UNCHANGED =>
        raise bir_inst_liftingAuxExn (BILED_msg_term ("failed to compute vars of exp", e_tm));

     fun comp_varnames e_tm vn_set = let
       val thm0 = comp_varnames_thm e_tm
       val vn_t = rhs (concl thm0)
       val vn_string_l = List.map stringSyntax.fromHOLstring (pred_setSyntax.strip_set vn_t)
       val vn_set' = HOLset.addList (vn_set, vn_string_l);
     in
       (thm0, vn_set')
     end;

     fun simplify_FULL_REL_vars_RULE thms =
       let
          val c = PURE_REWRITE_CONV (pred_setTheory.INSERT_UNION_EQ::pred_setTheory.UNION_EMPTY::thms)
       in
         CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV c)))
       end;

(* For debugging (from compute_updates):

         val (full_rel_thm, vn_set) =
           foldl add_imm_up (init_thm, vn_set) (List.take (imm_ups_tm_list, 62));
         val (v_t, lf_t, SOME res_t) = el 63 imm_ups_tm_list;
*)
     fun add_imm_up ((v_t, lf_t, NONE), (full_rel_thm, vn_set)) =
         let
           val (_, args) = strip_comb (concl full_rel_thm)
           val args' = List.drop (args, 2);
           val thm0  = MP (SPECL [v_t, lf_t] (SPECL args' comp_thm_updates_ADD_IMM_UP_NONE)) full_rel_thm    in (thm0, vn_set) end
       | add_imm_up ((v_t, lf_t, SOME res_t), (full_rel_thm, vn_set)) =
         let
           val lift_thm = PURE_REWRITE_RULE [bir_exp_liftingTheory.bir_is_lifted_exp_def]
              (exp_lift_fn res_t)
           val e_tm = rand (rator (concl lift_thm))

           val (vn_e_thm, vn_set') = comp_varnames e_tm vn_set

           (* compute temp *)
           val use_temp = let
             val vn_s = stringSyntax.fromHOLstring (fst(bir_envSyntax.dest_BVar v_t))
           in
             if HOLset.member (vn_set, vn_s) then T else F
           end;

           val (_, args) = strip_comb (concl full_rel_thm)
           val args' = List.drop (args, 2);
           val thm0 = SPECL [v_t, lf_t, res_t, e_tm, use_temp] (MP (SPECL args' comp_thm_updates_ADD_IMM_UP) full_rel_thm)
           val thm1 = MP thm0 lift_thm
           val (precond_tm, _) = dest_imp_only (concl thm1)

           val precond_thm = let
             val xthm0 = RAND_CONV (RATOR_CONV (RAND_CONV comp_upd_imm_varname_conv)) precond_tm
             val xthm1 = CONV_RULE (RHS_CONV comp_upd_imm_nin_conv) xthm0
             val xthm2 = EQT_ELIM xthm1
           in xthm2 end

           val thm3 = MP thm1 precond_thm
           val thm4 = simplify_FULL_REL_vars_RULE [vn_e_thm] thm3
         in
           (thm4, vn_set')
         end;
  in
(* For debugging RISC-V:

  val (mu_thm:thm, mm_precond_thm:thm) = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  val hex_code = String.map Char.toUpper "FCE14083"; (* "lbu x1,x2,-50" *)
  val hex_code_desc = hex_code;
  val (next_thms, mm_tm, label_tm) = mk_inst_lifting_theorems hex_code hex_code_desc
    val bir_is_lifted_inst_block_COMPUTE_precond_tm_mr =
      list_mk_comb (
        mk_icomb ( bir_is_lifted_inst_block_COMPUTE_precond_tm, #bmr_const mr),
        [bs_v, ms_v]);

    val list_CONV = SIMP_CONV list_ss []
  val inst_lift_thm0 =
    let
      val thm0 = MP (SPEC (rand (concl mu_thm)) inst_lift_THM) mu_thm
      val thm1 = SPECL [mm_tm, label_tm] thm0

      val precond_thm =
	let
	  val (pc_n_tm0, ml_tm) = pairSyntax.dest_pair mm_tm
	  val pc_n_tm = rand pc_n_tm0;
	  val thmp_0 = SPECL [pc_n_tm, ml_tm] mm_precond_thm
	  val thmp_1 = CONV_RULE (RATOR_CONV (RAND_CONV list_CONV)) thmp_0
	in
	  UNDISCH thmp_1
	end;

      val thm2 = MP thm1 precond_thm
    in
      thm2
    end;
  val bir_is_lifted_inst_block_COMPUTE_precond_tm0 =
    list_mk_comb (bir_is_lifted_inst_block_COMPUTE_precond_tm_mr,
     [label_tm, (rand (concl mu_thm)), mm_tm])
  val (lb, ms_case_cond_t, next_thm) = el 1 (preprocess_next_thms label_tm next_thms)

  val next_thm0 = REWRITE_RULE [ASSUME ms_case_cond_t] next_thm
     fun raiseErr s = raise (bir_inst_liftingAuxExn (BILED_msg s));


     (* compute ms' and al_step *)
     val (ms'_t, al_step_t, ms'_thm) = compute_al_step_ms' next_thm0
       handle HOL_ERR _ => raiseErr "computing al_step and ms' failed";

     (* next compute imm_ups *)
     val (imm_ups_t, imm_ups_thm) = compute_imm_ups ms'_t
       handle HOL_ERR _ => raiseErr "computing imm_ups failed";

     (* compute eup *)
     val (eup_t, eup_THM) = compute_eup ms'_t
       handle HOL_ERR _ => raiseErr "computing eup failed";

     (* compute mem_up *)
     val (mem_up_t, real_mem_up_opt, mem_up_thm, mem_ms'_thm) = compute_mem_up ms'_t
       handle HOL_ERR _ => raiseErr "computing mem_up failed";
*)
  fun compute_updates mem_up_t imm_ups_t eup_t =
  let
     (* Deal with mem_up *)
     val (init_thm, vn_set) = if (optionSyntax.is_none mem_up_t) then
          (comp_thm_updates_INTRO_NO_MEM, vn_set_empty)
        else let
           val mem_ms' = optionSyntax.dest_some mem_up_t
           val lift_thm = exp_lift_fn mem_ms'
           val e_tm = rand (rator (concl lift_thm));
           val (e_thm, vn_set) = comp_varnames e_tm vn_set_empty

           val thm0 = SPECL [e_tm, mem_ms'] comp_thm_updates_INTRO_MEM
           val thm1 = MP thm0 lift_thm
           val thm2 = simplify_FULL_REL_vars_RULE [e_thm] thm1
        in
           (thm2, vn_set)
        end;

     (* Deal with imm_ups *)
     val imm_ups_tm_list = List.rev (
        List.map (fn t => let
           val (t1, res_opt_t) = pairSyntax.dest_pair t
           val res_opt = SOME (optionSyntax.dest_some res_opt_t) handle HOL_ERR _ => NONE;
           val (v_t, lf_t) = dest_BMLI t1
        in
           (v_t, lf_t, res_opt)
        end)
        (fst (listSyntax.dest_list imm_ups_t)));

     (* TODO: Something will go wrong here when failing to lift an expression... *)
     val (full_rel_thm, vn_set_final) = foldl add_imm_up (init_thm, vn_set) imm_ups_tm_list;

     (* add eup *)
     val (eup_thm, eup_temp_tm) = let
       val (_, args) = strip_comb (concl full_rel_thm)
       val args' = List.drop (args, 2);

       val thm0 = SPEC eup_t (MP (SPECL args' comp_thm_updates_FULL_INTRO) full_rel_thm)

       val (eup_temp_v, precond_tm, updates_tm) = let
          val (eup_temp_v, t0) = dest_forall (concl thm0)
          val (precond_tm, t1) = dest_imp_only t0
          val updates_tm = rand t1
       in (eup_temp_v, precond_tm, updates_tm) end;
       val updates_thm = eval_updates_conv updates_tm

       val e_thm = REWRITE_CONV [bir_updateE_desc_exp_def] (mk_comb (bir_updateE_desc_exp_tm, eup_t))
       val e_opt = SOME (optionSyntax.dest_some (rhs (concl e_thm))) handle HOL_ERR _ => NONE

       val (precond_thm, temp_t) = if (is_none e_opt) then
       let
         (* We don't have an exp, therefore the F case holds trivially *)
         val precond_thm = EQT_ELIM (REWRITE_CONV [e_thm, optionTheory.NOT_NONE_SOME] (subst [eup_temp_v |-> F] precond_tm))
       in
         (precond_thm, F)
       end else if (listSyntax.is_null (rhs (concl updates_thm))) then (
       let
         (* We don't have have any other changes, therefore the F case holds trivially *)
         val precond_thm = EQT_ELIM (
            REWRITE_CONV [updates_thm, bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS,
              pred_setTheory.DISJOINT_EMPTY] (subst [eup_temp_v |-> F] precond_tm)
         )
       in
         (precond_thm, F)
       end) else (let
         (* We are in a more tricky situation. We just try it. *)
         val precond_thm0 = REWRITE_CONV [e_thm, updates_thm,
            bir_updateE_desc_var_def, optionTheory.option_CLAUSES] precond_tm
       in
         let
            val thm0 = INST [eup_temp_v |-> F] precond_thm0
            val vars_thm = comp_varnames_thm (valOf e_opt)
            val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV (std_ss) [vars_thm,
              bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS])) thm0
            val thm2 = CONV_RULE (RHS_CONV (SIMP_CONV (list_ss++stringSimps.STRING_ss) [
               pred_setTheory.DISJOINT_EMPTY, pred_setTheory.DISJOINT_INSERT])) thm1
         in (EQT_ELIM thm2, F) end handle HOL_ERR _ => let
            val thm0 = INST [eup_temp_v |-> T] precond_thm0
            val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV (list_ss++stringSimps.STRING_ss) [
               bir_envTheory.bir_var_name_def, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY])) thm0
         in
            (EQT_ELIM thm1, T)
         end handle HOL_ERR _ => failwith "Could not prove precond"
       end);

       val thm1 = MP (SPEC temp_t thm0) precond_thm
       val thm2 = CONV_RULE (RAND_CONV (K updates_thm)) thm1
     in (thm2, temp_t) end;

     val updates_tm' = rand (concl eup_thm)
   in
     (updates_tm', eup_temp_tm, eup_thm)
   end;

  end;


  (*---------------*)
  (* Compute block *)
  (*---------------*)

  (* Simple eval *)

  val compute_bl_compset = listSimps.list_compset ();
  val _ = computeLib.add_thms [bir_is_lifted_inst_block_COMPUTE_block_def,
             bir_update_assert_block_def, pairTheory.pair_case_thm,
             bir_assert_block_def, bir_update_blockE_INIT_def, bir_update_blockB_def,
             bir_updateE_desc_remove_var_def, bir_updateE_desc_var_def,
             bir_updateB_desc_use_temp_def,
             bir_updateE_desc_exp_def,
             bir_update_blockB_STEP1_def,
             bir_temp_varsTheory.bir_temp_var_def,
             bir_temp_varsTheory.bir_temp_var_name_def,
             bir_assert_desc_exp_def,
             bir_update_blockB_STEP2_def,
             bir_update_blockE_FINAL_def] compute_bl_compset
  val _ = optionLib.OPTION_rws compute_bl_compset
  val compute_bl_conv = computeLib.CBV_CONV compute_bl_compset

  fun compute_bl lb al_mem_t al_step_t eup_temp_t eup_t updates_t = let
    val bl0_tm = list_mk_comb (bir_is_lifted_inst_block_COMPUTE_block_tm,
        [lb, al_mem_t, al_step_t, eup_temp_t, eup_t, updates_t]);
    val bl_thm = compute_bl_conv bl0_tm
    val bl_t = rhs (concl bl_thm)
  in (bl_t, bl_thm) end;


  (*-------------------------------*)
  (* Combine it all, main function *)
  (*-------------------------------*)
  (* RISC-V TODO: All seemingly OK in lifting procedure up to here, except what has been
   * commented. *)
  (* DEBUG

     val (lb, ms_case_cond_t, next_thm) = el 1 sub_block_work_list
  *)
(* For debugging RISC-V:

  val (mu_thm:thm, mm_precond_thm:thm) = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  val hex_code = String.map Char.toUpper "007302B3";
  val hex_code_desc = hex_code;
  val (next_thms, mm_tm, label_tm) = mk_inst_lifting_theorems hex_code hex_code_desc
    val bir_is_lifted_inst_block_COMPUTE_precond_tm_mr =
      list_mk_comb (
        mk_icomb ( bir_is_lifted_inst_block_COMPUTE_precond_tm, #bmr_const mr),
        [bs_v, ms_v]);

    val list_CONV = SIMP_CONV list_ss []
  val inst_lift_thm0 =
    let
      val thm0 = MP (SPEC (rand (concl mu_thm)) inst_lift_THM) mu_thm
      val thm1 = SPECL [mm_tm, label_tm] thm0

      val precond_thm =
	let
	  val (pc_n_tm0, ml_tm) = pairSyntax.dest_pair mm_tm
	  val pc_n_tm = rand pc_n_tm0;
	  val thmp_0 = SPECL [pc_n_tm, ml_tm] mm_precond_thm
	  val thmp_1 = CONV_RULE (RATOR_CONV (RAND_CONV list_CONV)) thmp_0
	in
	  UNDISCH thmp_1
	end;

      val thm2 = MP thm1 precond_thm
    in
      thm2
    end;
  val bir_is_lifted_inst_block_COMPUTE_precond_tm0 =
    list_mk_comb (bir_is_lifted_inst_block_COMPUTE_precond_tm_mr,
     [label_tm, (rand (concl mu_thm)), mm_tm])
  val (lb, ms_case_cond_t, next_thm) = el 1 (preprocess_next_thms label_tm next_thms)

*)

  (* This is the main workhorse. It gets a single next theorem and tries to
     instantiate inst_thm to generate a block mimicking this next_thm. The
     block should use label "lb" and extra condition "ms_case_cond_t" can be assumed. *)
  fun lift_single_block inst_lift_thm0 bir_is_lifted_inst_block_COMPUTE_precond_tm0
     mu_thm (lb, ms_case_cond_t, next_thm) = let
     val next_thm0 = REWRITE_RULE [ASSUME ms_case_cond_t] next_thm
     fun raiseErr s = raise (bir_inst_liftingAuxExn (BILED_msg s));

     (* compute ms' and al_step *)
     val (ms'_t, al_step_t, ms'_thm) = compute_al_step_ms' next_thm0
       handle HOL_ERR _ => raiseErr "computing al_step and ms' failed";

     (* next compute imm_ups *)
     (* Gives lots of stuff... Is this correct? *)
     val (imm_ups_t, imm_ups_thm) = compute_imm_ups ms'_t
       handle HOL_ERR _ => raiseErr "computing imm_ups failed";

     (* compute eup *)
     val (eup_t, eup_THM) = compute_eup ms'_t
       handle HOL_ERR _ => raiseErr "computing eup failed";

     (* compute mem_up *)
     val (mem_up_t, real_mem_up_opt, mem_up_thm, mem_ms'_thm) = compute_mem_up ms'_t
       handle HOL_ERR _ => raiseErr "computing mem_up failed";

     (* compute al_mem *)
     val (al_mem_t, al_mem_THM) = compute_al_mem ms'_t mu_thm real_mem_up_opt mem_up_thm mem_ms'_thm
       handle HOL_ERR _ => raiseErr "computing al_mem failed";

     (* Now we need to compute the updates. This involves lifting of all computed immediates
        in imm_ups and checking whether the vars don't interfere with each other. *)
     (* TODO: Here, something fails... *)
     val (updates_t, eup_temp_t, updates_THM) = compute_updates mem_up_t imm_ups_t eup_t
       handle HOL_ERR _ => raiseErr "computing updates failed";

     (* compute bl *)
     val (bl_t, bl_thm) = compute_bl lb al_mem_t al_step_t eup_temp_t eup_t updates_t
       handle HOL_ERR _ => raiseErr "computing bl failed";

     (* derive the precond *)
     val precond_thm = let
       val tm0 = list_mk_comb (bir_is_lifted_inst_block_COMPUTE_precond_tm0,
         [bl_t, lb, mk_abs (ms_v, ms_case_cond_t)])

       val ex_insts = [ms'_t, al_step_t, imm_ups_t, mem_up_t, al_mem_t,
         eup_t, eup_temp_t, updates_t]

       val tm1 = list_mk_comb (tm0, ex_insts)

       val thm0 = EQT_ELIM (SIMP_CONV std_ss [bir_is_lifted_inst_block_COMPUTE_precond_def,
         al_mem_THM, updates_THM, bl_thm, eup_THM, mem_up_thm,
         imm_ups_thm, ms'_thm] tm1)

       val tm_goal = list_mk_exists (inst_lift_THM_ex_vars,
          list_mk_comb (tm0, inst_lift_THM_ex_vars));

       val thm1 = prove (``^tm_goal``,
         EVERY (List.map EXISTS_TAC ex_insts) >>
         REWRITE_TAC [thm0]);

       val thm2 = GENL [ms_v, bs_v] thm1
     in thm2 end
       handle HOL_ERR _ => raiseErr "proving precondition of theorem failed";

    val final_thm = let
       val thm0 = SPECL [mk_abs (ms_v, ms_case_cond_t), bl_t, lb] inst_lift_thm0
       val thm1 = MP thm0 precond_thm
    in thm1 end handle HOL_ERR _ => raiseErr ("proving final thm failed! Does the block still depend on ms and bs, e.g. because it was not completely evaluated?\n" ^ (term_to_string bl_t));
  in
    final_thm
  end handle HOL_ERR _ => raise (bir_inst_liftingAuxExn (BILED_msg "???"));


  (*----------------------------------------------------------------------------------*)
  (* Merge multiple bir_is_lifted_inst_block into one bir_is_lifted_inst_prog theorem *)
  (*----------------------------------------------------------------------------------*)

  (* val block_thm = hd sub_block_thms *)
  local
    val single_inst_INTRO_THM = inst_bmr_thm false
       bir_is_lifted_inst_prog_SINGLE_INTRO
    val bir_block_ss = rewrites (type_rws ``:'o bir_block_t``);

    val pre_conv = SIMP_CONV (std_ss++bir_block_ss) [BL_Address_HC_def]
  in

  (* Currently only single block programs are supported. This should be
     generalised in the future. *)
  fun merge_block_thms sub_block_thms =
    case sub_block_thms of
        [] => raise (bir_inst_liftingAuxExn (BILED_msg "merging block theorems failed, list of theorems is empty; this should be prevented by the control flow; this is a bug"))
      | [block_thm] => let
           val (_, extra_tm, l_tm, mu_tm, mm_tm, bl_tm) = dest_bir_is_lifted_inst_block (concl block_thm)
           val li_tm = rand (rator l_tm)
           val hc_tm = rand l_tm
           val thm0 = SPECL [li_tm, hc_tm, mu_tm, mm_tm, bl_tm, extra_tm] single_inst_INTRO_THM
           val thm1 = MP thm0 block_thm
           val (pre, _)  = dest_imp_only (concl thm1)
           val pre_thm = EQT_ELIM (pre_conv pre)
           val thm2 = MP thm1 pre_thm
        in thm2 end
      | _ =>
         raise (bir_inst_liftingAuxExn (BILED_msg "TODO: multiblock instructions are not supported yet"));

   end;


  (**************************)
  (* Lifting an instruction *)
  (**************************)

  (* Lifting single instructings, is the main workhorse of this library.
     The top-level interface provides a function "bir_lift_instr" that given

     - a memory region not to touch
     - the hex-code of an instruction
     - and a PC in form of a number to load it from

     derives a program consisting of one or multiple blocks that corresponds to
     executing the machine instruction and does not touch the memory region.

     The program starts at a block with a label corresponding to the PC. All other labels are
     not numeric (BL_Address) labels but string (BL_Label) label whose stringt starts with a
     prefix derived from the address.

     Usually whole programs are lifted. This means that this function "bir_lift_instr" is
     called very often with the same memory region that should stay unchanged. Moreover,
     usually the same hex-code is lifted multiple times for this region. Therefore, there are
     several layers to speed up computation.

     "bir_lift_instr" computes theorems about the unchanged memory region once and calls
     a function "bir_lift_instr_mu" which is intended to be called by functions translating
     while programs.

     "bir_lift_instr_mu" gets a program corresponding to the hex-code for a general PC
     either from a cache or derives it freshly via "bir_lift_instr_mu_gen_pc_compute".
     This general theorem is then instantiated for the concrete PC.
  *)

  type lift_inst_cache = (string, thm) Redblackmap.dict
  val lift_inst_cache_empty:lift_inst_cache = Redblackmap.mkDict String.compare


  (*
  val hex_code = "94000000"
  val hex_code = "D65F03C0";
  val hex_code = "12001C00"
  val hex_code = "54000061";
  val hex_code = "79000001"
  val hex_code = "A9B97BFD"
  val hex_code = "A9B97BFD"
  val cache = lift_inst_cache_empty
  val hex_code = "54FFE321"
  val hex_code_desc = "???"

  val hex_code = "704C"
  val hex_code = "BDF0"
  val hex_code = "09C2"
  val hex_code = "BDF7";
  val hex_code = "C500";
  *)
  local
    val bir_is_lifted_inst_block_COMPUTE_precond_tm_mr =
      list_mk_comb (
        mk_icomb ( bir_is_lifted_inst_block_COMPUTE_precond_tm, #bmr_const mr),
        [bs_v, ms_v]);

    val list_CONV = SIMP_CONV list_ss []
  in
(* For debugging RISC-V:

  val (mu_thm:thm, mm_precond_thm:thm) = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  val hex_code = String.map Char.toUpper "007302B3";
  val hex_code_desc = hex_code;

*)
  fun bir_lift_instr_mu_gen_pc_compute (mu_thm:thm, mm_precond_thm : thm) hex_code hex_code_desc =
  let
     (* call step lib to generate step theorems, compute mm and label *)
    (* TODO: Does this work correctly for RISC-V? Probably, but usage of "+=" as "assign" is funny.
     * Also see if it is necessary to use a static procID. *)
     val (next_thms, mm_tm, label_tm) = mk_inst_lifting_theorems hex_code hex_code_desc

     (* instantiate inst theorem *)
     val inst_lift_thm0 =
       let
         val thm0 = MP (SPEC (rand (concl mu_thm)) inst_lift_THM) mu_thm
         val thm1 = SPECL [mm_tm, label_tm] thm0

         val precond_thm =
           let
             val (pc_n_tm0, ml_tm) = pairSyntax.dest_pair mm_tm
             val pc_n_tm = rand pc_n_tm0;
             val thmp_0 = SPECL [pc_n_tm, ml_tm] mm_precond_thm
             val thmp_1 = CONV_RULE (RATOR_CONV (RAND_CONV list_CONV)) thmp_0
           in
             UNDISCH thmp_1
           end;

         val thm2 = MP thm1 precond_thm
       in
         thm2
       end;

     val bir_is_lifted_inst_block_COMPUTE_precond_tm0 =
       list_mk_comb (bir_is_lifted_inst_block_COMPUTE_precond_tm_mr,
        [label_tm, (rand (concl mu_thm)), mm_tm])

     (* preprocess next-theorems. Merge some, order them, derive conditions,
        assign auxiliary labels, ... *)
     val sub_block_work_list = preprocess_next_thms label_tm next_thms
       handle HOL_ERR _ =>
         raise bir_inst_liftingAuxExn (BILED_msg ("preprocessing next theorems failed"));

     (* TODO: Here, something fails... *)
     val sub_block_thms = map (lift_single_block inst_lift_thm0 bir_is_lifted_inst_block_COMPUTE_precond_tm0 mu_thm) sub_block_work_list

     val prog_thm = merge_block_thms sub_block_thms handle HOL_ERR _ =>
         raise (bir_inst_liftingAuxExn (BILED_msg "merging block theorems failed"));
  in
     prog_thm
  end handle bir_inst_liftingAuxExn d =>
    raise (bir_inst_liftingExn (hex_code, d));
  end

  (* Add a cache *)
(* For debugging RISC-V:

  val (mu_thm:thm, mm_precond_thm:thm) = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  val (cache:(string, thm) Redblackmap.dict) = Redblackmap.mkDict String.compare
  val hex_code = String.map Char.toUpper "007302B3";
  val hex_code_desc = hex_code;

*)
  fun bir_lift_instr_mu_gen_pc (mu_thm:thm, mm_precond_thm : thm) (cache : lift_inst_cache) hex_code hex_code_desc =
    (Redblackmap.find (cache, hex_code), cache, true) handle NotFound =>
  let
    val thm0 = bir_lift_instr_mu_gen_pc_compute (mu_thm, mm_precond_thm) hex_code hex_code_desc
    val cache' = Redblackmap.insert (cache, hex_code, thm0)
  in (thm0, cache', false) end

(*
val cache = lift_inst_cache_empty;
*)
  local
     val discharge_hyp_CONV = SIMP_CONV (arith_ss) [alignmentTheory.aligned_numeric, alignmentTheory.aligned_0]
     val final_CS = wordsLib.words_compset ()
     val final_CONV = computeLib.CBV_CONV final_CS
  in
(* For debugging RISC-V:

  val (mu_b, mu_e) = (Arbnum.fromInt 0, Arbnum.fromInt 0x1000000);
  val (mu_thm:thm, mm_precond_thm:thm) = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  val (cache:(string, thm) Redblackmap.dict) = Redblackmap.mkDict String.compare
  val pc =   Arbnum.fromInt 0x10030;
  val hex_code = String.map Char.toUpper "007302B3";
  val hex_code_desc = hex_code;

*)
  fun bir_lift_instr_mu (mu_b, mu_e) (mu_thm:thm, mm_precond_thm : thm)  cache (pc : Arbnum.num) hex_code hex_code_desc = let
    val _ = if (Arbnum.< (pc, mu_e) andalso Arbnum.<= (mu_b, pc)) then () else
            raise (bir_inst_liftingExn (hex_code, BILED_msg "pc outside unchanged memory region"))
(*
  val (thm0, cache', cache_used) =  bir_lift_instr_mu_gen_pc (mu_thm, mm_precond_thm) cache hex_code hex_code_desc
*)
    (* TODO: This fails... *)
    val (thm0, cache', cache_used) =  bir_lift_instr_mu_gen_pc (mu_thm, mm_precond_thm) cache hex_code hex_code_desc

    (* instantiate PC *)
    val thm1 = INST [pc_num_var |-> numSyntax.mk_numeral pc] thm0

    (* remove all remaining hyps *)
    fun discharge_hyp (tm, thm) = let
       val pre_thm  = EQT_ELIM (discharge_hyp_CONV tm)
    in (PROVE_HYP pre_thm thm) end handle HOL_ERR _ => thm
                                        | UNCHANGED => thm;

    val thm2 = List.foldl discharge_hyp thm1 (hyp thm1)

    (* simple arithmetic reduction, since we now have concrete values *)
    val thm3  = CONV_RULE final_CONV thm2
  in
    (thm3, cache', cache_used)
  end;
  end;


  local
    val mm_wf_REWR = INST_TYPE [Type.alpha |-> addr_sz_ty, Type.beta |-> mem_val_sz_ty]
         bir_is_lifted_inst_block_COMPUTE_mm_WF_REWR
    val precond_CONV = SIMP_CONV (arith_ss++wordsLib.SIZES_ss) [];
  in
  fun bir_lift_instr_prepare_mu_thms ((mu_b : Arbnum.num), (mu_e : Arbnum.num)) = let
     val (_, mu_thm) = mk_WI_end_of_nums_WFE addr_sz_ty mu_b mu_e

     val mm_precond_thm = let
       val thm1 = MATCH_MP mm_wf_REWR mu_thm
       val (pre, _) = dest_imp_only (concl thm1)
       val pre_thm = EQT_ELIM (precond_CONV pre)
       val thm2 = MP thm1 pre_thm
     in thm2 end
  in (mu_thm, mm_precond_thm) end;

  end;

  (* The main entry point for lifting an instruction. Details, please see above. *)
  fun bir_lift_instr ((mu_b : Arbnum.num), (mu_e : Arbnum.num)) = let
     val (mu_thm, mm_precond_thm) = bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  in
    fn pc => fn hex_code => fn hex_code_desc =>
       #1 (bir_lift_instr_mu (mu_b, mu_e) (mu_thm, mm_precond_thm) lift_inst_cache_empty pc hex_code hex_code_desc)
  end;



  (*****************************)
  (* Lifting the whole program *)
  (*****************************)

  (*
    val (mu_b, mu_e) = (Arbnum.fromInt 0x1000, Arbnum.fromInt 0x1000000)

    val region_1 = mk_bir_inst_lifting_region (Arbnum.fromInt 0x400470) [
      "D101C3FF","F9000FE0","B90017E1","F90007E2","F90003E3","B94017E0","51000400",
      "B9004FE0","F94007E0","B9400000","B9002FE0","F94007E0","B9400400","B90033E0"]

    val region_2 = mk_bir_inst_lifting_data_region (Arbnum.fromInt 0x400484) [
      "D101C3FF","F9000FE0","B90017E1","F90007E2","F90003E3"]

    val region_3 = BILMR (Arbnum.fromInt 0x400870, [
      ("D101C3FF", BILME_unknown), ("F9000FE0", BILME_code (SOME "???")) ,
      ("B90017E1", BILME_code NONE), ("F90007E2", BILME_data)])

    val regions = [region_1, region_2, region_3]

    val regions = [region_2]

    val (_, _, il) = region_2

    bir_lift_prog_gen (mu_b, mu_e) regions

    val (mu_b, mu_e) = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
    val regions = [((Arbnum.fromInt 0x400570), true, instrs)]

    val regions = [((Arbnum.fromInt 0x400570), true, List.take(instrs, 10))]

  *)

  local
    val data_INTRO_THM = inst_bmr_thm false bir_is_lifted_prog_LABELS_DISTINCT_DATA

    val prog_dist_EMPTY_THM = inst_bmr_thm false bir_is_lifted_prog_LABELS_DISTINCT_EMPTY
    val prog_dist_UNION_THM = inst_bmr_thm false bir_is_lifted_prog_LABELS_DISTINCT_UNION
    val prog_dist_ELIM_THM = inst_bmr_thm false bir_is_lifted_prog_LABELS_DISTINCT_ELIM
    val prog_dist_INST_THM = inst_bmr_thm false bir_is_lifted_prog_LABELS_DISTINCT_SINGLE_INST

    val prog_MMS_THM = inst_bmr_thm false bir_is_lifted_prog_MMS_EQUIV_COMPUTE

    val bir_block_rewrs = type_rws ``:'o bir_block_t``;

    val dist_labels_CS = reduceLib.num_compset ()
    val _ = computeLib.add_thms (bir_block_rewrs@[b2n_n2w_REWRS, bir_program_addr_labels_sorted_def,
      bir_label_addresses_of_program_def, bir_label_addresses_of_program_REWRS,
     bir_labels_of_program_REWRS, combinTheory.K_THM, sortingTheory.SORTED_DEF]) dist_labels_CS

    val dist_labels_CONV = computeLib.CBV_CONV dist_labels_CS

    val append_flat_CONV = PURE_REWRITE_CONV [listTheory.APPEND,
          listTheory.FLAT]


    val mm_equiv_merge_CS = reduceLib.num_compset ();
    val _ = computeLib.add_thms [bmr_mem_contains_regions_EQUIV_MERGE_REWRS,
      listTheory.LENGTH, listTheory.REV_DEF,
      listTheory.FLAT, listTheory.APPEND] mm_equiv_merge_CS

    val _ =  computeLib.add_conv (wordsSyntax.dimword_tm, 1, wordsLib.SIZES_CONV) mm_equiv_merge_CS

    val mm_equiv_merge_CONV = computeLib.CBV_CONV mm_equiv_merge_CS

(*
    val pre_thm = mm_equiv_merge_CONV pre

    val pre_thm = SIMP_CONV std_ss [bmr_mem_contains_regions_EQUIV_MERGE_REWRS] pre
*)
  in

  fun timer_start level = if ((!debug_trace) > level) then SOME (Time.now()) else NONE;
  fun timer_stop NONE = ""
    | timer_stop (SOME tm) = let
       val d_time = Time.- (Time.now(), tm);
       in (Time.toString d_time) end;

  fun bir_lift_prog_gen ((mu_b : Arbnum.num), (mu_e : Arbnum.num)) = let
     val (mu_thm, mm_precond_thm) = bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  in
    fn regions => let
      val timer = timer_start 0;
      val regions = sort (fn BILMR (pc1, _) => fn BILMR (pc2, _) => Arbnum.< (pc1, pc2)) regions
      val (len_codes, len_data, max_hc_len) = let
         fun count_inst ((hc, BILME_data), (len_codes, len_data, max_hc_len)) = (len_codes, len_data + 1, Int.max (max_hc_len, String.size hc))
           | count_inst ((hc, BILME_code NONE), (len_codes, len_data, max_hc_len)) = (len_codes + 1, len_data, Int.max (max_hc_len, String.size hc))
           | count_inst ((hc, BILME_code (SOME m)), (len_codes, len_data, max_hc_len)) = (len_codes + 1, len_data, Int.max (max_hc_len, String.size hc + String.size m + 3))
           | count_inst ((hc, BILME_unknown), (len_codes, len_data, max_hc_len)) = (len_codes + 1, len_data, Int.max (max_hc_len, String.size hc))

         fun count_region (BILMR (_, il), (len_codes, len_data, max_hc_len)) =
            foldl count_inst (len_codes, len_data, max_hc_len) il
      in foldl count_region (0, 0, 0) regions end

      fun print_padding 0 = ()
        | print_padding n = (print " "; print_padding (n-1));

      val len_codes_s = Int.toString len_codes;
      val len_data_s = Int.toString len_data;
      val print_current_data = if (len_data = 0) then (fn d => ()) else
        (fn d => let
           val d_s = Int.toString d;
           val _ = print_padding (String.size len_data_s - String.size d_s);
           val _ = print d_s;
           val _ = (print "/"; print len_data_s; print " ")
        in () end);

      fun print_current_instr_string c d is_code pc hex_code = let
         val c_s = (Int.toString c);
         val _ = print_padding (String.size len_codes_s - String.size c_s);
         val _ = print c_s;
         val _ = print "/";
         val _ = print len_codes_s;
         val _ = print " ";
         val _ = print_current_data d;
         val _ = print (if is_code then ": code \"" else ": data \"");
         val _ = print hex_code;
         val _ = print "\"";
         val _ = print_padding (max_hc_len - String.size hex_code);
         val _ = print " @ 0x";
         val _ = print ((Arbnum.toHexString pc));
      in () end;

      val cache_r = ref lift_inst_cache_empty
      val inst_no_r = ref 0;
      val data_no_r = ref 0;
      val failing_inst_r = ref ([] : (bir_inst_error list))

      val data_INTRO_THM' = MATCH_MP data_INTRO_THM mu_thm
      fun lift_data fallback (pc, hex_code) = let
         val mm_tm = (#bmr_mk_data_mm mr) pc hex_code
         val precond_thm = let
           val thm_0 = PART_MATCH (rand o snd o dest_imp_only o snd o strip_forall)
                          mm_precond_thm mm_tm
           val thm_1 = CONV_RULE (RATOR_CONV (RAND_CONV (SIMP_CONV list_ss []))) thm_0
           val thm_2 = MP thm_1 TRUTH
         in thm_2 end

         val thm0 = SPEC mm_tm data_INTRO_THM'
         val thm1 = MP thm0 precond_thm
         val _ = if fallback then () else let
           val _ = data_no_r := (!data_no_r) + 1
           val _ = if (!debug_trace > 1) then (
              print_current_instr_string (!inst_no_r) (!data_no_r) false pc hex_code; print "\n") else (if (!debug_trace = 1) then print "." else ());
         in () end;
      in thm1 end handle HOL_ERR _ =>
         raise (ERR "lift_data" ("lifting of hex-code '" ^ hex_code ^ "' failed, is the PC outside the protected memory region?"))


      fun lift_inst (pc, hex_code, entry_ty) = let
        val hex_code = String.map Char.toUpper hex_code
        val human_hex_code = (case entry_ty of
             BILME_code (SOME m) => (hex_code ^ " (" ^m ^")")
           | _ => hex_code);

        val _ = inst_no_r := (!inst_no_r) + 1
        val _ = if (!debug_trace > 1) then (
           print_current_instr_string (!inst_no_r) (!data_no_r) true pc human_hex_code) else (if (!debug_trace = 1) then print "." else ());
        val timer = timer_start 1;
        val (res, ed) = (SOME (bir_lift_instr_mu (mu_b, mu_e) (mu_thm, mm_precond_thm) (!cache_r) pc hex_code human_hex_code), NONE) handle
                       bir_inst_liftingExn (_, d)  => (NONE, SOME d)
                     | HOL_ERR _ => (NONE, NONE);

        val d_s = timer_stop timer;

        val _ = if (!debug_trace > 1) then (print (" - " ^ d_s ^ " s - ")) else ();
        val res' = case res of
             SOME (thm, cache', _) => (cache_r := cache'; MATCH_MP prog_dist_INST_THM thm)
           | NONE => lift_data true (pc, hex_code)

        val _ = case res of
             SOME (thm, _, cache_used) =>
                 if (!debug_trace > 1) then (
                   (print_with_style_ sty_OK "OK");
                   (if cache_used then (print " - "; print_with_style_ sty_CACHE "cached") else ());
                   (print "\n")) else ()
           | NONE => (
                (if (!debug_trace > 1) then (
                   (print_with_style_ sty_FAIL "FAILED\n");
                    case ed of NONE => () | SOME d =>
                    print_with_style_ sty_FAIL ("   " ^ (bir_inst_liftingExn_data_to_string d) ^ "\n")
                   ) else (
                HOL_WARNING "bir_inst_liftingLib" "bir_lift_prog_gen" (
                  "lifting of instruction '" ^ hex_code ^ " @ 0x" ^ (Arbnum.toHexString pc) ^ " failed" ^ (case ed of NONE => "" | SOME d => ": "^(bir_inst_liftingExn_data_to_string d)))));
                failing_inst_r := (pc, hex_code, human_hex_code, ed)::(!failing_inst_r))
      in res' end

      fun lift_ext_entry ((pc, hex_code, ty), thms) = let
          val thm = case ty of BILME_data => lift_data false (pc, hex_code)
                             | _ => lift_inst (pc, hex_code, ty)
        in (thm::thms) end

      val _ = if (!debug_trace = 1) then print "bir_lift_prog " else ();
      val prog_dist_EMPTY_THM' = MATCH_MP prog_dist_EMPTY_THM mu_thm

(*
      val (thm1::thm2::_) = hd basic_thms
*)

      val merge_prog_distinct_thms =
         foldl (fn (thm1, thm2) => let
            val (_, mu_tm, mms1_tm, p1_tm) = dest_bir_is_lifted_prog_LABELS_DISTINCT (concl thm1)
            val (_, mu_tm, mms2_tm, p2_tm) = dest_bir_is_lifted_prog_LABELS_DISTINCT (concl thm2)

            val thma = SPECL [mu_tm, mms1_tm, mms2_tm, p1_tm, p2_tm] prog_dist_UNION_THM                        val thmb = MP thma thm1
            val thmc = MP thmb thm2
            in thmc
            end)
           prog_dist_EMPTY_THM'

      val ext_entries = expand_bir_inst_lifting_mem_regions (#bmr_hex_code_size mr) regions
      val _ = case check_expanded_bir_inst_lifting_mem_regions ext_entries of
                   NONE =>
                     raise (ERR "preprocess regions"
                                "memory addresses of regions are not strictly increasing")
                 | SOME (pc_min, pc_max) => if (Arbnum.<= (mu_b, pc_min) andalso
                                                Arbnum.<= (pc_max, mu_e)) then () else
                     raise (ERR "preprocess regions" ("the program is not (completely) stored in the unchanged part of memory, please enforce that at least the interval [0x" ^ (Arbnum.toHexString pc_min) ^ ", 0x" ^ Arbnum.toHexString (Arbnum.+ (Arbnum.one, pc_max)) ^")" ^ " is enforced to be unchanged"))

      val basic_thms = let
          val timer = timer_start 1;

          val basic_thms = foldl lift_ext_entry [] ext_entries;

          val d_s = timer_stop timer;
          val _ = if (!debug_trace > 1) then (print ("\ntime to lift individual instructions only - " ^ d_s ^ " s\n")) else ();
        in
          basic_thms
        end;


      val prog_thm0 = let
        val _ = if (!debug_trace > 1) then (print ("merging code"))
                else if (!debug_trace = 1) then (print "!") else ();
        val timer = timer_start 1;
        val prog_dist_thm = merge_prog_distinct_thms basic_thms

        val thm0 = MATCH_MP prog_dist_ELIM_THM prog_dist_thm
        val (p_tm, mms_tm) = let
           val (aux_tm1, aux_tm2) = dest_imp_only (snd (strip_forall (concl thm0)))
           val p_tm = lhs aux_tm1
           val mms_tm = lhs (fst (dest_imp_only aux_tm2))
        in (p_tm, mms_tm) end
        val p_thm = append_flat_CONV p_tm
        val mms_thm = append_flat_CONV mms_tm

        val thm1 = MP (MP (SPECL [rhs (concl p_thm), rhs (concl mms_thm)] thm0) p_thm) mms_thm

        val d_s = timer_stop timer;
        val _ = if (!debug_trace > 1) then (print (" - " ^ d_s ^ " s\n")) else ();
      in thm1 end;


      val _ = if ((!debug_trace > 1) andalso (not (List.null (!failing_inst_r)))) then
                (print "\n"; print_bir_inst_errors (!failing_inst_r)) else ();

      val prog_thm1 = let
        val _ = if (!debug_trace > 1) then (print ("checking for duplicate labels"))
                else if (!debug_trace = 1) then (print "!") else ();
        val timer = timer_start 1;

        val (pre, _) = dest_imp_only (concl prog_thm0)
        val pre_thm = EQT_ELIM (dist_labels_CONV pre)
        val thm2 = MP prog_thm0 pre_thm

        val d_s = timer_stop timer;
        val _ = if (!debug_trace > 1) then (print (" - " ^ d_s ^ " s\n")) else ();
      in thm2 end;


      val prog_thm2 = let
        val _ = if (!debug_trace > 1) then (print ("merging memory-regions"))
                else if (!debug_trace = 1) then (print "!") else ();
        val timer = timer_start 1;

        val (_, mu_tm, mms_tm, p_tm) = dest_bir_is_lifted_prog (concl prog_thm1)
        val thm0 = SPECL [mu_tm, p_tm, mms_tm] prog_MMS_THM
        val thm1 = MP thm0 prog_thm1
        val pre = lhs (fst (dest_imp_only (snd (strip_forall (concl thm1)))))
        val pre_thm = mm_equiv_merge_CONV pre
        val mms'_tm = rhs (concl pre_thm)
        val thm2 = MP (SPEC mms'_tm thm1) pre_thm

        val d_s = timer_stop timer;
        val _ = if (!debug_trace > 1) then (print (" - " ^ d_s ^ " s\n")) else ();
      in thm2 end;


      val d_s = timer_stop timer;
      val _ = if (!debug_trace > 1) then
        print ("Total time :") else ();
      val _ = if (!debug_trace <> 0) then
         (print (" " ^ d_s ^ " s -");
         (if (List.null (!failing_inst_r)) then print_with_style_ sty_OK " OK\n" else
             print_with_style_ sty_FAIL " FAILED\n")) else ();

    in
      (prog_thm2, List.rev (!failing_inst_r))
    end
  end;

  end;

  fun bir_lift_prog (mu_b, mu_e) pc hex_codes =
     bir_lift_prog_gen (mu_b, mu_e) [BILMR (pc, List.map (fn hc => (hc, BILME_unknown)) hex_codes)]

end (* functor *)


structure bir_inst_liftingLib :> bir_inst_liftingLib =
struct

  structure bmil_arm8 = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.arm8_bmr_rec end);

  structure bmil_m0_LittleEnd_Process = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_bmr_rec_LittleEnd_Process end);
  structure bmil_m0_LittleEnd_Main    = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_bmr_rec_LittleEnd_Main end);
  structure bmil_m0_BigEnd_Process    = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_bmr_rec_BigEnd_Process end);
  structure bmil_m0_BigEnd_Main       = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_bmr_rec_BigEnd_Main end);

  structure bmil_m0_mod_LittleEnd_Process = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_mod_bmr_rec_LittleEnd_Process end);
  structure bmil_m0_mod_LittleEnd_Main    = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_mod_bmr_rec_LittleEnd_Main end);
  structure bmil_m0_mod_BigEnd_Process    = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_mod_bmr_rec_BigEnd_Process end);
  structure bmil_m0_mod_BigEnd_Main       = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.m0_mod_bmr_rec_BigEnd_Main end);

  structure bmil_riscv = bir_inst_liftingFunctor (struct val mr =
     bir_lifting_machinesLib_instances.riscv_bmr_rec end);

end (* struct *)
