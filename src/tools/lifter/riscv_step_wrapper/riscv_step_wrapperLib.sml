(* Adapted from HOL4 examples - see COPYRIGHT file in this directory *)

structure riscv_step_wrapperLib :> riscv_step_wrapperLib =
struct

open HolKernel boolLib bossLib;
open blastLib riscvTheory riscv_stepTheory riscv_stepLib;

structure Parse = struct
  open Parse
  val (Type, Term) = parse_from_grammars riscv_stepTheory.riscv_step_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "riscv_stepLib"

val s = ``s:riscv_state``

local
  val i16 = fcpSyntax.mk_int_numeric_type 16
  val i32 = fcpSyntax.mk_int_numeric_type 32
  val x = Term.mk_var ("x", ``:rawInstType``)
  fun padded_opcode v =
    let
      val (l, ty) = listSyntax.dest_list v
      val () = ignore (ty = Type.bool andalso List.length l <= 32 orelse
               raise ERR "mk_opcode" "bad opcode")
      fun ends_in_TT [] = false
        | ends_in_TT [x] = false
        | ends_in_TT [x,y] = aconv x y andalso aconv x boolSyntax.T
        | ends_in_TT (x::xs) = ends_in_TT xs
    in
      if ends_in_TT l then
        listSyntax.mk_list (utilsLib.padLeft boolSyntax.F 32 l, ty)
      else
        listSyntax.mk_list (utilsLib.padLeft boolSyntax.F 16 l, ty)
    end
  fun pad_opcode v =
    let
      val xs = padded_opcode v
      val (l,ty) = listSyntax.dest_list xs
    in
      if length l < 32 then mk_comb(``Half``,bitstringSyntax.mk_v2w (xs, i16))
                       else mk_comb(``Word``,bitstringSyntax.mk_v2w (xs, i32))
    end
in
  val padded_opcode = padded_opcode
  fun fetch v = let
    val vs = pad_opcode v
    val lemma = if can (match_term ``Word _``) vs
                then riscv_stepTheory.Fetch32 else riscv_stepTheory.Fetch16
    val bs = vs |> rand |> rand
    in lemma |> SPEC bs |> SIMP_RULE std_ss [listTheory.CONS_11]
             |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL end
  val fetch_hex = fetch o bitstringSyntax.bitstring_of_hexstring
end

val STATE_CONV =
  Conv.QCONV
    (REWRITE_CONV
       ([ASSUME ``^s.exception = riscv$NoException``,
         ASSUME ``^s.c_NextFetch ^s.procID = NONE``,
         riscv_stepTheory.update_pc, updateTheory.UPDATE_EQ] @
        utilsLib.datatype_rewrites true "riscv" ["riscv_state"]))

val state_rule = Conv.RIGHT_CONV_RULE STATE_CONV
val full_state_rule = utilsLib.ALL_HYP_CONV_RULE STATE_CONV o state_rule

val fetch_inst =
  Thm.INST []

local
  val rwts = List.map (full_state_rule o fetch_inst o DB.fetch "riscv_step")
               riscv_stepTheory.rwts
  val fnd = utilsLib.find_rw (utilsLib.mk_rw_net utilsLib.lhsc rwts)
  val rule = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
             THENC REWRITE_CONV [riscv_stepTheory.v2w_0_rwts]
  val eval_simp_rule =
    utilsLib.ALL_HYP_CONV_RULE rule o Conv.CONV_RULE (Conv.RHS_CONV rule)
  fun eval tm rwt =
    let
      val thm = eval_simp_rule (utilsLib.INST_REWRITE_CONV1 rwt tm)
    in
      if utilsLib.vacuous thm then NONE else SOME thm
    end
  val neg_count = List.length o List.filter boolSyntax.is_neg o Thm.hyp
  fun err tm s = ( Parse.print_term tm; print "\n"; raise ERR "run" s )
in
  fun run tm =
    (case List.mapPartial (eval tm) (fnd tm) of
        [] => err tm "no valid step theorem"
      | [x] => x
      | l => List.last (mlibUseful.sort_map neg_count Int.compare l))
    handle HOL_ERR {message = "not found", origin_function = "find_rw", ...} =>
      err tm "instruction instance not supported"
end


local
  fun mk_proj s =
    Lib.curry Term.mk_comb
      (Term.prim_mk_const {Thy = "riscv", Name = "riscv_state_" ^ s})
  fun proj f = STATE_CONV o f o utilsLib.rhsc
  val proj_exception = proj (mk_proj "exception")
  val proj_NextFetch = mk_proj "c_NextFetch"
  val proj_procID = mk_proj "procID"
  val proj_NextFetch_procID =
    proj (fn tm => Term.mk_comb (proj_NextFetch tm, proj_procID tm))
  val ap_snd = Thm.AP_TERM ``SND: unit # riscv_state -> riscv_state``
  val snd_conv = Conv.REWR_CONV pairTheory.SND
  fun spec_run thm3 ethm =
    Conv.RIGHT_CONV_RULE
      (Conv.RAND_CONV (Conv.REWR_CONV ethm) THENC snd_conv) (ap_snd thm3)
  fun next th = PURE_REWRITE_RULE [word_bit_0_lemmas] o state_rule o Drule.MATCH_MP th
  val MP_Next_n = next riscv_stepTheory.NextRISCV
  val MP_Next_c = next riscv_stepTheory.NextRISCV_cond_branch
  val MP_Next_b = next riscv_stepTheory.NextRISCV_branch
  val Run_CONV = utilsLib.Run_CONV ("riscv", s) o utilsLib.rhsc
  fun tidy_up_signalAddressException th ss_rem =
    let
      val rw = UNDISCH avoid_signalAddressException
      fun FORCE_REWR_CONV rw tm =
        let
          val (p,_) = match_term (rw |> concl |> rator |> rand) tm
        in INST p rw end handle HOL_ERR _ => NO_CONV tm;
    in
      CONV_RULE (DEPTH_CONV (FORCE_REWR_CONV rw)) th
      |> DISCH_ALL |> SIMP_RULE std_ss [word_bit_add_lsl_simp]
      |> SIMP_RULE (simpLib.remove_ssfrags ss_rem (srw_ss())) [] |> UNDISCH_ALL
    end
in
  fun riscv_step' ss_rem v =
    let
      val thm1 = fetch v
      val thm2 = riscv_decode v |> SIMP_RULE std_ss []
      val new_s = thm1 |> concl |> rand |> rand
      val thm3 = fetch_inst (Drule.SPEC_ALL (Run_CONV thm2)) |> INST [s |-> new_s]
      val tm = utilsLib.rhsc thm3
      val ethm = run tm
      val ethm = tidy_up_signalAddressException ethm ss_rem
      val thm4 = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV ethm) thm3
      val thm5 = proj_exception thm4
      val thm6 = proj_NextFetch_procID thm4
      val thm = Drule.LIST_CONJ [thm1, thm2, thm4, thm5, thm6]
      val tm = utilsLib.rhsc thm6
    in
      if optionSyntax.is_none tm
        then MP_Next_n thm
      else if boolSyntax.is_cond tm
        then MP_Next_c thm
      else MP_Next_b thm
    end
end

fun riscv_step_rem_ss ss_rem = riscv_step' ss_rem;

fun riscv_step_rem_ss_hex ss_rem = (riscv_step' ss_rem) o bitstringSyntax.bitstring_of_hexstring;

end
