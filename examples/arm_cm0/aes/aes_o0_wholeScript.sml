open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;
open bir_pred_cm0Lib;
open aes_o0_loopTheory;

val _ = new_theory "aes_o0_whole";

val birs_prog_config = ((fst o dest_eq o concl) aes_o0Lib.prog_def, aes_o0Lib.birenvtyl_def);

val _ = set_default_cheat_setting ();

val bin_offset = 0x0800910c (*new*) - 0x100003ac (*old*);

val gen_arg1 = (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x));
val gen_arg2 =
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) aesTheory.bir_o0_aes_progbin_def) (0x100007d4+bin_offset, 0x100007e4+bin_offset))@
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) aesTheory.bir_o0_aes_progbin_def) (0x100007fc+bin_offset, 0x10000808+bin_offset));

val pcond_new_tm = ref T;
val pcond_old_tm = ref T;

val _ = birs_conseqLib.birs_sys_pcond_RULE_debug_fun := SOME (fn pcond_new => fn pcond_old =>
  let
    val _ = pcond_new_tm := pcond_new;
    val _ = pcond_old_tm := pcond_old;
    (*val _ = print_term pcond_old;*)
  in
    raise Fail ""
  end
);

val _ = birs_strategiesLib.birs_from_summaries_debug_fun := SOME (fn state =>
  let
    (*val _ = print "\n\n\n\n\nstart\n"
    val _ = print_term state;
    val _ = print "\ndone\n\n\n\n\n"*)
    val _ = print "pre summary instantiation code runs now\n";
    val get_top_map = (birsSyntax.get_env_top_mapping o birsSyntax.dest_birs_state_env);
    val (mem_exp) = (snd o get_top_map o rhs o concl o birs_utilsLib.birs_env_var_top_CONV "MEM") state;
    val _ = birs_mergeLib.print_mem_exp 500 mem_exp;
  in
    ()
  end
);

(*
  val _ = Globals.max_print_depth := 8;
*)


(* ============================================================================================================ *)

(* ============================================================================================================ *)
(* ================================= DEBUG INSTANTIATION ISSUE, BETTER MOVE TO NARROWING FUNCTION LATER FOR READABLE REPORTING ========================================== *)
(*
fun is_imp_check be1 be2 =
  isSome (birs_utilsLib.check_imp_tm (birsSyntax.mk_birs_exp_imp (be1, be2)));

(*
val exp = List.nth(pcondl_filtered, 0);
identical (simplify_load_subexp exp) exp
*)
fun simplify_exp pcond exp =
  let
    val simp_fun = birs_simp_instancesLib.birs_simp_default_armcm0_gen false birs_simpLib.birs_simp_ID_fun [];
    (*val pcond = bslSyntax.bconst1 1;*)
    val simp_tm = birs_simpLib.birs_simp_gen_term pcond exp;
    (*val _ = print_term simp_tm;*)
    val res_thm = simp_fun simp_tm;
  in
    (rand o concl) res_thm
  end;

fun simplify_subexp is_exp pcond exp =
  let
    val t = birs_auxLib.GEN_match_conv is_exp (fn subexp => prove(mk_eq (subexp, simplify_exp pcond subexp), cheat)) exp;
  in
    (rhs o concl) t
  end;

val simplify_load_subexp =
  simplify_subexp (bir_expSyntax.is_BExp_Load);

val pcond_new = !pcond_new_tm;
(*val pcond_new = bslSyntax.band(bslSyntax.bconst1 1,pcond_new)*)
val pcond_old = !pcond_old_tm;

(*val imp_tm = mk_birs_exp_imp (pcond_new, pcond_old);*)
val pcondl = birsSyntax.dest_bandl pcond_old;


val pcondl_filtered = List.filter (not o is_imp_check pcond_new) pcondl;
val pcondl_mapped = List.map (simplify_load_subexp pcond_new) pcondl_filtered;

val _ = bir_smtLib.birsmt_check_unsat_write_query_to_disk := true;

val pcondl_filtered3 = List.filter (not o is_imp_check pcond_new) pcondl_mapped;



simplify_load_subexp pcond_new (List.nth(pcondl_filtered, 1))
length pcondl_filtered
*)
(*
BExp_BinPred BIExp_LessThan
      (BExp_BinExp BIExp_Minus
         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
         (BExp_Const (Imm32 104w))) (BExp_Const (Imm32 0x10001B4Cw))


“BExp_BinPred BIExp_LessThan
      (BExp_BinExp BIExp_Minus
         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
         (BExp_Const (Imm32 104w)))
   0x10001BEC
*)


(* ------------------------------------ *)

val balrob_summary_my_aes_thm =
  let
    val reqs = ((0, 96+8), 3755);
    val locs =
      (0x100007e4+bin_offset,
      [0x100007f8+bin_offset]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      [balrob_summary_aes_loop_body_forgotten_thm]
      reqs
      locs
  end;
Theorem balrob_summary_my_aes_thm =
  balrob_summary_my_aes_thm;
val _ = print_result balrob_summary_my_aes_thm ("0x8009558w", "pop {r7, pc}", "6");

(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
