open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;
open bir_pred_cm0Lib;

val _ = new_theory "aes_o0_loop";

val birs_prog_config = ((fst o dest_eq o concl) aes_o0Lib.prog_def, aes_o0Lib.birenvtyl_def);

val _ = set_default_cheat_setting ();

val bin_offset = 0x0800910c (*new*) - 0x100003ac (*old*);

val gen_arg1 = (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x));
val gen_arg2 =
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) aesTheory.bir_o0_aes_progbin_def) (0x100007d4+bin_offset, 0x100007e4+bin_offset))@
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) aesTheory.bir_o0_aes_progbin_def) (0x100007fc+bin_offset, 0x10000808+bin_offset));

(*
(*val _ = print_theorem_before_merging := true;*)
val balrob_summary_my_aes_thm =
  let
    val reqs = ((0, 96+0), 2000);
    val locs =
      (0x100007e4,
      [0x1000040E(*0x100005c4*)]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
val _ = print_thm balrob_summary_my_aes_thm;
val (_, mem_exp) = (birsSyntax.get_birs_Pi_first_env_top_mapping o concl o CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV "MEM"))) balrob_summary_my_aes_thm;
val _ = birs_mergeLib.print_mem_exp 100 mem_exp;
raise Fail "";


("R7",
              BExp_BinExp BIExp_Minus
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                (BExp_Const (Imm32 104w)));

rkptr = 12
  (BExp_BinExp BIExp_Minus
     (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
     (BExp_Const (Imm32 92w)))
    -> BExp_Const (Imm32 0x10001B4Cw)

roundnumber = at [r7, #52]
104-52 = 52

my_aes_inBlock = 4
  (BExp_BinExp BIExp_Minus
     (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
     (BExp_Const (Imm32 100w)))

my_aes_outBlock = 0
  BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
    (BExp_Const (Imm32 104w))
*)

(* ------------------------------------ *)
val rounds = 10; (* actually, could be 10, 12 or 14 depending on key size; but simplify for now *)

val blocksize = 128; (* bits *)
val roundkeysize = blocksize;
val roundkeys = rounds + 1;
val rkbufsz = (roundkeysize div 8) * roundkeys;
val blksz = blocksize div 8;

val alt_sp_bvar_aes_tm = ``BExp_Den (BVar "R7" (BType_Imm Bit32))``;
val rk_tm = mem_load_sp_tm alt_sp_bvar_aes_tm 12;
val inblk_tm = mem_load_sp_tm alt_sp_bvar_aes_tm 4;
val outblk_tm = mem_load_sp_tm alt_sp_bvar_aes_tm 0;

val round_tm = mem_load_sp_tm alt_sp_bvar_aes_tm 52; (* in memory at [r7, #52] *)

val mem_params = (``0x8009568w:word32``, ``0x30001820w:word32``); (* TODO: what is this? *)

val pred_conjs_extra_aes_tm = bslSyntax.bandl
 ([mem_addrs_stack_disj_bir_tm alt_sp_bvar_aes_tm (bslSyntax.bplus(rk_tm,bslSyntax.bconst32 blksz)),
   mem_addrs_stack_disj_bir_tm alt_sp_bvar_aes_tm (bslSyntax.bplus(inblk_tm,bslSyntax.bconst32 blksz)),
   mem_area_disj_reg_bir_tm (rk_tm, blksz) (inblk_tm, blksz)]
  @(List.map (mem_addrs_aligned_prog_disj_bir_tm mem_params)
      [alt_sp_bvar_aes_tm, rk_tm, inblk_tm]));

(*
val _ = pred_conjs_extra_tm := SOME pred_conjs_extra_aes_tm;
val _ = alt_sp_bvar_tm := SOME alt_sp_bvar_aes_tm;
val balrob_summary_aes_loop_body_thm =
  let
    val reqs = ((~104, 104), 353);
    val locs =
      (0x1000040e,
      [0x1000042c(*0x1000041e*)]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;

val _ = print_thm balrob_summary_aes_loop_body_thm;

val balrob_summary_aes_loop_body_forgotten1_thm =
  (birs_mergeLib.birs_Pi_first_env_top_mapping_forget_storeidxs [0] o
   CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV "MEM")))
  balrob_summary_aes_loop_body_thm;

val _ = print_thm balrob_summary_aes_loop_body_forgotten1_thm;

val _ = raise ERR "" "";
*)

(* ------------------------------------ *)

val _ = pred_conjs_extra_tm := SOME pred_conjs_extra_aes_tm;
val _ = alt_sp_bvar_tm := SOME alt_sp_bvar_aes_tm;
val balrob_summary_aes_loop_body_thm =
  let
    val reqs = ((~104, 104), 353);
    val locs =
      (0x1000040e+bin_offset,
      [0x100005c0+bin_offset(**)]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_aes_loop_body_thm;
val _ = alt_sp_bvar_tm := NONE;
val _ = pred_conjs_extra_tm := NONE;

val (_, mem_exp) = (birsSyntax.get_birs_Pi_first_env_top_mapping o concl o CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV "MEM"))) balrob_summary_aes_loop_body_thm;
val _ = birs_mergeLib.print_mem_exp 700 mem_exp;


val _ = print "\n\n"

val _ = print "\nstep 1:\n"
(* need to forget everything except for roundkey pointer update and rounds left counter, otherwise memory explodes in the face *)
val balrob_summary_aes_loop_body_forgotten1_thm =
  (birs_mergeLib.birs_Pi_first_env_top_mapping_forget_storeidxs [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] o
   CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV "MEM")))
  balrob_summary_aes_loop_body_thm;
val _ = print "\nstep 2:\n"
(* good to forget other stuff that will be instantiated over and over and contains the whole memory multiple times *)
val forget_env_varnames = ["R2", "PSR_C", "PSR_N", "PSR_V", "PSR_Z", "R3"];
val balrob_summary_aes_loop_body_forgotten_thm =
  List.foldl (fn (vn, thm_) =>
    (birs_mergeLib.birs_Pi_first_env_top_mapping_forget o
    CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV vn))) thm_)
  balrob_summary_aes_loop_body_forgotten1_thm
  forget_env_varnames;

val _ = print "\nstep 3:\n"
val (_, mem_exp) = (birsSyntax.get_birs_Pi_first_env_top_mapping o concl o CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV "MEM"))) balrob_summary_aes_loop_body_forgotten_thm;
val _ = birs_mergeLib.print_mem_exp 400 mem_exp;

val _ = print "\n\n"

(*val _ = print_thm balrob_summary_aes_loop_body_forgotten_thm;*)
Theorem balrob_summary_aes_loop_body_forgotten_thm =
  balrob_summary_aes_loop_body_forgotten_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
