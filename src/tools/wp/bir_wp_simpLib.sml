open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_wpTheory;

open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;

open bir_expLib;
open finite_mapSyntax;
open pairSyntax;

open bir_wp_simpTheory;

load "pairLib";


structure bir_wp_simpLib =
struct


  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_exp_substitutions"
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exp_subst1_tm, mk_bir_exp_subst1, dest_bir_exp_subst1, is_bir_exp_subst1) = syntax_fns3 "bir_exp_subst1";
  
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_wp_simp"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exp_imp_tm, mk_bir_exp_imp, dest_bir_exp_imp, is_bir_exp_imp) = syntax_fns2 "bir_exp_imp";
  val (bir_exp_and_tm, mk_bir_exp_and, dest_bir_exp_and, is_bir_exp_and) = syntax_fns2 "bir_exp_and";
  val (bir_exp_varsubst_tm, mk_bir_exp_varsubst, dest_bir_exp_varsubst, is_bir_exp_varsubst) = syntax_fns2 "bir_exp_varsubst";
  val (bir_exp_varsubst1_tm, mk_bir_exp_varsubst1, dest_bir_exp_varsubst1, is_bir_exp_varsubst1) = syntax_fns3 "bir_exp_varsubst1";

  val simp_extract = dest_bir_exp_imp o snd o dest_comb;
(*
  fun simp_extract goalterm =
    let
      val (prem, term) = (dest_bir_exp_imp o snd o dest_comb) goalterm;
(*
      val prem = (fst o dest_comb) prems;
      val term = (snd o dest_comb o fst o dest_comb o fst o dest_eq) beval;
*)
    in
      (prem, term)
    end;
*)

  fun is_bir_exp_subst term =
    let
      fun match_pat matchpat t = (let val _ = match_term matchpat t in (true) end) handle _ => (false);
    in
      match_pat ``bir_exp_subst substm e1`` term (* use mk_term!!! *)
    end;

  fun dest_bir_exp_subst term =
    let
      val substsm_var = mk_var ("substsm", ``:bir_var_t |-> bir_exp_t``);
      val e1_var = mk_var ("e1", ``:bir_exp_t``);
      val (substv, _) = match_term ``bir_exp_subst ^substsm_var ^e1_var`` term; (* use mk_term!!! *)
    in
      (subst substv substsm_var, subst substv e1_var)
    end;

  fun lookup_def def_str =
    let
      val (_, (def_thm, _)) = hd (DB.find def_str);
    in
      def_thm
    end;

  fun subsm_is_var_only subsm =
      if is_fempty subsm then true else
      let
        val (subsm1, ve) = dest_fupdate subsm;
        val e = (snd o dest_pair) ve;
      in
        (is_BExp_Den e) andalso (subsm_is_var_only subsm1)
      end;







  val get_concl_lhs = fst o dest_eq o concl;
  val get_concl_rhs = snd o dest_eq o concl;

  val bir_var_ss = rewrites (type_rws ``:bir_var_t``);
  val string_ss = rewrites (type_rws ``:string``);
  val char_ss = rewrites (type_rws ``:char``);
  val bir_type_option_pair_ss = rewrites (type_rws ``:bir_type_t option # bir_type_t option``);





(*
val bigset = ``
(
{BVar "R0" (BType_Imm Bit64); BVar "R0_wp_0" (BType_Imm Bit64);
   BVar "MEM" (BType_Mem Bit64 Bit8); BVar "R0_wp_1" (BType_Imm Bit64);
   BVar "R0_wp_3" (BType_Imm Bit64); BVar "R0_wp_4" (BType_Imm Bit64);
   BVar "MEM_wp_2" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_5" (BType_Imm Bit64); BVar "R0_wp_7" (BType_Imm Bit64);
   BVar "R0_wp_8" (BType_Imm Bit64);
   BVar "MEM_wp_6" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_9" (BType_Imm Bit64); BVar "R0_wp_11" (BType_Imm Bit64);
   BVar "MEM_wp_10" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_12" (BType_Imm Bit64); BVar "R0_wp_14" (BType_Imm Bit64);
   BVar "R0_wp_16" (BType_Imm Bit64); BVar "R0_wp_17" (BType_Imm Bit64);
   BVar "R1_wp_15" (BType_Imm Bit64); BVar "R0_wp_18" (BType_Imm Bit64);
   BVar "MEM_wp_13" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_19" (BType_Imm Bit64); BVar "R0_wp_21" (BType_Imm Bit64);
   BVar "R0_wp_23" (BType_Imm Bit64); BVar "R0_wp_24" (BType_Imm Bit64);
   BVar "R1_wp_22" (BType_Imm Bit64); BVar "R0_wp_25" (BType_Imm Bit64);
   BVar "MEM_wp_20" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_26" (BType_Imm Bit64); BVar "R0_wp_28" (BType_Imm Bit64);
   BVar "R0_wp_30" (BType_Imm Bit64); BVar "R0_wp_31" (BType_Imm Bit64);
   BVar "R1_wp_29" (BType_Imm Bit64); BVar "R0_wp_32" (BType_Imm Bit64);
   BVar "MEM_wp_27" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_33" (BType_Imm Bit64); BVar "R0_wp_35" (BType_Imm Bit64);
   BVar "R0_wp_37" (BType_Imm Bit64); BVar "R0_wp_38" (BType_Imm Bit64);
   BVar "R1_wp_36" (BType_Imm Bit64); BVar "R0_wp_39" (BType_Imm Bit64);
   BVar "MEM_wp_34" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_40" (BType_Imm Bit64); BVar "R0_wp_43" (BType_Imm Bit64);
   BVar "R1_wp_42" (BType_Imm Bit64); BVar "R0_wp_45" (BType_Imm Bit64);
   BVar "R1_wp_44" (BType_Imm Bit64); BVar "R0_wp_47" (BType_Imm Bit64);
   BVar "R1_wp_46" (BType_Imm Bit64); BVar "R0_wp_49" (BType_Imm Bit64);
   BVar "R0_wp_50" (BType_Imm Bit64); BVar "R1_wp_48" (BType_Imm Bit64);
   BVar "MEM_wp_41" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_51" (BType_Imm Bit64); BVar "R0_wp_53" (BType_Imm Bit64);
   BVar "R0_wp_54" (BType_Imm Bit64);
   BVar "MEM_wp_52" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_55" (BType_Imm Bit64); BVar "R0_wp_57" (BType_Imm Bit64);
   BVar "R0_wp_58" (BType_Imm Bit64);
   BVar "MEM_wp_56" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_59" (BType_Imm Bit64); BVar "R0_wp_61" (BType_Imm Bit64);
   BVar "R0_wp_62" (BType_Imm Bit64);
   BVar "MEM_wp_60" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_63" (BType_Imm Bit64); BVar "R0_wp_65" (BType_Imm Bit64);
   BVar "MEM_wp_64" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_66" (BType_Imm Bit64); BVar "R0_wp_68" (BType_Imm Bit64);
   BVar "R0_wp_70" (BType_Imm Bit64); BVar "R0_wp_71" (BType_Imm Bit64);
   BVar "R1_wp_69" (BType_Imm Bit64); BVar "R0_wp_72" (BType_Imm Bit64);
   BVar "MEM_wp_67" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_73" (BType_Imm Bit64); BVar "R0_wp_75" (BType_Imm Bit64);
   BVar "R0_wp_77" (BType_Imm Bit64); BVar "R0_wp_78" (BType_Imm Bit64);
   BVar "R1_wp_76" (BType_Imm Bit64); BVar "R0_wp_79" (BType_Imm Bit64);
   BVar "MEM_wp_74" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_80" (BType_Imm Bit64); BVar "R0_wp_82" (BType_Imm Bit64);
   BVar "R0_wp_84" (BType_Imm Bit64); BVar "R0_wp_85" (BType_Imm Bit64);
   BVar "R1_wp_83" (BType_Imm Bit64); BVar "R0_wp_86" (BType_Imm Bit64);
   BVar "MEM_wp_81" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_87" (BType_Imm Bit64); BVar "R0_wp_89" (BType_Imm Bit64);
   BVar "R0_wp_91" (BType_Imm Bit64); BVar "R0_wp_92" (BType_Imm Bit64);
   BVar "R1_wp_90" (BType_Imm Bit64); BVar "R0_wp_93" (BType_Imm Bit64);
   BVar "MEM_wp_88" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_94" (BType_Imm Bit64); BVar "R0_wp_97" (BType_Imm Bit64);
   BVar "R1_wp_96" (BType_Imm Bit64); BVar "R0_wp_99" (BType_Imm Bit64);
   BVar "R1_wp_98" (BType_Imm Bit64);
   BVar "R0_wp_101" (BType_Imm Bit64);
   BVar "R1_wp_100" (BType_Imm Bit64);
   BVar "R0_wp_103" (BType_Imm Bit64);
   BVar "R0_wp_104" (BType_Imm Bit64);
   BVar "R0_wp_105" (BType_Imm Bit64);
   BVar "R1_wp_102" (BType_Imm Bit64);
   BVar "MEM_wp_95" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_106" (BType_Imm Bit64);
   BVar "R0_wp_108" (BType_Imm Bit64);
   BVar "R0_wp_109" (BType_Imm Bit64);
   BVar "MEM_wp_107" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_110" (BType_Imm Bit64);
   BVar "R0_wp_112" (BType_Imm Bit64);
   BVar "R0_wp_113" (BType_Imm Bit64);
   BVar "MEM_wp_111" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_114" (BType_Imm Bit64);
   BVar "R0_wp_116" (BType_Imm Bit64);
   BVar "R0_wp_117" (BType_Imm Bit64);
   BVar "MEM_wp_115" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_118" (BType_Imm Bit64);
   BVar "R0_wp_120" (BType_Imm Bit64);
   BVar "MEM_wp_119" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_121" (BType_Imm Bit64);
   BVar "R0_wp_123" (BType_Imm Bit64);
   BVar "R0_wp_125" (BType_Imm Bit64);
   BVar "R0_wp_126" (BType_Imm Bit64);
   BVar "R1_wp_124" (BType_Imm Bit64);
   BVar "R0_wp_127" (BType_Imm Bit64);
   BVar "MEM_wp_122" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_128" (BType_Imm Bit64);
   BVar "R0_wp_130" (BType_Imm Bit64);
   BVar "R0_wp_132" (BType_Imm Bit64);
   BVar "R0_wp_133" (BType_Imm Bit64);
   BVar "R1_wp_131" (BType_Imm Bit64);
   BVar "R0_wp_134" (BType_Imm Bit64);
   BVar "MEM_wp_129" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_135" (BType_Imm Bit64);
   BVar "R0_wp_137" (BType_Imm Bit64);
   BVar "R0_wp_139" (BType_Imm Bit64);
   BVar "R0_wp_140" (BType_Imm Bit64);
   BVar "R1_wp_138" (BType_Imm Bit64);
   BVar "R0_wp_141" (BType_Imm Bit64);
   BVar "MEM_wp_136" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_142" (BType_Imm Bit64);
   BVar "R0_wp_144" (BType_Imm Bit64);
   BVar "R0_wp_146" (BType_Imm Bit64);
   BVar "R0_wp_147" (BType_Imm Bit64);
   BVar "R1_wp_145" (BType_Imm Bit64);
   BVar "R0_wp_148" (BType_Imm Bit64);
   BVar "MEM_wp_143" (BType_Mem Bit64 Bit8);
   BVar "R0_wp_149" (BType_Imm Bit64);
   BVar "R0_wp_152" (BType_Imm Bit64);
   BVar "R1_wp_151" (BType_Imm Bit64);
   BVar "R0_wp_154" (BType_Imm Bit64);
   BVar "R1_wp_153" (BType_Imm Bit64);
   BVar "R1_wp_157" (BType_Imm Bit64);
   BVar "R0_wp_156" (BType_Imm Bit64);
   BVar "R1_wp_155" (BType_Imm Bit64);
   BVar "MEM_wp_150" (BType_Mem Bit64 Bit8);
   BVar "SP_EL0" (BType_Imm Bit64); BVar "R0_wp_159" (BType_Imm Bit64);
   BVar "R0_wp_158" (BType_Imm Bit64)}
)
``;

val settocheck = ``^bigset UNION ({BVar "R1_wp_158" (BType_Imm Bit64)} UNION ({BVar "R0_wp_159" (BType_Imm Bit64)} UNION {BVar "R0_wp_1" (BType_Imm Bit64)}))``;
*)

(*
val acc = [];
val thm2 = Define `settocheck = ^settocheck`;
val useEval = false;

val acc = varexps_thms;
val def_thm = prem_def;
val useEval = false;
*)
  val helper_thm = prove (``!x s t. t UNION (x INSERT s) = if x IN t then t UNION s else (x INSERT t) UNION s``, METIS_TAC [pred_setTheory.INSERT_UNION, pred_setTheory.UNION_COMM, pred_setTheory.INSERT_UNION_EQ]);

  fun preproc_vars_thm useEval acc def_thm =
    let
      val thm1 = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss) ([def_thm, GSYM bir_exp_subst1_def, bir_vars_of_exp_def, bir_exp_subst1_USED_VARS]@acc) ``bir_vars_of_exp ^((fst o dest_eq o concl) def_thm)``;

      val thm2 = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) ([bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_vars_of_exp_def, bir_exp_subst1_USED_VARS, pred_setTheory.IN_INSERT]@acc) ((snd o dest_eq o concl) thm1)
        handle UNCHANGED => REFL ((snd o dest_eq o concl) thm1);

      val conv3 = if (useEval) then (
                    EVAL
                  ) else (
                    (RAND_CONV (REWRITE_CONV [pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY])) THENC

                    REPEATC (
                      (fn x => REWRITE_CONV [Once helper_thm] x) THENC
                      ((RATOR_CONV o LAND_CONV) ((REWRITE_CONV [pred_setTheory.IN_INSERT]) THENC
                                                 (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss) [pred_setTheory.NOT_IN_EMPTY])))
                    ) THENC

                    REWRITE_CONV [pred_setTheory.UNION_EMPTY]
                  )
      val thm3 = conv3 ((snd o dest_eq o concl) thm2)
        handle UNCHANGED => REFL ((snd o dest_eq o concl) thm2);

      val thm4 = TRANS (TRANS thm1 thm2) thm3;
    in
      thm4
    end;

(* val acc = []; *)
  fun preproc_vars acc [] = acc
    | preproc_vars acc (lbl_str::lbl_list) =
        let
          val _ = print ((Int.toString (length acc)) ^ "        \r");
          val def_thm = lookup_def ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str);
(*
          val vars_def_var_id = "bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str ^ "_vars";
          val vars_def_var = mk_var (vars_def_var_id, ``:bir_var_t -> bool``);
          val vars_def_thm = Define `^vars_def_var = bir_vars_of_exp ^((fst o dest_eq o concl) def_thm)`;
*)
          val thm = preproc_vars_thm true acc def_thm;
        in
          preproc_vars ((*(GSYM vars_def_thm)::*)thm::acc) lbl_list
        end
      ;




  (*
    what we need generally
  *)
  exception UNCHANGED_bir_wp_simp_step_CONV;
  exception UNEXPECTED_bir_wp_simp_step_CONV of exn;


(*
for debugging:
  val rec_step_CONV = bir_wp_simp_step_CONV useBigstep;

  val rec_step_CONV = bir_wp_simp_step_CONV false;
  val (prem, term) = simp_extract goalterm;

  val varexps_thms = varexps_thms@(!varexps_prems_only);
*)

  val printRuleName = false;
  fun enterRule rulename =
              if (printRuleName) then (
                print ("entr " ^ rulename ^ "\r\n" )
              ) else ();
  fun intrRule rulename =
              if (printRuleName) then (
                print ("intr " ^ rulename ^ "\r\n" )
              ) else ();
  fun exitRule rulename =
              if (printRuleName) then (
                print ("exit " ^ rulename ^ "\r\n" )
              ) else ();

  (*
    rule 1 - conjunction
  *)
  fun bir_wp_simp_step_CONV_match_1_conj term = is_bir_exp_and term;

  fun bir_wp_simp_step_CONV_conv_1_conj recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "1 and";
      val _ = enterRule rulename;

      val (e1, e2) = dest_bir_exp_and term;

      val thm_1 = SPECL [prem, e1, e2] bir_wp_simp_taut_and_thm;(*bir_wp_simp_eval_and_thm;*)

      val thm_2_lhs = get_concl_rhs thm_1;
      val (term_2a, term_2bc) = (dest_conj) thm_2_lhs; (* val goalterm = term_2a; *)
      val (term_2b, term_2c) = (dest_conj) term_2bc; (* val goalterm = term_2b; *)

 (* poor and quick solution with the REFL theorem *)
      val (thm_2a_chgd, thm_2a) = (true, rec_step_CONV varexps_thms term_2a) handle UNCHANGED => (false, REFL term_2a);
      val (thm_2b_chgd, thm_2b) = (true, rec_step_CONV varexps_thms term_2b) handle UNCHANGED => (false, REFL term_2b);

      val _ = if (false, false) = (thm_2a_chgd, thm_2b_chgd) then (
                intrRule rulename;
                raise UNCHANGED_bir_wp_simp_step_CONV
              ) else ();

      val e1_new = (snd o simp_extract o get_concl_rhs) thm_2a;
      val e2_new = (snd o simp_extract o get_concl_rhs) thm_2b;

(*
(* conversion for welltyped-check *)
      val simp_conv_for_bir_var_set_is_well_typed0 = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) ([bir_vars_of_exp_def, bir_exp_subst1_USED_VARS, bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_varsubst_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE, bir_exp_varsubst1_def]@varexps_thms);
      val simp_conv_for_bir_var_set_is_well_typed1 = SIMP_CONV (std_ss++stringSimps.STRING_ss++string_ss++char_ss) []; (* TODO: this has to be touched again, new expressions may contain varsubst *)
      val simp_conv_for_bir_var_set_is_well_typed2 = computeLib.RESTR_EVAL_CONV [``bir_var_set_is_well_typed``];
      val simp_conv_for_bir_var_set_is_well_typed3 = SIMP_CONV pure_ss [GSYM listTheory.LIST_TO_SET, bir_var_set_is_well_typed_REWRS];
(*      val simp_conv_for_bir_var_set_is_well_typed4 = SIMP_CONV list_ss [bir_var_name_def, bir_var_type_def];*)

      val simp_conv_for_bir_var_set_is_well_typed =
                     simp_conv_for_bir_var_set_is_well_typed0 THENC
                     simp_conv_for_bir_var_set_is_well_typed2 THENC
                     simp_conv_for_bir_var_set_is_well_typed3 THENC
                     EVAL;
      val thm_2c1 = simp_conv_for_bir_var_set_is_well_typed term_2c;


      val simp_conv_for_bir_var_set_is_well_typed =
                     simp_conv_for_bir_var_set_is_well_typed0 THENC
                     simp_conv_for_bir_var_set_is_well_typed1 THENC
                     simp_conv_for_bir_var_set_is_well_typed2 THENC
                     simp_conv_for_bir_var_set_is_well_typed3 THENC
                     EVAL;

      (*val timer_start = Lib.start_time ();*)
      val thm_2c1 = simp_conv_for_bir_var_set_is_well_typed term_2c;
      val term_2c2 = ``bir_var_set_is_well_typed ((bir_vars_of_exp ^prem) UNION (bir_vars_of_exp ^e1_new) UNION (bir_vars_of_exp ^e2_new))``;
      val thm_2c2 = simp_conv_for_bir_var_set_is_well_typed term_2c2;
      val thm_2c = TRANS thm_2c1 (GSYM thm_2c2);
      (*val _ = Lib.end_time timer_start;*)
*)
      val thm_2c = prove(mk_eq (term_2c, ``bir_var_set_is_well_typed ((bir_vars_of_exp ^prem) UNION (bir_vars_of_exp ^e1_new) UNION (bir_vars_of_exp ^e2_new))``), cheat);

      val thm_2 = REWRITE_CONV [Once thm_2a, Once thm_2b, Once thm_2c] thm_2_lhs handle UNCHANGED => (
          intrRule rulename;
          raise UNCHANGED_bir_wp_simp_step_CONV
        );
(*
val dbg_def_1 = Define `debug_def_wpsimp_1 = ^prem`;
val dbg_def_2 = Define `debug_def_wpsimp_2 = ^e1_new`;
val dbg_def_3 = Define `debug_def_wpsimp_3 = ^e2_new`;
val thm_2_dbg = REWRITE_CONV [GSYM dbg_def_1, GSYM dbg_def_2, GSYM dbg_def_3] (get_concl_rhs thm_2);
*)

      val thm_3 = REWRITE_CONV [GSYM bir_wp_simp_taut_and_thm] (get_concl_rhs thm_2);
      val thm = TRANS (TRANS thm_1 thm_2) thm_3;
      val _ = exitRule rulename;
    in
      thm
    end;







  (*
    rule 2 - implication
  *)
  fun bir_wp_simp_step_CONV_match_2_impl term = is_bir_exp_imp term;

  val prem_id_ctr = ref 0;
  val prem_id_prefix = "bir_wp_simp_step_prem_";
  val varexps_prems_only = ref ([]:thm list);
  fun bir_wp_simp_step_CONV_conv_2_impl recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "2 impl";
      val _ = enterRule rulename;

      val (e1, e2) = dest_bir_exp_imp term;
      val thm_gen = (Q.GENL [`prem`, `e1`, `e2`]) (MATCH_MP bir_exp_tautologiesTheory.bir_exp_is_taut_WEAK_CONG_IFF (Q.SPECL [`prem`, `e1`, `e2`, `fixme`] bir_exp_CONG_imp_imp_thm));
      val thm_1 = SPECL [prem, e1, e2] thm_gen;

      val prem_id_idx = !prem_id_ctr;
      val _ = prem_id_ctr := (!prem_id_ctr) + 1;
      val prem_id = prem_id_prefix ^ (Int.toString prem_id_idx);
      val prem_id_var = mk_var (prem_id, ``:bir_exp_t``);
      val prem_def = Define `^prem_id_var = bir_exp_and ^prem ^e1`;
      val prem_id_const = mk_const (prem_id, ``:bir_exp_t``);

      val vars_thm = preproc_vars_thm false varexps_thms prem_def;
      val varexps_thms = vars_thm::varexps_thms;
      val _ = varexps_prems_only := (vars_thm::(!varexps_prems_only));

      val thm_2 = REWRITE_CONV [GSYM prem_def] (get_concl_rhs thm_1);
      val thm_3 = TRANS thm_1 thm_2;

      val _ = if (false andalso (prem_id_idx = 8)) then (
                print "\r\n-------------------------- debug printout -------------------------\r\n";
                print_term goalterm;
                print "\r\n-------------------------------------------------------------------\r\n"
              ) else ();

      val goalterm_new = get_concl_rhs thm_3; (* val goalterm = goalterm_new; *)
      val thm_3_rec = rec_step_CONV varexps_thms goalterm_new handle UNCHANGED => (
          intrRule rulename;
          raise UNCHANGED_bir_wp_simp_step_CONV (*REFL goalterm_new;*)
        );

      val thm_4_struct_rev = TRANS thm_3_rec (((REWRITE_CONV [prem_def, ((SPECL [prem, e1]) o GSYM) thm_gen]) o get_concl_rhs) thm_3_rec);
      val _ = exitRule rulename;
    in
      TRANS thm_3 thm_4_struct_rev
    end;





  (* 3-5 - (varsubst vs (not a subst1)) - expand a const, propagate varsubst *)
  (*
    rule 3 - varsubst const
  *)
  fun bir_wp_simp_step_CONV_match_3_vsconst term =
    (is_bir_exp_varsubst term) andalso
      let
        val (term_vs, term_e) = dest_bir_exp_varsubst term;
      in
        is_const term_e
      end;

  fun bir_wp_simp_step_CONV_conv_3_vsconst recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "3 vsconst";
      val _ = enterRule rulename;

      val (term_vs, term_e) = dest_bir_exp_varsubst term;
      val const_n = (fst o dest_const) term_e;
      val _ = print ("\r\n" ^ const_n ^ "\r\n");

(* bir_wp_comp_wps_iter_step2_wp_0x4008C0w *)
      val _ = if (false andalso (const_n = "bir_wp_comp_wps_iter_step2_wp_0x400970w")) then (
                print "\r\n-------------------------- debug printout -------------------------\r\n";
                print_term goalterm;
                print "\r\n-------------------------------------------------------------------\r\n"
              ) else ();

      val _ = if (false andalso (const_n = "bir_wp_comp_wps_iter_step2_wp_0x400860w")) then (
                print "\r\n-------------------------- debug printout -------------------------\r\n";
                print_term goalterm;
                print "\r\n-------------------------------------------------------------------\r\n";
                raise UNCHANGED
              ) else ();

      val def_thm = lookup_def const_n;
      val thm_1 = REWRITE_CONV [def_thm] goalterm;
      val thm_in = thm_1; (* val goalterm = get_concl_rhs thm_in; *)
      val _ = exitRule rulename;
    in
      recStepFun thm_in
    end;



  (*
    rule 4 - varsubst (not subst1)
  *)
  fun bir_wp_simp_step_CONV_match_4_vsns1 term =
    (is_bir_exp_varsubst term) andalso
      let
        val (term_vs, term_e) = dest_bir_exp_varsubst term;
      in
        not (is_bir_exp_subst1 term_e)
      end;

  fun bir_wp_simp_step_CONV_conv_4_vsns1 recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "4 vsns1";
      val _ = enterRule rulename;

      val (term_vs, term_e) = dest_bir_exp_varsubst term;
      val varsubst_propagate_conv = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss) [bir_exp_varsubst_REWRS, bir_exp_varsubst_REWRS_ALT, bir_exp_varsubst_and_imp_REWRS, bir_exp_varsubst_var_REWR, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY];
      val thm_1a = varsubst_propagate_conv term;
      val thm_1 = REWRITE_CONV [thm_1a] goalterm;
      val thm_in = thm_1; (* val goalterm = get_concl_rhs thm_in; *)
      val _ = exitRule rulename;
    in
      recStepFun thm_in
    end;




  (*
    rule 5 - varsubst (subst1)
  *)
  fun bir_wp_simp_step_CONV_match_5_vss1 term =
    (is_bir_exp_varsubst term) andalso
      let
        val (term_vs, term_e) = dest_bir_exp_varsubst term;
      in
        is_bir_exp_subst1 term_e
      end;

  fun bir_wp_simp_step_CONV_conv_5_vss1 recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "5 vss1";
      val _ = enterRule rulename;

      val (term_vs, term_e) = dest_bir_exp_varsubst term;
      val (term_v, term_ve, term_e2) = dest_bir_exp_subst1 term_e;
      val thm_1 = SPECL [term_vs, term_v, term_ve, term_e2] bir_exp_varsubst_subst1_swap_thm;
      val assum = (fst o dest_imp o concl) thm_1;
      val feveryvarneq_conv = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss) [finite_mapTheory.FEVERY_FEMPTY, finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY]; (* TODO: this has to be touched again *)
      val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (feveryvarneq_conv assum);
      val thm_2 = MP thm_1 assum_thm;
      val restrict1_conv = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss) [bir_exp_subst_restrict1_REWRS, bir_exp_varsubst_REWRS, bir_exp_varsubst_REWRS_ALT, bir_exp_varsubst_var_REWR, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY, LET_DEF];
      val thm_2 = TRANS thm_2 ((restrict1_conv o get_concl_rhs) thm_2); (* TODO: this as well, add holbasimps *)
      val thm_3 = REWRITE_CONV [thm_2] goalterm;
      val thm_in = thm_3; (* val goalterm = get_concl_rhs thm_in; *)
      val _ = exitRule rulename;
    in
      recStepFun thm_in
    end;




  (*
    rule 6-8 - subst1
  *)
  fun bir_wp_simp_step_CONV_match_6_7_8_s1 term = is_bir_exp_subst1 term;

  val wp_var_idx = ref 0;
  fun bir_wp_simp_step_CONV_conv_6_7_8_s1 recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "6_7_8 s1";
      val _ = enterRule rulename;

      val (term_v, term_ve, term_e) = dest_bir_exp_subst1 term;
      val term_v_is_Imm_thm = REWRITE_CONV [bir_var_type_def, bir_type_checker_REWRS] ``bir_type_is_Imm (bir_var_type ^term_v)``;
      val term_v_is_Imm_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] term_v_is_Imm_thm;
      val term_v_is_Mem_thm = REWRITE_CONV [bir_var_type_def, bir_type_checker_REWRS] ``bir_type_is_Mem (bir_var_type ^term_v)``;
      val term_v_is_Mem_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] term_v_is_Mem_thm;

      val varused_thm = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss) ([bir_exp_varsubst_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE]@varexps_thms) ``^term_v IN (bir_vars_of_exp ^term_e)``; (* TODO: has to be touched again *)
      val varused_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] varused_thm;
    in
      if ((is_neg o concl) varused_thm) then
        (* raise ERR "bir_wp_simp_CONV" "rule 6 missing" *)
        let
          val thm_1 = SPECL [term_v, term_ve, term_e] bir_exp_subst1_UNUSED_VAR;
          val thm_2 = MP thm_1 varused_thm;
          val thm_3 = REWRITE_CONV [thm_2] goalterm;
          val thm_in = thm_3; (* val goalterm = get_concl_rhs thm_in; *)
          val _ = exitRule rulename;
        in
          recStepFun thm_in
        end
      else
        let
          val thm_gen =
            if ((not o is_neg o concl) term_v_is_Imm_thm) then
              (* raise ERR "bir_wp_simp_CONV" "rule 7 missing" *)
              MATCH_MP bir_exp_is_taut_imp_imp_subst1_thm term_v_is_Imm_thm
            else if ((not o is_neg o concl) term_v_is_Mem_thm) then
              (* raise ERR "bir_wp_simp_CONV" "rule 8 missing" *)
              MATCH_MP bir_exp_is_taut_imp_imp_subst1_mem_thm term_v_is_Mem_thm
            else
              raise ERR "bir_wp_simp_CONV" "unknown variable type";

          val wp_var_idx_num = !wp_var_idx;
          val _ = wp_var_idx := ((!wp_var_idx) + 1);
          val wp_var_suffix = "_wp_" ^ (Int.toString wp_var_idx_num);
          val (term_v_str, term_v_type) = dest_BVar_string term_v;
          val term_v2 = mk_BVar_string (term_v_str ^ wp_var_suffix, term_v_type);

          val thm_1 = SPECL [term_v2, prem, term_ve, term_e] thm_gen;

          val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``bir_var_type ^term_v2 = bir_var_type ^term_v``);
          val thm_1 = MP thm_1 assum_thm;

          val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (prove (``type_of_bir_exp ^term_ve = SOME ^(((get_concl_rhs o EVAL) ``bir_var_type ^term_v``))``, cheat));(* (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++bir_type_option_pair_ss) [type_of_bir_exp_def, bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def] ``type_of_bir_exp ^term_ve``);*)
          val assum_thm = TRANS assum_thm (GSYM (REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``SOME (bir_var_type ^term_v)``)));
          val thm_1 = MP thm_1 assum_thm;
          val thm_1 = MP thm_1 varused_thm;


          fun varnameset_discharge thm_1 varname term_exp term_v2 =
            let
              val varnameset_conv = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++string_ss) ([bir_vars_of_exp_def, bir_exp_subst1_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, bir_var_name_def, bir_exp_varsubst_USED_VARS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE, bir_exp_and_def]@varexps_thms);

              val varnameset_exp_thm = varnameset_conv ``IMAGE bir_var_name (bir_vars_of_exp ^term_exp)`` handle UNCHANGED => raise ERR "bir_wp_simp_CONV" ("varnameset "^varname^" not resolvable");
              val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``(bir_var_name ^term_v2) IN (^(get_concl_rhs varnameset_exp_thm))``); (* TODO: add neg conclusion check for debug error messages *)
              val thm_1 = MP (REWRITE_RULE [varnameset_exp_thm] thm_1) assum_thm;
            in
              thm_1
            end;

          fun varnameset_discharge_cheat thm_1 varname term_exp term_v2 =
            MP thm_1 (prove (``~ ((bir_var_name ^term_v2) IN (IMAGE bir_var_name (bir_vars_of_exp ^term_exp)))``, cheat));

          val thm_1 = varnameset_discharge_cheat thm_1 "prem"    prem    term_v2;
          val thm_1 = varnameset_discharge_cheat thm_1 "term_ve" term_ve term_v2;
          val thm_1 = varnameset_discharge_cheat thm_1 "term_e"  term_e  term_v2;

          val thm_2 = REWRITE_CONV [thm_1] goalterm;
          val thm_in = thm_2; (* val goalterm = get_concl_rhs thm_in; *)
          val _ = exitRule rulename;
        in
          recStepFun thm_in
        end
    end;





  (*
    rule 9 - varsubst1 (not varsubst)
  *)
  fun bir_wp_simp_step_CONV_match_9_vs1nvs term =
    (is_bir_exp_varsubst1 term) andalso
      let
        val (term_v, term_v2, term_e) = dest_bir_exp_varsubst1 term;
      in
        not (is_bir_exp_varsubst term_e)
      end;

  fun bir_wp_simp_step_CONV_conv_9_vs1nvs recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    raise (ERR "bir_wp_simp_step_CONV_conv_9_vs1nvs" "not implemented");




  (*
    rule 10 - varsubst1 (varsubst)
  *)
  fun bir_wp_simp_step_CONV_match_10_vs1vs term =
    (is_bir_exp_varsubst1 term) andalso
      let
        val (term_v, term_v2, term_e) = dest_bir_exp_varsubst1 term;
      in
        is_bir_exp_varsubst term_e
      end;

  fun bir_wp_simp_step_CONV_conv_10_vs1vs recStepFun rec_step_CONV prem term varexps_thms (goalterm:term) =
    let
      val rulename = "10 vs1vs";
      val _ = enterRule rulename;

      val (term_v, term_v2, term_e) = dest_bir_exp_varsubst1 term;
      val (term_vs, term_e) = dest_bir_exp_varsubst term_e;
      val thm_1 = SPECL [term_v, term_v2, term_vs, term_e] bir_exp_varsubst1_varsubst_merge_thm;
      val thm_1 = TRANS thm_1 (((SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss) [LET_DEF, bir_exp_subst_update_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE]) o get_concl_rhs) thm_1);

      val thm_2 = REWRITE_CONV [thm_1] goalterm;
      val thm_in = thm_2; (* val goalterm = get_concl_rhs thm_in; *)
      val _ = exitRule rulename;
    in
      recStepFun thm_in
    end;






  (*
    rule list
  *)
  val bir_wp_simp_step_CONV_list =
          [(bir_wp_simp_step_CONV_match_1_conj, bir_wp_simp_step_CONV_conv_1_conj),
           (bir_wp_simp_step_CONV_match_2_impl, bir_wp_simp_step_CONV_conv_2_impl),
           (bir_wp_simp_step_CONV_match_3_vsconst, bir_wp_simp_step_CONV_conv_3_vsconst),
           (bir_wp_simp_step_CONV_match_4_vsns1, bir_wp_simp_step_CONV_conv_4_vsns1),
           (bir_wp_simp_step_CONV_match_5_vss1, bir_wp_simp_step_CONV_conv_5_vss1),
           (bir_wp_simp_step_CONV_match_6_7_8_s1, bir_wp_simp_step_CONV_conv_6_7_8_s1),
           (bir_wp_simp_step_CONV_match_9_vs1nvs, bir_wp_simp_step_CONV_conv_9_vs1nvs),
           (bir_wp_simp_step_CONV_match_10_vs1vs, bir_wp_simp_step_CONV_conv_10_vs1vs)];

  (*
    step relation
  *)
  val cannotHandleOutput = false;
  fun bir_wp_simp_step_CONV useBigstep varexps_thms goalterm =
    let
      val rec_step_CONV = bir_wp_simp_step_CONV useBigstep;
      fun recStepFun thm_in = if useBigstep then
                         (TRANS thm_in (rec_step_CONV varexps_thms (get_concl_rhs thm_in)) handle UNCHANGED => thm_in)
                       else
                         (thm_in);

      val thm =
        let
          val (prem, term) = simp_extract goalterm;
          val conv_fun_opt = List.find (fn (matchfun, _) => matchfun term) bir_wp_simp_step_CONV_list;
        in
          case conv_fun_opt of
             NONE => (
                if cannotHandleOutput then (
                  print "--------------- cannot handle -----------------\r\n";
                  print_term goalterm;
                  print "\r\n-----------------------------------------------\r\n"
                ) else ();
                  raise UNCHANGED
             )
           | SOME(_, conv_fun) => (
                conv_fun recStepFun rec_step_CONV prem term varexps_thms goalterm
                handle
                   UNCHANGED_bir_wp_simp_step_CONV => raise UNCHANGED
                 | UNEXPECTED_bir_wp_simp_step_CONV ex => raise (UNEXPECTED_bir_wp_simp_step_CONV ex)
                 | Interrupt => raise Interrupt
                 | ex => (
                           print "--------------- unexpected -----------------\r\n";
                           print_term goalterm;
                           print "\r\n--------------------------------------------\r\n";
                           print (exn_to_string ex) handle _ => ();
                           raise (UNEXPECTED_bir_wp_simp_step_CONV ex)
                         )
             )
        end;
    in
      let
        (* check goalterm matching lhs *)
        val goaltermIsOnLhs = (goalterm = (get_concl_lhs thm));
        (* check structure expectation *)
        val (premL, _) = ((simp_extract) goalterm);
        val (premR, _) = ((simp_extract o get_concl_rhs) thm);
        val structPreserv = (premL = premR);
      in
        if not (goaltermIsOnLhs andalso structPreserv) then
          raise (ERR "bir_wp_simp_step_CONV" "term mismatch, some unexpected error, debug me")
        else
          thm
      end
    end;


  (*
    step-wise conversion
  *)
  val useBigstep = true;
  val printSteps = false;
  fun bir_wp_simp_CONV varexps_thms goalterm =
    let
      val bir_wp_simp_step_CONV_s = bir_wp_simp_step_CONV useBigstep varexps_thms;
      val thm1 = (REFL goalterm);
      fun bir_wp_simp_CONV_rec thm1 =
        let
          val goalterm = get_concl_rhs thm1;
          val _ = if (printSteps) then (
                    print "----------------- step ------------------\r\n";
                    print_term goalterm;
                    print "\r\n-----------------------------------------\r\n"
                  ) else ()
          val thm2 = bir_wp_simp_step_CONV_s goalterm;
          val thm = TRANS thm1 thm2;
        in
          if useBigstep then (
            thm
          ) else (
            bir_wp_simp_CONV_rec thm
            handle UNCHANGED => thm
          )
        end
    in
      bir_wp_simp_CONV_rec thm1
    end;








(*
(* =================== TESTING ========================================= *)
val varexps_thms = preproc_vars [] (tl (rev lbl_list));


val i = 230; (*60 - 230;*)
val lbl_str = List.nth (lbl_list, (List.length lbl_list) - 2 - i);

val def_thm = lookup_def ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str);
val term = (snd o dest_eq o concl) def_thm;


(* include this in the beginning as expansion step from definition, i.e., replace ^term in goalterm by aes_wps variable and propagate definition theorems accordingly *)
val aes_wp_def = Define `aes_wp = ^term`;
val aes_wp_term = ``aes_wp``;
(*
val aes_wp_term = ``(bir_exp_subst
               (FEMPTY |+
                (BVar "R0" (BType_Imm Bit64),
                 BExp_Cast BIExp_UnsignedCast
                   (BExp_Load
                      (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 76w))) BEnd_LittleEndian
                      Bit32) Bit64))
               bir_wp_comp_wps_iter_step2_wp_0x400978w)``;
*)

val btautology = ``BExp_Const (Imm1 1w)``;
val prem_init = ``^btautology``;
(*
val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (^aes_wp_term))``;
val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (bir_exp_imp ^btautology ^aes_wp_term))``;
val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (bir_exp_imp ^btautology (bir_exp_varsubst FEMPTY ^aes_wp_term)))``;
val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (bir_exp_imp (bir_exp_and ^btautology ^btautology) (bir_exp_varsubst FEMPTY ^aes_wp_term)))``;
*)
val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (bir_exp_varsubst FEMPTY ^aes_wp_term))``;
(*
fun expandDef defname goalterm =
  let
    val def_thm = lookup_def defname;
  in
    (snd o dest_eq o concl) (REWRITE_CONV [def_thm] goalterm)
  end;

val goalterm = expandDef "aes_wp" goalterm;
*)
(*
val goalterm = (snd o dest_eq o concl o (REWRITE_CONV [aes_wp_def])) goalterm;
*)

(*
val bir_wp_simp_eval_imp_spec_thm = ((SIMP_RULE std_ss [EVAL ``^prem_init s``]) o (SPEC prem_init) o GSYM) bir_wp_simp_eval_imp_thm;
*)


(*
val lbl_str = hd (tl (rev lbl_list));




      val simp_conv_for_bir_var_set_is_well_typed1 = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++string_ss) ([bir_vars_of_exp_def, bir_exp_subst1_USED_VARS, bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_varsubst_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE, bir_exp_varsubst1_def]@varexps_thms); (* TODO: this has to be touched again, new expressions may contain varsubst *)





List.take ([1,2,3,4,5,6], 2)
List.drop ([1,2,3,4,5,6], 2)

val lbls = (tl (rev lbl_list));
val acc = [];

val acc = preproc_vars acc (List.take (lbls, 56));
val lbls = List.drop (lbls, 56);


val lbl_str = hd lbls;
val lbls = tl lbls;
val acc = preproc_vars acc [lbl_str];




*)


(*
val _ = prem_id_ctr := 100;
*)


val timer_start = Lib.start_time ();
val simp_thm = bir_wp_simp_CONV varexps_thms goalterm;
val _ = Lib.end_time timer_start;


val varexps_thms = varexps_thms@(!varexps_prems_only);
val bir_wp_simp_step_CONV_s = bir_wp_simp_step_CONV false varexps_thms;
fun step_fun goalterm = (
    let
      val simp_thm = bir_wp_simp_step_CONV_s goalterm;
      val goalterm = get_concl_rhs simp_thm;
    in
      (*
      print "----------------- step ------------------\r\n";
      print_term goalterm;
      print "\r\n-----------------------------------------\r\n";
      *)
      goalterm
    end
  );

val goalterm_last = goalterm;
val goalterm = step_fun goalterm;


(*
val goalterm = goalterm_last;
*)






val vars_of_simp_thm = (snd o dest_eq o concl o EVAL) ``bir_vars_of_exp ^((snd o dest_comb o snd o dest_eq o concl) simp_thm)``;

(*
val simp_thm = TRANS (GSYM (REWRITE_CONV [EVAL ``^prem_init s``] ((fst o dest_eq o concl) simp_thm))) simp_thm;
val simp_thm = TRANS simp_thm (SIMP_CONV std_ss [boolTheory.BETA_THM, bir_wp_simp_eval_imp_spec_thm] ((snd o dest_eq o concl) simp_thm));
*)

*)



(*

val goalterm = ``
bir_exp_is_taut
   (bir_exp_imp (BExp_Const (Imm1 1w))
      (bir_exp_imp
         (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "R0_wp_11" (BType_Imm Bit64)))
            (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
               (BExp_Const (Imm64 3608w))))
         (bir_exp_imp
            (BExp_BinPred BIExp_Equal
               (BExp_Den (BVar "R0_wp_12" (BType_Imm Bit64)))
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "R0_wp_11" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R1" (BType_Imm Bit64)))))
            (bir_exp_varsubst
               (FEMPTY |+
                (BVar "R0" (BType_Imm Bit64),
                 BVar "R0_wp_12" (BType_Imm Bit64)))
               bir_wp_comp_wps_iter_step2_wp_0x4008BCw))))
``;

*)



(*
length (!goalterms_failing);
val goalterm = List.nth (((!goalterms_failing)), 5);

val goalterm = List.nth (((!goalterms_failing)), 2);
val goalterm = List.nth ((rev (!goalterms_failing)), 0);
val _ = goalterms_failing := [];

val goalterm = (snd o dest_eq o concl) simp_thm;
*)


end

