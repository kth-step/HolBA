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

(* val acc = []; *)
  fun preproc_vars acc [] = acc
    | preproc_vars acc (lbl_str::lbl_list) =
        let
          val def_thm = lookup_def ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str);
(*
          val vars_def_var_id = "bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str ^ "_vars";
          val vars_def_var = mk_var (vars_def_var_id, ``:bir_var_t -> bool``);
          val vars_def_thm = Define `^vars_def_var = bir_vars_of_exp ^((fst o dest_eq o concl) def_thm)`;
*)
          val thm = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss) ([def_thm, GSYM bir_exp_subst1_def, bir_vars_of_exp_def, bir_exp_subst1_USED_VARS]@acc) ``bir_vars_of_exp ^((fst o dest_eq o concl) def_thm)``;
          val thm = TRANS thm (EVAL ((snd o dest_eq o concl) thm));
        in
          preproc_vars ((*(GSYM vars_def_thm)::*)thm::acc) lbl_list
        end
      ;

  val bir_var_ss = rewrites (type_rws ``:bir_var_t``);
  val string_ss = rewrites (type_rws ``:string``);
  val bir_type_option_pair_ss = rewrites (type_rws ``:bir_type_t option # bir_type_t option``);
  val wp_var_idx = ref 0;
  fun bir_wp_simp_CONV varexps_thms goalterm =
    let
      val (prem, term) = simp_extract goalterm;
      val get_concl_lhs = fst o dest_eq o concl;
      val get_concl_rhs = snd o dest_eq o concl;
      val thm =
        if is_bir_exp_and term then
          (* 1 - and simplification propagation *)
          let
            val (e1, e2) = dest_bir_exp_and term;

            val thm_1 = SPECL [prem, e1, e2] bir_wp_simp_taut_and_thm;(*bir_wp_simp_eval_and_thm;*)

            val thm_2_lhs = get_concl_rhs thm_1;
            val (term_2a, term_2bc) = (dest_conj) thm_2_lhs;
            val (term_2b, term_2c) = (dest_conj) term_2bc; (* val goalterm = term_2b; *)

            val thm_2a = bir_wp_simp_CONV varexps_thms term_2a handle UNCHANGED => REFL term_2a; (* poor and quick solution *)
            val thm_2b = bir_wp_simp_CONV varexps_thms term_2b handle UNCHANGED => REFL term_2b;

            val simp_conv_for_bir_var_set_is_well_typed = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++string_ss) ([bir_vars_of_exp_def, bir_exp_subst1_USED_VARS, bir_var_set_is_well_typed_def, bir_exp_and_def, bir_exp_varsubst_USED_VARS_REWRS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE]@varexps_thms); (* TODO: this has to be touched again, new expressions may contain varsubst *)
            val thm_2c1 = simp_conv_for_bir_var_set_is_well_typed term_2c;
            val e1_new = (snd o simp_extract o get_concl_rhs) thm_2a;
            val e2_new = (snd o simp_extract o get_concl_rhs) thm_2b;
            val thm_2c2 = simp_conv_for_bir_var_set_is_well_typed ``bir_var_set_is_well_typed ((bir_vars_of_exp ^prem) UNION (bir_vars_of_exp ^e1_new) UNION (bir_vars_of_exp ^e2_new))``;
            val thm_2c = TRANS thm_2c1 (GSYM thm_2c2);
            val thm_2 = REWRITE_CONV [Once thm_2a, Once thm_2b, Once thm_2c] thm_2_lhs handle UNCHANGED => REFL thm_2_lhs;

            val thm_3 = REWRITE_CONV [GSYM bir_wp_simp_taut_and_thm] (get_concl_rhs thm_2);
            val thm = TRANS (TRANS thm_1 thm_2) thm_3;
          in
            thm
          end	  
        else if is_bir_exp_imp term then
          (* 2 - imp simplification propagation *)
          let
            val (e1, e2) = dest_bir_exp_imp term;
            val thm_gen = (Q.GENL [`prem`, `e1`, `e2`]) (MATCH_MP bir_exp_tautologiesTheory.bir_exp_is_taut_WEAK_CONG_IFF (Q.SPECL [`prem`, `e1`, `e2`, `fixme`] bir_exp_CONG_imp_imp_thm));
            val thm_1 = SPECL [prem, e1, e2] thm_gen;

	    val goalterm_new = get_concl_rhs thm_1;
            val thm_1_rec = bir_wp_simp_CONV varexps_thms goalterm_new handle UNCHANGED => REFL goalterm_new;

            val thm_2_struct_rev = TRANS thm_1_rec ((SIMP_CONV pure_ss [GSYM thm_gen] o get_concl_rhs) thm_1_rec);
          in
            TRANS thm_1 thm_2_struct_rev
          end
        else if is_bir_exp_varsubst term then
          (* 3-5 - (varsubst vs (not a subst1)) - expand a const, propagate varsubst *)
          let
            val (term_vs, term_e) = dest_bir_exp_varsubst term;
          in
            if is_const term_e then
              (* 3 - expand const *)
              let
                val const_n = (fst o dest_const) term_e;
                val _ = print ("\r\n" ^ const_n ^ "\r\n");
                val def_thm = lookup_def const_n;
                val thm_1 = REWRITE_CONV [def_thm] goalterm;
                val goalterm_new = get_concl_rhs thm_1; (* val goalterm = goalterm_new; *)
                val thm_1_rec = bir_wp_simp_CONV varexps_thms goalterm_new handle UNCHANGED => REFL goalterm_new;
              in
                TRANS thm_1 thm_1_rec
              end
            else if not (is_bir_exp_subst1 term_e) then
              (* 4 - propagate varsubst further *)
              (*raise ERR "bir_wp_simp_CONV" "rule 4 missing"*)
              let
                val thm_1a = SIMP_CONV std_ss [bir_exp_varsubst_REWRS, bir_exp_varsubst_and_imp_REWRS, bir_exp_varsubst_var_REWR, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] term;
                val thm_1 = REWRITE_CONV [thm_1a] goalterm;
                val goalterm_new = get_concl_rhs thm_1; (* val goalterm = goalterm_new; *)
                val thm_1_rec = bir_wp_simp_CONV varexps_thms goalterm_new handle UNCHANGED => REFL goalterm_new;
              in
                TRANS thm_1 thm_1_rec
              end
            else
              (* 5 - resolve subst1 as implication of equality check and varsubst1 *)
              (* raise ERR "bir_wp_simp_CONV" "rule 5 missing" *)
              let
                val (term_v, term_ve, term_e2) = dest_bir_exp_subst1 term_e;
                val thm_1 = SPECL [term_vs, term_v, term_ve, term_e2] bir_exp_varsubst_subst1_swap_thm;
                val assum = (fst o dest_imp o concl) thm_1;
                val assum_thm = SIMP_CONV std_ss [finite_mapTheory.FEVERY_FEMPTY, finite_mapTheory.FEVERY_FUPDATE] assum; (* TODO: this has to be touched again *)
                val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] assum_thm;
                val thm_2 = MP thm_1 assum_thm;
                val thm_2 = TRANS thm_2 (((SIMP_CONV std_ss [bir_exp_subst_restrict1_REWRS, bir_exp_varsubst_REWRS, bir_exp_varsubst_var_REWR, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY]) o get_concl_rhs) thm_2); (* TODO: this as well, add holbasimps *)
                val thm_3 = REWRITE_CONV [thm_2] goalterm;
                val goalterm_new = get_concl_rhs thm_3; (* val goalterm = goalterm_new; *)
                val thm_3_rec = bir_wp_simp_CONV varexps_thms goalterm_new handle UNCHANGED => REFL goalterm_new;
              in
                TRANS thm_3 thm_3_rec
              end
          end
        else if is_bir_exp_subst1 term then
          (* 6-8 - subst1 where var is not present, where var is an imm, and where var is a mem *)
          (* raise ERR "bir_wp_simp_CONV" "rule 6-8 missing" *)
          let
            val (term_v, term_ve, term_e) = dest_bir_exp_subst1 term;
            val term_v_is_Imm_thm = REWRITE_CONV [bir_var_type_def, bir_type_checker_REWRS] ``bir_type_is_Imm (bir_var_type ^term_v)``;
            val term_v_is_Imm_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] term_v_is_Imm_thm;
            val term_v_is_Mem_thm = REWRITE_CONV [bir_var_type_def, bir_type_checker_REWRS] ``bir_type_is_Mem (bir_var_type ^term_v)``;
            val term_v_is_Mem_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] term_v_is_Mem_thm;

            val varused_thm = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++string_ss) ([bir_exp_varsubst_USED_VARS_REWRS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE]@varexps_thms) ``^term_v IN (bir_vars_of_exp ^term_e)``; (* TODO: has to be touched again *)
            val varused_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] varused_thm;
          in
            if ((is_neg o concl) varused_thm) then
              (* raise ERR "bir_wp_simp_CONV" "rule 6 missing" *)
              let
                val thm_1 = SPECL [term_v, term_ve, term_e] bir_exp_subst1_UNUSED_VAR;
                val thm_2 = MP thm_1 varused_thm;
                val thm_3 = REWRITE_CONV [thm_2] goalterm;
                val goalterm_new = get_concl_rhs thm_3; (* val goalterm = goalterm_new; *)
                val thm_3_rec = bir_wp_simp_CONV varexps_thms goalterm_new handle UNCHANGED => REFL goalterm_new;
              in
                TRANS thm_3 thm_3_rec
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

                val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++bir_type_option_pair_ss) [type_of_bir_exp_def] ``type_of_bir_exp ^term_ve``);
                val assum_thm = TRANS assum_thm (GSYM (REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``SOME (bir_var_type ^term_v)``)));
                val thm_1 = MP thm_1 assum_thm;
                val thm_1 = MP thm_1 varused_thm;

                val varnameset_conv = SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++string_ss) ([bir_vars_of_exp_def, bir_exp_subst1_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, bir_var_name_def, bir_exp_varsubst_USED_VARS_REWRS, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FDOM_FUPDATE]@varexps_thms);
                val varnameset_exp_thm = varnameset_conv ``IMAGE bir_var_name (bir_vars_of_exp ^prem)``;
                val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``(bir_var_name ^term_v2) IN (^(get_concl_rhs varnameset_exp_thm))``); (* TODO: add neg conclusion check for debug error messages *)
                val thm_1 = MP (REWRITE_RULE [varnameset_exp_thm] thm_1) assum_thm;
                val varnameset_exp_thm = varnameset_conv ``IMAGE bir_var_name (bir_vars_of_exp ^term_ve)``;
                val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``(bir_var_name ^term_v2) IN (^(get_concl_rhs varnameset_exp_thm))``); (* TODO: add neg conclusion check for debug error messages *)
                val thm_1 = MP (REWRITE_RULE [varnameset_exp_thm] thm_1) assum_thm;
                val varnameset_exp_thm = varnameset_conv ``IMAGE bir_var_name (bir_vars_of_exp ^term_e)``;
                val assum_thm = REWRITE_RULE [boolTheory.EQ_CLAUSES] (EVAL ``(bir_var_name ^term_v2) IN (^(get_concl_rhs varnameset_exp_thm))``); (* TODO: add neg conclusion check for debug error messages *)
                val thm_1 = MP (REWRITE_RULE [varnameset_exp_thm] thm_1) assum_thm;

                val thm_2 = REWRITE_CONV [thm_1] goalterm;
                val goalterm_new = get_concl_rhs thm_2; (* val goalterm = goalterm_new; *)
                val thm_2_rec = bir_wp_simp_CONV varexps_thms goalterm_new handle UNCHANGED => REFL goalterm_new;
              in
                TRANS thm_2 thm_2_rec
              end
          end
        else if is_bir_exp_varsubst1 term then
          (* 9-10 - (varsubst1 v v2 e) - propagate varsubst1, merge with varsubst *)
          (* raise ERR "bir_wp_simp_CONV" "rule 9-10 missing" *)
          let
            val (term_v, term_v2, term_e) = dest_bir_exp_varsubst1 term;
          in
            if not (is_bir_exp_varsubst term_e) then
              (* 9 - propagate varsubst1 *)
              raise ERR "bir_wp_simp_CONV" "rule 9 missing"
(*
              let
              in
                TRANS thm_1 thm_1_rec
              end
*)
            else
              (* 10 - merge with varsubst *)
              raise ERR "bir_wp_simp_CONV" "rule 10 missing"
(*
bir_exp_varsubst1_varsubst_merge_thm
*)
          end
        else
          (* other expression, we don't touch this *)
          raise UNCHANGED
        ;
    in
      (* check goalterm matching lhs *)
      if (goalterm = (get_concl_lhs thm)) then
        thm
      else
        raise (ERR "bir_wp_simp_CONV" "term mismatch, some unexpected error, debug me")
    end;











(*
(* =================== TESTING ========================================= *)
val i = 49;
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
val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (bir_exp_imp ^btautology ^aes_wp_term))``;
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
val bir_wp_simp_eval_imp_spec_thm = ((SIMP_RULE std_ss [EVAL ``^prem_init s``]) o (SPEC prem_init) o GSYM) bir_wp_simp_eval_imp_thm;
*)


(*
val lbl_str = hd (tl (rev lbl_list));
*)
val varexps_thms = preproc_vars [] (tl (rev lbl_list));


val simp_thm = bir_wp_simp_CONV varexps_thms goalterm;

val vars_of_simp_thm = (snd o dest_eq o concl o EVAL) ``bir_vars_of_exp ^((snd o dest_comb o snd o dest_eq o concl) simp_thm)``;

(*
val simp_thm = TRANS (GSYM (REWRITE_CONV [EVAL ``^prem_init s``] ((fst o dest_eq o concl) simp_thm))) simp_thm;
val simp_thm = TRANS simp_thm (SIMP_CONV std_ss [boolTheory.BETA_THM, bir_wp_simp_eval_imp_spec_thm] ((snd o dest_eq o concl) simp_thm));
*)

*)


end
