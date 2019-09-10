structure easy_noproof_wpLib :> easy_noproof_wpLib =
struct

  open Abbrev

  local

  open HolKernel Parse boolLib bossLib;
  open finite_mapSyntax finite_mapTheory;

  open bir_expSyntax;
  open bir_immSyntax;
  open bir_envSyntax;
  open bir_exp_immSyntax;
  open bir_exp_memSyntax;
  open bir_bool_expSyntax;

  val ERR = Feedback.mk_HOL_ERR "easy_noproof_wpLib";
  val wrap_exn = Feedback.wrap_exn "easy_noproof_wpLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("easy_noproof_wpLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "easy_noproof_wpLib" level_log;

  (* Defines a lambda matching all terms in the given list.
   *
   * For example:
   * > mk_lambda_matching_any_of [``"s1"``, ``"s2"``];
   * val it =
   *   “λx. (x = "s1") ∨ (x = "s2")”: term
   *)
  fun mk_lambda_matching_any_of terms =
    let
      val ty = (type_of o hd) terms
      val var = mk_var ("x", ty)
      val eq_list = List.map (fn tm => mk_eq (var, tm)) terms
      val disj = list_mk_disj eq_list
    in
      mk_abs (var, disj)
    end;

  fun mk_fmap_of (key_ty, value_ty) key_value_list =
    let
      val empty = mk_fempty (key_ty, value_ty)
      val updates = List.map (fn kv => pairSyntax.mk_pair kv) key_value_list
    in
      list_mk_fupdate (empty, updates)
    end;

  in (* local *)

  fun bir_label_to_wps_id_suffix bir_lbl =
    let
      fun escape_non_alphanum c = if Char.isAlphaNum c then String.str c else "_"
      fun to_ident name = String.translate escape_non_alphanum name
      val raw_suffix =
        if (is_BL_Address bir_lbl)
          then (term_to_string o snd o gen_dest_Imm o dest_BL_Address) bir_lbl
          else (stringSyntax.fromHOLstring o dest_BL_Label) bir_lbl
    in
      to_ident raw_suffix
    end
      handle exn => raise wrap_exn "bir_label_to_wps_id_suffix" exn;

  fun compute_wps_tm define_prefix prog_def (postcond_lbls, postcond_bir_tm) =
    let
      val trace = trace ("compute_wps_tm::'" ^ define_prefix ^ "'")

      (* Turn the postcondition list into what HolBA/tools/wp wants *)
      val _ = trace "Translating data to HolBA/tools/wp format...";
      (** postcondition **)
      val (post_tm, post_def) = (
        postcond_bir_tm,
        xDefine ("compute_wps_def__" ^ define_prefix ^ "__post") `post = ^postcond_bir_tm`)
        handle exn => raise wrap_exn "compute_wp_thm::post_def" exn;

      (** labels **)
      val wps_labels_lambda_tm = mk_lambda_matching_any_of postcond_lbls
        handle exn => raise wrap_exn "compute_wp_thm::wps_labels_lambda_tm" exn;
      val wps_labels_lambda_def = xDefine ("compute_wps_def__" ^ define_prefix ^ "__wps_labels_lambda")
          `wps_labels_lambda = ^wps_labels_lambda_tm`
        handle exn => raise wrap_exn "compute_wp_thm::wps_labels_lambda_def" exn;

      (** WPs map **)
      val postcondition_list = (List.map (fn lbl => (lbl, post_tm)) postcond_lbls)
        handle exn => raise wrap_exn "compute_wp_thm::postcondition_list" exn;
      val wps0_tm = (mk_fmap_of (Type `:bir_label_t`, Type `:bir_exp_t`) postcondition_list)
        handle exn => raise wrap_exn "compute_wp_thm::wps0_tm" exn;
      val wps0_def = xDefine ("compute_wps_def__" ^ define_prefix ^ "__wps0") `wps0 = ^wps0_tm`
        handle exn => raise wrap_exn "compute_wp_thm::wps0_def" exn;

      (** prog **)
      val prog_tm = ((snd o dest_comb o concl) prog_def)
        handle _ => raise Fail "compute_wp_thm::prog_def isn't a def";

      (** definitions **)
      val defs = [prog_def, post_def, wps0_def, wps_labels_lambda_def];

      (* wps_bool_sound_thm for initial wps *)
      val _ = trace "wps_bool_sound_thm for initial WPs...";
      val prog_term = (snd o dest_comb o concl) prog_def
      val wps_bool_sound_thm = (bir_wpLib.bir_wp_init_wps_bool_sound_thm
        (prog_tm, post_tm, wps_labels_lambda_tm) wps0_tm defs)
        handle exn => raise wrap_exn "compute_wp_thm::wps_bool_sound_thm" exn;
      val (wpsdom, blstodo) = (bir_wpLib.bir_wp_init_rec_proc_jobs prog_term wps0_tm [])
        handle exn => raise wrap_exn "compute_wp_thm::wpsdom, blstodo" exn;

      (* prepare "problem-static" part of the theorem *)
      val _ = trace "Building reusable thm...";
      val reusable_thm = (bir_wpTheory.bir_wp_exec_of_block_reusable_thm)
        handle exn => raise wrap_exn "compute_wp_thm::reusable_thm" exn;

      val _ = trace "WP: step 0 init...";
      val prog_thm = (bir_wpLib.bir_wp_comp_wps_iter_step0_init
        reusable_thm
        (prog_tm, post_tm, wps_labels_lambda_tm)
        defs)
        handle exn => raise wrap_exn "compute_wp_thm::bir_wp_comp_wps_iter_step0_init" exn;

      val _ = trace "WP: computing WPs...";
      val (new_wps_tm, new_wps_bool_sound_thm) = (bir_wpLib.bir_wp_comp_wps
        prog_thm
        ((wps0_tm, wps_bool_sound_thm), (wpsdom, List.rev blstodo))
        (prog_tm, post_tm, wps_labels_lambda_tm)
        defs)
        handle exn => raise wrap_exn "compute_wp_thm::bir_wp_comp_wps" exn;

      val _ = trace "Done.";
    in
      new_wps_tm
    end;

  fun bir_wp_simp define_prefix prog_def wps_tm wp_lbl precond_bir_tm =
    let
      val trace = trace ("bir_wp_simp::'" ^ define_prefix ^ "'")

      (* Extract the WP from the WPs map *)
      val _ = trace "Extracting the WP from the WPs map...";
      val lbl_list = bir_wp_expLib.gen_lbl_list wps_tm
        handle e => raise wrap_exn "[bir_wp_simp] Failed to gen_lbl_list" e;
      val varexps_thms = bir_wp_simpLib.preproc_vars [] (tl (rev lbl_list))
        handle e => raise wrap_exn "[bir_wp_simp] Failed to preproc_vars" e;
      val wp_thm_suffix = bir_label_to_wps_id_suffix wp_lbl
        handle e => raise wrap_exn "[bir_wp_simp] Failed to create wp_thm_suffix" e;
      val wp_thm = bir_wp_simpLib.lookup_def (bir_wpLib.wps_id_prefix ^ wp_thm_suffix)
        handle e => raise wrap_exn ("[bir_wp_simp] Failed to lookup_def '" ^ bir_wpLib.wps_id_prefix ^ wp_thm_suffix ^ "'") e;
      val wp_const = (fst o dest_eq o concl) wp_thm

        handle e => raise wrap_exn "[bir_wp_simp] Failed to extract the WP" e;

      (* Precondition *)
      val _ = trace "Precondition...";
      val precond_def = xDefine ("bir_wp_simp__" ^ define_prefix ^ "__precond") `precond = ^precond_bir_tm`;
      val varexps_thms = (bir_wp_simpLib.preproc_vars_thm true [] precond_def)::varexps_thms

        handle e => raise wrap_exn "[bir_wp_simp] Failed to define the precond" e;

      (* goalterm: P ==> WP *)
      val _ = trace "goalterm: P ==> WP...";
      val goalterm = ``
        bir_exp_is_taut (bir_exp_imp
          ^precond_bir_tm
          (bir_exp_varsubst FEMPTY ^wp_const))``

        handle e => raise wrap_exn "[bir_wp_simp] Failed to define the goalterm" e;

      (* Well-typed theorem init thingy *)
      val _ = trace "Well-typed theorem init thingy...";
      val wt0_thm = prove (
        ``^(bir_wp_simpLib.simp_construct_wt (bir_wp_simpLib.simp_extract goalterm) NONE)``,
        CONV_TAC (bir_wp_simpLib.well_typed_conv varexps_thms))

        handle e => raise wrap_exn "[bir_wp_simp] Failed to prove well-typedness" e;

      (* Simp'ed and well-type theorems *)
      val _ = trace "Simp'ed and well-typed theorems...";
      val (simp_thm, wt_thm) = bir_wp_simpLib.bir_wp_simp_CONV varexps_thms goalterm wt0_thm

        handle e => raise wrap_exn "[bir_wp_simp] bir_wp_simp_CONV failed" e;

      (* Extract the simp'ed term *)
      val _ = trace "Extracting the simp'ed term...";
      val wp_simp_term =
        (snd o dest_comb o snd o dest_eq o concl)
        simp_thm
          handle e => raise wrap_exn "[bir_wp_simp] bir_wp_simp_CONV misbehaved" e;

      val _ = trace ("Quickfix: term before quickfix:\n" ^ ((ppstring pp_term) wp_simp_term));

      val _ = trace "Quickfix: EVALuating the term...";
      val eval'ed = (snd o dest_eq o concl) (EVAL wp_simp_term)
      val _ = trace ("Quickfix: EVAL'ed term:\n" ^ ((ppstring pp_term) eval'ed));

      val _ = trace "Quickfix: SIMPlificating the term...";
      val simp'ed = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) [
          finite_mapTheory.fmap_EXT,
          finite_mapTheory.FDOM_FINITE,
          finite_mapTheory.FUN_FMAP_DEF,
          finite_mapTheory.FDOM_FUPDATE,
          finite_mapTheory.FAPPLY_FUPDATE_THM
        ] eval'ed)
        handle e => eval'ed
      val _ = trace ("Quickfix: SIMP'ed term:\n" ^ ((ppstring pp_term) simp'ed));

      val _ = trace "Done.";
    in
      (*wp_simp_term*)
      simp'ed
    end;

(*
easy_noproof_wpLib.compute_p_imp_wp_tm ""
      (* prog_def *) bir_mem_prog_def
      (* Precondition *)
      (``BL_Label "entry"``, ``
        BExp_BinPred BIExp_Equal
          (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
          (BExp_Den (BVar "ADDR2" (BType_Imm Bit32)))``)
      (* Postconditions *) (
        [``BL_Label "end"``], ``
          BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "x" (BType_Imm Bit16)))
            (BExp_Const (Imm16 42w))
        ``)
val define_prefix = "";
val prog_def = bir_mem_prog_def;
val (precond_lbl, precond_bir_tm) = (``BL_Label "entry"``, ``
        BExp_BinPred BIExp_Equal
          (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
          (BExp_Den (BVar "ADDR2" (BType_Imm Bit32)))``);
val (postcond_lbls, postcond_bir_tm) = (
        [``BL_Label "end"``], ``
          BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "x" (BType_Imm Bit16)))
            (BExp_Const (Imm16 42w))
        ``);
*)
  fun compute_p_imp_wp_tm define_prefix prog_def
    (precond_lbl, precond_bir_tm) (postcond_lbls, postcond_bir_tm) =
    let
      val info = info ("P ==> WP::'" ^ define_prefix ^ "'")

      val _ = info "Computing WPS...";
      val wps_tm = compute_wps_tm define_prefix prog_def (postcond_lbls, postcond_bir_tm)
        handle e => raise wrap_exn "compute_p_imp_wp_tm::compute_wps_tm" e;
      val _ = info "Done.";

      val _ = info "Translating to ``P ==> WP``...";
(*
      val p_imp_wp_tm = bir_wp_simp define_prefix prog_def wps_tm precond_lbl precond_bir_tm
        handle e => raise wrap_exn "compute_p_imp_wp_tm::bir_wp_simp" e;
*)
      val p_tm = precond_bir_tm;
      val wp_tm = (snd o dest_eq o concl o EVAL) ``THE (FLOOKUP ^wps_tm ^precond_lbl)``;
      val p_imp_wp_tm = ``BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ^p_tm) (^wp_tm)``;

      val _ = info "Done.";
    in
      p_imp_wp_tm
    end;

  end (* local *)

end
