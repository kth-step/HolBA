structure bir_exec_envLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open BasicProvers;

  open bir_envSyntax;
  open bir_valuesSyntax;
  open finite_mapSyntax;

  open HolBACoreSimps;

  open bir_envTheory;
  open finite_mapTheory;

  open bir_exec_auxLib;
  open bir_exec_typingLib;

  open pairSyntax;
  open optionSyntax;

(*
  val vars = [``BVar "bit1" (BType_Bool)``,
              ``BVar "R1" (BType_Imm Bit32)``,
              ``BVar "R2" (BType_Imm Bit32)``,
              ``BVar "R3" (BType_Imm Bit32)``];

  val env = bir_exec_env_initd_env vars;
  val var_eq_thms = gen_var_eq_thms vars;

  val var = List.nth(vars,1);
  val b_val = ``(BVal_Imm (Imm32 9w))``;


  val t = ``bir_env_write ^var ^b_val ^env``;

  val t = ``bir_env_read ^var ^env``;

  val t = ````;
*)

  fun bir_exec_env_initd_env vars =
    let
      val fempty_env_tm = (dest_BEnv o snd o dest_eq o concl) bir_empty_env_def;
      val var_pairs = List.map dest_BVar vars;
      (*
      bir_valuesTheory.bir_default_value_of_type_def
      bir_programTheory.bir_declare_initial_value_def
      *)
      val var_assigns = List.map (fn (n,t) =>
            mk_pair (n, (mk_pair (t, (snd o dest_eq o concl o EVAL) ``SOME (bir_default_value_of_type ^t)``)))) var_pairs;

      val env = mk_BEnv (list_mk_fupdate (fempty_env_tm, var_assigns));
      (* TODO: check that "bir_env_vars_are_initialised ^env (bir_vars_of_prog ^prog)" *)
(* bir_envTheory.bir_env_vars_are_initialised_def *)
    in
      env
    end;



  (* TODO: organize these and other theorem lists in simpsets if suitable *)
  (* list of theorems to evaluate environment lookups *)
  val env_lookup_thms =
       [bir_var_name_def,
	bir_var_type_def,
	FLOOKUP_EMPTY,
	FLOOKUP_UPDATE,
	bir_env_lookup_def
       ];

  val env_check_type_thms =
       [bir_env_lookup_type_def,
	bir_env_check_type_def,
        BType_Bool_def
       ]@env_lookup_thms;

  val type_of_bir_val_thms =
    [type_of_bir_val_def, type_of_bir_imm_def];




  fun bir_exec_env_write_conv var_eq_thms =
    let
      val is_tm_fun = is_bir_env_write;
      val check_tm_fun = (fn t => is_none t orelse (is_some t andalso is_BEnv (dest_some t)));
      fun conv t =
        let
          (* make sure that the type of the variable in the environment matches *)
          val thm1 = SIMP_CONV (std_ss++bir_TYPES_ss) (bir_env_write_def::env_check_type_thms@var_eq_thms) t;

          (* now we can update the environment accordingly *)
          val thm2 = CONV_RULE (RAND_CONV (
                                    (SIMP_CONV (std_ss++bir_TYPES_ss)
                                               ([bir_env_update_def]@type_of_bir_val_thms))
                                 )) thm1;

          (* finally we start purging of redundant updates *)
          val thm3 = CONV_RULE (RAND_CONV (
                       REWRITE_CONV [Once FUPDATE_PURGE]
                     )) thm2;

          (* propagation of the purging operation *)
          val thm4 = CONV_RULE (RAND_CONV (
                       SIMP_CONV (std_ss)
                         ([DOMSUB_FEMPTY, DOMSUB_FUPDATE, DOMSUB_FUPDATE_NEQ]@var_eq_thms)
                     )) thm3;
        in
          thm4
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;


  fun bir_exec_env_read_conv var_eq_thms =
    let
      val is_tm_fun = is_bir_env_read;
      val check_tm_fun = (fn t => (List.exists (fn f => f t) [is_BVal_Imm1,
                                                              is_BVal_Imm8,
                                                              is_BVal_Imm16,
                                                              is_BVal_Imm32,
                                                              is_BVal_Imm64]
                                  ) orelse is_BVal_Mem t);
      fun conv t =
        let
          (* make sure that the type of the variable in the environment matches *)
          (* and take its value *)
          val thm1 = ((SIMP_CONV (std_ss++bir_TYPES_ss)
                                 (bir_env_read_def::env_check_type_thms@var_eq_thms)) THENC
                      CASE_SIMP_CONV
                     ) t;
        in
          thm1
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;



end
