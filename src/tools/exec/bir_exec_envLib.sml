open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_envSyntax;
open finite_mapSyntax;

open bir_envTheory;
open finite_mapTheory;

open pairSyntax;


structure bir_exec_envLib =
struct

(*
  val vars = [``BVar "bit1" (BType_Bool)``,
              ``BVar "R1" (BType_Imm Bit32)``,
              ``BVar "R2" (BType_Imm Bit32)``,
              ``BVar "R3" (BType_Imm Bit32)``];

  val env = bir_exec_env_initd_env vars;
  val var_eq_thm = gen_var_eq_thm vars;

  val var = List.nth(vars,1);
  val b_val = ``(BVal_Imm (Imm32 9w))``;


  val t = ``bir_env_write ^var ^b_val ^env``;

  val t = ``bir_env_read ^var ^env``;
*)

  fun gen_var_eq_thm vars =
        let
          val vars = List.map (fst o dest_BVar) vars;
        in
          LIST_CONJ (List.map ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL)
                     (List.foldl (fn (v,l) => (List.map (fn v2 => mk_eq(v,v2)) vars)@l) [] vars)
                    )
        end;

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
    in
      env
    end;


  fun bir_exec_env_write_conv_help var_eq_thm t =
    if not (is_bir_env_write t) then
      raise UNCHANGED
    else
      let
        val thm1 = SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [
                FLOOKUP_EMPTY,
                FLOOKUP_UPDATE,
                bir_env_update_def,
                bir_env_lookup_def,
                bir_env_lookup_type_def,
                bir_env_check_type_def,
                bir_env_write_def,
                var_eq_thm] t;

        val thm2 = REWRITE_CONV [Once FUPDATE_PURGE] ((snd o dest_eq o concl) thm1);

        val thm3 = SIMP_CONV (std_ss) [
                DOMSUB_FEMPTY, DOMSUB_FUPDATE, DOMSUB_FUPDATE_NEQ,
                var_eq_thm] ((snd o dest_eq o concl) thm2);

      in
        TRANS (TRANS thm1 thm2) thm3
      end;


  fun bir_exec_env_read_conv_help var_eq_thm t =
    if not (is_bir_env_read t) then
      raise UNCHANGED
    else
      let
        val thm1 = SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [
                FLOOKUP_EMPTY,
                FLOOKUP_UPDATE,
                bir_env_lookup_def,
                bir_env_lookup_type_def,
                bir_env_check_type_def,
                bir_env_read_def,
                var_eq_thm] t;

        val thm2 = CONV_RULE (RAND_CONV (EVAL)) thm1; (* quick fix *)

      in
        thm2
      end;


(* TODO: *)
(* bir_envTheory.bir_env_vars_are_initialised_def *)




  fun GEN_bir_env_write_conv conv tm =
    if is_bir_env_write tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_env_write_conv conv)) THENC
         (RATOR_CONV (GEN_bir_env_write_conv conv))) tm
    else
      raise UNCHANGED
    ;

  fun GEN_bir_env_read_conv conv tm =
    if is_bir_env_read tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_env_read_conv conv)) THENC
         (RATOR_CONV (GEN_bir_env_read_conv conv))) tm
    else
      raise UNCHANGED
    ;




  val bir_exec_env_write_conv = GEN_bir_env_write_conv o bir_exec_env_write_conv_help;

  val bir_exec_env_read_conv = GEN_bir_env_read_conv o bir_exec_env_read_conv_help;


end
