open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_typing_progTheory;
open bir_typing_expTheory;
open bir_programTheory;
open bir_programSyntax;

open bir_valuesTheory;
open bir_immTheory;

open pred_setSyntax;

open bir_exec_auxLib;

open optionSyntax;
open listSyntax;

open listTheory;
open bir_program_valid_stateTheory;


structure bir_exec_typingLib =
struct


(*
val prog = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "bit1" BType_Bool)
                           (BExp_MSB Bit32 (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x102w) "abc";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``;


val t = ``type_of_bir_val (BVal_Imm (Imm32 x))``

val t = ``type_of_bir_val (BVal_Mem Bit32 Bit32 x)``

val t = ``type_of_bir_val (BVal_Mem Bit32 Bit32 (K 0))``

*)



  fun gen_vars_of_prog prog =
    let
      val var_usage_list = GEN_find_all_subterm is_BVar prog;

      fun filter_doubles [] acc = acc
	| filter_doubles (x::xs) acc = filter_doubles (List.filter (fn y => y <> x) xs) (x::acc);
    in
      filter_doubles var_usage_list [] (* TODO: double check that these are all variables? *)
    end;


  fun gen_labels_of_prog prog =
    let
      val rep_gen_set_and_eval_conv =
                   (REWRITE_CONV [bir_labels_of_program_def]) THENC
                   (REPEATC ((SIMP_CONV list_ss []) THENC
                             ((fn t => if op=((dest_eq o concl) t) then raise UNCHANGED else t) o EVAL)
                            ));
      val label_set = (snd o dest_eq o concl o rep_gen_set_and_eval_conv) ``bir_labels_of_program ^prog``;
    in
      (fst o dest_list) label_set
    end;

(* TODO: *)
(*
type_of_bir_exp
(bir_vars_of_exp)
(bir_var_set_is_well_typed vs)
((bir_exp_is_well_typed))
bir_is_well_typed_program
*)

(*
  val bir_exec_typing_exp_conv =
    let
      val is_tm_fun = is_type_of_bir_val;
      val check_tm_fun = (fn t => is_none t orelse
                                  (is_some t andalso
                                   let
                                     val bt = dest_some t;
                                   in
                                     (List.exists (fn f => f bt) [is_BType_Imm1,
                                                                  is_BType_Imm8,
                                                                  is_BType_Imm16,
                                                                  is_BType_Imm32,
                                                                  is_BType_Imm64]
                                     ) orelse is_BType_Mem bt
                                   end)
                         );
      val conv = (REWRITE_CONV [type_of_bir_val_def, type_of_bir_imm_def]);
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;
*)

  fun bir_exec_valid_prog prog_l_def =
    let
      val prog_l_const = (fst o dest_eq o concl) prog_l_def;
      val prog_const = (mk_BirProgram prog_l_const);

      val rep_gen_set_and_eval_conv =
                   (REWRITE_CONV [bir_labels_of_program_def]) THENC
                   (REPEATC ((SIMP_CONV list_ss []) THENC
                             ((fn t => if op=((dest_eq o concl) t) then raise UNCHANGED else t) o EVAL)
                            ));
      val label_set_thm = (REWRITE_CONV [prog_l_def] THENC (rep_gen_set_and_eval_conv)) ``bir_labels_of_program ^prog_const``;
      val valid_labels_thm =
        (
          (REWRITE_CONV [bir_is_valid_labels_def, label_set_thm]) THENC
          (REPEATC (
            (fn t => 
             ((if ((!debug_trace) > 0) then (print "!") else ());
              REWRITE_CONV [Once ALL_DISTINCT] t)) THENC
            (LAND_CONV (EVAL))
          ))
(*          (SIMP_CONV list_ss [ALL_DISTINCT])*)
        )
        ``bir_is_valid_labels ^prog_const``;

      val valid_prog_thm = prove(``bir_is_valid_program ^prog_const``,
                             REWRITE_TAC [bir_is_valid_program_def] >>
                             STRIP_TAC >- (
                               REWRITE_TAC [valid_labels_thm, ALL_DISTINCT]
                             ) >>
                             SIMP_TAC list_ss [bir_program_is_empty_def, prog_l_def]
                           )
                  handle _ => raise ERR "bir_exec_valid_prog"
                                        "check for valid program failed";
    in
      valid_prog_thm
    end;



  local
    open bir_immTheory;
    open bir_valuesTheory;
    open bir_envTheory;

    open bir_exp_memTheory;
    open bir_bool_expTheory;
    open bir_extra_expsTheory;
    open bir_nzcv_expTheory;
  in
    fun bir_exec_well_typed_prog prog_l_def =
      let
        val prog_typed_thms = [
			    bir_is_well_typed_program_def,bir_is_well_typed_block_def,
                            bir_is_well_typed_stmtE_def,bir_is_well_typed_stmtB_def,
			    bir_is_well_typed_label_exp_def,

			    type_of_bir_exp_def,bir_var_type_def,bir_type_is_Imm_def,
                            type_of_bir_imm_def,
			    BExp_Aligned_type_of,BExp_unchanged_mem_interval_distinct_type_of,
			    bir_number_of_mem_splits_REWRS, BType_Bool_def, bir_exp_true_def,
                            bir_exp_false_def, BExp_MSB_type_of,
			    BExp_nzcv_ADD_DEFS, BExp_nzcv_SUB_DEFS, n2bs_def, BExp_word_bit_def,
			    BExp_Align_type_of, BExp_ror_type_of, BExp_LSB_type_of,
                            BExp_word_bit_exp_type_of,
			    BExp_ADD_WITH_CARRY_type_of, BExp_word_reverse_type_of,
                            BExp_ror_exp_type_of
			    ];

        val prog_l_const = (fst o dest_eq o concl) prog_l_def;
        val prog_const = (mk_BirProgram prog_l_const);

        val thm = prove(``bir_is_well_typed_program ^prog_const``,
                      REWRITE_TAC [prog_l_def] >>
                      SIMP_TAC (srw_ss()) prog_typed_thms)
                  handle _ => raise ERR "bir_exec_well_typed_prog"
                                        "typechecking of program failed";
      in
        thm
      end;
  end;

end
