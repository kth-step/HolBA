open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_wpTheory;

(*
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

load "pairLib";
*)


val program = ``
		           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm64 0x400570w)
                     "D101C3FF (sub sp, sp, #0x70)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 112w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400574w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400574w)
                     "F9000FE0 (str x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400578w)
                     "B90017E1 (str w1, [sp,#20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64
							 0x40057Cw)))|>
	      ])``;


val post = ``(BExp_Const (Imm1 1w))``;
val label = ``BL_Address (Imm64 0x400570w)``;
val wps = ``(FEMPTY |+ (BL_Address (Imm64 0x400574w), ^post))``;


val post_thm = EVAL ``bir_is_bool_exp ^post``;

val thm1 = SPECL [program, label, ``\(x:bir_label_t).T``, post, 
       wps,
       ``wps':bir_label_t |-> bir_exp_t``
      ] bir_wp_exec_of_block_sound_thm;

(fst o dest_imp o concl) thm1;
val thm2 = MP thm1 (SIMP_RULE std_ss [] post_thm);

(fst o dest_imp o concl) thm2;

val prog_type_thm = SIMP_CONV (srw_ss()) [
bir_is_well_typed_program_def,
bir_is_well_typed_block_def,
bir_is_well_typed_stmtE_def,bir_is_well_typed_stmtB_def,
bir_is_well_typed_label_exp_def,
type_of_bir_exp_def,bir_var_type_def,
bir_type_is_Imm_def,
type_of_bir_imm_def,
bir_extra_expsTheory.BExp_Aligned_type_of,
BExp_unchanged_mem_interval_distinct_type_of,
bir_mem_expTheory.bir_number_of_mem_splits_REWRS
] ``bir_is_well_typed_program ^program``;

val thm3 = MP thm2 (SIMP_RULE std_ss [] prog_type_thm);

(fst o dest_imp o concl) thm3;
val prog_valid_thm = SIMP_CONV (srw_ss()) [
bir_program_valid_stateTheory.bir_is_valid_program_def,
bir_program_valid_stateTheory.bir_program_is_empty_def,
bir_program_valid_stateTheory.bir_is_valid_labels_def,
bir_labels_of_program_def,
BL_Address_HC_def
] ((fst o dest_imp o concl) thm3);

val thm4 = MP thm3 (SIMP_RULE std_ss [] prog_valid_thm);


(fst o dest_imp o concl) thm4;
val prog_declare_free_thm = prove((fst o dest_imp o concl) thm4, cheat);
val thm5 = MP thm4 (SIMP_RULE std_ss [] prog_declare_free_thm);

(fst o dest_imp o concl) thm5;
val prog_direct_jmp_thm = prove((fst o dest_imp o concl) thm5, cheat);
val thm6 = MP thm5 (SIMP_RULE std_ss [] prog_direct_jmp_thm);

(fst o dest_imp o concl) thm6;
val label_thm = EVAL ((fst o dest_imp o concl) thm6);
val thm7 = MP thm6 (SIMP_RULE std_ss [] label_thm);


(fst o dest_imp o concl) thm7;
val prog_edges_thm = prove((fst o dest_imp o concl) thm7, cheat);
val thm8 = MP thm7 (SIMP_RULE std_ss [] prog_edges_thm);

(fst o dest_imp o concl) thm8;
val wrong_condition_thm = prove((fst o dest_imp o concl) thm8, cheat);
val thm9 = MP thm8 (SIMP_RULE std_ss [] wrong_condition_thm);

(fst o dest_imp o concl) thm9;
val wps_bool_thm = SIMP_CONV (srw_ss()) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.FEVERY_FEMPTY, bir_is_bool_exp_def, type_of_bir_exp_def, type_of_bir_imm_def] ((fst o dest_imp o concl) thm9);
val thm10 = MP thm9 (SIMP_RULE std_ss [] wps_bool_thm);

(fst o dest_imp o concl) thm10;
val wps_sound_thm = SIMP_CONV (srw_ss()) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.FEVERY_FEMPTY, bir_exec_to_labels_triple_def] ((fst o dest_imp o concl) thm10);
val thm10 = MP thm9 (SIMP_RULE std_ss [] wps_bool_thm);


fun bir_determine_wp_core p lstart lend post =
  let
    val x = 4;
  in
    x
  end;


    
