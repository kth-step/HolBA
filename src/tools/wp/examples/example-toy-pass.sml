open HolKernel Parse;

open bir_wpTheory bir_wpLib;

(* This file contains the same example as toy1-test, but
 * passified. *)

(* Some settings *)
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

(* Passified version of the program found in toy1-test.sml *)
val aes_program_def = Define `
     aes_program =
		           (BirProgram
  [<|bb_label :=
       BL_Address_HC (Imm64 0x400570w) "D101C3FF (sub sp, sp, #0x70)";
     bb_statements :=
       [BStmt_Assume
          (BExp_BinPred BIExp_Equal
             (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64)))
             (BExp_BinExp BIExp_Minus
                (BExp_Den (BVar "SP_EL0_0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 112w))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400574w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400574w) "F9000FE0 (str x0, [sp,#24])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 3
             (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64)))
                (BExp_Const (Imm64 24w))) 8);
        BStmt_Assume
          (BExp_MemEq (BExp_Den (BVar "MEM_1" (BType_Mem Bit64 Bit8)))
             (BExp_Store
                (BExp_Den (BVar "MEM_0" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                (BExp_Den (BVar "R0_0" (BType_Imm Bit64)))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400578w) "B90017E1 (str w1, [sp,#20])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64)))
                (BExp_Const (Imm64 20w))) 4);
        BStmt_Assume
          (BExp_MemEq (BExp_Den (BVar "MEM_2" (BType_Mem Bit64 Bit8)))
             (BExp_Store
                (BExp_Den (BVar "MEM_1" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R1_0" (BType_Imm Bit64))) Bit32)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40057Cw)))|>])`;

(* Note: Changed variable to SP_EL0_1 *)
(* Note: This approach does not obtain a HT for the last block. *)
val aes_post_def = Define `
      aes_post = (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "SP_EL0_1" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 112w))
                 )`;
val aes_ls_def = Define `
      aes_ls = \x.(x = (BL_Address (Imm64 0x400578w)))`;
val aes_wps_def = Define `
      aes_wps = (FEMPTY |+ (BL_Address (Imm64 0x400578w),
                  aes_post)
                )`;

(* Terms with just the abbreviations in the above definitions. *)
val program = ``aes_program``;
val post = ``aes_post``;
val ls = ``aes_ls``;
val wps = ``aes_wps``;
val defs = [aes_program_def, aes_post_def, aes_ls_def, aes_wps_def];

(* 1. Initialization and scheduling of jobs *)
val prog_term = (snd o dest_comb o concl) aes_program_def;
val wps_term =
  (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) wps;
val wps_bool_sound_thm =
  bir_wp_init_wps_bool_sound_thm (program, post, ls) wps defs;
val (wpsdom, blstodo) =
  bir_wp_init_rec_proc_jobs prog_term wps_term [];

(* 2. Computation of the parts independent on individual WPs *)
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val prog_thm =
  bir_wp_comp_wps_iter_step0_init reusable_thm (program, post, ls)
                                  defs;

(* 3a. Finally, recursively compute the rest of the WPs *)
val (wpsrec, wpsrec_bool_sound_thm) =
  bir_wp_comp_wps prog_thm ((wps, wps_bool_sound_thm),
                            (wpsdom, blstodo)
                           ) (program, post, ls) defs;

(* 3b. Introduce abbreviations for legibility *)
val aes_wpsrec_def = Define `
      aes_wpsrec = ^wpsrec
`;
val wpsrec_bool_sound_thm_readable =
  REWRITE_RULE [GSYM aes_wpsrec_def] wpsrec_bool_sound_thm;
