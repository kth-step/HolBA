open HolKernel Parse;

open bir_wpTheory;


(*
   -------------------------------------------------------------
                             TESTING
   -------------------------------------------------------------
*)

val prog = ``
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
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>
])``;

val post = ``    (BExp_BinPred BIExp_Equal
	      (* (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) *)
		  (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Const (Imm64 60w)) BEnd_LittleEndian
                            Bit64)
              (BExp_Const (Imm64 0w)))
``;

val test_prog_post_thm = EVAL ``bir_wp_of_block (^prog) (BL_Address (Imm64 0x400574w)) 
  {(BL_Address (Imm64 0x400578w))} (Imm1 1w) 
  (FEMPTY |+ ((BL_Address (Imm64 0x400578w)), (^post)
  ))``;



(*
open bir_inst_liftingLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style [Bold, Underline] "Lifting aes-aarch64.da\n";

val (region_map, aes_sections) = read_disassembly_file_regions "aes-aarch64.da"

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  aes_sections


val _ = print "\n\n\n";
val _ = print_with_style [Bold, Underline] "Lifting aes-m0-cortex.da\n";
val (region_map, aes_sections) = read_disassembly_file_regions "aes-m0-cortex.da"

val (thm_m0, errors) = bmil_m0_LittleEnd_Process.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x10000))
  aes_sections

val _ = print "\n\n";

val _ = new_theory "aes";
val _ = save_thm ("aes_arm8_program_THM", thm_arm8);
val _ = save_thm ("aes_m0_program_THM", thm_m0);
val _ = export_theory();
*)
