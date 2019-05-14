open HolKernel Parse boolTheory boolLib pairTheory

open HolKernel Parse boolLib bossLib;
open bir_bool_expSyntax;
open bir_exp_substitutionsSyntax;
open bir_extra_expsSyntax;
open bir_interval_expSyntax;
open HolBASimps;

val _ = print "HolBA bir-support files successfully loaded.\n";


val _ = print "Testing HolBASimps - vars_of_program.\n";

val prog = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "Mem" (BType_Mem Bit64 Bit8))
                           (BExp_Store (BExp_Den (BVar "Mem" (BType_Mem Bit64 Bit8)))
                                       (BExp_Const (Imm64 25w))
                                       BEnd_LittleEndian
                                       (BExp_Const (Imm64 26w)));
	      BStmt_Assign (BVar "Mem" (BType_Mem Bit64 Bit8))
                           (BExp_Store (BExp_Den (BVar "Mem" (BType_Mem Bit64 Bit8)))
                                       (BExp_Const (Imm64 25w))
                                       BEnd_LittleEndian
                                       (BExp_Const (Imm64 25w)))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;

         <|bb_label :=
             BL_Address (Imm32 0x102w);
           bb_statements :=
             [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                           (BExp_Cast BIExp_UnsignedCast
                                      (BExp_Load (BExp_Den (BVar "Mem" (BType_Mem Bit64 Bit8)))
                                                 (BExp_Const (Imm64 24w))
                                                 BEnd_LittleEndian
                                                 Bit32)
                                      Bit64)];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x200w))) |>;

         <|bb_label :=
             BL_Address (Imm32 0x200w);
           bb_statements := [];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``;

val progvars_expected = ``
  {BVar "R0" (BType_Imm Bit64);
   BVar "Mem" (BType_Mem Bit64 Bit8)}``;

val progvars_val = (rhs o concl o ((SIMP_CONV (pure_ss++VARS_OF_PROG_ss) []) THENC EVAL)) ``bir_vars_of_program ^prog``;

val _ = if progvars_expected = progvars_val then () else
        raise Fail "Incorrect result for variables of program.";


val _ = Process.exit Process.success;
