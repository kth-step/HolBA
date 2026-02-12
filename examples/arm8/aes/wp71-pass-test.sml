open HolKernel Parse;

open bir_wpTheory bir_wpLib;

(* This file contains the AES fragment of 71 statements. *)

(* Some settings *)
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

(* Time measurement should start here... *)

(* Passified version of the AES fragment of 71 statements. *)
val aes_program_def = Define `
     aes_program =
		           (BirProgram
  [<|bb_label :=
       BL_Address_HC (Imm64 0x400868w) "B90057E0 (str w0, [sp,#84])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 84w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 84w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40086Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40086Cw) "B94063E0 (ldr w0, [sp,#96])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 96w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400870w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400870w) "53187C00 (lsr w0, w0, #24)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_RightShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 24w))) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400874w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400874w) "53001C00 (uxtb w0, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400878w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400878w) "B9004BE0 (str w0, [sp,#72])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 72w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 72w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40087Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40087Cw) "B9406FE0 (ldr w0, [sp,#108])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 108w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400880w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400880w) "53107C00 (lsr w0, w0, #16)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_RightShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 16w))) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400884w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400884w) "53001C00 (uxtb w0, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400888w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400888w) "B90047E0 (str w0, [sp,#68])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 68w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 68w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40088Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40088Cw) "B9406BE0 (ldr w0, [sp,#104])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 104w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400890w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400890w) "53087C00 (lsr w0, w0, #8)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_RightShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 8w))) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400894w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400894w) "53001C00 (uxtb w0, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400898w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400898w) "B90043E0 (str w0, [sp,#64])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 64w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 64w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40089Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40089Cw) "B94067E0 (ldr w0, [sp,#100])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 100w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008A0w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008A0w) "53001C00 (uxtb w0, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008A4w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008A4w) "B9003FE0 (str w0, [sp,#60])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 60w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 60w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008A8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008A8w) "B9404BE0 (ldr w0, [sp,#72])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 72w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008ACw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008ACw) "D37EF401 (lsl x1, x0, #2)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_BinExp BIExp_And
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
             (BExp_BinExp BIExp_LeftShift
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 2w))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008B0w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008B0w)
         "90000000 (adrp x0, 400000 <_init-0x378>)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Const (Imm64 0x400000w))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008B4w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008B4w) "91386000 (add x0, x0, #0xe18)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Const (Imm64 3608w)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008B8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008B8w) "8B000020 (add x0, x1, x0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008BCw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008BCw) "B9400000 (ldr w0, [x0])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "R0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                BEnd_LittleEndian Bit32) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008C0w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008C0w) "B9003BE0 (str w0, [sp,#56])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 56w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 56w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008C4w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008C4w) "B94047E0 (ldr w0, [sp,#68])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 68w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008C8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008C8w) "D37EF401 (lsl x1, x0, #2)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_BinExp BIExp_And
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
             (BExp_BinExp BIExp_LeftShift
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 2w))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008CCw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008CCw)
         "B0000000 (adrp x0, 401000 <Te+0x1e8>)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Const (Imm64 0x401000w))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008D0w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008D0w) "91086000 (add x0, x0, #0x218)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Const (Imm64 536w)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008D4w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008D4w) "8B000020 (add x0, x1, x0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008D8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008D8w) "B9400000 (ldr w0, [x0])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "R0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                BEnd_LittleEndian Bit32) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008DCw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008DCw) "B90037E0 (str w0, [sp,#52])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 52w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 52w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008E0w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008E0w) "B94043E0 (ldr w0, [sp,#64])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 64w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008E4w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008E4w) "D37EF401 (lsl x1, x0, #2)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_BinExp BIExp_And
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
             (BExp_BinExp BIExp_LeftShift
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 2w))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008E8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008E8w)
         "B0000000 (adrp x0, 401000 <Te+0x1e8>)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Const (Imm64 0x401000w))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008ECw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008ECw) "91186000 (add x0, x0, #0x618)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Const (Imm64 1560w)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008F0w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008F0w) "8B000020 (add x0, x1, x0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008F4w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008F4w) "B9400000 (ldr w0, [x0])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "R0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                BEnd_LittleEndian Bit32) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008F8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008F8w) "B90033E0 (str w0, [sp,#48])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 48w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 48w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008FCw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x4008FCw) "B9403FE0 (ldr w0, [sp,#60])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 60w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400900w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400900w) "D37EF401 (lsl x1, x0, #2)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_BinExp BIExp_And
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
             (BExp_BinExp BIExp_LeftShift
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 2w))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400904w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400904w)
         "B0000000 (adrp x0, 401000 <Te+0x1e8>)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Const (Imm64 0x401000w))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400908w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400908w) "91286000 (add x0, x0, #0xa18)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Const (Imm64 2584w)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40090Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40090Cw) "8B000020 (add x0, x1, x0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400910w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400910w) "B9400000 (ldr w0, [x0])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "R0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                BEnd_LittleEndian Bit32) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400914w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400914w) "B9002FE0 (str w0, [sp,#44])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 44w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 44w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400918w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400918w) "B9403BE1 (ldr w1, [sp,#56])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 56w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40091Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40091Cw) "B94037E0 (ldr w0, [sp,#52])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 52w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400920w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400920w) "4A000021 (eor w1, w1, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_Xor
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400924w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400924w) "B94033E0 (ldr w0, [sp,#48])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 48w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400928w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400928w) "4A000021 (eor w1, w1, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_Xor
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40092Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40092Cw) "B9402FE0 (ldr w0, [sp,#44])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 44w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400930w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400930w) "4A000021 (eor w1, w1, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_Xor
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400934w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400934w) "F9400FE0 (ldr x0, [sp,#24])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 3
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 24w))) BEnd_LittleEndian Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400938w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400938w) "91003000 (add x0, x0, #0xc)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Const (Imm64 12w)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40093Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40093Cw) "B9400000 (ldr w0, [x0])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "R0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                BEnd_LittleEndian Bit32) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400940w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400940w) "4A000020 (eor w0, w1, w0)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_Xor
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32))
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400944w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400944w) "B90053E0 (str w0, [sp,#80])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 80w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 80w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400948w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400948w) "B9405FE0 (ldr w0, [sp,#92])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 92w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40094Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40094Cw) "B9006FE0 (str w0, [sp,#108])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 108w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 108w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400950w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400950w) "B9405BE0 (ldr w0, [sp,#88])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 88w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400954w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400954w) "B9006BE0 (str w0, [sp,#104])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 104w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 104w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400958w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400958w) "B94057E0 (ldr w0, [sp,#84])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 84w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40095Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40095Cw) "B90067E0 (str w0, [sp,#100])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 100w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 100w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400960w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400960w) "B94053E0 (ldr w0, [sp,#80])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 80w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400964w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400964w) "B90063E0 (str w0, [sp,#96])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 96w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 96w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400968w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400968w) "F9400FE0 (ldr x0, [sp,#24])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 3
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 24w))) BEnd_LittleEndian Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40096Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40096Cw) "91004000 (add x0, x0, #0x10)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R0" (BType_Imm Bit64)))
             (BExp_Const (Imm64 16w)))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400970w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400970w) "F9000FE0 (str x0, [sp,#24])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 3
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 24w))) 8);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 24w))) BEnd_LittleEndian
             (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400974w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400974w) "B9404FE0 (ldr w0, [sp,#76])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400978w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400978w) "51000400 (sub w0, w0, #0x1)";
     bb_statements :=
       [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_Minus
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 1w))) Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40097Cw)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x40097Cw) "B9004FE0 (str w0, [sp,#76])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 76w))) 4);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                (BExp_Const (Imm64 76w))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400980w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 0x400980w) "B9404FE0 (ldr w0, [sp,#76])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 2
             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
        BStmt_Assign (BVar "R0" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit32)
             Bit64)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400984w)))|>]
)`;

(* Note: Using same postcondition as in AESWpsScript, apart from
 * indexing. *)
(* Note: This approach does not obtain a HT for the last block. *)
val aes_post_def = Define `
  aes_post =
    (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "R0_post" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R0_47" (BType_Imm Bit64)))
    )
`;

val aes_ls_def = Define `
      aes_ls = \x.(x = (BL_Address (Imm64 0x400980w)))
`;

val aes_wps_def = Define `
      aes_wps = (FEMPTY |+ (BL_Address (Imm64 0x400980w), aes_post))
`;

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

(* 2. Computation of the parts independent of individual WPs *)
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
      aes_wpsrec = ^wpsrec`;
val wpsrec_bool_sound_thm_readable =
  REWRITE_RULE [GSYM aes_wpsrec_def] wpsrec_bool_sound_thm;
