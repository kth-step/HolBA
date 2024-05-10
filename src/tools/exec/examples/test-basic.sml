open HolKernel Parse bossLib boolLib;
open bslSyntax;

open bir_execLib;

val alpha = ``:'a``;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

(* Helper function to check equality between BSL and BIR programs, assuming that
 * a and b are tuples where programs are in the second position (like here) *)
fun assert_same_progs (a, b) =
  let
    val semantically_equals_thm = EVAL ``^(snd a) = ^(snd b)``;
    val semantically_equals = identical ((snd o dest_eq o concl) semantically_equals_thm) T;
    (*val semantically_equals = ((snd a) = (snd b));*)
  in if semantically_equals then ()
  else let
    val exn_message = "BIR and BSL programs differ: " ^ (fst a) ^ " and " ^ (fst b);
    val _ = print (exn_message ^ "\n");
    val _ = print ((fst a) ^ ":\n");
    val _ = Hol_pp.print_term (snd a);
    val _ = print "\n";
    val _ = print ((fst b) ^ ":\n");
    val _ = Hol_pp.print_term (snd b);
    val _ = print "\n";
    in raise Fail exn_message end
  end;


val _ = print "Loading program... ";

val prog1 = ("prog1", ``
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
                (BExp_Const (Imm32 25w));
              BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                (BExp_Const (Imm32 7w))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x104w))) |>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x104w) "eeee";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``);
val prog1_bsl = ("prog1_bsl", bprog_list alpha [
  (blabel_str "entry", [
    bassign (bvarimm1 "bit1", bmsbi 32 ((bden o bvarimm32) "R1"))
  ], (bjmp o belabel_addr32) 0x102),
  (blabel_addr32_s 0x102 "abc", [
    bassign (bvarimm32 "R3", bconst32 25),
    bassign (bvarimm32 "R2", bconst32 7)
  ], (bjmp o belabel_addr32) 0x104),
  (blabel_addr32_s 0x104 "eeee", [
    bassign (bvarimm32 "R3", bplusl [
      (bden o bvarimm32) "R2",
      (bden o bvarimm32) "R3"
    ])
  ], bhalt (bconst32 1))
]);
val _ = assert_same_progs (prog1, prog1_bsl);

val prog2 = ("prog2", ``
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
                (BExp_Const (Imm32 25w));
              BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                (BExp_Const (Imm32 7w))];
           bb_last_statement :=
             BStmt_CJmp (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 8w)) (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                        (BLE_Label (BL_Address (Imm32 0x104w)))
                        (BLE_Label (BL_Address (Imm32 0x106w))) |>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x104w) "eeee";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x106w) "eeeeggg";
           bb_statements :=
             [];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 0w)) |>
       ]``);
val prog2_bsl = ("prog2_bsl", bprog_list alpha [
  (blabel_str "entry", [
    bassign (bvarimm1 "bit1", bmsbi 32 ((bden o bvarimm32) "R1"))
  ], (bjmp o belabel_addr32) 0x102),
  (blabel_addr32_s 0x102 "abc", [
    bassign (bvarimm32 "R3", bconst32 25),
    bassign (bvarimm32 "R2", bconst32 7)
  ], bcjmp (beq (bconst32 8, (bden o bvarimm32) "R2"),
            belabel_addr32 0x104,
            belabel_addr32 0x106)),
  (blabel_addr32_s 0x104 "eeee", [
    bassign (bvarimm32 "R3", bplusl [
      (bden o bvarimm32) "R2",
      (bden o bvarimm32) "R3"
    ])
  ], bhalt (bconst32 1)),
  (blabel_addr32_s 0x106 "eeeeggg", [], bhalt (bconst32 0))
]);
val _ = assert_same_progs (prog2, prog2_bsl);

val prog3 = ("prog3", ``
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
       ]``);
val prog3_bsl = ("prog2_bsl", bprog_list alpha [
  (blabel_str "entry", [
    bassign (bvarmem64_8 "Mem",
             bstore_le ((bden o bvarmem64_8) "Mem") (bconst64 25) (bconst64 26)),
    bassign (bvarmem64_8 "Mem",
             bstore_le ((bden o bvarmem64_8) "Mem") (bconst64 25) (bconst64 25))
  ], (bjmp o belabel_addr32) 0x102),
  (blabel_addr32 0x102, [
    bassign (bvarimm64 "R0",
             bucast64 (bload32_le ((bden o bvarmem64_8) "Mem") (bconst64 24)))
  ], (bjmp o belabel_addr32) 0x200),
  (blabel_addr32 0x200, [], bhalt (bconst32 1))
]);
val _ = assert_same_progs (prog3, prog3_bsl);


val (name, prog) = prog3;

val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = NONE;

val n_max = 50;

val _ = print "ok\n";


val _ = bir_exec_prog_print name prog n_max validprog_o welltypedprog_o state_o;

