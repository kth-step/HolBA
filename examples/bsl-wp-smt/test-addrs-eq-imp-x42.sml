open HolKernel Parse boolLib bossLib;
open pretty_exnLib;

(* Load dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "easy_noproof_wpLib"; (* ../lib *)
  load "HolBA_HolSmtLib"; (* HOL/src/HolSmt *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(*
val _ = Globals.linewidth := 100;
val _ = Globals.show_types := true;
val _ = Globals.show_assums := true;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolBA_HolSmtLib" 0;
val _ = Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 2;
val _ = Feedback.set_trace "easy_noproof_wpLib" logLib.TRACE;
val _ = Feedback.set_trace "Define.storage_message" 1;
*)

(* BIR program *)
val _ = print "Defining BIR program...\n";
val bir_mem_prog_def = Define `
  bir_mem_prog = BirProgram [
    <|bb_label := BL_Label "entry";
      bb_statements := [];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "mem_store"))
    |>;
    <|bb_label := BL_Label "mem_store"; (* init *)
      bb_statements := [
        BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
          (BExp_Store
            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
            (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
            BEnd_BigEndian
            (BExp_Const (Imm16 42w)))
      ];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "mem_load"))
    |>;
    <|bb_label := BL_Label "mem_load";
      bb_statements := [
        BStmt_Assign (BVar "x" (BType_Imm Bit16))
          (BExp_Load
            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
            (BExp_Den (BVar "ADDR2" (BType_Imm Bit32)))
            BEnd_BigEndian
            Bit16)
      ];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "end"))
    |>;
    <|bb_label := BL_Label "end";
      bb_statements := [];
      bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))
    |>
  ]`;
val _ = print "Done!\n";

(* Equivalent-ish Z3 program
 *
 * the difference is that here we use val instead of 42.

(declare-const mem0 (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const mem (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const addr1 (_ BitVec 32))
(declare-const addr2 (_ BitVec 32))

(assert (= mem
  (store
    (store mem0
      (bvadd addr1 (_ bv0 32)) ((_ extract 7 0) (_ bv42 32)))
    (bvadd addr1 (_ bv1 32)) ((_ extract 15 8) (_ bv42 32)))
))

(assert
  (and
    (= (select mem (bvadd addr2 (_ bv0 32))) ((_ extract 7 0) (_ bv42 32)))
    (= (select mem (bvadd addr2 (_ bv1 32))) ((_ extract 15 8) (_ bv42 32)))
  ))

(assert (=
  mem0
  ((as const (Array (_ BitVec 32) (_ BitVec 8))) (_ bv0 8))))

(assert (not (= addr1 addr2)))

(check-sat)
(get-model)
*)

(* ADDR1=ADDR2 ==> x=42 *)
val addrs_eq_imp_x42_thm =
  let
    (* prog + P + Q => ``P ==> WP`` *)
    val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm ""
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

      handle e => raise pp_exn_s "compute_p_imp_wp_tm failed" e

    (* BIR expr => SMT-ready expr*)
    val smt_ready_tm = bir_exp_to_wordsLib.bir2bool p_imp_wp_bir_tm
      handle e => raise pp_exn_s "bir2bool failed" e
  in
    HolBA_HolSmtLib.Z3_ORACLE_PROVE smt_ready_tm
      handle e => raise pp_exn_s "Z3_ORACLE_PROVE failed" e
  end;
val _ = (Hol_pp.print_thm addrs_eq_imp_x42_thm; print "\n");

