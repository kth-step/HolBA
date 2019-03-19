open HolKernel Parse;

open bir_execLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;


val _ = log_setfile "toy-test.log";

val _ = print "loading...";

val name = "thomas_crazy_program";

val prog = ``
BirProgram [
  (******** Prelude ********)
  <|bb_label := BL_Label "entry";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "init"))
  |>;
  (* Initializes the state *)
  <|bb_label := BL_Label "init";
    bb_statements := [
      (* Alice state *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x0w));
      BStmt_Assign (BVar "state.alice.stamina" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x0w));
      BStmt_Assign (BVar "state.alice.hunger" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x18w));
      (* Bob state *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x0w));
      BStmt_Assign (BVar "state.bob.stamina" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x0w));
      BStmt_Assign (BVar "state.bob.fun" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x0w))
    ];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "entrypoints.autonomous_step"))
    (* bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "entrypoints.bus_arrived")) *)
    (* bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "entrypoints.taxi_arrived")) *)
  |>;
  (******** Entry-points ********)
  (* Performs one autonomous step, by calling the scheduler. *)
  <|bb_label := BL_Label "entrypoints.autonomous_step";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "scheduler"))
  |>;
  (* Bus arrived *)
  <|bb_label := BL_Label "entrypoints.bus_arrived";
    bb_statements := [
      (* TODO: Assert that Alice is waiting the bus? *)
      (* state.alice.step := 3 *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x3w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* Taxi arrived *)
  <|bb_label := BL_Label "entrypoints.taxi_arrived";
    bb_statements := [
      (* TODO: Assert that Bob is waiting a taxi? *)
      (* state.bob.step := 5 *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x5w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (******** Scheduler ********)
  <|bb_label := BL_Label "scheduler";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "scheduler.init"))
  |>;
  (* Initializes the scheduler memory *)
  <|bb_label := BL_Label "scheduler.init";
    bb_statements := [
      (* BStmt_Assign (BVar "scheduler.oracle_index" (BType_Imm Bit32)) *)
        (* BExp_Const (Imm32 0x0w); *)
      (* BStmt_Assign (BVar "oracle" (BType_Imm Bit32)) *)
        (* BExp_Const (Imm32 0x0w); *)
    ];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "scheduler.oracle_jump"))
  |>;
  (* Jumps to the automaton according to the oracle's value *)
  <|bb_label := BL_Label "scheduler.oracle_jump";
    bb_statements := [];
    bb_last_statement :=
      BStmt_Jmp (BLE_Exp
        (BExp_IfThenElse
          (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "oracle" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x0w)))
          (BExp_Const (Imm32 0x001000w)) (* alice_automaton *)
          (BExp_Const (Imm32 0x002000w)))) (* bob_automaton *)
  |>;
  (******** Alice automaton ********)
  <|bb_label := BL_Address_HC (Imm32 0x001000w) "alice_automaton";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "alice_automaton.cases"))
  |>;
  (* Jumps to the right automaton state depending on the current step. *)
  <|bb_label := BL_Label "alice_automaton.cases";
    bb_statements := [];
    bb_last_statement :=
      BStmt_Jmp (BLE_Exp
        (BExp_IfThenElse
          (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "state.alice.step" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x0w)))
          (BExp_Const (Imm32 0x001100w)) (* alice_automaton.step.0 *)
          (BExp_IfThenElse
            (BExp_BinPred BIExp_Equal
              (BExp_Den (BVar "state.alice.step" (BType_Imm Bit32)))
              (BExp_Const (Imm32 0x1w)))
            (BExp_Const (Imm32 0x001101w)) (* alice_automaton.step.1 *)
            (BExp_IfThenElse
              (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "state.alice.step" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0x2w)))
              (BExp_Const (Imm32 0x001102w)) (* alice_automaton.step.2 *)
              (BExp_IfThenElse
                (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "state.alice.step" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 0x3w)))
                (BExp_Const (Imm32 0x001103w)) (* alice_automaton.step.3 *)
                (BExp_IfThenElse
                  (BExp_BinPred BIExp_Equal
                    (BExp_Den (BVar "state.alice.step" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 0x4w)))
                  (BExp_Const (Imm32 0x001104w)) (* alice_automaton.step.4 *)
                  (BExp_IfThenElse
                    (BExp_BinPred BIExp_Equal
                      (BExp_Den (BVar "state.alice.step" (BType_Imm Bit32)))
                      (BExp_Const (Imm32 0x5w)))
                    (BExp_Const (Imm32 0x001105w)) (* alice_automaton.step.5 *)
                    (BExp_Const (Imm32 0x001200w)) (* alice_automaton.step.unknown *)
                    )))))))
  |>;
  (* Unknown step *)
  <|bb_label := BL_Address_HC (Imm32 0x001200w) "alice_automaton.step.unknown";
    bb_statements := [];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x888888w))
  |>;
  (* A0. Sleeping *)
  <|bb_label := BL_Address_HC (Imm32 0x001100w) "alice_automaton.step.0";
    bb_statements := [
      (* state.alice.stamina += 20 *)
      BStmt_Assign (BVar "state.alice.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "state.alice.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 20w)));
      (* state.alice.hunger += 2 *)
      BStmt_Assign (BVar "state.alice.hunger" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "state.alice.hunger" (BType_Imm Bit32)))
            (BExp_Const (Imm32 2w)));
      (* state.alice.step := 1 *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 1w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* A1. Eating *)
  <|bb_label := BL_Address_HC (Imm32 0x001101w) "alice_automaton.step.1";
    bb_statements := [
      (* state.alice.hunger -= 20 *)
      BStmt_Assign (BVar "state.alice.hunger" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.alice.hunger" (BType_Imm Bit32)))
            (BExp_Const (Imm32 20w)));
      (* state.alice.step := 2 *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 2w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* A2. WaitingBus -> not an autonomous step *)
  <|bb_label := BL_Address_HC (Imm32 0x001102w) "alice_automaton.step.2";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "alice_automaton.step.2.dead"))
  |>;
  (* A3. Working *)
  <|bb_label := BL_Address_HC (Imm32 0x001103w) "alice_automaton.step.3";
    bb_statements := [
      (* state.alice.stamina -= 10 *)
      BStmt_Assign (BVar "state.alice.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.alice.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 10w)));
      (* state.alice.hunger += 5 *)
      BStmt_Assign (BVar "state.alice.hunger" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "state.alice.hunger" (BType_Imm Bit32)))
            (BExp_Const (Imm32 5w)));
      (* state.alice.step := 4 *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 4w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* A4. Working *)
  <|bb_label := BL_Address_HC (Imm32 0x001104w) "alice_automaton.step.4";
    bb_statements := [
      (* state.alice.stamina -= 8 *)
      BStmt_Assign (BVar "state.alice.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.alice.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 8w)));
      (* state.alice.hunger += 13 *)
      BStmt_Assign (BVar "state.alice.hunger" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "state.alice.hunger" (BType_Imm Bit32)))
            (BExp_Const (Imm32 13w)));
      (* state.alice.step := 5 *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 5w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* A5. Cooking *)
  <|bb_label := BL_Address_HC (Imm32 0x001105w) "alice_automaton.step.5";
    bb_statements := [
      (* state.alice.stamina -= 2 *)
      BStmt_Assign (BVar "state.alice.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.alice.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 2w)));
      (* state.alice.step := 0 *)
      BStmt_Assign (BVar "state.alice.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (******** Bob automaton ********)
  <|bb_label := BL_Address_HC (Imm32 0x002000w) "bob_automaton";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "bob_automaton.cases"))
  |>;
  (* Jumps to the right automaton state depending on the current step. *)
  <|bb_label := BL_Label "bob_automaton.cases";
    bb_statements := [];
    bb_last_statement :=
      BStmt_Jmp (BLE_Exp
        (BExp_IfThenElse
          (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "state.bob.step" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x0w)))
          (BExp_Const (Imm32 0x002100w)) (* bob_automaton.step.0 *)
          (BExp_IfThenElse
            (BExp_BinPred BIExp_Equal
              (BExp_Den (BVar "state.bob.step" (BType_Imm Bit32)))
              (BExp_Const (Imm32 0x1w)))
            (BExp_Const (Imm32 0x002101w)) (* bob_automaton.step.1 *)
            (BExp_IfThenElse
              (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "state.bob.step" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0x2w)))
              (BExp_Const (Imm32 0x002102w)) (* bob_automaton.step.2 *)
              (BExp_IfThenElse
                (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "state.bob.step" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 0x3w)))
                (BExp_Const (Imm32 0x002103w)) (* bob_automaton.step.3 *)
                (BExp_IfThenElse
                  (BExp_BinPred BIExp_Equal
                    (BExp_Den (BVar "state.bob.step" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 0x4w)))
                  (BExp_Const (Imm32 0x002104w)) (* bob_automaton.step.4 *)
                  (BExp_IfThenElse
                    (BExp_BinPred BIExp_Equal
                      (BExp_Den (BVar "state.bob.step" (BType_Imm Bit32)))
                      (BExp_Const (Imm32 0x5w)))
                    (BExp_Const (Imm32 0x002105w)) (* bob_automaton.step.5 *)
                    (BExp_Const (Imm32 0x002200w)) (* bob_automaton.step.unknown *)
                    )))))))
  |>;
  (* Unknown step *)
  <|bb_label := BL_Address_HC (Imm32 0x002200w) "bob_automaton.step.unknown";
    bb_statements := [];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x777777w))
  |>;
  (* B0. Sleeping *)
  <|bb_label := BL_Address_HC (Imm32 0x002100w) "bob_automaton.step.0";
    bb_statements := [
      (* state.bob.stamina += 20 *)
      BStmt_Assign (BVar "state.bob.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "state.bob.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x20w)));
      (* state.bob.step := 1 *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x1w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* B1. Eating *)
  <|bb_label := BL_Address_HC (Imm32 0x002101w) "bob_automaton.step.1";
    bb_statements := [
      (* state.bob.fun += 10 *)
      BStmt_Assign (BVar "state.bob.fun" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "state.bob.fun" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x10w)));
      (* state.bob.stamina -= 5 *)
      BStmt_Assign (BVar "state.bob.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x5w)));
      (* state.bob.step := 2 *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x2w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* B2. Walking *)
  <|bb_label := BL_Address_HC (Imm32 0x002102w) "bob_automaton.step.2";
    bb_statements := [
      (* state.bob.fun -= 6 *)
      BStmt_Assign (BVar "state.bob.fun" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.fun" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x6w)));
      (* state.bob.stamina -= 8 *)
      BStmt_Assign (BVar "state.bob.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x8w)));
      (* state.bob.step := 3 *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x3w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* B3. Cooking *)
  <|bb_label := BL_Address_HC (Imm32 0x002103w) "bob_automaton.step.3";
    bb_statements := [
      (* state.bob.fun -= 1 *)
      BStmt_Assign (BVar "state.bob.fun" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.fun" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x1w)));
      (* state.bob.stamina -= 5 *)
      BStmt_Assign (BVar "state.bob.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x5w)));
      (* state.bob.step := 4 *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x4w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>;
  (* B4. WaitingTaxi -> not an autonomous step *)
  <|bb_label := BL_Address_HC (Imm32 0x002104w) "bob_automaton.step.4";
    bb_statements := [];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "bob_automaton.step.4.dead"))
  |>;
  (* B5. Eating *)
  <|bb_label := BL_Address_HC (Imm32 0x002105w) "bob_automaton.step.5";
    bb_statements := [
      (* state.bob.fun -= 2 *)
      BStmt_Assign (BVar "state.bob.fun" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.fun" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x2w)));
      (* state.bob.stamina -= 3 *)
      BStmt_Assign (BVar "state.bob.stamina" (BType_Imm Bit32))
        (BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "state.bob.stamina" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0x3w)));
      (* state.bob.step := 0 *)
      BStmt_Assign (BVar "state.bob.step" (BType_Imm Bit32))
        (BExp_Const (Imm32 0x0w))
    ];
    bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x000000w))
  |>
]``;

val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = NONE;

val n_max = 50;

val _ = print "ok\n";


val _ = bir_exec_prog_print name prog n_max validprog_o welltypedprog_o state_o;
