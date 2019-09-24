(********************************************************)
(* Functions definied within this file are use to       *)
(* initialize the environment / memory                  *)
(* This is mostly SML -- not HOL definitions!           *)
(********************************************************)

(* 
app load ["bir_symb_envTheory", "bir_symb_execTheory", "stringLib"]
*)

structure bir_symb_init_envLib :> bir_symb_init_envLib = 
struct

local

open HolKernel;
open bir_expTheory;
open bir_symb_execTheory 
open bir_symb_envTheory;
open bir_valuesTheory;
open bir_immTheory;
open finite_mapTheory;
open bitstringTheory;
open stringLib;
open bir_exp_memTheory;

in

(* Initialize all the Registers / Variables we have *)

(* Functions to generate symolbic registers of _64 _8 and _1 bits *)
fun generate_symbolic_register_64 (name: string) = 
  mk_var(name, Type `:word64`);

fun generate_symbolic_register_1 (name : string) = 
  mk_var(name, Type `:word1`);

fun generate_symbolic_register_8 (name : string) = 
  mk_var(name, Type `:word8`);


(* Add symbolic registers byte-wise in environment *)
fun add_symbolic_register_to_env_64 name env = 
    let 
        val r =
          generate_symbolic_register_64 name
        val name_hol = fromMLstring name 
    in
        (rhs o concl o EVAL) 
    `` bir_symb_env_update 
    ^name_hol (BExp_Const (Imm64 ^r)) (BType_Imm Bit64) ^env
    ``
  end;

fun add_symbolic_register_to_env_8 name env = 
    let 
      val r = generate_symbolic_register_8 name
      val name_hol = fromMLstring name
    in
      (rhs o concl o EVAL)
    `` bir_symb_env_update 
        ^name_hol (BExp_Const (Imm8 ^r)) (BType_Imm Bit8) ^env
    ``
    end;

fun add_symbolic_register_to_env_1 name env = 
    let 
      val r = generate_symbolic_register_1 name
      val name_hol = fromMLstring name
    in
      (rhs o concl o EVAL)
    ``
      bir_symb_env_update
        ^name_hol (BExp_Const  (Imm1 ^r)) (BType_Imm Bit1) ^env
    ``
    end;

fun add_memory_to_env env = 
    let val mem = fromMLstring "MEM"
        val holmem = mk_var ("MEM",Type`:num |-> num`)
  in
    (rhs o concl o EVAL) 
    ``
    bir_symb_env_update 
    ^mem (BExp_MemConst Bit64 Bit8 ^holmem) (BType_Mem Bit64 Bit8) ^env
    ``
  end;


fun add_registers_to_env_64 [] env = env
  | add_registers_to_env_64 (reg :: regs) env = 
        add_registers_to_env_64 regs (add_symbolic_register_to_env_64 reg env)

fun add_registers_to_env_8 [] env = env
  | add_registers_to_env_8 (reg :: regs) env = 
        add_registers_to_env_8 regs (add_symbolic_register_to_env_8 reg env)

fun add_registers_to_env_1 [] env = env
  | add_registers_to_env_1 (reg :: regs) env =
        add_registers_to_env_1 regs (add_symbolic_register_to_env_1 reg env)

fun init_env () = 
    let
      fun regs n = List.tabulate (n, fn x => "R" ^ (Int.toString x))
      (* 64 Bit Registers *)
      val reg_list_64 =
          regs 30;
      (* 1 Bit flags *)
      val reg_list_1  = [
        "ProcState_N", "ProcState_Z",
        "ProcState_C", "ProcState_V" ]
      val e = add_registers_to_env_64 reg_list_64 ``BEnv FEMPTY`` 
    in add_memory_to_env (
          add_registers_to_env_1 reg_list_1 e)
    end;

end (* local *)

end (* struct *)
