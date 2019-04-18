(********************************************************)
(* Functions definied within this file are use to       *)
(* initialize the environment / memory                  *)
(* This is mostly SML -- not HOL definitions!           *)
(********************************************************)

(* 
app load ["bir_symb_envTheory", "bir_symb_execTheory", "stringLib"]
*)

structure bir_symb_init_envLib = 
struct

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
  in
    (rhs o concl o EVAL) 
    ``
    bir_symb_env_update 
    ^mem (BExp_Den (BVar ^mem (BType_Mem Bit64 Bit8))) (BType_Mem Bit64 Bit8) ^env
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
      (* 64 Bit Registers *)
      val reg_list_64 = [
        "R0", "R1", "R2", "R3", "R4", 
        "R5", "R6", "R7", "R8", "R9",
        "R10","R11","R12", "SP_EL0",
        "SP_process", "ADDR"]
      (* 1 Byte registers *)
      val reg_list_8 = [ "VAL" ]
      (* 1 Bit flags *)
      val reg_list_1  = [
        "ProcState_N", "ProcState_Z",
        "ProcState_C", "ProcState_V" ]
    in
      let
        val e = add_registers_to_env_64 reg_list_64 ``BEnv FEMPTY`` 
      in 
        let 
          val ee =  add_registers_to_env_8 reg_list_8 e 
        in add_memory_to_env (
          add_registers_to_env_1 reg_list_1 ee)
        end
      end
    end;
end
