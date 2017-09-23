(* The main structure provided by bir_inst_liftingLib is
   "bir_inst_lifting". It contains functions for lifting machine
   instructions and whole programs to bir programs.

   A module with this signature is provided for multiple architectures. *)

signature bir_inst_lifting = sig

  (* bir_inst_lifting (mem_unchanged_begin, mem_unchanged_end) pc hexcode

     tries to lift the given hexcode. It assumes this code is stored at location
     of "pc" in memory and tries to guarentee that the memory adresses in
     interval [mem_unchanged_begin, mem_unchanged_end) are not changed. *)
  val bir_lift_instr : (Arbnum.num * Arbnum.num) -> Arbnum.num -> string -> Abbrev.thm

end

(* Instances for different machine types *)
signature bir_inst_liftingLib = sig

  (* Errors are reported via the exception bir_inst_liftingExn (hex_code, reason)
     which indicates that lifting of the given hex-code failed for the given reason. *)
  datatype bir_inst_liftingExn_data =
     BILED_msg of string
   | BILED_msg_term of string * Abbrev.term
   | BILED_lifting_failed of Abbrev.term

  exception bir_inst_liftingExn of string * bir_inst_liftingExn_data;


  (* ARM 8 instance *)
  structure bmil_arm8 : bir_inst_lifting;

end


(* Tests for ARM 8

   open bir_inst_liftingLib;
   open bmil_arm8

   fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)

   val mu_b = Arbnum.fromInt 0;
   val mu_e = Arbnum.fromInt 0x100000;
   val pc = Arbnum.fromInt 0x10000;

   fun lift_instr hex_code = let
      val timer = (Time.now())
      val thm = bir_lift_instr (mu_b, mu_e) pc hex_code
      val d_time = Time.- (Time.now(), timer);
      val d_s = (Time.toString d_time);
   in
     (thm, d_s)
   end;

   fun lift_instr_asm asm =
     lift_instr (hex_code_of_asm asm)

   val (res, time) = lift_instr_asm `add x0, x1, x2`;
   val (res, time) = lift_instr_asm `adds x0, x1, x2`;
   val (res, time) = lift_instr_asm `add x0, x0, x2`;
   val (res, time) = lift_instr_asm `sub x0, x1, x2`;
   val (res, time) = lift_instr_asm `mul x0, x1, x2`;
   val (res, time) = lift_instr_asm `mul w0, w1, w1`;
   val (res, time) = lift_instr_asm `cmp w0, #0`;
   val (res, time) = lift_instr_asm `cmn w0, #0`;
   val (res, time) = lift_instr_asm `cmn w0, w1`;
   val (res, time) = lift_instr_asm `cmn x0, x9`;
   val (res, time) = lift_instr_asm `adds x0, x2, #8`;
   val (res, time) = lift_instr_asm `subs x0, x2, #8`;

   (* THERE ARE STILL MANY TODOs !!! *)
   val (res, time) = lift_instr_asm `lsl x0, x2, #8`;
   val (res, time) = lift_instr_asm `ldr x0, [x2, #8]`;
   val (res, time) = lift_instr_asm `str x0, [x2, #8]`;
*)
