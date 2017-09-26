open HolKernel Parse
open testutils

open bir_inst_liftingLib;
open bmil_arm8
open PPBackEnd Parse

(* Tests for ARM 8 *)

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

(* For manual
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
*)

fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)

(*

val mu_b = Arbnum.fromInt 0;
val mu_e = Arbnum.fromInt 0x1000000;
val pc = Arbnum.fromInt 0x10030;
val hex_code = "12001C00"

*)

fun lift_instr mu_b mu_e pc hex_code = let
  val _ = print (hex_code ^ " @ 0x" ^ (Arbnum.toHexString pc));
  val timer = (Time.now())
  val (res, ed) = (SOME (bir_lift_instr (mu_b, mu_e) pc hex_code), NONE) handle
                   bir_inst_liftingExn (_, d)  => (NONE, SOME d)
                 | HOL_ERR _ => (NONE, NONE);

  val d_time = Time.- (Time.now(), timer);
  val d_s = (Time.toString d_time);


  val _ = print (" - " ^ d_s ^ " s - ");
  val _ = if is_some res then
             print_with_style [FG Green] "OK\n"
          else
             (print_with_style [FG OrangeRed] "FAILED\n");
  val _ = case ed of
      NONE => ()
    | SOME d => (let
        val s = ("   "^(bir_inst_liftingExn_data_to_string d) ^ "\n");
      in print_with_style [FG OrangeRed] s end)
in
  (res, ed, d_s)
end;

fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)

fun lift_instr_asm mu_b mu_e pc asm =
  lift_instr mu_b mu_e pc (hex_code_of_asm asm);



(* SOME MANUAL TESTS *)
val mu_b = Arbnum.fromInt 0;
val mu_e = Arbnum.fromInt 0x1000000;
val pc = Arbnum.fromInt 0x10030;
val test_asm = lift_instr_asm mu_b mu_e pc

val _ = print_with_style [Bold, Underline] "\n\n\nMANUAL TESTS\n\n";
val _ = test_asm `add x0, x1, x2`;
val _ = test_asm `add x1, x1, x1`;
val _ = test_asm `adds x0, x1, x2`;
val _ = test_asm `add x0, x0, x2`;
val _ = test_asm `sub x0, x1, x2`;
val _ = test_asm `mul x0, x1, x2`;
val _ = test_asm `mul w0, w1, w1`;
val _ = test_asm `cmp w0, #0`;
val _ = test_asm `cmn w0, #0`;
val _ = test_asm `cmn w0, w1`;
val _ = test_asm `cmn x0, x9`;
val _ = test_asm `ret`;
val _ = test_asm `adds x0, x2, #8`;
val _ = test_asm `subs x0, x2, #8`;
val _ = test_asm `adds x0, x1, x2`;
val _ = test_asm `add x0, x0, x2`;
val _ = test_asm `sub x0, x1, x2`;
val _ = test_asm `add x4, SP, #8`;
val _ = test_asm `add x4, SP, #8`;
val _ = test_asm `adds x1, x1, #0`;
val res = test_asm `lsr x1, x2, #5`;
val res = test_asm `lsr x1, x2, #0`;
val res = test_asm `lsr x1, x1, #0`;
val res = test_asm `lsr x1, x2, x3`;
val res = test_asm `lsl x1, x2, #5`;
val res = test_asm `lsl x1, x2, #0`;
val res = test_asm `lsl x1, x1, #0`;
val res = test_asm `lsl x1, x2, x3`;
val res = test_asm `asr x1, x2, #5`;
val res = test_asm `asr x1, x2, #0`;
val res = test_asm `asr x1, x1, #0`;
val res = test_asm `asr x1, x2, x3`;
val _ = test_asm `ldr x0, [x2, #0]`;

  (* THERE ARE STILL MANY TODOs !!! *)
val _ = test_asm `lsl x0, x2, #8`;
val _ = test_asm `lsr x0, x2, #8`;
val _ = test_asm `str x0, [x2, #8]`;



(* And a list version *)

fun lift_instr_list mu_b mu_e pc hex_codes = let
  val timer = (Time.now())
  val len_codes = (length hex_codes);

  val _ = print ("running " ^ (Int.toString (len_codes)) ^ " instrutions; first pc 0x" ^
              (Arbnum.toHexString pc) ^ "\n\n");

  fun run_inst (i, (c, pc, res)) = let
    val _ = print ((Int.toString c) ^ "/" ^ (Int.toString (length hex_codes)) ^ ": ");
    val r = lift_instr mu_b mu_e pc i
    val c' = c+1;
    val pc' = Arbnum.+ (pc, Arbnum.fromInt 8);
  in (c+1, pc', r::res) end

  val (_, _, resL) = foldl run_inst (1, pc, []) hex_codes

  val d_time = Time.- (Time.now(), timer);
  val d_s = (Time.toString d_time);
  val success_c = foldl (fn ((res, _, _), c) =>
       if (is_some res) then c+1 else c) 0 resL
  val fail_c = len_codes - success_c

  val _ = print "\n";
  val _ = print ("Instructions OK    : " ^ (Int.toString success_c) ^ "\n");
  val _ = print ("Instructions FAILED: " ^ (Int.toString fail_c) ^ "\n");

  val _ = print ("Time needed        : " ^ d_s ^ " s\n\n");
in
  (fail_c, success_c, resL)
end




(* Test it with the instructions from aes example *)
val instrs = [
  "D101C3FF","F9000FE0","B90017E1","F90007E2","F90003E3","B94017E0","51000400",
  "B9004FE0","F94007E0","B9400000","B9002FE0","F94007E0","B9400400","B90033E0",
  "F94007E0","B9400800","B90037E0","F94007E0","B9400C00","B9003BE0","F9400FE0",
  "B9400000","B9402FE1","4A000020","B9002FE0","F9400FE0","91001000","B9400000",
  "B94033E1","4A000020","B90033E0","F9400FE0","91002000","B9400000","B94037E1",
  "4A000020","B90037E0","F9400FE0","91003000","B9400000","B9403BE1","4A000020",
  "B9003BE0","F9400FE0","91004000","F9000FE0","140000E6","B9402FE0","53187C00",
  "B90053E0","B94033E0","53107C00","12001C00","B90057E0","B94037E0","53087C00",
  "12001C00","B9005BE0","B9403BE0","12001C00","B9005FE0","B94053E0","D37EF401",
  "90000000","91394000","8B000020","B9400000","B90063E0","B94057E0","D37EF401",
  "B0000000","91094000","8B000020","B9400000","B90067E0","B9405BE0","D37EF401",
  "B0000000","91194000","8B000020","B9400000","B9006BE0","B9405FE0","D37EF401",
  "B0000000","91294000","8B000020","B9400000","B9006FE0","B94063E1","B94067E0",
  "4A000021","B9406BE0","4A000021","B9406FE0","4A000021","F9400FE0","B9400000",
  "4A000020","B9003FE0","B94033E0","53187C00","B90053E0","B94037E0","53107C00",
  "12001C00","B90057E0","B9403BE0","53087C00","12001C00","B9005BE0","B9402FE0",
  "12001C00","B9005FE0","B94053E0","D37EF401","90000000","91394000","8B000020",
  "B9400000","B90063E0","B94057E0","D37EF401","B0000000","91094000","8B000020",
  "B9400000","B90067E0","B9405BE0","D37EF401","B0000000","91194000","8B000020",
  "B9400000","B9006BE0","B9405FE0","D37EF401","B0000000","91294000","8B000020",
  "B9400000","B9006FE0","B94063E1","B94067E0","4A000021","B9406BE0","4A000021",
  "B9406FE0","4A000021","F9400FE0","91001000","B9400000","4A000020","B90043E0",
  "B94037E0","53187C00","B90053E0","B9403BE0","53107C00","12001C00","B90057E0",
  "B9402FE0","53087C00","12001C00","B9005BE0","B94033E0","12001C00","B9005FE0",
  "B94053E0","D37EF401","90000000","91394000","8B000020","B9400000","B90063E0",
  "B94057E0","D37EF401","B0000000","91094000","8B000020","B9400000","B90067E0",
  "B9405BE0","D37EF401","B0000000","91194000","8B000020","B9400000","B9006BE0",
  "B9405FE0","D37EF401","B0000000","91294000","8B000020","B9400000","B9006FE0",
  "B94063E1","B94067E0","4A000021","B9406BE0","4A000021","B9406FE0","4A000021",
  "F9400FE0","91002000","B9400000","4A000020","B90047E0","B9403BE0","53187C00",
  "B90053E0","B9402FE0","53107C00","12001C00","B90057E0","B94033E0","53087C00",
  "12001C00","B9005BE0","B94037E0","12001C00","B9005FE0","B94053E0","D37EF401",
  "90000000","91394000","8B000020","B9400000","B90063E0","B94057E0","D37EF401",
  "B0000000","91094000","8B000020","B9400000","B90067E0","B9405BE0","D37EF401",
  "B0000000","91194000","8B000020","B9400000","B9006BE0","B9405FE0","D37EF401",
  "B0000000","91294000","8B000020","B9400000","B9006FE0","B94063E1","B94067E0",
  "4A000021","B9406BE0","4A000021","B9406FE0","4A000021","F9400FE0","91003000",
  "B9400000","4A000020","B9004BE0","B9403FE0","B9002FE0","B94043E0","B90033E0",
  "B94047E0","B90037E0","B9404BE0","B9003BE0","F9400FE0","91004000","F9000FE0",
  "B9404FE0","51000400","B9004FE0","B9404FE0","7100001F","54FFE321","B9403FE0",
  "53187C00","B90053E0","B94043E0","53107C00","12001C00","B90057E0","B94047E0",
  "53087C00","12001C00","B9005BE0","B9404BE0","12001C00","B9005FE0","B94053E0",
  "D37EF401","B0000000","91194000","8B000020","B9400000","B90063E0","B94057E0",
  "D37EF401","B0000000","91294000","8B000020","B9400000","B90067E0","B9405BE0",
  "D37EF401","90000000","91394000","8B000020","B9400000","B9006BE0","B9405FE0",
  "D37EF401","B0000000","91094000","8B000020","B9400000","B9006FE0","B94063E0",
  "12081C01","B94067E0","12101C00","4A000021","B9406BE0","12181C00","4A000021",
  "B9406FE0","12001C00","4A000021","F9400FE0","B9400000","4A000020","B9002FE0",
  "B94043E0","53187C00","B90053E0","B94047E0","53107C00","12001C00","B90057E0",
  "B9404BE0","53087C00","12001C00","B9005BE0","B9403FE0","12001C00","B9005FE0",
  "B94053E0","D37EF401","B0000000","91194000","8B000020","B9400000","B90063E0",
  "B94057E0","D37EF401","B0000000","91294000","8B000020","B9400000","B90067E0",
  "B9405BE0","D37EF401","90000000","91394000","8B000020","B9400000","B9006BE0",
  "B9405FE0","D37EF401","B0000000","91094000","8B000020","B9400000","B9006FE0",
  "B94063E0","12081C01","B94067E0","12101C00","4A000021","B9406BE0","12181C00",
  "4A000021","B9406FE0","12001C00","4A000021","F9400FE0","91001000","B9400000",
  "4A000020","B90033E0","B94047E0","53187C00","B90053E0","B9404BE0","53107C00",
  "12001C00","B90057E0","B9403FE0","53087C00","12001C00","B9005BE0","B94043E0",
  "12001C00","B9005FE0","B94053E0","D37EF401","B0000000","91194000","8B000020",
  "B9400000","B90063E0","B94057E0","D37EF401","B0000000","91294000","8B000020",
  "B9400000","B90067E0","B9405BE0","D37EF401","90000000","91394000","8B000020",
  "B9400000","B9006BE0","B9405FE0","D37EF401","B0000000","91094000","8B000020",
  "B9400000","B9006FE0","B94063E0","12081C01","B94067E0","12101C00","4A000021",
  "B9406BE0","12181C00","4A000021","B9406FE0","12001C00","4A000021","F9400FE0",
  "91002000","B9400000","4A000020","B90037E0","B9404BE0","53187C00","B90053E0",
  "B9403FE0","53107C00","12001C00","B90057E0","B94043E0","53087C00","12001C00",
  "B9005BE0","B94047E0","12001C00","B9005FE0","B94053E0","D37EF401","B0000000",
  "91194000","8B000020","B9400000","B90063E0","B94057E0","D37EF401","B0000000",
  "91294000","8B000020","B9400000","B90067E0","B9405BE0","D37EF401","90000000",
  "91394000","8B000020","B9400000","B9006BE0","B9405FE0","D37EF401","B0000000",
  "91094000","8B000020","B9400000","B9006FE0","B94063E0","12081C01","B94067E0",
  "12101C00","4A000021","B9406BE0","12181C00","4A000021","B9406FE0","12001C00",
  "4A000021","F9400FE0","91003000","B9400000","4A000020","B9003BE0","F94003E0",
  "B9402FE1","B9000001","F94003E0","91001000","B94033E1","B9000001","F94003E0",
  "91002000","B94037E1","B9000001","F94003E0","91003000","B9403BE1","B9000001",
  "D503201F","9101C3FF","D65F03C0"
];


val _ = print_with_style [Bold, Underline] "\n\n\nTESTING AES CODE\n\n";
val _ = lift_instr_list (Arbnum.fromInt 0) (Arbnum.fromInt 0x1000000) (Arbnum.fromInt 0x400570)
    (Lib.mk_set instrs)
