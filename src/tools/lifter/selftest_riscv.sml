open HolKernel Parse
open testutils
open bir_inst_liftingLib;
open PPBackEnd

val unicode = false;
val raw_output = false;

val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else
                                     PPBackEnd.vt100_terminal);
val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)

val log = TextIO.openOut "riscv_selftest.log";


(**************************)
(* Testing infrastructure *)
(**************************)

(* style for success, fail and header *)
val sty_OK     = [FG Green];
val sty_CACHE  = [FG Yellow];
val sty_FAIL   = [FG OrangeRed];
val sty_HEADER = [Bold, Underline];

fun print_log_with_style sty f s = let
  val _ = if f then TextIO.output (log, s) else ();
  val _ = print_with_style_ sty s;
in () end;

fun print_log s = print_log_with_style [] s;


functor test_bmr (MD : bir_inst_lifting) = struct

(* TODO: This gives error... *)
open MD;

val failed_hexcodes_list = ref ([]:(string * string option * bir_inst_liftingExn_data option) list);
val success_hexcodes_list = ref ([]: (string * string option * thm) list);
(* For debugging:

  val log_f = true;
  val mu_be = (Arbnum.fromInt 0, Arbnum.fromInt 0x1000000);
  val mu_thms = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  val cache = test_RISCV.lift_inst_cache_empty
  val pc =   Arbnum.fromInt 0x10030;
  val hex_code = "007302B3";
  val desc = (NONE:string option);

*)
fun lift_instr_cached log_f mu_be mu_thms cache pc hex_code desc = let
  val hex_code = String.map Char.toUpper hex_code
  val _ = print_log log_f hex_code;
  val d' = case desc of
            NONE => hex_code
          | SOME d => (print_log log_f (" (" ^ d ^")"); d)
  val _ = print_log log_f (" @ 0x" ^ (Arbnum.toHexString pc));
  val timer = (Time.now())
  (* TODO: The below returns an exception. Keep debugging inside bir_lift_instr_mu mu_be mu_thms *)
(*

  val (res, ed) = (SOME (test_RISCV.bir_lift_instr_mu mu_be mu_thms cache pc hex_code d'), NONE) handle
                   bir_inst_liftingExn (_, d)  => (NONE, SOME d)
                 | HOL_ERR _ => (NONE, NONE);

*)
  val (res, ed) = (SOME (bir_lift_instr_mu mu_be mu_thms cache pc hex_code d'), NONE) handle
                   bir_inst_liftingExn (_, d)  => (NONE, SOME d)
                 | HOL_ERR _ => (NONE, NONE);

  val d_time = Time.- (Time.now(), timer);
  val d_s = (Time.toString d_time);

  val _ = print_log log_f (" - ");
  val _ = print (d_s ^ " s - ");
  val (res', cache') = case res of
             SOME (thm, cache', _) => ((SOME thm), cache')
           | NONE => (NONE, cache)
  val _ = case res of
             SOME (thm, _, cache_used) =>
                 (success_hexcodes_list := (hex_code, desc, thm)::(!success_hexcodes_list);
                 (print_log_with_style sty_OK log_f "OK");
                 (if cache_used then (print_log log_f " - "; print_log_with_style sty_CACHE log_f "cached") else ());
                 (print_log log_f "\n");
                 (if log_f then ((TextIO.output (log, thm_to_string thm));
                                 (TextIO.output (log, "\n"))) else ()))
           | NONE =>
             (failed_hexcodes_list := (hex_code, desc, ed)::(!failed_hexcodes_list);
             (print_log_with_style sty_FAIL log_f "FAILED\n"));
  val _ = case ed of
      NONE => ()
    | SOME d => (let
        val s = ("   "^(bir_inst_liftingExn_data_to_string d) ^ "\n");
      in print_log_with_style sty_FAIL log_f s end)
  val _ = if log_f then TextIO.output (log, "\n") else ();
in
  (res', ed, d_s, cache')
end;

(* For debugging:
val mu_b = Arbnum.fromInt 0;
val mu_e = Arbnum.fromInt 0x1000000;
val pc =   Arbnum.fromInt 0x10030;
val hex_code = "007302B3";
val desc = (NONE:string option);
*)
fun lift_instr mu_b mu_e pc hex_code desc = let
  (* Debug:
       val mu_thms = test_RISCV.bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  *)
  val mu_thms = bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
  (* Debug:
       val lift_inst_cache_empty = test_RISCV.lift_inst_cache_empty

       (* ERROR HERE!
          Continue on line 41, in definition of "lift_instr_cached"
        *)
       val (res, ed, d_s, _) =
         test_RISCV.lift_instr_cached true (mu_b, mu_e) mu_thms lift_inst_cache_empty pc hex_code desc
  *)
  val (res, ed, d_s, _) = lift_instr_cached true (mu_b, mu_e) mu_thms lift_inst_cache_empty pc hex_code desc
in
  (res, ed, d_s)
end;


(* And a list version *)

fun lift_instr_list mu_b mu_e pc hex_codes = let
  val timer = (Time.now())
  val len_codes = (length hex_codes);

  val _ = print ("running " ^ (Int.toString (len_codes)) ^ " instrutions; first pc 0x" ^
              (Arbnum.toHexString pc) ^ "\n\n");

  val mu_thms = bir_lift_instr_prepare_mu_thms (mu_b, mu_e)

  fun run_inst (i, (c, pc, res, cache)) = let
    val _ = print ((Int.toString c) ^ "/" ^ (Int.toString (length hex_codes)) ^ ": ");
    val (r', ed, d_s, cache') = lift_instr_cached false (mu_b, mu_e) mu_thms cache pc i NONE
    val c' = c+1;
    val pc' = Arbnum.+ (pc, (#bmr_hex_code_size mr) i);
    val r = (r', ed, d_s);
  in (c+1, pc', r::res, cache') end

  val (_, _, resL, _) = foldl run_inst (1, pc, [], lift_inst_cache_empty) hex_codes

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
end;


fun final_results name expected_failed_hexcodes = let
  val _ = print_log_with_style sty_HEADER true ("\n\n\nSUMMARY FAILING HEXCODES " ^ name ^ "\n\n");
  val _ = print_log true "\n";
  val failing_l = op_mk_set (fn (x, _, _) => fn (y, _, _) => (x = y)) (!failed_hexcodes_list)
  val ok_l = op_mk_set (fn (x, _, _) => fn (y, _, _) => (x = y)) (!success_hexcodes_list)

  (* look for freshly failing ones *)
  val failing_l' = map (fn (hc, d, edo) =>
     (hc, d, edo, not (Lib.mem hc expected_failed_hexcodes))) failing_l;
  val fixed_l = List.filter (fn hc => List.exists (fn (e, _, _) => e = hc) ok_l) expected_failed_hexcodes

  (* Show all failing instructions and format them such that they can be copied
     in the code of selftest.sml
     as content of list expected_failed_hexcodes *)
  val _ = print_log true ("Instructions FAILED: " ^ (Int.toString (length failing_l)) ^ "/" ^
         (Int.toString (length failing_l + length ok_l)) ^ "\n\n");

  fun comment_of_failing desc ed_opt =
    case (desc, ed_opt) of
         (NONE, NONE) => ""
       | (SOME d, NONE) => (" (* " ^ d ^ " *)")
       | (NONE, SOME d') => (" (* " ^ (bir_inst_liftingExn_data_to_string d') ^ " *)")
       | (SOME d, SOME d') => (" (* " ^ d ^ "; "^(bir_inst_liftingExn_data_to_string d')  ^ " *)");

  fun print_failed [] = ()
    | print_failed ((hex_code, desc, ed_opt, broken)::l) =
  let
    (* print the ones that failed, but were not excepted to in red *)
    val st = if broken then sty_FAIL else [];
    val _ = print_log true "   ";
    val _ = print_log_with_style st true ("\""^hex_code^"\"");

    val _ = print_log_with_style st true (comment_of_failing desc ed_opt)

  in if List.null l then (print_log true "\n]\n\n") else
         (print_log true ",\n"; print_failed l)
  end;
  val _ = if List.null failing_l' then () else (print "[\n"; print_failed failing_l');


  (* Show the hex-codes that were expected to fail, but succeeded. These
     are the ones fixed by recent changes. *)
  val _ = print_log true ("Instructions FIXED: " ^ (Int.toString (length fixed_l)) ^ "\n\n");
  val _ = List.map (fn s => print_log_with_style sty_OK true ("   " ^ s ^"\n")) fixed_l;
  val _ = print_log true "\n\n";

  (* Show the hex-codes that were expected to succeed, but failed. These
     are the ones broken by recent changes. *)
  val broken_l = List.filter (fn (hc, d, edo, br) => br) failing_l';
  val _ = print_log true ("Instructions BROKEN: " ^ (Int.toString (List.length broken_l)) ^ "\n\n");
  val _ = List.map (fn (hc, desc, ed_opt, _) => print_log_with_style sty_FAIL true ("   " ^ hc ^
       (comment_of_failing desc ed_opt) ^ "\n")) broken_l;
  val _ = print_log true "\n\n";

in
  ()
end;
end;


structure test_RISCV = test_bmr(bmil_riscv);
(* In order to use the below, we need a RISC-V assembler *)
(*
fun riscv_hex_code_of_asm asm = hd (riscvAssemblerLib.riscv_code [QUOTE asm])
fun riscv_lift_instr_asm mu_b mu_e pc asm =
  test_RISCV.lift_instr mu_b mu_e pc (riscv_hex_code_of_asm asm) (SOME asm);
*)


(* TODO: Double-check these numbers are OK, should work with arbitrary ones though *)
val mu_b = Arbnum.fromInt 0;
val mu_e = Arbnum.fromInt 0x1000000;
val pc =   Arbnum.fromInt 0x10030;

(* TODO: Pending addition of RISC-V disassembler
val riscv_test_asm = riscv_lift_instr_asm mu_b mu_e pc
*)
fun riscv_test_hex hex = test_RISCV.lift_instr mu_b mu_e pc hex NONE

val res = print_log_with_style sty_HEADER true "\nMANUAL TESTS (HEX) - RISC-V\n\n";
(* Good presentation of RISC-V instructions at https://inst.eecs.berkeley.edu/~cs61c/sp19/lectures/lec05.pdf *)
(* R-format *)
val res = riscv_test_hex "007302B3"; (* OK: "add x5, x6, x7" *)

(* I-format *)
val res = riscv_test_hex "FCE08793"; (* OK: "addi x15,x1,-50" *)

(* S-format *)
(* String widths:
 * 000: byte
 * 001: halfword
 * 010: word
 * 011: doubleword *)
(* TODO: Should work pending fixing the lifter to be able to store 32-bits of 64-bit registers... *)
val res = riscv_test_hex "00E12423"; (* "sw x14, 8(x2)" *)
(* Should only work in 64-bit mode *)
val res = riscv_test_hex "00E13423"; (* OK: "sd x14, 8(x2)" *)

(* B-format *)
val res = riscv_test_hex "00A98863"; (* "beq x19, x10, offset = 16 bytes" *)

(* U-format *)
val res = riscv_test_hex "0DEAD537"; (* OK: "lui x10, 0xDEAD" *)

(* J-format *)
val res = riscv_test_hex "0000006F"; (* "jal x0, 0x0" *)
