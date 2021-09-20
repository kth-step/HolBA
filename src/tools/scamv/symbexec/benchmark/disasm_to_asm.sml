open HolKernel Parse boolLib bossLib;

open bir_inst_liftingLib;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;
open PPBackEnd Parse;


fun encode_hex (w:int) (n:num) = let
  val s = Arbnum.toHexString n
  val s_len = String.size s
in
  if Int.< (s_len, w) then (String.implode (List.tabulate (Int.- (w, s_len), fn _ => #"0"))^s) else
  if s_len = w then s else
  failwith "invalid input"
end;

open bir_fileLib;

val dafilename = "retonly-aarch64.da";

(*
=============================================================================
*)

val _ = print_with_style_ [Bold, Underline] ("Parsing disasseembly file " ^ dafilename ^ "\n");

val (region_map, aes_sections) = read_disassembly_file_regions dafilename;

val _ = print "\nParsing done.\n\n";

(*
=============================================================================
*)


fun bir_inst_lifting_me_to_asm (BILME_code asm_opt) =
  if isSome asm_opt then valOf asm_opt else raise Fail "SCRIPT: code memory entry has to have a code string"
  | bir_inst_lifting_me_to_asm _ =
      raise Fail "SCRIPT: can only handle code";

fun bir_inst_lifting_mr_to_asm (BILMR (addr, mementries)) =
  let
    val mrlabel = "0x" ^ (encode_hex 8 addr) ^ ":";
    fun foldfun ((_, me), str) =
      str ^ ("\t" ^ (bir_inst_lifting_me_to_asm me) ^ "\n");
    val codelines = List.foldl foldfun "" mementries;
  in mrlabel ^ "\n" ^ codelines end;


fun bir_inst_lifting_to_asm mrl =
  let
    val _ = if (length mrl) = 1 then () else
              raise Fail "SCRIPT: can only handle single memory region/c function";
  in (bir_inst_lifting_mr_to_asm (hd mrl)) ^ "\n" end;


val asmcode = bir_inst_lifting_to_asm aes_sections;

val _ = print asmcode;

val filename = "./" ^ dafilename ^ ".s";

val _ = write_to_file filename asmcode;
