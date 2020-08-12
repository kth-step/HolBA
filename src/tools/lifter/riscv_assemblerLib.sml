structure riscv_assemblerLib :> riscv_assemblerLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

(* Exception for use in this structure. *)
val ERR = mk_HOL_ERR "riscv_assemblerLib";

(* TODO: These should be nested... *)
datatype inst_type =
      (* opcode,  funct3,  funct7 *)
    R of string * string * string
      (* opcode,  funct3 *)
  | I of string * string
  (* TODO: S-type instructions *)
  | UnknownInstType;

datatype inst_args =
           (* rd,      rs1,     rs2 *)
    R_args of string * string * string
           (* rd,      rs1,     imm[11:0] *)
  | I_args of string * string * string
  (* TODO: S-type instructions *)
  | UnknownInstArg
;

(***********************)
(* String manipulation *)
(***********************)

fun to_lowercase char =
  if ((ord char) >= (ord #"A")) andalso ((ord char) <= (ord #"Z"))
  then chr ( (ord char) + ((ord #"a") - (ord #"A")) )
  else char
;

fun to_lowercases str = String.implode (map to_lowercase (String.explode str));

val split_by_comma = String.tokens (fn c => c = #",");

fun remove_whitespaces str =
  String.implode 
    (filter (fn c => c <> #" ") (String.explode str))
;

(* Gets the substring before first whitespace *)
local
  fun split_first_whitespace' [] = ([], [])  
    | split_first_whitespace' (h::t) =
	if Char.isSpace h
        then ([], t)
	else let
               val (l, r) = split_first_whitespace' t
	     in (h::l, r)
	     end
in
fun split_first_whitespace str =
    (fn (a, b) => (String.implode a, String.implode b)) (split_first_whitespace' (String.explode str))
end;

(* Adds leading zeroes to the string str until it reaches length target_length *)
local
  fun generate_zeroes' 0 str = str
    | generate_zeroes' n str = generate_zeroes' (n-1) ("0"^str)

  fun generate_zeroes n = generate_zeroes' n ""
in
fun add_leading_zeroes target_length str =
  let
    val str_len = String.size str
  in
    if str_len >= target_length
    then str
    else ((generate_zeroes (target_length-str_len))^str)
  end
end
;

(********************)
(* Register parsing *)
(********************)

(* Gets a RISC-V GPR as a binary string of length len from
 * a string arg_str.
 * Example: get_bin_reg_arg 5 "x2" = "00010" *)
fun get_bin_reg_arg len arg_str =
  let
    val char_list = String.explode arg_str
    val reg_index_str = String.implode (tl char_list)
    val reg_index_opt = Int.fromString reg_index_str
    val reg_bin_str =
      case reg_index_opt of
        SOME reg_index => Int.fmt StringCvt.BIN reg_index
      | NONE => raise (ERR "get_bin_reg_arg"
		          ("The string "^(reg_index_str)^
		           " could not be parsed to a RISC-V GPR.")
		          )
  in
    add_leading_zeroes len reg_bin_str
  end
;

(*********************)
(* Immediate parsing *)
(*********************)

(* Gets a binary (twos complement) representation of length len
 * of the number (in decimal representation) in the string arg_str *)
local
  fun power b e =
    if e = 0
    then 1
    else b * power b (e-1);
in
fun get_bin_imm_arg len arg_str =
  let
    val scan_res_opt =
      TextIO.scanStream
        (Int.scan StringCvt.DEC)
        (TextIO.openString arg_str)
    val res_int =
      case scan_res_opt of
	SOME i => i
      | NONE   => raise (ERR "get_bin_imm_arg"
		          ("The immediate "^(arg_str)^
		           " could not be read from a decimal representation.")
		          )
    val res_bin =
      let
	val res_bin_prel = (Int.fmt StringCvt.BIN res_int)
      in
	if (size res_bin_prel) <= len
	then res_bin_prel
	else raise (ERR "get_bin_imm_arg"
			("The immediate "^(arg_str)^
			  " was too large to convert to a binary of size "^(Int.toString res_int)^".")
		   )
      end
    val sign_res_str =
      case (substring (res_bin, 0, 1)) of
        "~" => (
          let
            val twos_comp_res_int = ((power 2 len) - 1) + (res_int + 1)
          in
            (add_leading_zeroes len (Int.fmt StringCvt.BIN twos_comp_res_int))
          end
        )
      | _   => (add_leading_zeroes len res_bin)
  in
    if (size sign_res_str) = len
    then sign_res_str
    else raise (ERR "get_bin_imm_arg"
		    ("The immediate "^(arg_str)^
		      " was too large to convert to a binary of size "^(Int.toString res_int)^".")
	       )
  end
end
;

(*********************************)
(* Conversion to datatype format *)
(*********************************)

fun get_inst_type inst_t_str =
  case inst_t_str of
  (* R-type instructions *)
    "add"  => R ("0110011", "000", "0000000")
  | "sub"  => R ("0110011", "000", "0100000")
  | "sll"  => R ("0110011", "001", "0000000")
  | "slt"  => R ("0110011", "010", "0000000")
  | "sltu" => R ("0110011", "011", "0000000")
  | "xor"  => R ("0110011", "100", "0000000")
  | "srl"  => R ("0110011", "101", "0000000")
  | "sra"  => R ("0110011", "101", "0100000")
  | "or"   => R ("0110011", "110", "0000000")
  | "and"  => R ("0110011", "111", "0000000")
  (* I-type instructions *)
  | "addi"   => I ("0010011", "000")
  | "slti"   => I ("0010011", "010")
  | "sltiu"  => I ("0010011", "011")
  | "xori"   => I ("0010011", "100")
  | "ori"    => I ("0010011", "110")
  | "andi"   => I ("0010011", "111")
  | "slli"   => I ("0010011", "001")
  | "srli"   => I ("0010011", "101")
  | "srai"   => I ("0010011", "101")
  (* TODO: S-type instructions *)
  (* Unknown instruction *)
  | _        => UnknownInstType
;

(* Gets a datatype representation of the instruction arguments in args_str, given
 * the instruction type in inst *)
fun get_inst_args inst_t_str inst args_str = 
  let
    val args_clean_list =
      map remove_whitespaces (split_by_comma args_str)
  in
    case inst of
      R (opcode, funct3, funct7) => (
        let
          val reg_args_bin_list = map (get_bin_reg_arg 5) args_clean_list
        in
	  R_args (el 1 reg_args_bin_list,
		  el 2 reg_args_bin_list,
		  el 3 reg_args_bin_list)
        end
      )
    | I (opcode, funct3)         => (
        let
          val reg_args_bin_list = map (get_bin_reg_arg 5) (List.take (args_clean_list, 2))
          val imm_arg_bin = get_bin_imm_arg 12 (el 3 args_clean_list)
        in
          case inst_t_str of
            "slli" =>
              if ((String.substring (imm_arg_bin, 0, 6)) = "000000")
              then I_args (el 1 reg_args_bin_list,
		           el 2 reg_args_bin_list,
		           imm_arg_bin)
              else raise (ERR "get_inst_args"
	                   (imm_arg_bin^" is an invalid immediate value for the SLLI instruction.")
	                 )
          | "srli" =>
              if ((String.substring (imm_arg_bin, 0, 6)) = "000000")
              then I_args (el 1 reg_args_bin_list,
		           el 2 reg_args_bin_list,
		           imm_arg_bin)
              else raise (ERR "get_inst_args"
	                   (imm_arg_bin^" is an invalid immediate value for the SRLI instruction.")
	                 )
          | "srai" =>
              if ((String.substring (imm_arg_bin, 0, 6)) = "010000")
              then I_args (el 1 reg_args_bin_list,
		           el 2 reg_args_bin_list,
		           imm_arg_bin)
              else raise (ERR "get_inst_args"
	                   (imm_arg_bin^" is an invalid immediate value for the SRAI instruction.")
	                 )
          | _ => I_args (el 1 reg_args_bin_list,
		         el 2 reg_args_bin_list,
		         imm_arg_bin)
        end
      )
    | _                          =>
        raise (ERR "get_inst_args"
	        ("The instruction type is unknown.")
	      )
  end
;

(**************************************)
(* Assembly of binary and hex strings *)
(**************************************)

(* Assembles a binary string from a datatype representation of the instruction *)
fun assemble_bin_inst (R (opcode, funct3, funct7))
                      (R_args (rd, rs1, rs2)) =
  (funct7^rs2^rs1^funct3^rd^opcode)
 | assemble_bin_inst (I (opcode, funct3))
                     (I_args (rd, rs1, imm)) =
  (imm^rs1^funct3^rd^opcode)
 | assemble_bin_inst _ _ = raise (ERR "assemble_bin_inst"
	        ("The instruction and/or arguments' type is unknown.")
	      )
;

(* Converts binary string to integer *)
local
fun mul_2 [] = [] |
    mul_2 (h::t) = (h*2)::(mul_2 t)

fun bconv_a [] list = list |
    bconv_a (h::t) list = (bconv_a t (((ord h)-48)::(mul_2 list)))
in
  fun bconv s = foldr (fn (x, y) => x+y) 0 (bconv_a (explode s) [])
end;

(* Gets a hex instruction from a binary string instruction *)
fun get_hex_inst bin_inst =
  add_leading_zeroes 8 (Int.fmt StringCvt.HEX (bconv bin_inst))
;

(*****************)
(* Main function *)
(*****************)

(* Debugging:

   val asm_str = "addi x15,x1,-50"

*)
fun riscv_hex_from_asm asm_str = 
  let
    (* 1. Convert all capital letters to lowercase for easier
     *    matching later on *)
    val lowercase_str = to_lowercases asm_str

    (* 2. Get the instruction from the string (add, sub, jal, ...) *)
    val (inst_t_str, args_str) = split_first_whitespace lowercase_str

    (* 3. Get datatype representations of static instruction parts
     *    as well as arguments *)
    val inst = get_inst_type inst_t_str
    val args = get_inst_args inst_t_str inst args_str

    (* 4. Assemble a binary string from the datatype
     *    representations *)
    val bin_inst = assemble_bin_inst inst args

    (* 5. Get the hexcode of the bit string *)
    val hex_inst = get_hex_inst bin_inst

  in
    hex_inst
  end
;

end
