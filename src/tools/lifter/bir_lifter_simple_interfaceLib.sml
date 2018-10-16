
open bir_inst_liftingLib;
open gcc_supportLib;


structure bir_lifter_simple_interfaceLib =
struct



val log_filename = "benchmark.log";
val log = TextIO.openOut log_filename;

fun print_log_with_style sty f s = let
  val _ = if f then TextIO.output (log, s) else ();
  val _ = print_with_style sty s;
in () end;

val print_log = print_log_with_style [];
val print_l = print_log true;


(* error printing function *)
fun err_to_str disassemble_fun ((err_pc, err_inst, err_inst_desc, err_descr):bir_inst_error) =
  let
    fun asm_of_hex_code_fun code = hd (disassemble_fun [QUOTE code]);
    val err_str = (
             case err_descr of
                 SOME x => bir_inst_liftingExn_data_to_string x
               | NONE => "??? no error description ???"
      );
  in
    (err_inst ^ (" (" ^ err_inst ^ "; " ^ err_inst_desc ^ ")  @ 0x" ^ (Arbnum.toHexString err_pc)) ^ "\r\n\t" ^ err_str)
  end;



(* generic lifting call *)
fun disassembly_section_to_minmax section =
  case section of
      BILMR(addr_start, entries) =>
        let
          val data_strs = List.map fst entries;
	  (* val _ = List.map (fn x => print (x ^ "\r\n")) data_strs; *)
          val lengths_st = List.map String.size data_strs;
          val _ = List.map (fn x => ()) lengths_st;
          val lengths = List.map (fn x => Arbnum.fromInt (x div 2)) lengths_st;
          val length = List.foldr (Arbnum.+) Arbnum.zero lengths;
        in
          (addr_start, Arbnum.+(addr_start, length))
        end;

fun minmax_fromlist ls = List.foldl (fn ((min_1,max_1),(min_2,max_2)) =>
  ((if Arbnum.<(min_1, min_2) then min_1 else min_2),
   (if Arbnum.>(max_1, max_2) then max_1 else max_2))
  ) (hd ls) (tl ls);

fun da_sections_minmax sections = minmax_fromlist (List.map disassembly_section_to_minmax sections);


fun arch_str_to_funs arch_str = case arch_str of
            "arm8" => (bmil_arm8.bir_lift_prog_gen, arm8AssemblerLib.arm8_disassemble)
          | "m0"   => (bmil_m0_LittleEnd_Process.bir_lift_prog_gen, m0AssemblerLib.m0_disassemble)
          | _      => raise (ERR "arch_str_to_funs" ("architecture \"" ^ arch_str ^ "\" unknown"))
        ;


fun lift_file arch_str da_file =
  let
    val (bmil_bir_lift_prog_gen, disassemble_fun) = arch_str_to_funs arch_str

    val _ = print_log_with_style [Bold, Underline] true ("Lifting \""^da_file^"\" ("^arch_str^")\n");

    val (region_map, sections) = read_disassembly_file_regions da_file;

    (* TODO: calculate instruction number *)

    (*
    (* predefined program range *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
    (* max for arm8 *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFFFFFFFFFF));
    (* max for m0 *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFF));
    (* max for prog *)
    *)
    val prog_range = da_sections_minmax sections;

    val timer = (Time.now());

    val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;

    (* TODO: sum up bir blocks and bir statements in thm_prog *)

    val d_time = Time.- (Time.now(), timer);
    val d_s = (Time.toString d_time);
    val _ = print_l ("time_to_lift = " ^ d_s ^ " s\n\n\n");

    (* print out only the failing instructions *)
    val _ = if errors <> [] then
      let
        val _ = print_l "\n\n";
        val _ = print_log_with_style [Bold, Underline] true ("There are " ^ (Int.toString (length errors)) ^ " failing instruction(s)\n");
        val _ = print_with_style [Bold, Underline] "Failing instructions\n";
        val _ = List.foldl (fn (x, ()) => print ((err_to_str disassemble_fun x) ^ "\n")) () errors;
      in
        ()
      end else ();
  in
    thm_prog
  end;

(*
val da_file = "binaries/bzip2-1.0.6/aarch64-libbz2-emptymain.da";
val da_file = "binaries/aes-aarch64.da";
val da_file = "binaries/bignum/aarch64-bignum-emptymain.da";

val arch_str = "arm8";
val _ = lift_file arch_str da_file;

val da_file = "binaries/bzip2-1.0.6/m0-libbz2-emptymain.da";
val da_file = "binaries/bignum/m0-bignum-emptymain.da";

val arch_str = "m0";
val _ = lift_file arch_str da_file;
*)






fun gen_sections disassemble_fun (pc:Arbnum.num) (inst:string) =
  let
    fun asm_of_hex_code_fun code = hd (disassemble_fun [QUOTE code]);
  in
    [BILMR (pc, [(inst, BILME_code (SOME (asm_of_hex_code_fun inst)))])]
  end;

fun lift_inst arch_str (pc:Arbnum.num) (inst:string) =
  let
    val (bmil_bir_lift_prog_gen, disassemble_fun) = arch_str_to_funs arch_str
(*
    val pc = (Arbnum.fromInt 0xCFEE);
    val inst = "4770";
*)
    val sections = gen_sections disassemble_fun pc inst;
    val prog_range = da_sections_minmax sections;
    val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;
  in
    thm_prog
  end;

(*
val arch_str = "arm8";
val thm_prog = lift_inst arch_str (Arbnum.fromInt 0x40C2A4) ("78206A61");

val arch_str = "m0";
val thm_prog = lift_inst arch_str (Arbnum.fromInt 0xCFEE) ("4770");
*)




end

