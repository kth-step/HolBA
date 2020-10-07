structure bir_lifter_interfaceLib =
struct

local

open HolKernel Parse;
open bir_inst_liftingLib;
open gcc_supportLib;

in

(* Debug values:
  val da_name = "../1-code/src/add_reg.da"
  val prog_name = "add_reg"
  val prog_name = "arm8"
  val prog_interval = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  val bmil = bmil_arm8
*)

val ERR = mk_HOL_ERR "bir_lifter_interfaceLib"

fun choose_isa_lift_fun isa_name =
  case isa_name of
    "arm8" => bmil_arm8.bir_lift_prog_gen
  | "riscv" => bmil_riscv.bir_lift_prog_gen
  | _ => Raise (ERR "lift_da_and_store" ("Unknown ISA: "^isa_name))
;

fun lift_da_and_store prog_name da_name isa_name prog_interval =
  let
    val _ = print_with_style_ [Bold, Underline] ("Lifting "^da_name^"\n");

    val (region_map, aes_sections) = read_disassembly_file_regions da_name

    val (thm_lifted, errors) = (choose_isa_lift_fun isa_name)
			       prog_interval
			       aes_sections

    val (lift_app_1_tm, bir_prog_tm) = (dest_comb o concl) thm_lifted;
    val (_, bir_progbin_tm) = dest_comb lift_app_1_tm;

    val _ = print "\n\n";

    (* now save the definitions *)
    val bir_x_prog_var = mk_var("bir_"^prog_name^"_prog", type_of bir_prog_tm)
    val bir_x_prog_def = Define `^bir_x_prog_var = ^bir_prog_tm`;
    val bir_x_progbin_var = mk_var("bir_"^prog_name^"_progbin", type_of bir_progbin_tm)
    val bir_x_progbin_def = Define `^bir_x_progbin_var = ^bir_progbin_tm`;

    (* now save the lifter theorem using the definitions *)
    val bir_x_isa_lift_THM = save_thm ("bir_"^prog_name^"_"^isa_name^"_lift_THM",
	   REWRITE_RULE [GSYM bir_x_prog_def,
			 GSYM bir_x_progbin_def] thm_lifted);
  in
    ()
  end;

end

end
