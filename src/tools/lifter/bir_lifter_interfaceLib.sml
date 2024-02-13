structure bir_lifter_interfaceLib :> bir_lifter_interfaceLib =
struct

datatype da_isa =
  da_arm8
| da_riscv

local


(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_extra_expsTheory
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
open PPBackEnd Parse

open bir_inst_liftingHelpersLib;
(* ================================================ *)

open HolKernel Parse;
open bir_inst_liftingLib;
open gcc_supportLib;

in

(* Debug values:
  val da_name = "../1-code/src/add_reg.da"
  val prog_name = "add_reg"
  val prog_interval = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
*)
fun lift_da_and_store prog_name da_name da_isa prog_interval =
  let
    val _ = print_with_style_ [Bold, Underline] ("Lifting "^da_name^"\n");

    val (region_map, aes_sections) = read_disassembly_file_regions da_name

    val (thm_riscv, errors) = bmil_riscv.bir_lift_prog_gen
			       prog_interval
			       aes_sections

    val (lift_app_1_tm, bir_prog_tm) = (dest_comb o concl) thm_riscv;
    val (_, bir_progbin_tm) = dest_comb lift_app_1_tm;

    val _ = print "\n\n";

    (* now save the definitions *)
    val bir_x_prog_var = mk_var("bir_"^prog_name^"_prog", type_of bir_prog_tm)
    val bir_x_prog_def = Define `^bir_x_prog_var = ^bir_prog_tm`;
    val bir_x_progbin_var = mk_var("bir_"^prog_name^"_progbin", type_of bir_progbin_tm)
    val bir_x_progbin_def = Define `^bir_x_progbin_var = ^bir_progbin_tm`;

    (* now save the lifter theorem using the definitions *)
    val bir_x_riscv_lift_THM = save_thm ("bir_"^prog_name^"_riscv_lift_THM",
	   REWRITE_RULE [GSYM bir_x_prog_def,
			 GSYM bir_x_progbin_def] thm_riscv);
  in
    ()
  end;

end

end
