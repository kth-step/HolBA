structure bir_lifter_interfaceLib =
struct

local


(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory;
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

open bir_inst_liftingLib;
open gcc_supportLib;

in

val ERR = mk_HOL_ERR "bir_lifter_interfaceLib"
val wrap_exn = Feedback.wrap_exn "bir_lifter_interfaceLib"

(* Debug values:

  structure MD = bmil_riscv;
  open MD;

  val da_name = "add_reg.da"
  val prog_name = "add_reg_riscv"
  val prog_interval = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  val is_multicore = true
  val arch = "riscv"
*)
fun lift_da_and_store_gen prog_name da_name prog_interval is_multicore arch =
  let
    val _ = print_with_style_ [Bold, Underline] ("Lifting "^da_name^"\n");

    val (region_map, regions) = read_disassembly_file_regions da_name

    (* TODO: Use "let val bmil = if-then-else" for fewer cases *)
    val (thm_arch, errors) =
      if arch = "arm8"
      then if is_multicore
           then if isSome (#bmr_mc_lift_instr arm8_bmr_rec)
                then bmil_arm8.bir_lift_prog_gen_mc
                       prog_interval
                       regions
                else raise ERR "lift_da_and_store_gen" ("Multicore not supported for "^arch)
           else bmil_arm8.bir_lift_prog_gen
                  prog_interval
                  regions
      else if arch = "riscv"
      then if is_multicore
           then if isSome (#bmr_mc_lift_instr riscv_bmr_rec)
                then bmil_riscv.bir_lift_prog_gen_mc
                       prog_interval
                       regions
(*
  val (mu_b, mu_e) = prog_interval

*)
                else raise ERR "lift_da_and_store_gen" ("Multicore not supported for "^arch)
           else bmil_riscv.bir_lift_prog_gen
             prog_interval
             regions
      else raise ERR "lift_da_and_store_gen" ("Unsupported architecture: "^arch)

    val (lift_app_1_tm, bir_prog_tm) = (dest_comb o concl) thm_arch;
    val (_, bir_progbin_tm) = dest_comb lift_app_1_tm;

    val _ = print "\n\n";

    (* now save the definitions *)
    val bir_x_prog_var = mk_var("bir_"^prog_name^"_prog", type_of bir_prog_tm)
    val bir_x_prog_def = Define `^bir_x_prog_var = ^bir_prog_tm`;
    val bir_x_progbin_var = mk_var("bir_"^prog_name^"_progbin", type_of bir_progbin_tm)
    val bir_x_progbin_def = Define `^bir_x_progbin_var = ^bir_progbin_tm`;

    (* now save the lifter theorem using the definitions *)
    val bir_x_arch_lift_THM = save_thm ("bir_"^prog_name^"_"^arch^"_lift_THM",
	   REWRITE_RULE [GSYM bir_x_prog_def,
			 GSYM bir_x_progbin_def] thm_arch);
  in
    (bir_x_progbin_def, bir_x_prog_def, bir_x_arch_lift_THM)
  end
;

(* TODO: Default is ARMv8 for now... *)
fun lift_da_and_store prog_name da_name prog_interval =
  lift_da_and_store_gen prog_name da_name prog_interval false "arm8"
;

fun lift_da_and_store_mc_riscv prog_name da_name prog_interval =
  lift_da_and_store_gen prog_name da_name prog_interval true "riscv"
;
(* TEST

val _ = lift_da_and_store_mc_riscv "add_reg_riscv" "add_reg.da" (Arbnum.fromInt 0, Arbnum.fromInt 999999999)

*)

end

end
