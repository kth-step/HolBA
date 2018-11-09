open HolKernel Parse;


(* open bir_inst_liftingLibTypes; *)

open bir_lifter_simple_interfaceLib;



val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;










(* various projects *)
val benchmark_descriptors_0 = [
  ("arm8", ["binaries/bignum/aarch64-bignum-emptymain.da",
            "binaries/wolfssl_manual/aarch64-wolfssl_manual-emptymain.da",
            "binaries/bzip2-1.0.6/aarch64-libbz2-emptymain.da"]),
  ("m0"  , ["binaries/bignum/m0-bignum-emptymain.da",
            "binaries/wolfssl_manual/m0-wolfssl_manual-emptymain.da"])
];

(* linux distro repository binaries *)
val benchmark_descriptors_1_0 = [
  ("arm8", ["binaries/libc/libc.da",
            "binaries/libc/libm.da",
            "binaries/sqlite/libsqlite.da"])
];

val benchmark_descriptors_1_1 = [
  ("arm8", ["binaries/lua/lua.da"])
];

val benchmark_descriptors_1_2 = [
  ("arm8", ["binaries/vim/vim.da"])
];

(* android *)
val benchmark_descriptors_2_0 = [
  ("arm8", ["binaries/android/taimen-ppr2.181005.003_bins/system/system/bin/run-as.da",
            "binaries/android/taimen-ppr2.181005.003_bins/system/system/bin/uncrypt.da"])
];

val benchmark_descriptors_2_1 = [
  ("arm8", ["binaries/android/taimen-ppr2.181005.003_bins/system/system/bin/iptables.da"])
];

val benchmark_descriptors_2_2 = [
  ("arm8", ["binaries/android/taimen-ppr2.181005.003_bins/system/system/bin/toybox.da"])
];

(* pure m0 *)
val benchmark_descriptors_3 = [
  ("m0",   ["binaries/freertos_nrf51/m0-freertos_nrf51.da"])
];



val benchmark_descriptors = benchmark_descriptors_2_1;

fun run_benchmark (arch_str, da_files) = List.map (fn da_file =>
    let
      val thm_prog = lift_file arch_str da_file;
    in
      ()
    end
  ) da_files;



val _ = List.map run_benchmark benchmark_descriptors;



(* export a theory for these binaries *)
(*
val _ = print "\n\n";

val _ = new_theory "bzip2";
val _ = save_thm ("bzip2_arm8_program_THM", thm_arm8);
val _ = save_thm ("bzip2_m0_program_THM", thm_m0);
val _ = export_theory();
*)

