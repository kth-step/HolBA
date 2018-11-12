open HolKernel Parse

open bir_lifter_simple_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


val configuration = [
  ("arm8", "aes/aes-aarch64.da"                                         , "aes_arm8_program_THM"),
  ("m0"  , "aes/aes-m0.da"                                              , "aes_m0_program_THM")(*,
  ("arm8", "bignum/aarch64-bignum-emptymain.da"                         , "bignum_arm8_program_THM"),
  ("m0"  , "bignum/m0-bignum-emptymain.da"                              , "bignum_m0_program_THM"),
  ("arm8", "wolfssl_manual/aarch64-wolfssl_manual-emptymain.da"         , "wolfssl_arm8_program_THM"),
  ("m0"  , "wolfssl_manual/m0-wolfssl_manual-emptymain.da"              , "wolfssl_m0_program_THM")
*)
];


val _ = new_theory "binaries";

val _ = List.map (fn (arch_str, da_file, thm_name) =>
  let
    val thm_prog = lift_file arch_str da_file;
    val _ = save_thm (thm_name, thm_prog);
  in
    ()
  end) configuration;

val _ = export_theory();
