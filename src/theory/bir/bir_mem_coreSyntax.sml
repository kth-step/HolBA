structure bir_mem_coreSyntax :> bir_mem_coreSyntax =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_mem_coreTheory;

  val mem_init_tm = prim_mk_const{Name = "mem_init",
                                  Thy  = "bir_mem_core"};

end
