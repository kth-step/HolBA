structure program_logicSimps :> program_logicSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open transition_systemTheory;

val wm_type = mk_thy_type {Tyop="transition_system_t",
                           Thy="transition_system",
                           Args=[``:bir_state_t``,
                                 ``:bir_label_t``]
                          };

val bir_wm_SS = rewrites (flatten (map type_rws [wm_type]));

end
