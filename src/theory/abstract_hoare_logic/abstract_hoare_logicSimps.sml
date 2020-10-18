structure abstract_hoare_logicSimps :> abstract_hoare_logicSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open abstract_hoare_logicTheory;

val wm_type = mk_thy_type {Tyop="abstract_model_t",
                           Thy="abstract_hoare_logic",
                           Args=[``:bir_state_t``,
                                 ``:bir_label_t``]
                          };

val bir_wm_SS = rewrites (flatten (map type_rws [wm_type]));

end
