structure bir_obs_modelLib =
struct

local
    open bir_obs_modelTheory;
in

structure bir_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_pc ^t``));
end

structure bir_arm8_cache_line_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t list``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_armv8 ^t``));
end
end
end
