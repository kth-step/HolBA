structure bir_obs_modelLib :> bir_obs_modelLib =
struct

local
    open bir_obs_modelTheory;
in

structure bir_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_pc ^t``));
end

structure bir_arm8_mem_addr_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_mem_addr_pc_armv8 ^t``));
end

structure bir_arm8_cache_line_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_armv8 ^t``));
end

structure bir_arm8_cache_line_tag_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_tag_armv8 ^t``));
end

structure bir_arm8_cache_line_index_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_index_armv8 ^t``));
end

structure bir_arm8_cache_line_subset_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_subset_armv8 ^t``));
end

structure bir_arm8_cache_line_subset_page_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_subset_page_armv8 ^t``));
end

fun get_obs_model id =
  let
    val obs_hol_type =
	  if id = "mem_address_pc_trace" then
	    bir_arm8_mem_addr_pc_model.obs_hol_type
          else if id = "cache_tag_index" then
            bir_arm8_cache_line_model.obs_hol_type
          else if id = "cache_tag_only" then
            bir_arm8_cache_line_tag_model.obs_hol_type
          else if id = "cache_index_only" then
            bir_arm8_cache_line_index_model.obs_hol_type
          else if id = "cache_tag_index_part" then
            bir_arm8_cache_line_subset_model.obs_hol_type
          else if id = "cache_tag_index_part_page" then
            bir_arm8_cache_line_subset_page_model.obs_hol_type
          else
            raise ERR "get_obs_model" ("unknown obs_model selected: " ^ id);

    val add_obs =
	  if id = "mem_address_pc_trace" then
	    bir_arm8_mem_addr_pc_model.add_obs
          else if id = "cache_tag_index" then
            bir_arm8_cache_line_model.add_obs
          else if id = "cache_tag_only" then
            bir_arm8_cache_line_tag_model.add_obs
          else if id = "cache_index_only" then
            bir_arm8_cache_line_index_model.add_obs
          else if id = "cache_tag_index_part" then
            bir_arm8_cache_line_subset_model.add_obs
          else if id = "cache_tag_index_part_page" then
            bir_arm8_cache_line_subset_page_model.add_obs
          else
            raise ERR "get_obs_model" ("unknown obs_model selected: " ^ id);
  in
    { id = id,
      obs_hol_type = obs_hol_type,
      add_obs = add_obs }
  end;

end (* local *)
end (* struct *)
