signature visited_statesLib =
sig
  include Abbrev;
  
  type visited_map;
  
  val init_visited : unit -> visited_map;
  val add_visited : visited_map -> scamv_path_structLib.path_spec -> term -> visited_map;
  val lookup_visited : visited_map -> scamv_path_structLib.path_spec -> term;
  val lookup_visited_all_paths : visited_map -> term;
  val transform_visited : visited_map -> (term -> term) -> visited_map;
end
