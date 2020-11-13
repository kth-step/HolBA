signature bir_rel_synthLib =
sig
    include Abbrev;

    type exp;
    type cobs;
    type path_spec;
    datatype enum_strategy = enum_extensional of int list
                           | enum_range of int * int;
    type enum_env;

    val split_obs_list :
        ''a ->
        (''a * 'b) list -> 'b list * 'b list

    val rel_synth_jit :
        path_spec -> int -> scamv_path_structLib.path_struct -> exp

    val rel_synth_init :
        scamv_path_structLib.path_struct ->
        int ->
        enum_env ->
        scamv_path_structLib.path_struct * exp * ((path_spec -> bool) -> (path_spec * term) option)

end;
