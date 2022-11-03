signature bir_rel_synthLib =
sig
    include Abbrev;

    type exp;
    type cobs;

    datatype enum_strategy = enum_extensional of int list
                           | enum_range of int * int;
    type enum_env;

    val split_obs_list :
        ''a ->
        (''a * 'b) list -> 'b list * 'b list

    val rel_synth_jit :
        scamv_path_structLib.path_spec ->
        int -> scamv_path_structLib.path_struct -> bool -> exp

    val rel_synth_init :
        scamv_path_structLib.path_struct ->
        int ->
        enum_env ->
        scamv_path_structLib.path_spec list *
            exp * ((scamv_path_structLib.path_spec -> bool) ->
                   (scamv_path_structLib.path_spec * term) option)

end;
