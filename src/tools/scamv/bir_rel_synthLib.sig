signature bir_rel_synthLib =
sig
    include Abbrev;

    type exp;
    type cobs;
    type cobs_repr;
    type path_repr;
    type path_spec;
    type path_struct;
    datatype enum_strategy = enum_extensional of int list
                           | enum_range of int * int;
    type enum_env;

    val path_cond_of : path_repr -> exp
    val path_obs_of : path_repr -> cobs_repr list
    val cobs_id_of : cobs_repr -> int
    val path_domain : path_struct -> int list
    val split_obs_list :
        ''a ->
        (''a * 'b) list -> 'b list * 'b list
    val obs_domain_path : cobs_repr list -> int list
    val obs_domain : path_struct -> int list
    val lookup_path : int -> path_repr list -> path_repr option
    val lookup_obs : int -> cobs_repr list -> cobs_repr option

    val print_path_struct : path_struct -> unit;

    val rel_synth_jit :
        path_spec -> int -> path_repr list -> exp

    val rel_synth_init :
        (exp * cobs list option) list ->
        int ->
        enum_env ->
        path_struct * exp * ((path_spec -> bool) -> (path_spec * term) option)

end;
