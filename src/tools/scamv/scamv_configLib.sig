signature scamv_configLib =
sig
    type scamv_config
    datatype gen_type = gen_rand
                      | rand_simple
                      | mock
                      | qc
                      | slice
                      | from_file of string

    val default_cfg : scamv_config
    val print_scamv_opt_usage : unit -> unit
    val scamv_getopt_config : unit -> scamv_config
end
