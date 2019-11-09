structure scamv_configLib : scamv_configLib =
struct

open bir_scamv_helpersLib;

datatype 'cfg opt_entry =
         Arity0 of string * string * string * ('cfg -> bool -> 'cfg)
         | Arity1 of string * string * string * ('cfg -> string -> 'cfg)

datatype gen_type = gen_rand
                  | rand_simple
                  | prefetch_strides
                  | mock
                  | qc
                  | slice
                  | from_file of string

datatype obs_model = cache_tag_index
                   | cache_index_only
                   | cache_tag_index_part
                   | cache_tag_index_part_page

datatype hw_obs_model = hw_cache_tag_index
                      | hw_cache_tag_index_part
                      | hw_cache_tag_index_part_page

type scamv_config = { max_iter : int,
                      prog_size : int,
                      max_tests : int,
                      generator : gen_type,
                      obs_model : obs_model,
                      hw_obs_model : hw_obs_model,
                      only_gen : bool,
                      verbosity : int
                    }

val default_cfg = { max_iter = 10
                  , prog_size = 5
                  , max_tests = 4
                  , generator = gen_rand
                  , obs_model = cache_tag_index
                  , hw_obs_model = hw_cache_tag_index
                  , only_gen = true
                  , verbosity = 1
                  }

fun gen_type_fromString gt =
    case gt of
        "rand"             => SOME gen_rand
      | "rand_simple"      => SOME rand_simple
      | "prefetch_strides" => SOME prefetch_strides
      | "mock"             => SOME mock
      | "qc"               => SOME qc
      | "slice"            => SOME slice
      | "file"             => SOME (from_file "asm/test.s") (* FIXME temporary *)
      | _                  => NONE

fun obs_model_fromString om =
    case om of
        "cache_tag_index"           => SOME cache_tag_index
      | "cache_index_only"          => SOME cache_index_only
      | "cache_tag_index_part"      => SOME cache_tag_index_part
      | "cache_tag_index_part_page" => SOME cache_tag_index_part_page
      | _                           => NONE

fun hw_obs_model_fromString hwom =
    case hwom of
        "hw_cache_tag_index"           => SOME hw_cache_tag_index
      | "hw_cache_tag_index_part"      => SOME hw_cache_tag_index_part
      | "hw_cache_tag_index_part_page" => SOME hw_cache_tag_index_part_page
      | _                              => NONE

(* setter boilerplate because SML doesn't have lenses *)

fun set_max_iter (cfg : scamv_config) n =
    { max_iter = n,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      obs_model = # obs_model cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      only_gen = # only_gen cfg };

fun set_prog_size (cfg : scamv_config) n =
    { max_iter = # max_iter cfg,
      prog_size = n,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      obs_model = # obs_model cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      only_gen = # only_gen cfg };

fun set_max_tests (cfg : scamv_config) n =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = n,
      generator = # generator cfg,
      obs_model = # obs_model cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      only_gen = # only_gen cfg };

fun set_generator (cfg : scamv_config) gen =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = gen,
      obs_model = # obs_model cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      only_gen = # only_gen cfg };

fun set_obs_model (cfg : scamv_config) om =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      obs_model = om,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      only_gen = # only_gen cfg };

fun set_hw_obs_model (cfg : scamv_config) hwom =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      obs_model = # obs_model cfg,
      hw_obs_model = hwom,
      verbosity = # verbosity cfg,
      only_gen = # only_gen cfg };

fun set_only_gen (cfg : scamv_config) b =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      obs_model = # obs_model cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      only_gen = b };

fun set_verbosity (cfg : scamv_config) v =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      obs_model = # obs_model cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = v,
      only_gen = # only_gen cfg };


(* end boilerplate *)

local
    fun handle_conv_arg_with str_conv f cfg str =
        let val SOME n = str_conv str
        in
            f cfg n
        end;
in
val opt_table =
    [ Arity1 ("i", "max_iter", "Number of pipeline iterations",
              handle_conv_arg_with Int.fromString set_max_iter)
    , Arity1 ("v", "verbosity", "Verbosity level (0 = quiet, 10 = show me everything)",
              handle_conv_arg_with Int.fromString set_verbosity)
    , Arity1 ("sz", "prog_size", "Size hint for program generator",
              handle_conv_arg_with Int.fromString set_prog_size)
    , Arity1 ("t", "max_tests", "Number of state pairs to generate per iteration",
              handle_conv_arg_with Int.fromString set_max_tests)
    , Arity1 ("gen", "generator", "Program generator",
              handle_conv_arg_with gen_type_fromString set_generator)
    , Arity1 ("om", "obs_model", "Observation model",
              handle_conv_arg_with obs_model_fromString set_obs_model)
    , Arity1 ("hwom", "hw_obs_model", "HW observation model",
              handle_conv_arg_with hw_obs_model_fromString set_hw_obs_model)
    , Arity0 ("m", "is_mock", "Enable mock generator (option deprecated, equivalent to -gen mock)",
              fn cfg => fn b => if b
                                then set_generator cfg mock
                                else cfg)
    , Arity0 ("og", "only_gen", "Generate experiments without running them (default)",
              set_only_gen)
    , Arity0 ("r", "run_experiments", "Automatically run each experiment after generating it (requires active connection)",
              fn cfg => fn b => set_only_gen cfg (not b))
    ];
end

fun opt_strings (Arity1 (s, l, _, _)) = (s,l)
  | opt_strings (Arity0 (s, l, _, _)) = (s,l)

fun match_opt str (short_name, long_name) =
    str = ("-" ^ short_name) orelse str = ("--" ^ long_name)

exception OptNotFound of string;
fun opt_lookup tok [] = raise (OptNotFound tok)
  | opt_lookup tok (entry :: es) =
    if match_opt tok (opt_strings entry)
    then entry
    else opt_lookup tok es

fun print_scamv_opt_usage () =
    let fun separation x = if x >= 32
                           then "\t"
                           else implode (List.tabulate (32 - x, fn _ => #" "));
        fun print_entry entry =
            case entry of
                Arity1 (s, l, desc, _) =>
                let val first_part = "-" ^ s ^ " <arg>, --" ^ l ^ " <arg>"
                in
                    print (first_part ^ separation (size first_part) ^ desc ^ "\n")
                end
              | Arity0 (s, l, desc, _) =>
                let val first_part = "-" ^ s ^ ", --" ^ l
                in print (first_part ^ separation (size first_part) ^ desc ^ "\n")
                end
    in
        print "Scam-V Usage:\n\n";
        List.map print_entry opt_table;
        print ("\ngenerator arg should be one of: rand, prefetch_strides, rand_simple, qc, mock, slice, file\n");
        print ("\nobs_model arg should be one of: cache_tag_index, cache_index_only, cache_tag_index_part, cache_tag_index_part_page\n");
        print ("\nhw_obs_model arg should be one of: hw_cache_tag_index, hw_cache_tag_index_part, hw_cache_tag_index_part_page\n");
        print ("\nDefaults are: " ^ PolyML.makestring default_cfg ^ "\n")
    end

fun scamv_getopt_config_go () =
    let val args = String.tokens Char.isSpace (get_script_args ());
        exception ArgNotFound
        fun process_opt [] cfg = (cfg, [])
          | process_opt (tok::ts) cfg =
            if String.isPrefix "-" tok
            then
            (case opt_lookup tok opt_table of
                Arity1 (_,_,_,f) =>
                (case ts of
                     arg1 :: ts' =>
                     (f cfg arg1, ts')
                   | _  => raise ArgNotFound)
              | Arity0 (_,_,_,f) => (f cfg true, ts))
            else
                (cfg, ts)
        fun process_opts ts cfg =
            let val (cfg', rs) = process_opt ts cfg
            in case rs of
                   [] => cfg'
                 | _ => process_opts rs cfg'
            end
    in
        (process_opts args default_cfg
         handle ArgNotFound =>
                (print_scamv_opt_usage ();
                 raise ERR "scamv_getopt_config"
                       "missing argument in command-line option")
              | OptNotFound str =>
                (print_scamv_opt_usage ();
                 raise ERR "scamv_getopt_config"
                       ("unrecognized command-line option " ^ str))
              | Bind =>
                (print_scamv_opt_usage ();
                raise ERR "scamv_getopt_config" "parse error in command-line options"))
    end

fun memo f =
    let
        val r = ref (NONE : scamv_config option);
    in
        fn () =>
           case !r of
               NONE => let val v = f ();
                       in (r := SOME v; v) end
              | SOME v => v
    end

val scamv_getopt_config = memo scamv_getopt_config_go;

end
