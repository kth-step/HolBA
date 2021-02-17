structure scamv_configLib : scamv_configLib =
struct

open holba_entryLib;

  (* error handling *)
  val libname  = "scamv_configLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

datatype 'cfg opt_entry =
         Arity0 of string * string * string * ('cfg -> bool -> 'cfg)
         | Arity1 of string * string * string * ('cfg -> string -> 'cfg)

datatype gen_type = gen_rand
                  | prefetch_strides
                  | qc
                  | slice
                  | from_file
                  | from_list

datatype obs_model = mem_address_pc
                   | cache_tag_index
                   | cache_tag_only
                   | cache_index_only
                   | cache_tag_index_part
                   | cache_tag_index_part_page
                   | cache_speculation
                   | cache_speculation_first

datatype hw_obs_model = hw_cache_tag_index
                      | hw_cache_index_numvalid
                      | hw_cache_tag_index_part
                      | hw_cache_tag_index_part_page

type scamv_config = { max_iter  : int,
                      prog_size : int,
                      max_tests : int,
                      enumerate : bool,
                      generator : gen_type,
                      generator_param : string option,
                      obs_model : obs_model,
                      refined_obs_model : obs_model option,
                      obs_projection : int,
                      hw_obs_model : hw_obs_model,
                      verbosity : int,
                      seed_rand : bool,
                      do_training : bool,
                      run_description : string option,
                      exec_conc : bool
                    }

val default_cfg = { max_iter  = 10
                  , prog_size = 5
                  , max_tests = 4
                  , enumerate = false
                  , generator = gen_rand
                  , generator_param = NONE
                  , obs_model = cache_tag_index
                  , refined_obs_model = NONE
                  , obs_projection = 1
                  , hw_obs_model = hw_cache_tag_index
                  , verbosity = 1
                  , seed_rand = true
                  , do_training = false
                  , run_description = NONE
                  , exec_conc = false
                  }

fun gen_type_fromString gt =
    case gt of
        "rand"             => SOME gen_rand
      | "prefetch_strides" => SOME prefetch_strides
      | "qc"               => SOME qc
      | "slice"            => SOME slice
      | "file"             => SOME from_file
      | "list"             => SOME from_list
      | _                  => NONE

fun obs_model_fromString om =
    case om of
        "mem_address_pc"            => SOME mem_address_pc
      | "cache_tag_index"           => SOME cache_tag_index
      | "cache_tag_only"            => SOME cache_tag_only
      | "cache_index_only"          => SOME cache_index_only
      | "cache_tag_index_part"      => SOME cache_tag_index_part
      | "cache_tag_index_part_page" => SOME cache_tag_index_part_page
      | "cache_speculation"         => SOME cache_speculation
      | "cache_speculation_first"   => SOME cache_speculation_first
      | _                           => NONE

fun hw_obs_model_fromString hwom =
    case hwom of
        "hw_cache_tag_index"           => SOME hw_cache_tag_index
      | "hw_cache_index_numvalid"      => SOME hw_cache_index_numvalid
      | "hw_cache_tag_index_part"      => SOME hw_cache_tag_index_part
      | "hw_cache_tag_index_part_page" => SOME hw_cache_tag_index_part_page
      | _                              => NONE

(* setter boilerplate because SML doesn't have lenses *)

fun set_max_iter (cfg : scamv_config) n =
    { max_iter = n,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg,
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_prog_size (cfg : scamv_config) n =
    { max_iter = # max_iter cfg,
      prog_size = n,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_max_tests (cfg : scamv_config) n =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = n,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_enumerate (cfg : scamv_config) enum =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = enum,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg,
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_generator (cfg : scamv_config) gen =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = gen,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_generator_param (cfg : scamv_config) gen_param =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = gen_param,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_obs_model (cfg : scamv_config) om =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = om,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_refined_obs_model (cfg : scamv_config) om =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = om,
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };


fun set_obs_projection (cfg : scamv_config) obs_number =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg,
      obs_projection = obs_number,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };


fun set_hw_obs_model (cfg : scamv_config) hwom =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = hwom,
      verbosity = # verbosity cfg,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_verbosity (cfg : scamv_config) v =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = v,
      seed_rand = # seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_seed_rand (cfg : scamv_config) s =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = s,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_do_training (cfg : scamv_config) s =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = #seed_rand cfg,
      do_training = s,
      run_description = # run_description cfg,
      exec_conc = # exec_conc cfg };

fun set_run_description (cfg : scamv_config) s =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = #seed_rand cfg,
      do_training = # do_training cfg,
      run_description = s,
      exec_conc = # exec_conc cfg };

fun set_exec_conc (cfg : scamv_config) s =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      enumerate = # enumerate cfg,
      generator = # generator cfg,
      generator_param = # generator_param cfg,
      obs_model = # obs_model cfg,
      refined_obs_model = # refined_obs_model cfg, 
      obs_projection = # obs_projection cfg,
      hw_obs_model = # hw_obs_model cfg,
      verbosity = # verbosity cfg,
      seed_rand = #seed_rand cfg,
      do_training = # do_training cfg,
      run_description = # run_description cfg,
      exec_conc = s };

fun set_h4ltl (cfg : scamv_config) s =
    (Library.trace := s; cfg);

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
    , Arity0 ("enum", "enumerate", "enable enumeration for test case generation",
              fn cfg => fn b => set_enumerate cfg b)
    , Arity1 ("gen", "generator", "Program generator",
              handle_conv_arg_with gen_type_fromString set_generator)
    , Arity1 ("genpar", "generator_param", "Program generator parameter",
              handle_conv_arg_with (fn x => SOME (SOME x)) set_generator_param)
    , Arity1 ("om", "obs_model", "Observation model",
              handle_conv_arg_with obs_model_fromString set_obs_model)
    , Arity1 ("rom", "refined_obs_model", "Refined observation model",
              handle_conv_arg_with (SOME o obs_model_fromString) set_refined_obs_model)
    , Arity1 ("proj", "obs_projection", "Observation projection",
              handle_conv_arg_with Int.fromString set_obs_projection)
    , Arity1 ("hwom", "hw_obs_model", "HW observation model",
              handle_conv_arg_with hw_obs_model_fromString set_hw_obs_model)
    , Arity0 ("frs", "fix_rand_seed", "Fix the seed for the random number generators (for debugging and testing).",
              fn cfg => fn b => set_seed_rand cfg (not b))
    , Arity0 ("T", "training", "Train branch predictor (only works if observing PC)",
              fn cfg => fn b => set_do_training cfg b)
    , Arity1 ("rundes", "run_description", "Run description text",
              handle_conv_arg_with (fn x => SOME (SOME x)) set_run_description)
    , Arity0 ("ec", "exec_conc", "Execute generated states to validate obs eq",
              fn cfg => fn b => set_exec_conc cfg b)
    , Arity1 ("h4ltl", "hol4_library_trace_level", "Set hol4 library trace level (e.g., 5 to let HolSmt keep temporary files with z3)",
              handle_conv_arg_with Int.fromString set_h4ltl)
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
        print ("\ngenerator arg should be one of: rand, prefetch_strides, qc, slice, file, list\n");
        print ("\nobs_model arg should be one of: mem_address_pc, cache_tag_index, cache_tag_only, cache_index_only, cache_tag_index_part, cache_tag_index_part_page, cache_speculation\n");
        print ("\nrefined_obs_model arg is like obs_model\n");
        print ("\nobs_projection is an observation id as a number\n");
        print ("\nhw_obs_model arg should be one of: hw_cache_tag_index, hw_cache_index_numvalid, hw_cache_tag_index_part, hw_cache_tag_index_part_page\n");
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
