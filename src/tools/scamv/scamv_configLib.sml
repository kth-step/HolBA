structure scamv_configLib : scamv_configLib =
struct

open bir_scamv_helpersLib;

datatype 'cfg opt_entry =
         Arity0 of string * string * ('cfg -> bool -> 'cfg)
         | Arity1 of string * string * ('cfg -> string -> 'cfg)

datatype gen_type = gen_rand
                  | rand_simple
                  | mock
                  | qc
                  | slice
                  | from_file of string
                                     
type scamv_config = { max_iter : int,
                      prog_size : int,
                      max_tests : int,
                      generator : gen_type,
                      only_gen : bool
                    }

val default_cfg = { max_iter = 10
                  , prog_size = 5
                  , max_tests = 4
                  , generator = gen_rand
                  , only_gen = false
                  }

fun gen_type_fromString gt =
    case gt of
        "rand" => SOME gen_rand
      | "rand_simple" => SOME rand_simple
      | "mock" => SOME mock
      | "qc" => SOME qc
      | "slice" => SOME slice
      | "file" => SOME (from_file "asm/test.s") (* FIXME temporary *)
      | _ => NONE

(* setter boilerplate because SML doesn't have lenses *)

fun set_max_iter (cfg : scamv_config) n =
    { max_iter = n,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      only_gen = # only_gen cfg };

fun set_prog_size (cfg : scamv_config) n =
    { max_iter = # max_iter cfg,
      prog_size = n,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      only_gen = # only_gen cfg };

fun set_max_tests (cfg : scamv_config) n =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = n,
      generator = # generator cfg,
      only_gen = # only_gen cfg };

fun set_generator (cfg : scamv_config) gen =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = gen,
      only_gen = # only_gen cfg };

fun set_only_gen (cfg : scamv_config) b =
    { max_iter = # max_iter cfg,
      prog_size = # prog_size cfg,
      max_tests = # max_tests cfg,
      generator = # generator cfg,
      only_gen = b };

(* end boilerplate *)

local
    fun handle_conv_arg_with str_conv f cfg str =
        let val SOME n = str_conv str
        in
            f cfg n
        end;
in
val opt_table =
    [ Arity1 ("i", "max_iter",
             handle_conv_arg_with Int.fromString set_max_iter)
    , Arity1 ("sz", "prog_size",
             handle_conv_arg_with Int.fromString set_prog_size)
    , Arity1 ("t", "max_tests",
             handle_conv_arg_with Int.fromString set_max_tests)
    , Arity1 ("gen", "generator",
             handle_conv_arg_with gen_type_fromString set_generator)
    , Arity0 ("m", "is_mock", fn cfg => fn b => if b
                                          then set_generator cfg mock
                                          else cfg)
    , Arity0 ("og", "only_gen", set_only_gen)
    ];
end

fun opt_strings (Arity1 (s, l, _)) = (s,l)
  | opt_strings (Arity0 (s, l, _)) = (s,l)

fun match_opt str (short_name, long_name) =
    str = ("-" ^ short_name) orelse str = ("--" ^ long_name)

exception OptNotFound of string;
fun opt_lookup tok [] = raise (OptNotFound tok)
  | opt_lookup tok (entry :: es) =
    if match_opt tok (opt_strings entry)
    then entry
    else opt_lookup tok es

fun print_scamv_opt_usage () =
    let fun print_entry entry =
            case entry of
                Arity1 (s, l, _) =>
                print ("-" ^ s ^ " <arg>, --" ^ l ^ " <arg>\n")
              | Arity0 (s, l, _) =>
                print ("-" ^ s ^ ", --" ^ l ^ "\n")
    in
        print "Scam-V Usage:\n\n";
        List.map print_entry opt_table;
        print ("\ngenerator arg should be one of: rand, rand_simple, qc, mock, slice, file\n");
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
                Arity1 (_,_,f) =>
                (case ts of
                     arg1 :: ts' =>
                     (f cfg arg1, ts')
                   | _  => raise ArgNotFound)
              | Arity0 (_,_,f) => (f cfg true, ts))
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
                       ("unrecognized command-line option " ^ str)))
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
