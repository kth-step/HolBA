structure bir_angrLib =
struct

datatype 'a exec_path =
         exec_path of {
           final_pc : string,
           jmp_history : string list,
           guards : 'a list,
           observations : 'a list }

local
  open Json bslSyntax bir_quotationLib;

  infix 9 <?>;
  infix 8 <|>;
  fun init [x] = []
    | init (x::y::ys) = let val zs = init (y::ys) in x::zs end;
  fun intercalate x zs = foldr (fn (z,zs) => if null zs then z::zs else z::x::zs) [] zs;

  val angr_variable =
      fmap (concat o intercalate "_" o init o init)
           (bind (sep_by1 (fmap implode (many1 (sat Char.isAlphaNum))) (char #"_"))
                 (fn list => seq (many (sat (not o Char.isSpace))) (return list)))
           <?> "angr variable";

  val bir_angr_var = gen_bir_var angr_variable 64;
  val bir_angr_bool_exp =  try (seq (token (string "True")) (return btrue))
                               <|> try (seq (token (string "False")) (return bfalse))
                               <|> gen_bir_exp bir_angr_var 64;

  (* error handling *)
  val libname = "bir_angrLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in
  fun result_from_json json =
      let open String;
          fun fromJsonString (STRING str) = str;
          fun match_bracket left right s =
              if not (size s = 0) andalso sub(s,0) = left andalso sub(s,size s - 1) = right
              then extract(s,1,SOME(size s - 2))
              else raise ERR "result_from_json"
                         ("couldn't parse outer brackets " ^ Char.toString left ^ " and " ^ Char.toString right ^ " in string: " ^ s);
          fun match_prefix prefix s =
              if not (size s = 0) andalso Int.<=(size prefix, size s)
                 andalso isPrefix prefix s
              then extract(s,size prefix,NONE)
              else raise ERR "result_from_json"
                         ("couldn't parse exact prefix '" ^ prefix ^ "' in string: " ^ s);
          fun match_BExp str = parse (seq junk bir_angr_bool_exp) str
                               handle e => raise ERR "match_BExp" (make_string_parse_error e);
          fun parse_guard str = match_BExp (match_prefix "Bool " (match_bracket #"<" #">" str));
          fun parse_obs str = match_BExp (match_prefix "BV64 " (match_bracket #"<" #">"
                                         (match_prefix "SAO " (match_bracket #"<" #">" str))));
      in
        case json of
            OBJECT [("addr",STRING addr_str)
                   ,("path",
                     ARRAY path_list)
                   ,("guards",
                     ARRAY guard_list)
                   ,("observations",
                     ARRAY obs_list)] =>
            exec_path { final_pc = addr_str
            , jmp_history = List.map fromJsonString path_list
            , guards = List.map (parse_guard o fromJsonString) guard_list
            , observations = List.map (parse_obs o fromJsonString) obs_list }
          | _ => raise ERR "result_from_json" "ill-formed result"
      end;

  fun parse_json_output output =
      case Json.parse output of
          ERROR err_string => raise ERR "parse_json_output" err_string
        | OK (ARRAY json_leaves) => List.map result_from_json json_leaves
        | OK _ => raise ERR "parse_json_output" "result from python script is not a list"


  fun get_pythondir () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_DIR")) of
          NONE => raise ERR "get_pythondir" "the environment variable HOLBA_DIR is not set"
        | SOME p => (p ^ "/src/tools/angr/python");

(*
  val bprog_t = bprog;
*)
  fun do_symb_exec bprog_t =
    let
      val pythonscript = (get_pythondir()) ^ "/symbolic_execution_wrapper.py";
      val magicinputfilename = (get_pythondir()) ^ "/magicinput.bir";

      val _ = bir_fileLib.makedir true (get_pythondir());

      val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog_t;
      val _ = bir_fileLib.write_to_file magicinputfilename bprog_json_str;

      val usePythonPackage = true;

      val output =
        if usePythonPackage then (
          print "... using python package of bir_angr ...\n";
          print "... metadata of package:\n";
          if OS.Process.isSuccess (OS.Process.system "python3 -m pip show bir_angr") then () else
            raise ERR "do_symb_exec" "python package bir_angr is not installed";
          print "... metadata end.\n";
          bir_exec_wrapLib.get_exec_output ("python3 -E -m bir_angr.symbolic_execution \"" ^ magicinputfilename ^ "\"")
        ) else (
          print "... using symbolic_execution_wrapper.py in python subdirectory ...\n";
          bir_exec_wrapLib.get_exec_output ("python3 -E \"" ^ pythonscript ^ "\" \"" ^ magicinputfilename ^ "\"")
        );
      val _ = print output;
    in
      ()
    end;



end (* local *)

end (* struct *)
