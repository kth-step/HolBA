structure bir_angrLib =
struct

datatype 'a exec_path =
         exec_path of {
           final_pc : string,
           path : string list,
           guards : string list,
           observations : 'a list }

local
  open Json;

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
          fun parse_guard str = match_prefix "Bool " (match_bracket #"<" #">" str);
          fun parse_obs str = match_prefix "SAO " (match_bracket #"<" #">" str);
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
            , path = List.map fromJsonString path_list
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
      val pythonscript = (get_pythondir()) ^ "/symbolic_execution.py";
      val magicinputfilename = (get_pythondir()) ^ "/magicinput.bir";

      val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog_t;
      val _ = bir_fileLib.write_to_file magicinputfilename bprog_json_str;

      val output = bir_exec_wrapLib.get_exec_output ("python3 \"" ^ pythonscript ^ "\" \"" ^ magicinputfilename ^ "\"");
      val _ = print output;
    in
      ()
    end;



end (* local *)

end (* struct *)
