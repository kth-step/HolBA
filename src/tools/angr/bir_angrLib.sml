structure bir_angrLib =
struct

datatype 'a exec_path =
         exec_path of {
           final_pc : string,
           jmp_history : string list,
           guards : 'a list,
           observations : (Arbnum.num * 'a * 'a list * Abbrev.term) list }

local
  open HolKernel Parse boolLib bossLib;

  open Json bslSyntax bir_quotationLib;

  infix 9 <?>;
  infix 8 <|>;
  fun init [x] = []
    | init (x::y::ys) = let val zs = init (y::ys) in x::zs end;
  fun intercalate x zs = foldr (fn (z,zs) => if null zs then z::zs else z::x::zs) [] zs;

  fun gen_bir_exp var_parser sz =
    fix (fn bir_exp =>
            let val mem_load =
                    seq (string "MEM")
                        (bind (bracket (char #"[") bir_exp (char #"]")) (fn addr =>
                        (return (bload8_le default_mem addr))))
                val range = bind digit (fn lower => seq (char #":")
                           (bind digit (fn upper => return (lower, upper)))
                val masked_var = bin (fmap bden var_parser)
                                 (fn var => try bracket (char #"[") range (char #"]")
                val logical = choicel [bracket (char #"(") bir_exp (char #")")
                                      ,bind unary_op
                                            (fn oper => fmap oper bir_exp)
                                      ,try mem_load
                                      ,fmap bconstimm (gen_bir_imm sz)
                                      ,masked_var]
                                      <?> "logical expression"
                val factor = chainr1 logical (binop binary_op_bitwise)
                                     <?> "factor"
                val term = chainr1 factor (binop binary_op_factor) <?> "term"
                val binexp = chainl1 term (binop binary_op_term)
                                     <?> "BIR binary expression"
                val binpred = bind (token binexp) (fn e1 =>
                              bind (binop binary_pred) (fn oper =>
                              bind (token binexp) (fn e2 =>
                              return (oper e1 e2))))
                                   <?> "BIR binary predicate"
            in
             try binpred <|> binexp
            end
        ) <?> "BIR expression";

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
 local
  open String;

  fun fromJsonString (STRING str) = str
    | fromJsonString _ = raise ERR "result_from_json:fromJsonString" "not a string";

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
                               handle e => raise ERR "match_BExp" (make_string_parse_error e)
                               handle Match => raise ERR "parser match error" ("cannot deal with: " ^ str);

  fun parse_guard str = match_BExp (match_prefix "Bool " (match_bracket #"<" #">" str));

  (* NOTE: this function restricts the observation expressions to 64-bit Imm expressions *)
  fun parse_obs_exp str =
    match_BExp (match_prefix "BV64 " (match_bracket #"<" #">"
                  (match_prefix "SAO " (match_bracket #"<" #">" str))));

  fun parse_obscond_exp str =
    match_BExp (match_prefix "BV1 " (match_bracket #"<" #">"
                  (match_prefix "SAO " (match_bracket #"<" #">" str))));

  fun parse_obs obsrefmap json =
    case json of
      ARRAY [NUMBER obs_ref,
	     obs_cnd,
	     ARRAY obs_exp_list] =>
      let val (id_tm, obsf_tm) = Redblackmap.find(obsrefmap, obs_ref) in
       (numSyntax.dest_numeral id_tm,
        (parse_obscond_exp o fromJsonString) obs_cnd,
        List.map (parse_obs_exp o fromJsonString) obs_exp_list,
        obsf_tm)
      end
     | _ => raise ERR "parse_obs" "ill-formed result";

 in
  fun result_from_json obsrefmap json =
        case json of
            OBJECT [("addr",STRING addr_str)
                   ,("path",
                     ARRAY path_list)
                   ,("constraints",
                     ARRAY guard_list)
                   ,("observations",
                     ARRAY obs_list)] =>
            exec_path { final_pc = addr_str
            , jmp_history = List.map fromJsonString path_list
            , guards = List.map (parse_guard o fromJsonString) guard_list
            , observations = List.map (parse_obs obsrefmap) obs_list }
          | _ => raise ERR "result_from_json" "ill-formed result";
 end;

  fun parse_json_output obsrefmap output =
      case Json.parse output of
          ERROR err_string => raise ERR "parse_json_output" err_string
        | OK (ARRAY json_leaves) => List.map (result_from_json obsrefmap) json_leaves
        | OK _ => raise ERR "parse_json_output" "result from python script is not a list";


  fun get_pythondir () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_DIR")) of
          NONE => raise ERR "get_pythondir" "the environment variable HOLBA_DIR is not set"
        | SOME p => (p ^ "/src/tools/angr/python");

(*
"_JSON_obs_ref_id/fun_12345"
*)
  fun obsrefmap_conv_stmt (stmt, (stmts, obsrefmap)) =
    if not (bir_programSyntax.is_BStmt_Observe stmt) then (stmt::stmts, obsrefmap) else
    let
      open bir_programSyntax;

      val (id_tm, cnd_tm, obss_tm, obsf_tm) = dest_BStmt_Observe stmt;

      val ref_num_new = (Arbnum.fromInt o List.length o Redblackmap.listItems) obsrefmap;
      val matchingobsrefnum_opt = List.find (fn (_, (x,y)) => identical x id_tm andalso identical y obsf_tm) (Redblackmap.listItems obsrefmap);
      val (ref_num, obsrefmap_m) =
        if isSome matchingobsrefnum_opt then
          ((fst o valOf) matchingobsrefnum_opt, obsrefmap)
        else
          let
            val obsrefmap_m = Redblackmap.insert (obsrefmap, ref_num_new, (id_tm, obsf_tm));
          in (ref_num_new, obsrefmap_m) end;

      val id_var_tm = mk_var ("_JSON_obs_ref_id_" ^ (Arbnum.toString ref_num), type_of id_tm);
      val obsf_var_tm = mk_var ("_JSON_obs_ref_fun_" ^ (Arbnum.toString ref_num), type_of obsf_tm);
      val stmt_m = mk_BStmt_Observe (id_var_tm, cnd_tm, obss_tm, obsf_var_tm);
    in
      (stmt_m::stmts, obsrefmap_m)
    end;

  fun obsrefmap_conv_block (block, (blocks, obsrefmap)) =
    let
      open bir_programSyntax;
      open listSyntax;

      val (tm_lbl, tm_stmts, tm_last_stmt) = dest_bir_block block;
      val (tm_stmt_list, obs_ty) = (dest_list) tm_stmts;

      val (tm_stmt_list_m, obsrefmap_m) = List.foldl obsrefmap_conv_stmt ([], obsrefmap) tm_stmt_list;

      val tm_stmts_m = (mk_list) (List.rev tm_stmt_list_m, obs_ty);

      val block_m = mk_bir_block (tm_lbl, tm_stmts_m, tm_last_stmt);
    in
      (block_m::blocks, obsrefmap_m)
    end;

  fun obsrefmap_conv_prog bprog_t =
    let
      open bir_programSyntax;
      open listSyntax;

      val (blocks, obs_ty) = (dest_list o dest_BirProgram) bprog_t;
      val obsrefmap = Redblackmap.mkDict Arbnum.compare;
      val (blocks_m, obsrefmap_m) = List.foldl obsrefmap_conv_block ([], obsrefmap) blocks;
    in
      ((mk_BirProgram o mk_list) (List.rev blocks_m, obs_ty), obsrefmap_m)
    end;

(*
  val bprog_t = bprog;
*)
  fun do_symb_exec bprog_t =
    let
      val pythonscript = (get_pythondir()) ^ "/symbolic_execution_wrapper.py";
      val magicinputfilename = (get_pythondir()) ^ "/magicinput.bir";

      val _ = bir_fileLib.makedir true (get_pythondir());

(*
      val _ = print "DEBUG BEFORE\n\n\n";
*)
      val (bprog_t_m, obsrefmap) = obsrefmap_conv_prog bprog_t;
(*
      val _ = print_term bprog_t_m;
      val _ = print (if identical bprog_t bprog_t_m then "EQUAL PROG\n\n" else "UNEQUAL PROG\n\n");
      (* debug print obsrefmap *)
      val _ = List.map (fn (k,(obsid,obsfun)) => print ((Arbnum.toString k) ^ " -> (" ^ (term_to_string obsid) ^ ", " ^ (term_to_string obsfun) ^ ")\n")) (Redblackmap.listItems obsrefmap);
      val _ = print "DEBUG AFTER\n\n\n";
*)

      local
        open listSyntax;
        open bir_programSyntax;
        open bir_immSyntax;
        open wordsSyntax;

        val blocks = (fst o dest_list o dest_BirProgram) bprog_t_m;
        val (lbl_tm, _, _) = dest_bir_block (List.nth (blocks, 0));
        (* val _ = print_term lbl_tm; *)
        val lbl_word_tm = (snd o gen_dest_Imm o dest_BL_Address o snd o dest_eq o concl o EVAL) lbl_tm;
      in
        val start_lbl_str = (Arbnum.toString o dest_word_literal) lbl_word_tm;
      end
      val _ = if false then print start_lbl_str else ();

      val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog_t_m;
      val _ = bir_fileLib.write_to_file magicinputfilename bprog_json_str;

      val usePythonPackage = true;

      val output =
        if usePythonPackage then (
          print "... using python package of bir_angr ...\n";
          print "... metadata of package:\n";
          if OS.Process.isSuccess (OS.Process.system "python3 -m pip show bir_angr") then () else
            raise ERR "do_symb_exec" "python package bir_angr is not installed";
          print "... metadata end.\n";
          bir_exec_wrapLib.get_exec_output ("python3 -E -m bir_angr.symbolic_execution \"" ^ magicinputfilename ^ "\" -ba " ^ start_lbl_str)
        ) else (
          print "... using symbolic_execution_wrapper.py in python subdirectory ...\n";
          bir_exec_wrapLib.get_exec_output ("python3 -E \"" ^ pythonscript ^ "\" \"" ^ magicinputfilename ^ "\" -ba " ^ start_lbl_str)
        );
      val _ = if false then print output else ();

      (* extract json structure from output *)
      val lines = String.tokens (fn x => x = #"\n") output;
      val marker_line = "========== JSON START =========="
      val (json_str, _) =
        List.foldl
          (fn (line, (s, found)) =>
             if found then
               (s ^ line ^ "\n", found)
             else
               (s, line = marker_line))
          ("", false)
          lines;
      val _ = if false then print json_str else ();
      val result = parse_json_output obsrefmap json_str;
    in
      result
    end;



end (* local *)

end (* struct *)
