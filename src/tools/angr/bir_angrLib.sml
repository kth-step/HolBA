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

  open Json bslSyntax bir_quotationLib listSyntax;
  open bir_exp_memTheory bir_exp_memSyntax;
  open bir_valuesTheory bir_valuesSyntax;
  open bir_expTheory bir_expSyntax;
  open bir_immTheory bir_immSyntax;
  open bir_interval_expTheory;
  open bir_typing_expTheory;
  open bir_bool_expSyntax;
  open bir_envSyntax;
  open numSyntax;

  open bir_angrTheory;

  open bir_exp_immTheory;
  open bir_exp_memTheory;

  (* error handling *)
  val libname = "bir_angrLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  infix 9 <?>;
  infix 8 <|>;
  fun init [x] = []
    | init (x::y::ys) = let val zs = init (y::ys) in x::zs end;
  fun intercalate x zs = foldr (fn (z,zs) => if null zs then z::zs else z::x::zs) [] zs;


 fun type_of_bir_exp_CONV term =
    (* Manual test
    val term = ``
      BExp_BinExp BIExp_Plus
        (BExp_Const (Imm32 20w))
        (BExp_Const (Imm32 22w))
    ``;
    val thm = type_of_bir_exp_CONV ``type_of_bir_exp ^term``;
    *)
    let
      open bir_immTheory
      open bir_valuesTheory
      open bir_envTheory
      open bir_exp_memTheory
      open bir_bool_expTheory
      open bir_extra_expsTheory
      open bir_nzcv_expTheory
      val type_of_bir_exp_thms = [
        type_of_bir_exp_def,
        bir_var_type_def,
        bir_type_is_Imm_def,
        type_of_bir_imm_def,
        BExp_Aligned_type_of,
        BExp_unchanged_mem_interval_distinct_type_of,
        bir_number_of_mem_splits_REWRS,
        BType_Bool_def,
        bir_exp_true_def,
        bir_exp_false_def,
        BExp_MSB_type_of,
        BExp_nzcv_ADD_DEFS,
        BExp_nzcv_SUB_DEFS,
        n2bs_def,
        BExp_word_bit_def,
        BExp_Align_type_of,
        BExp_ror_type_of,
        BExp_LSB_type_of,
        BExp_word_bit_exp_type_of,
        BExp_ADD_WITH_CARRY_type_of,
        BExp_word_reverse_type_of,
        BExp_ror_exp_type_of,
        BExp_CastMask_type_of,
        BExp_AppendMask_type_of,
        bir_immtype_of_size_def
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end
      handle e => raise wrap_exn "type_of_bir_exp_CONV" e;

  fun bir_type_of term =
    let
      open optionSyntax;
      val type_o_thm = type_of_bir_exp_CONV ``type_of_bir_exp ^term``
      val type_o_tm = (snd o dest_eq o concl) type_o_thm
    in
      dest_some type_o_tm
    end
    handle e => raise ERR "bir_type_of" ("ill-typed term: " ^ Parse.term_to_string term);

  fun strip_var ss =
      let val sz_str::_::name = rev (List.map implode ss);
          val sz = case Int.fromString sz_str of
                       NONE => 64
                     | SOME n => n;
          val ty = gen_mk_BType_Imm sz;
      in
        mk_BVar_string (concat (intercalate "_" (rev name)),ty)
      end;
  
  val angr_var =
      token (fmap strip_var (sep_by1 (many1 (sat Char.isAlphaNum)) (char #"_")));

  (* TODO complete with missing operators *)
  val binary_op_factor =
      choicel [seq (char #"*") (return bmult)
	      ,seq (string "/s") (return bsdiv)
              ,seq (char #"/") (return bdiv)
              ,seq (string "%s") (return bsmod)
	      ,seq (char #"%") (return bmod)
	      ,seq (char #"^") (return bxor)] <?> "multiplication or division operator";
  
  val binary_op_term =
      choicel [seq (char #"+") (return bplus)
              ,seq (char #"-") (return bminus)] <?> "term operator";
  fun consappend (t1,t2) = t1@t2;

  val binary_pred =
      choicel [seq (string "==") (return beq)
              ,seq (string "!=") (return bneq)
              ,seq (string "<=s") (return bsle)
	      ,seq (string "<=") (return ble)
	      ,seq (string "<s") (return bslt)
              ,seq (char #"<") (return blt)
              ,seq (string ">=s") (return bsge)
	      ,seq (string ">=") (return bge)
              ,seq (string ">s") (return bsgt)
	      ,seq (char #">") (return bgt)] <?> "binary predicate operator";
  
  fun is_BExp_AppendMask expr =
      if is_comb expr
      then let open boolSyntax;
               val (func, [list]) = strip_comb expr;
           in
             identical func “BExp_AppendMask” andalso
             type_of list = Type‘:(num # num # bir_exp_t) list’
           end handle _ => false
      else false;
  fun is_BExp_CastMask expr =
      if is_comb expr
      then let open boolSyntax;
               val (func, [sz,u,l,var,csz]) = strip_comb expr;
           in
             identical func “BExp_CastMask” andalso
             type_of sz = Type‘:bir_immtype_t’ andalso
             type_of u = Type‘:num’ andalso
             type_of l = Type‘:num’ andalso
             type_of var = Type‘:bir_exp_t’ andalso
             type_of csz = Type‘:bir_immtype_t’
           end handle _ => false
      else false;
  fun dest_BExp_CastMask expr =
      if is_BExp_CastMask expr
      then let open boolSyntax;
               val (func, [sz,u,l,var,csz]) = strip_comb expr;
           in
             (sz,u,l,var,csz)
           end
      else raise ERR "dest_BExp_CastMask" "not a BExp_CastMask";
  fun fill_mask expr =
      let open bir_expSyntax bir_envSyntax bir_immSyntax numSyntax;
      in
        if is_BExp_CastMask expr
        then let val (sz,u,l,var,csz) = dest_BExp_CastMask expr
             in
               “(^u, ^l, ^var)”
             end
        else
          let val sz = size_of_bir_immtype_t (dest_BType_Imm (bir_type_of expr))
          in
            “(^(term_of_int (Int.- (sz,1))), 0:num, ^expr)”
          end
      end;
  fun list_bappend_mask [y] = y
    | list_bappend_mask ys =
      let fun flatten_appmask [] = []
            | flatten_appmask (t::ts) =
              if is_BExp_AppendMask t
              then let val (_,inner) = dest_comb t
                       val (es,_) = dest_list inner
                   in
                     es @ flatten_appmask ts
                   end
              else
                fill_mask t :: flatten_appmask ts
          val es = mk_list (flatten_appmask ys, Type‘: num # num # bir_exp_t’)
      in “BExp_AppendMask ^es”
      end;

  fun bmask exp (u,l) =
    let
      val sz = (dest_BType_Imm o bir_type_of o (snd o dest_eq o concl o EVAL)) exp;
      val csz = “THE (bir_immtype_of_size ^(term_of_int ((u - l) + 1)))”;
      val maskexp = “BExp_CastMask ^sz ^(term_of_int u) ^(term_of_int l) ^exp ^csz”;
    in
      return maskexp
    end;

  fun bitvalue p =
      let val bv = seq (string "BV") (bind (token (fmap Arbnum.toInt dec)) (token o p))
      in
        bracket (char #"<") bv (char #">")
      end;

  fun boolvalue p =
      let val bv = seq (token (string "Bool")) (token p)
      in
        bracket (char #"<") bv (char #">")
      end;
  
  fun gen_bir_exp_angr sz =
    fix (fn bir_exp =>
            let open Word;
                val angr_num = try hex <|> dec <?> "angr numeric literal";
                val annotated_imm = bind angr_num (fn n =>
                                    seq (char #"#")
                                    (bind dec (fn sz =>
                                                  return (mk_Imm_of_num (Arbnum.toInt sz) n))));
                val annotated_imm_ignore = try (bind angr_num (fn n =>
                                    seq (char #"#")
                                    (bind dec (fn sz =>
                                    return n)))) <|> angr_num;
                val mem_string = string "MEM";
                val load_type = seq (char #"_")
                                (seq (many1 (sat Char.isAlphaNum))
                                     (seq (char #"_") (fmap Arbnum.toInt dec)))
                val mem_load =
                    seq mem_string
                    (bind (bracket (char #"[") (bitvalue (fn _ => bir_exp)) (char #"]"))  (fn addr =>
                     option load_type  (bload8_le default_mem addr) (return o bloadi_le default_mem addr)));
                val range = bind dec (fn lower => seq (char #":")
                           (bind dec (fn upper => return (Arbnum.toInt lower, Arbnum.toInt upper))))
                val ifthenelse = seq (token (string "if"))
                                 (bind bir_exp (fn cond =>
                                 (seq (token (string "then"))
                                 (bind bir_exp (fn e1 =>
                                 (seq (token (string "else"))
                                 (bind bir_exp (fn e2 =>
                                 return (bite (cond,e1,e2))))))))))
                                 <?> "if-then-else";
                val shift_expr = seq (string "LShR")
                                 (bind (token (pairp bir_exp bir_exp)) (fn (exp1,exp2) =>
                                 return (brshift (exp1,exp2))))
                                    <?> "LShR expression";
                val signext_expr = seq (string "SignExt")
                                 (bind (token (pairp (bind dec (fn len => return (Arbnum.toInt len))) bir_exp)) (fn (n,exp) =>
				 return (list_bappend_mask
				 [“BExp_AppendMask [(^(term_of_int (Int.- (n,1))), 0, ^(bite (bhighcast1 exp, ``BExp_Const (Imm128 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw)``, bconst128 0)))]”, exp])))
                                    <?> "SignExt expression";
		val logical =  choicel [bracket (char #"(") bir_exp (char #")")
                                      ,bind unary_op
                                            (fn oper => fmap oper bir_exp)
                                      ,try mem_load
                                      ,try ifthenelse
                                      ,try shift_expr
				      ,try signext_expr
                                      ,try (fmap bconstimm annotated_imm)
                                      ,fmap bconstimm (gen_bir_imm sz)
                                      ,fmap bden angr_var
                                   ] <?> "logical expression"
                val term = chainr1 (token logical) (binop binary_op_factor) <?> "term"
                val appterm = bind (chainl1 (token term) (binop binary_op_term))
				   (fn exp => option (bracket (char #"[") range (char #"]")) exp (bmask exp))
				     <?> "binary expression"
		val factor = chainr1 (token appterm) (binop binary_op_bitwise)
                                     <?> "factor"
                val binexp = fmap list_bappend_mask
                                  (chainr1 (bind (token factor) (fn v => return [v]))
                                  (binop (seq (token (string "..")) (return consappend))))
                                     <?> "angr appendmask expression"
	        val binpred = bind (token binexp) (fn e1 =>
                              bind (binop binary_pred) (fn oper =>
                              bind (token binexp) (fn e2 =>
                              return (oper e1 e2))))
                                   <?> "binary predicate"
            in
             try binpred <|> binexp
            end
        ) <?> "angr expression";

(*  val angr_variable =
      fmap (concat o intercalate "_" o init o init)
           (bind (sep_by1 (fmap implode (many1 (sat Char.isAlphaNum))) (char #"_"))
                 (fn list => seq (many (sat (not o Char.isSpace))) (return list)))
           <?> "angr variable";

  val bir_angr_var = gen_bir_var angr_variable 64; *)
  fun bir_angr_bool_exp sz =  try (seq (token (string "True")) (return btrue))
                               <|> try (seq (token (string "False")) (return bfalse))
                               <|> token (gen_bir_exp_angr sz);

in  (* local *)
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

  fun match p str = parse (seq junk p) str
                    handle e => raise ERR "match" (make_string_parse_error e)
                    handle Match => raise ERR "parser match error" ("cannot deal with: " ^ str);

  fun parse_guard str = match (boolvalue (bir_angr_bool_exp 1)) str

  (* Should parse_obs_exp and parse_obscond_exp restrict input bitsize? *)
  fun parse_obs_exp str =
      match (bitvalue bir_angr_bool_exp) str;
  
  fun parse_obscond_exp str =
      match (bitvalue bir_angr_bool_exp) str;
  
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

(*
val json = STRING "<Bool (R27_3_64[7:0] & 7#8) == 0#8>";
(parse_guard o fromJsonString) json;

val obsrefmap = Redblackmap.insert (Redblackmap.mkDict Arbnum.compare,
                  Arbnum.fromInt 0, (``0:num``, ``HD``));
val json = ARRAY [NUMBER (Arbnum.fromInt 0), STRING "<BV1 1#1>", ARRAY [STRING "<BV64 0x16#64>"]];
parse_obs obsrefmap json;
*)

 in
  (* make this function available for mechanized testing (test scripts) *)
  val parse_guard = parse_guard;

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

      val usePythonPackage = not (Option.getOpt(OS.Process.getEnv("HOLBA_ANGR_USE_PYTHONDIR"), "") = "1");

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
