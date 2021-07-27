structure birprogjsonexportLib =
struct
local
  open HolKernel Parse boolLib bossLib;

  open bir_programSyntax;

  open listSyntax;

  (* error handling *)
  val libname = "birprogjsonexportLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

  fun estmttojson estmt =
    if is_BStmt_Halt estmt then
      Json.OBJECT [("estmttype", Json.STRING "HALT"), ("exp", Json.STRING (term_to_string (dest_BStmt_Halt estmt)))]
    else if is_BStmt_Jmp estmt then
      Json.OBJECT [("estmttype", Json.STRING "JMP"), ("lbl", Json.STRING (term_to_string (dest_BStmt_Jmp estmt)))]
    else if is_BStmt_CJmp estmt then
      let
        val (cnd_tm, lblet_tm, lblef_tm) = dest_BStmt_CJmp estmt;
      in
        Json.OBJECT [("estmttype", Json.STRING "CJMP"),
                     ("cnd", Json.STRING (term_to_string cnd_tm)),
                     ("lblt", Json.STRING (term_to_string lblet_tm)),
                     ("lblf", Json.STRING (term_to_string lblef_tm))]
      end
    else
      raise ERR "estmttojson" ("unknown end statement type: " ^ (term_to_string estmt));


  fun stmttojson stmt =
    if is_BStmt_Assign stmt then
      let
        val (var_tm, exp_tm) = dest_BStmt_Assign stmt;
      in
        Json.OBJECT [("stmttype", Json.STRING "ASSIGN"),
                     ("var", Json.STRING (term_to_string var_tm)),
                     ("exp", Json.STRING (term_to_string exp_tm))]
      end
    else if is_BStmt_Assert stmt then
      Json.OBJECT [("stmttype", Json.STRING "ASSERT"), ("exp", Json.STRING (term_to_string (dest_BStmt_Assert stmt)))]
    else if is_BStmt_Assume stmt then
      Json.OBJECT [("stmttype", Json.STRING "ASSUME"), ("exp", Json.STRING (term_to_string (dest_BStmt_Assume stmt)))]
    else if is_BStmt_Observe stmt then
      let
        val (id_tm, cnd_tm, obss_tm, obsf_tm) = dest_BStmt_Observe stmt;

        val obs_tm_list = (fst o dest_list) obss_tm;
        val obs_json_list = List.map (fn obs_tm => Json.STRING (term_to_string obs_tm)) obs_tm_list;
      in
        Json.OBJECT [("stmttype", Json.STRING "OBSERVE"),
                     ("id", Json.STRING (term_to_string id_tm)),
                     ("cnd", Json.STRING (term_to_string cnd_tm)),
                     ("obss", Json.ARRAY obs_json_list),
                     ("obsf", Json.STRING (term_to_string obsf_tm))]
      end
    else
      raise ERR "stmttojson" ("unknown basic statement type: " ^ (term_to_string stmt));


  fun blocktojson block =
    let
      val (tm_lbl, tm_stmts, tm_last_stmt) = dest_bir_block block;

      val tm_stmt_list = (fst o dest_list) tm_stmts;

      val lbl_json  = Json.STRING (term_to_string tm_lbl);
      val stmts_json = Json.ARRAY (List.map stmttojson tm_stmt_list);
      val estmt_json = estmttojson tm_last_stmt;
    in
      Json.OBJECT [("lbl", lbl_json), ("stmts", stmts_json), ("estmt", estmt_json)]
    end;

(*
  val bprog_t = bprog;
*)
  fun birprogtojsonstr bprog_t =
    let
       (* simple normalization to get rid of shorthand definitions from lifter and similar *)
       val bprog_norm_t = (snd o dest_eq o concl o EVAL) bprog_t;

       (* translation to json format (serialize), including term pretty printing for bir expressions and the like *)
       val blocks = (fst o dest_list o dest_BirProgram) bprog_norm_t;

      val addIndents = true;
      val serialize = if addIndents then Json.serialiseIndented else Json.serialise;
    in
      serialize (Json.ARRAY (List.map blocktojson blocks))
    end;


end (* local *)

end (* struct *)
