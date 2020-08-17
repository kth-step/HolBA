open HolKernel Parse

open bir_expSyntax;
open bir_programSyntax;
open bir_block_collectionLib;

open binariesLib;

fun bexp_of_stmt s =
  if is_BStmt_Assign s then
    (snd o dest_BStmt_Assign) s
  else if is_BStmt_Assert s then
    dest_BStmt_Assert s
  else raise ERR "bexps_of_stmt" "unknown statement type";

fun bexps_of_jtgt tgt =
  if is_BLE_Label tgt then []
  else if is_BLE_Exp tgt then [dest_BLE_Exp tgt]
  else raise ERR "bexps_of_jtgt" "unknown jump target type";

fun bexps_of_estmt s =
  if is_BStmt_Jmp s then bexps_of_jtgt (dest_BStmt_Jmp s)
  else if is_BStmt_CJmp s then
    let
      val (c,t1,t2) = dest_BStmt_CJmp s
    in
      c::((bexps_of_jtgt t1)@(bexps_of_jtgt t2))
    end
  else raise ERR "bexps_of_estmt" "unknown end statement type";

fun gen_bexp_list bl_dict lbl_tm =
  let
    val bl = (valOf o (lookup_block_dict bl_dict)) lbl_tm;
    val (_, stmts_tm, est) = dest_bir_block bl;

    val stmts = (fst o listSyntax.dest_list) stmts_tm;

    val exps = (bexps_of_estmt est)@(List.map bexp_of_stmt stmts)
  in
    exps
  end;


val prog_lbl_tms = get_block_dict_keys bl_dict_;

val exps = List.concat (List.map (gen_bexp_list bl_dict_) prog_lbl_tms);

(*
length exps
hd exps
*)

val n_loads = (List.length o List.filter is_BExp_Load) exps;
val n_stores = (List.length o List.filter is_BExp_Store) exps;

(*
val n_str_loads =
  (List.length o
   List.filter (String.isSubstring "BExp_Load" o term_to_string)
  ) exps;
*)

fun find_subterm is_tm_fun tm =
    if is_tm_fun tm then
      SOME tm
    else if is_comb tm then
      let
        val (l,r) = dest_comb tm;
      in
        case find_subterm is_tm_fun l of
           SOME tm2 => SOME tm2
         | NONE => find_subterm is_tm_fun r
      end
    else
      NONE
    ;

val n_sub_loads =
  (List.length o
   List.filter (isSome o find_subterm is_BExp_Load)
  ) exps;
val n_sub_stores =
  (List.length o
   List.filter (isSome o find_subterm is_BExp_Store)
  ) exps;


val exact_sub_loads =
  (List.filter (fn tm => (isSome o find_subterm is_BExp_Load) tm andalso
                         (not o is_BExp_Load) tm)
  ) exps;
