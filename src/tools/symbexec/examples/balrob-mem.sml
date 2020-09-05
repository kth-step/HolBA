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

fun collect_subterm is_tm_fun combine_fun acc tm =
    if is_comb tm then
      let
        val (l,r) = dest_comb tm;

        val acc_   = if is_tm_fun tm then
                       combine_fun (tm, acc)
                     else
                       acc;
        val acc_l  = collect_subterm is_tm_fun combine_fun acc_  l;
        val acc_lr = collect_subterm is_tm_fun combine_fun acc_l r;
      in
        acc_lr
      end
    else
      acc
    ;

fun load_to_size_endi tm =
  if (not o is_BExp_Load) tm then
    raise ERR "load_to_size" "not a load!"
  else
  let
    val (_,_,en,sz) = dest_BExp_Load tm;
  in
    (sz,en)
  end;

(* ================================================================================= *)
(* this is copied code from somewhere else *)
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
        BExp_ror_exp_type_of
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end;
(* ================================================================================= *)

(*
val tm = ``
BExp_Store
       (BExp_Store
          (BExp_Store
             (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                (BExp_BinExp BIExp_Minus
                   (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                   (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                (BExp_Den (BVar "R5" (BType_Imm Bit32))))
             (BExp_BinExp BIExp_Minus
                (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                (BExp_Const (Imm32 12w))) BEnd_LittleEndian
             (BExp_Den (BVar "R6" (BType_Imm Bit32))))
          (BExp_BinExp BIExp_Minus
             (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
             (BExp_Const (Imm32 8w))) BEnd_LittleEndian
          (BExp_Den (BVar "R7" (BType_Imm Bit32))))
       (BExp_BinExp BIExp_Minus
          (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
          (BExp_Const (Imm32 4w))) BEnd_LittleEndian
       (BExp_Den (BVar "LR" (BType_Imm Bit32)))
``;
*)

fun store_to_size_endi tm =
  if (not o is_BExp_Store) tm then
    raise ERR "store_to_size" "not a store!"
  else
  let
    val (_,_,en,tm_v) = dest_BExp_Store tm;
    val bty_v_o = (snd o dest_eq o concl o type_of_bir_exp_CONV) ``type_of_bir_exp ^tm_v``;
    val bty_v = if optionSyntax.is_some bty_v_o then
                  optionSyntax.dest_some bty_v_o
                else
                  raise ERR "store_to_size" "couldn't resolve expression type";

    val sz =
      if bir_valuesSyntax.is_BType_Imm bty_v then
        bir_valuesSyntax.dest_BType_Imm bty_v
      else
        raise ERR "store_to_size" "no bir imm";
  in
    (sz,en)
  end;

(*
collect_subterm is_BExp_Store (fn (tm, acc) => ((store_to_size_endi) tm)::acc) [] tm
*)

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


val size_loads =
   (List.concat o List.map (collect_subterm is_BExp_Load (fn (tm, acc) => ((pairSyntax.mk_pair o load_to_size_endi) tm)::acc) [])) exps;

val size_stores =
   (List.concat o List.map (collect_subterm is_BExp_Store (fn (tm, acc) => ((pairSyntax.mk_pair o store_to_size_endi) tm)::acc) [])) exps;


fun mk_histogram_h []        acc = acc
  | mk_histogram_h (tm::tms) acc =
     let
       val tm_num = Redblackmap.find (acc, tm) handle _ => 0;
       val acc_n  = Redblackmap.insert (acc, tm, tm_num + 1);
     in
       mk_histogram_h tms acc_n
     end;


fun mk_histogram tms =
  (Redblackmap.listItems o mk_histogram_h tms) (Redblackmap.mkDict Term.compare);

val size_loads_nums =
  mk_histogram size_loads;

val size_stores_nums =
  mk_histogram size_stores;
