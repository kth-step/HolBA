open HolKernel Parse

open binariesLib;
open binariesDefsLib;

open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open optionSyntax;
open wordsSyntax;
open listSyntax;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val entry_label = "imu_handler_pid_entry";

fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")");

datatype cfg_target =
    CFGT_DIR   of term
  | CFGT_INDIR of term;

(* Unknown: if not determined yet *)
(* Halt, Basic, Jump, CondJump can be determined from BIR code for direct jumps *)
(* indirect jumps as well as Call and Return needs annotation or some form of analysis*)
datatype cfg_node_type =
    CFGNT_Unknown
  | CFGNT_Halt
  | CFGNT_Basic
  | CFGNT_Jump
  | CFGNT_CondJump
  | CFGNT_Call
  | CFGNT_Return;

(* cfg nodes correspond to BIR blocks *)
type cfg_node = {
  (* id: BIR label term *)
  CFGN_lbl_tm : term,
  (* meta information from binary *)
  CFGN_descr  : string,
  CFGN_succ   : term option,
  (* flow information exported from BIR *)
  CFGN_goto   : cfg_target list,
  (* type can be unknown and filled in by later passes *)
  CFGN_type   : cfg_node_type
};

type cfg_graph = {
  CFGG_name  : string,
  CFGG_entry : term,
  CFGG_nodes : cfg_node list
};

(*
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 1006);
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 0xc1c);
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 10164);
val lbl_tm = (mk_lbl_tm o valOf) (mem_find_rel_symbol_addr_ "motor_prep_input");
val lbl_tm = (mk_lbl_tm o valOf) (mem_find_rel_symbol_addr_ "motor_set_l");
val lbl_tm = (mk_lbl_tm o valOf) (mem_find_rel_symbol_addr_ entry_label);
val entry_lbl_tm = lbl_tm;

build_cfg entry_lbl_tm
*)


fun is_lbl_in_cfg_nodes lbl_tm (ns:cfg_node list) =
  List.exists (fn n => (#CFGN_lbl_tm n) = lbl_tm) ns;

(* val ble = (dest_BStmt_Jmp bbes) *)
fun BLE_to_cfg_target ble =
  if is_BLE_Label ble then
    CFGT_DIR (dest_BLE_Label ble)
  else if is_BLE_Exp ble then
    let
      val exp = dest_BLE_Exp ble;
      val res = (snd o dest_eq o concl o EVAL) ``bir_eval_exp ^exp (BEnv (\x. NONE))``;
    in
      if is_none res then
        CFGT_INDIR exp
      else if is_some res then
        CFGT_DIR ((mk_BL_Address o dest_BVal_Imm o dest_some) res)
      else
        raise ERR "BLE_to_cfg_target" "what happened here during trial evaluation?"
    end
  else
    raise ERR "BLE_to_cfg_target" "unknown BLE type";

fun bir_es_to_cfg_targets bbes = List.map BLE_to_cfg_target (
          if is_BStmt_Jmp bbes then
            [dest_BStmt_Jmp bbes]
          else if is_BStmt_CJmp bbes then
            ((fn (_, a, b) => [a, b]) (dest_BStmt_CJmp bbes))
          else if is_BStmt_Halt bbes then
            []
          else
            raise ERR "bir_es_to_bles"
                      ("unknown BStmt end stmt type: " ^
                       (term_to_string bbes)));

local
 fun list_split_pred_aux acc p [] = fail ()
    | list_split_pred_aux acc p (x::xs) =
      (if x = p then (List.rev acc, xs)
       else list_split_pred_aux (x::acc) p xs)

  fun list_split_pred p = list_split_pred_aux [] p
in
fun lbl_hc_tm_to_descr_succ lbl =
  let
    val _ = if is_BL_Address_HC lbl then ()
            else raise ERR "lbl_hc_tm_to_descr_succ"
                   ("we can only deal with output from the lifter, need BL_Address_HC: " ^
                    (term_to_string lbl));
    val (addr_tm, descr_tm) = dest_BL_Address_HC lbl;
    val descr = stringSyntax.fromHOLstring descr_tm;
    val addr = (dest_word_literal o dest_Imm32) addr_tm;

    val instrLen2 = (length o fst o (list_split_pred #" ") o explode) descr;
    val _ = if instrLen2 mod 2 = 0 then () else
            raise ERR "lbl_hc_tm_to_descr_succ"
                      ("something went wrong when trying to find the binary " ^
                       "instruction code: " ^
                       (term_to_string lbl));
    val instrLen = instrLen2 div 2;
    val _ = if instrLen = 2 orelse instrLen = 4 then () else
            raise ERR "lbl_hc_tm_to_descr_succ"
                      ("something went wrong when trying to find the binary " ^
                       "instruction code, wrong instruction length: " ^
                       (term_to_string lbl));

    val addr_succ = Arbnum.+ (addr, Arbnum.fromInt instrLen);
    val succ_lbl_tm = mk_lbl_tm addr_succ;
  in
    (descr, succ_lbl_tm)
  end;
end

fun determine_cfg_node_type cfg_t_l succ_tm_o =
  let
    val contains_indir = List.foldr (fn (x, b) => b orelse
                    (fn CFGT_INDIR _ => true | CFGT_DIR _ => false) x
                ) false cfg_t_l;
    val cfgn_type =
      if contains_indir then CFGNT_Unknown else
      case cfg_t_l of
          []  => CFGNT_Halt
        | [x] => if not (isSome succ_tm_o) then CFGNT_Jump else
                 if x = CFGT_DIR (valOf succ_tm_o) then CFGNT_Basic else
                   CFGNT_Jump
        | _   => CFGNT_CondJump;
  in
    cfgn_type
  end;

(*
val lbl_tm = hd prog_lbl_tms_;
List.map to_cfg_node prog_lbl_tms_;
*)
fun to_cfg_node lbl_tm =
  let
    val bl = case prog_get_block_ lbl_tm of SOME x => x
                    | NONE => raise ERR "to_cfg_nodes" ("label couldn't be found: " ^ (term_to_string lbl_tm));
    val (lbl, _, bbes) = dest_bir_block bl;

    val (descr, succ_lbl_tm) = lbl_hc_tm_to_descr_succ lbl;
    val succ_tm_o = if isSome (prog_get_block_ succ_lbl_tm) then SOME succ_lbl_tm else NONE;

    val cfg_t_l = bir_es_to_cfg_targets bbes;

    val cfgn_type = determine_cfg_node_type cfg_t_l succ_tm_o;

    val n = { CFGN_lbl_tm = lbl_tm,
              CFGN_descr  = descr,
              CFGN_succ   = succ_tm_o,
              CFGN_goto   = cfg_t_l,
              CFGN_type   = cfgn_type
            } : cfg_node;

  in n end;


(*
fun cfg_target_to_lbl_tm (CFGT_DIR   tm) = SOME tm
  | cfg_target_to_lbl_tm (CFGT_INDIR _ ) = NONE;
*)
fun cfg_targets_to_lbl_tms l = SOME (List.map (fn
         CFGT_DIR tm  => tm
       | CFGT_INDIR _ => raise ERR "cfg_targets_to_lbl_tms" "") l)
   handle HOL_ERR _ => NONE;

val BVarLR32_tm = ``BVar "LR" (BType_Imm Bit32)``;
fun is_Assign_LR tm =
  if is_BStmt_Assign tm then
    ((fst o dest_BStmt_Assign) tm) = BVarLR32_tm
  else
    false;

fun find_node (ns: cfg_node list) lbl_tm =
  valOf (List.find (fn n => (#CFGN_lbl_tm n) = lbl_tm) ns)
  handle Option => raise ERR "find_node" ("couldn't find node: " ^ (term_to_string lbl_tm));

(*
val ns = List.map to_cfg_node prog_lbl_tms_;
val n  = find_node ns lbl_tm;
val ns = List.map (update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
*)
fun update_node_guess_type_call n =
  if #CFGN_type n <> CFGNT_Jump then n else
  let
    val debug_on = false;

    val lbl_tm = #CFGN_lbl_tm n;
    val cfg_t_l = #CFGN_goto n;

    val bl = case prog_get_block_ lbl_tm of SOME x => x
                    | NONE => raise ERR "to_cfg_nodes" ("label couldn't be found: " ^ (term_to_string lbl_tm));
    val (_, bbs, _) = dest_bir_block bl;

    val goto_tm = (((hd o valOf o cfg_targets_to_lbl_tms) cfg_t_l
        handle Empty => raise Option)
        handle Option => raise ERR "update_node_guess_type_call"
                                   "there should be exactly 1 direct jump");

    val isCall_lr  = List.exists is_Assign_LR ((fst o dest_list) bbs);
    val isCall_to_entry = ((length cfg_t_l = 1) andalso
                           (List.exists (fn x => x = goto_tm) prog_fun_entry_lbl_tms));

    val _ = if isCall_lr = isCall_to_entry then ()
            else raise ERR "update_node_guess_type_call"
                           "something in call detection is unexpected";
    val isCall = isCall_lr;

    val _ = if not (debug_on andalso isCall) then () else
            (print "call        ::: "; print (#CFGN_descr n); print "\t"; print_term lbl_tm);

    val new_type = if isCall then CFGNT_Call else #CFGN_type n;

    val new_n =
            { CFGN_lbl_tm = #CFGN_lbl_tm n,
              CFGN_descr  = #CFGN_descr n,
              CFGN_succ   = #CFGN_succ n,
              CFGN_goto   = #CFGN_goto n,
              CFGN_type   = new_type
            } : cfg_node;
  in
    new_n
  end;

(*
length ns

val ns = List.map (update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 7936);
val n  = find_node ns lbl_tm;
val _ = List.map (update_node_guess_type_return o update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
*)
fun update_node_guess_type_return n =
  if #CFGN_type n <> CFGNT_Unknown then n else
  let
    val debug_on = false;

    val lbl_tm = #CFGN_lbl_tm n;
    val descr = #CFGN_descr n;

    val isReturn = ((String.isSubstring "pop {" descr) andalso
                    (String.isSubstring "pc}" descr))
                   orelse
                   (String.isSubstring "(bx lr)" descr);

    (* hack for hand inspected instructions *)
    val isReturn = isReturn orelse (
                   (lbl_tm = mk_lbl_tm (Arbnum.fromInt 0x1fc)) andalso
                   (String.isPrefix "4718 (" descr)
        );

    val _ = if not (debug_on andalso isReturn) then () else
            (print "return      ::: "; print descr; print "\t"; print_term lbl_tm);

    (* hack for indirect jumps *)
    val isIndirJump = false (*String.isSubstring "(mov pc," descr;*);
    val _ = if not (isReturn andalso isIndirJump) then () else
            raise ERR "update_node_guess_type_return" "cannot be both, weird.";

    val _ = if not (debug_on andalso isIndirJump) then () else
            (print "indirect J  ::: "; print descr; print "\t"; print_term lbl_tm);

    (* still unclear type... *)
    val _ = if (isReturn orelse isIndirJump) (* orelse (not debug_on) *) then ()
            else print ("update_node_guess_type_return :: " ^
                           "cannot determine type: " ^ descr ^
                            "\t" ^ (term_to_string lbl_tm) ^ "\n");


    val new_type = #CFGN_type n;
    val new_type = if isReturn    then CFGNT_Return else new_type;
    val new_type = if isIndirJump then CFGNT_Call   else new_type;

    val new_goto = if false (*isReturn*)    then [] else #CFGN_goto n;

    val new_n =
            { CFGN_lbl_tm = #CFGN_lbl_tm n,
              CFGN_descr  = #CFGN_descr n,
              CFGN_succ   = #CFGN_succ n,
              CFGN_goto   = new_goto,
              CFGN_type   = new_type
            } : cfg_node;
  in
    new_n
  end;



fun cfg_targets_to_lbl_tms_exn l et =
    (valOf o cfg_targets_to_lbl_tms) l
    handle Option => raise ERR "cfg_targets_to_lbl_tms_exn" ("unexpected indirection: " ^ et);

fun cfg_targets_to_direct_lbl_tms l = List.foldr (fn
         (CFGT_DIR   tm, ls) => tm::ls
       | (CFGT_INDIR tm , ls) => (print ("unexpected indirection: " ^
                                        (term_to_string tm) ^ "\n"); ls)
  ) [] l;

fun get_fun_cfg_walk_succ (n: cfg_node) =
  let
    val lbl_tm = #CFGN_lbl_tm n;
    val descr  = #CFGN_descr n;
    val n_type = #CFGN_type n;
    val n_goto = #CFGN_goto n;
    val debug_on = false;
    val _ = if not debug_on then () else
            print ("node: " ^ (term_to_string lbl_tm) ^ "\n" ^
                   " - " ^ descr ^ "\n");
  in
    case n_type of
        CFGNT_Unknown   => (if debug_on then print "UNRESOLVED NODE\n" else (); [])
      | CFGNT_Halt      => []
      | CFGNT_Basic     => cfg_targets_to_direct_lbl_tms n_goto
      | CFGNT_Jump      => cfg_targets_to_direct_lbl_tms n_goto
      | CFGNT_CondJump  => cfg_targets_to_direct_lbl_tms n_goto
      | CFGNT_Call      => (* ((valOf o #CFGN_succ) n)::ls*)
                           (*cfg_targets_to_direct_lbl_tms n_goto*)
                           [(valOf o #CFGN_succ) n]
                          (* TODO: remove this successor hack for the returns later *)
      | CFGNT_Return    => [] (* cfg_targets_to_direct_lbl_tms n_goto *)
  end;


fun build_fun_cfg_nodes _  acc []                 = acc
  | build_fun_cfg_nodes ns acc (lbl_tm::lbl_tm_l) =
      let
        val n = find_node ns lbl_tm;
        val n_type = #CFGN_type n;

        val _ = if n_type <> CFGNT_Unknown then () else
                (print "indirection ::: in ";
                 print (prog_lbl_to_mem_rel_symbol lbl_tm);
                 print "\t"; print (#CFGN_descr n);
                 print "\t"; print_term lbl_tm);

        val new_node  = if n_type = CFGNT_Unknown then [] else [n];
        val new_nodes = new_node@acc;

        val next_tm_l      = List.filter (fn x => not ((is_lbl_in_cfg_nodes x new_nodes) orelse
                                                       (List.exists (fn y => x = y) lbl_tm_l)))
                                         (get_fun_cfg_walk_succ n);
        val new_lbl_tm_l   = next_tm_l@lbl_tm_l;
      in
        build_fun_cfg_nodes ns new_nodes new_lbl_tm_l
      end;

fun build_fun_cfg ns name =
  let
    val entry_lbl_tm = mem_symbol_to_prog_lbl name;
    val cfg_comp_ns = build_fun_cfg_nodes ns [] [entry_lbl_tm];
    val _ = print ("walked " ^ (Int.toString (length cfg_comp_ns)) ^
                   " nodes (" ^ name ^ ")\n");
    (* validate that all collected nodes belong to the function *)
    val ns_names   = List.map (fn n =>
           (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) (#CFGN_lbl_tm n)
      ) cfg_comp_ns
      handle Option => raise ERR "build_fun_cfg" "cannot find label for node address";
    val allAreName = List.foldr (fn (n,b) => b andalso (
           n = name
      )) true ns_names;
  in
    {
      CFGG_name  = name,
      CFGG_entry = entry_lbl_tm,
      CFGG_nodes = cfg_comp_ns
    } : cfg_graph
  end;

val lbl_tm = mem_symbol_to_prog_lbl entry_label;
val entry_lbl_tm = lbl_tm;

val ns = List.map (update_node_guess_type_return o update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;

val _ = build_fun_cfg ns entry_label;
val _ = build_fun_cfg ns "__aeabi_fmul";


(*
fun sanity_check_controlflow prog_tm entry_label =

fun enumerate_paths
(* what happens if we try this? *)
*)


