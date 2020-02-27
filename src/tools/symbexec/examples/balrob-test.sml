open HolKernel Parse

open binariesLib;

open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open optionSyntax;
open wordsSyntax;
open listSyntax;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


val entry_label = "imu_handler_pid_entry";

(*
fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")\n");

val _ = print_option (print o Int.toString)
                     (read_byte_from_init_mem_ (Arbnum.fromInt 0x10000002));

val _ = print_option print_term
                     (get_block_byAddr_ (Arbnum.fromInt 440));

val _ = print_option (print o Arbnum.toString)
                     (find_label_addr_ entry_label);

val _ = print_option (print)
                     (find_label_by_addr_ (Arbnum.fromInt 0x10000002));
*)

datatype cfg_target =
    CFGT_DIR   of term
  | CFGT_INDIR of term;

type cfg_node = {
  CFGN_lbl_tm : term,
  CFGN_next   : cfg_target list
};

type cfg_graph = {
  CFGG_entry : term,
  CFGG_nodes : cfg_node list
};

(*
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 1006);
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 0xc1c);
val lbl_tm = (mk_lbl_tm o valOf) (find_label_addr_ "motor_prep_input");
val lbl_tm = (mk_lbl_tm o valOf) (find_label_addr_ "motor_set_l");
val lbl_tm = (mk_lbl_tm o valOf) (find_label_addr_ entry_label);
val entry_lbl_tm = lbl_tm;
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

fun cfg_target_to_lbl_tm (CFGT_DIR   tm) = SOME tm
  | cfg_target_to_lbl_tm (CFGT_INDIR _ ) = NONE;

val BVarLR32_tm = ``BVar "LR" (BType_Imm Bit32)``;
fun is_Assign_LR tm =
  if is_BStmt_Assign tm then
    ((fst o dest_BStmt_Assign) tm) = BVarLR32_tm
  else
    false;

local
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_valuesTheory bir_programTheory;


val ERR = mk_HOL_ERR "bir_program_labelsSyntax"
val wrap_exn = Feedback.wrap_exn "bir_program_labelsSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_labels"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
in
val (BL_Address_HC_tm,  mk_BL_Address_HC, dest_BL_Address_HC, is_BL_Address_HC)  = syntax_fns2 "BL_Address_HC";
end

local
 fun list_split_pred_aux acc p [] = fail ()
    | list_split_pred_aux acc p (x::xs) =
      (if x = p then (List.rev acc, xs)
       else list_split_pred_aux (x::acc) p xs)

  fun list_split_pred p = list_split_pred_aux [] p
in
fun is_call_with_next_lbl_tm bl cfg_t_l =
  let
    val (lbl, bbs, bbes) = dest_bir_block bl;

    (* TODO: refine the call detection: fail if jump is to the next instruction, this should not happen normally *)
    val isCall  = List.exists is_Assign_LR ((fst o dest_list) bbs);

    val _ = if is_BL_Address_HC lbl then ()
            else raise ERR "is_call_with_next_lbl_tm" "we can only deal with output from the lifter, need BL_Address_HC";
    val (addr_tm, descr) = dest_BL_Address_HC lbl;

    val instrLen2 = (length o fst o (list_split_pred #" ") o explode o stringSyntax.fromHOLstring) descr;
    val _ = if instrLen2 mod 2 = 0 then () else
            raise ERR "is_call_with_next_lbl_tm" "something went wrong when trying to find the binary instruction code";
    val instrLen = instrLen2 div 2;
    val _ = if instrLen = 2 orelse instrLen = 4 then () else
            raise ERR "is_call_with_next_lbl_tm" "something went wrong when trying to find the binary instruction code, wrong instruction length";

    val addr = (dest_word_literal o dest_Imm32) addr_tm;
    val nextLbl = mk_lbl_tm (Arbnum.+ (addr, Arbnum.fromInt instrLen));
  in
    (isCall, nextLbl)
  end;
end

fun build_cfg_nodes acc []                 = (print ("computed " ^ (Int.toString (length acc)) ^ "\n"); acc)
  | build_cfg_nodes acc (lbl_tm::lbl_tm_l) =
      let
        val bl = case get_block_ lbl_tm of SOME x => x
                    | NONE => raise ERR "build_cfg_nodes" "label couldn't be found";
        val (_, _, bbes) = dest_bir_block bl;

        val cfg_t_l_jumps =
          if is_BStmt_Jmp bbes then
            [BLE_to_cfg_target (dest_BStmt_Jmp bbes)]
          else if is_BStmt_CJmp bbes then
            List.map BLE_to_cfg_target
                     ((fn (_, a, b) => [a, b]) (dest_BStmt_CJmp bbes))
          else if is_BStmt_Halt bbes then
            []
          else
            raise ERR "build_cfg_nodes" "unknown BStmt end stmt type";

        fun lbl_tm_opt_proc (SOME x) = SOME x
	  | lbl_tm_opt_proc NONE     = (print "indirection @"; print_term lbl_tm; NONE);
        (* TODO: inspect the indirections and detected calls, best print the assembly code for simplicity *)

        (* call detection and include the expected jump back as continuation in the worklist *)
        val (isCall, nextLbl) = is_call_with_next_lbl_tm bl cfg_t_l_jumps;
        val cfg_t_l = (if isCall then [CFGT_DIR nextLbl] else [])@cfg_t_l_jumps;

        val new_n = { CFGN_lbl_tm = lbl_tm,
                      CFGN_next   = cfg_t_l} : cfg_node;
        val new_nodes = new_n::acc;

        val next_tm_l_full = List.map (lbl_tm_opt_proc o cfg_target_to_lbl_tm) cfg_t_l;
        val next_tm_l_full = List.foldr (fn (x, l) => if isSome x then (valOf x)::l else l)
                                        [] next_tm_l_full;
        val next_tm_l      = List.filter (fn x => not ((is_lbl_in_cfg_nodes x new_nodes) orelse
                                                       (List.exists (fn y => x = y) lbl_tm_l)))
                                         next_tm_l_full;
        val new_lbl_tm_l   = next_tm_l@lbl_tm_l;
      in
        build_cfg_nodes new_nodes new_lbl_tm_l
      end;

fun build_cfg entry_lbl_tm =
  if not (is_BL_Address entry_lbl_tm) then
    raise ERR "build_cfg" "entry_lbl must be a BL_Address"
  else
    {
     CFGG_entry = entry_lbl_tm,
     CFGG_nodes = build_cfg_nodes [] [entry_lbl_tm]
    } : cfg_graph;




(*
fun sanity_check_controlflow prog_tm entry_label =

fun enumerate_paths
(* what happens if we try this? *)
*)


