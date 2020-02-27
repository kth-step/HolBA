open HolKernel Parse

open binariesLib;

open bir_programSyntax;

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
    CFGT_INDIR (dest_BLE_Exp ble)
  else
    raise ERR "BLE_to_cfg_target" "unknown BLE type";

fun cfg_target_to_lbl_tm (CFGT_DIR   tm) = SOME tm
  | cfg_target_to_lbl_tm (CFGT_INDIR _ ) = NONE;
  

fun build_cfg_nodes acc []                 = (print ("computed " ^ (Int.toString (length acc)) ^ "\n"); acc)
  | build_cfg_nodes acc (lbl_tm::lbl_tm_l) =
      let
        val bl = case get_block_ lbl_tm of SOME x => x
                    | NONE => raise ERR "build_cfg_nodes" "label couldn't be found";
                      (* TODO: test trigger the NONE case *)
        val (_, _, bbes) = dest_bir_block bl;

        val cfg_t_l =
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
	  | lbl_tm_opt_proc NONE     = (print "indirection @"; print_term lbl_tm; print "\n"; NONE);
        (* TODO: inspect the indirections *)
        (* TODO: we need some form of call detection and include
                 the jump back as continuation in the worklist *)

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


