open HolKernel boolLib liteLib;
open bir_inst_liftingLibTypes

structure gcc_supportLib :> gcc_supportLib =
struct

  (*******************)
  (* Auxiliary stuff *)
  (*******************)

  val ERR = mk_HOL_ERR "gcc_supportLib"


  fun list_split_pred_aux acc p [] = fail ()
    | list_split_pred_aux acc p (x::xs) =
      (if x = p then (List.rev acc, xs)
       else list_split_pred_aux (x::acc) p xs)

  fun list_split_pred p = list_split_pred_aux [] p


  fun read_file_lines file_name = let
    val instream = TextIO.openIn file_name
    fun read_it acc =
      case TextIO.inputLine instream of
          NONE => List.rev acc
        | SOME s => read_it (s::acc);
    val input = read_it [] before TextIO.closeIn instream
  in input end;


  (*******************)
  (* File Operations *)
  (*******************)

(*
val file_name = "examples/aes-aarch64.da"

val lines = read_file_lines file_name
val (lbls, acc, c_lbl, c_data) = ([], [], NONE, [])
val l = el 120 lines
val l = el 10 lines
length lines
*)

fun process_disassembly_file_line (acc, c_lbl, c_data)  l = 
  let val cl = butlast (String.explode l) in
  if (List.null cl) then (acc, c_lbl, c_data) else
  if hd cl = #" " then let
    val (addr_l, cl') = list_split_pred #":" cl
    val addr = Arbnum.fromHexString (String.implode addr_l)
    val (hc_l, cl') = list_split_pred #"\t" (tl cl')
    val hc = String.implode (filter (fn c => c <> #" ") hc_l)
    val mm_s = String.map (fn c => if c = #"\t" then #" " else c) (String.implode cl')
  in (acc, c_lbl, ((hc, mm_s)::c_data)) end else
  if hd cl = #"0" then let 
    val (addr_l, lbl') = list_split_pred #" " cl
    val addr = Arbnum.fromHexString (String.implode addr_l)
    val lbl = String.implode (List.take (List.drop (lbl',1), List.length lbl' - 3))
  in 
    ((c_lbl, List.rev c_data)::acc, (lbl, addr), [])
  end else
  (acc, c_lbl, c_data)
end handle HOL_ERR _ => raise (ERR "" ("can't parse line '"^ l ^"'"))

fun process_disassembly_file_line_finish (acc, c_lbl, c_data) =
   tl ((List.rev ((c_lbl, List.rev c_data)::acc)));

  (* val file_name = "examples/aes-aarch64.da" *)
fun read_disassembly_file_raw file_name = let
  val instream = TextIO.openIn file_name
  fun read_it st =
    case TextIO.inputLine instream of
        NONE => st
      | SOME s => let
          val st' = process_disassembly_file_line st s
        in read_it st' end
  val input = read_it ([], ("", Arbnum.zero), []) before TextIO.closeIn instream
in process_disassembly_file_line_finish input end;

(*
  fun secname_P s = true
*)
fun read_disassembly_file secname_P file_name = let
  val raw = read_disassembly_file_raw file_name
  val raw' = List.filter (fn ((sn, _), _) => secname_P sn) raw

  val sec_mapping = List.map fst raw'

  fun string_to_entry_type s =
    if String.isPrefix ".word" s then BILME_data else BILME_code (SOME s)

  val regions = List.map (fn ((_, pc), el) =>
     BILMR (pc, List.map (fn (hc, s) => (hc, string_to_entry_type s)) el)) raw'
in
  (sec_mapping, regions)
end;

end
