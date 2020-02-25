structure gcc_supportLib :> gcc_supportLib =
struct

  local

  open HolKernel boolLib liteLib;
  open bir_inst_liftingLibTypes

  open bir_auxiliaryLib;
  open bir_fileLib;

  val ERR = mk_HOL_ERR "gcc_supportLib"

  in (* local *)

(*
val file_name = "examples/wolfssl-aarch64.da"

val lines = read_file_lines file_name
val l = el 70 lines
val l = el 5 lines
val l = el 5 lines
length lines
*)

(* A single enty in a disassembly file consisting of an address, the hex-code and
   description *)
type disassembly_entry = {
  DAE_addr : Arbnum.num,
  DAE_hex  : string,
  DAE_desc : string
};

(* A block is a list of entries with consecutive addresses *)
type disassembly_block = disassembly_entry list;

(* A labeled part, e.g. a function has a name, a start address and multiple blocks *)
type disassembly_lbl = {
  DAL_name   : string,
  DAL_addr   : Arbnum.num,
  DAL_blocks : disassembly_block list
}

type disassembly_section = {
  DAS_name : string,
  DAS_lbls : disassembly_lbl list
}

type disassembly_data = disassembly_section list;


fun encode_hex (w:int) (n:num) = let
  val s = Arbnum.toHexString n
  val s_len = String.size s
in
  if Int.< (s_len, w) then (String.implode (List.tabulate (Int.- (w, s_len), fn _ => #"0"))^s) else
  if s_len = w then s else
  failwith "invalid input"
end;


fun disassembly_entry_to_string (e:disassembly_entry) =
  ("   " ^ (encode_hex 8 (#DAE_addr e)) ^ ": " ^ (#DAE_hex e) ^ "   " ^(#DAE_desc e))

fun disassembly_block_to_string (bl:disassembly_block) =
  String.concatWith "\n" (List.map disassembly_entry_to_string bl)

fun disassembly_lbl_to_string (l:disassembly_lbl) =
(encode_hex 8 (#DAL_addr l)) ^ ": " ^ (#DAL_name l) ^ "\n" ^
(String.concatWith "\n     ...\n" (List.map disassembly_block_to_string (#DAL_blocks l)))

fun disassembly_section_to_string (l:disassembly_section) =
("Section " ^ (#DAS_name l) ^ "\n\n" ^
(String.concatWith "\n\n" (List.map disassembly_lbl_to_string (#DAS_lbls l))))


fun disassembly_data_to_string (d:disassembly_data) =
(String.concatWith "\n\n" (List.map disassembly_section_to_string d))

fun print_disassembly_data da = print (disassembly_data_to_string da)




datatype disassembly_line =
    DASL_section of string
  | DASL_lbl of string * Arbnum.num
  | DASL_sep
  | DASL_whitespace
  | DASL_entry of disassembly_entry

fun parse_disassembly_file_line skipentries l =
  let val cl = butlast (String.explode l) in
  if (List.null cl) then DASL_whitespace else
  if hd cl = #" " then
    if skipentries then DASL_whitespace else
    let
      val (addr_l, cl') = list_split_pred #":" cl
      val addr = Arbnum.fromHexString (String.implode addr_l)
      val (hc_l, cl') = list_split_pred #"\t" (tl cl')
      val hc = String.implode (filter (fn c => c <> #" ") hc_l)
      val mm_s = String.map (fn c => if c = #"\t" then #" " else c) (String.implode cl')
    in DASL_entry {
         DAE_addr = addr,
         DAE_desc = mm_s,
         DAE_hex  = hc}
    end
  else
  if hd cl = #"0" then let
    val (addr_l, lbl') = list_split_pred #" " cl
    val addr = Arbnum.fromHexString (String.implode addr_l)
    val lbl = String.implode (List.take (List.drop (lbl',1), List.length lbl' - 3))
  in
    (DASL_lbl (lbl, addr))
  end else if String.isPrefix "Disassembly of section" l then
    DASL_section (String.implode (butlast (List.drop (cl, 23))))
  else DASL_sep
end handle HOL_ERR _ => raise (ERR "parse_disassembly_file_line" ("can't parse line '"^ l ^"'"))


type disassembly_file_acc =
       disassembly_section list * (* finished sections                         *)
       disassembly_lbl     list * (* finished symbols    : for current section *)
       disassembly_block   list * (* finished block list : for current symbol  *)
       string                   * (* current section                           *)
       (string * num)           * (* current lbl (symbol)                      *)
       disassembly_entry   list ; (* current state of the block                *)

val empty_disassembly_file_acc:disassembly_file_acc =
  ([], [], [], "", ("", Arbnum.zero), [])

local

fun add_entry ((acc, acc_sec, acc_lbl, c_sec, c_lbl, c_data):disassembly_file_acc) e : disassembly_file_acc =
    (acc, acc_sec, acc_lbl, c_sec, c_lbl, e :: c_data)

fun finish_block ((acc, acc_sec, acc_lbl, c_sec, c_lbl, c_data):disassembly_file_acc) : disassembly_file_acc =
    (acc, acc_sec,
     if List.null c_data then acc_lbl else (List.rev c_data)::acc_lbl,
     c_sec, c_lbl, [])

fun finish_lbl i nl = let
  val (acc, acc_sec, acc_lbl, c_sec, c_lbl, _) = finish_block i
  val acc_sec' = if List.null acc_lbl then acc_sec else (
    {DAL_name = (fst c_lbl), DAL_addr = snd c_lbl, DAL_blocks = List.rev acc_lbl}::acc_sec)
in
  (acc, acc_sec', [], c_sec, nl, []):disassembly_file_acc
end;

fun finish_sec i ns = let
  val (acc, acc_sec, _, c_sec, _, _) = finish_lbl i ("", Arbnum.zero)
  val acc' = if List.null acc_sec then acc else
    {DAS_name = c_sec, DAS_lbls = List.rev acc_sec}::acc
in
  (acc', [], [], ns, ("", Arbnum.zero), []):disassembly_file_acc
end;

fun is_included fi ((acc, acc_sec, acc_lbl, c_sec, (c_lbl_id, _), c_data):disassembly_file_acc) =
  (c_lbl_id = "") orelse (fi c_sec c_lbl_id);

in

fun process_disassembly_file_line fi i l =
  let val skip_to_next_lbl = not (is_included fi i) in
    case parse_disassembly_file_line skip_to_next_lbl l of
        DASL_whitespace => i
      | DASL_entry e    => add_entry i e
      | DASL_sep        => finish_block i
      | DASL_lbl (s, a) => finish_lbl i (s, a)
      | DASL_section n  => finish_sec i n
  end;

fun finish_disassembly_file_acc i : disassembly_data = let
  val (acc, _, _, _, _, _) = finish_sec i ""
in
  List.rev acc
end;


end;

(* val file_name = "examples/aes-aarch64.da" *)
fun read_disassembly_file fi file_name = let
  val instream = TextIO.openIn file_name
  fun read_it st =
    case TextIO.inputLine instream of
        NONE => st
      | SOME s => let
          val st' = process_disassembly_file_line fi st s
        in read_it st' end
  val input = read_it empty_disassembly_file_acc before TextIO.closeIn instream
in finish_disassembly_file_acc input end;


(* getting list of section addresses *)

fun disassembly_section_to_labels (s:disassembly_section) =
  List.map (fn l => (#DAS_name s, #DAL_name l, #DAL_addr l)) (#DAS_lbls s)

fun disassembly_data_to_labels (d:disassembly_data) =
flatten (List.map disassembly_section_to_labels d)

fun disassembly_section_filter f (i:disassembly_section) : disassembly_section =
  {
    DAS_name = #DAS_name i,
    DAS_lbls = List.filter (fn l => f (#DAL_name l)) (#DAS_lbls i)
  };

fun disassembly_data_filter f i = let
  val i' = List.map (fn s => disassembly_section_filter (f (#DAS_name s)) s) i
  val i'' = List.filter (fn s => not (List.null (#DAS_lbls s))) i'
in i'' end;


fun disassembly_entry_relocate i (e:disassembly_entry) : disassembly_entry = {
  DAE_hex = #DAE_hex e,
  DAE_desc = #DAE_desc e,
  DAE_addr = Arbint.toNat (Arbint.+ (Arbint.fromNat (#DAE_addr e), i))};

fun disassembly_lbl_relocate i (l:disassembly_lbl) : disassembly_lbl = {
  DAL_name = #DAL_name l,
  DAL_addr = Arbint.toNat (Arbint.+ (Arbint.fromNat (#DAL_addr l), i)),
  DAL_blocks = List.map (List.map (disassembly_entry_relocate i)) (#DAL_blocks l)}


fun disassembly_section_relocate i (s:disassembly_section) : disassembly_section = {
  DAS_name = #DAS_name s,
  DAS_lbls = List.map (disassembly_lbl_relocate i) (#DAS_lbls s)}

fun disassembly_data_relocate fi (d:disassembly_data) : disassembly_data =
  List.map (fn s => disassembly_section_relocate (fi (#DAS_name s)) s) d;


fun desc_string_to_entry_type s =
    if String.isPrefix ".word" s then BILME_data else
    if String.isPrefix ".inst" s then BILME_data else
    BILME_code (SOME s)

fun disassembly_entry_to_annotated_hex (e:disassembly_entry) =
  (#DAE_hex e, desc_string_to_entry_type (#DAE_desc e));

fun disassembly_block_to_mem_region ([]:disassembly_block) = failwith "empty block"
  | disassembly_block_to_mem_region (e::bl) =
    BILMR (#DAE_addr e, List.map disassembly_entry_to_annotated_hex (e::bl))


fun disassembly_lbl_to_mem_regions (l:disassembly_lbl) =
  List.map disassembly_block_to_mem_region (#DAL_blocks l);

fun disassembly_section_to_mem_regions (s:disassembly_section) =
  flatten (List.map disassembly_lbl_to_mem_regions (#DAS_lbls s));


fun disassembly_data_to_mem_regions (d:disassembly_data) =
  flatten (List.map disassembly_section_to_mem_regions d);


fun read_disassembly_file_regions_filter fi filename = let
  val d = read_disassembly_file fi filename
  val d' = d (*disassembly_data_filter fi d*);
  val r = disassembly_data_to_mem_regions d'
  val l =  disassembly_data_to_labels d'
in
  (l, r)
end

fun read_disassembly_file_regions filename = let
  val d = read_disassembly_file (fn _ => fn _ => true) filename
  val r = disassembly_data_to_mem_regions d
  val l =  disassembly_data_to_labels d
in
  (l, r)
end

end (* local *)

end (* gcc_supportLib *)
