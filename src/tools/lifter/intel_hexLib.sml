structure intel_hexLib :> intel_hexLib =
struct

  open HolKernel boolLib liteLib;

  open Arbnum

  (*******************)
  (* Auxiliary stuff *)
  (*******************)

  val ERR = mk_HOL_ERR "intel_hexLib"

  fun encode_hex (w:int) (n:num) = let
    val s = toHexString n
    val s_len = String.size s
  in
    if Int.< (s_len, w) then (String.implode (List.tabulate (Int.- (w, s_len), fn _ => #"0"))^s) else
    if s_len = w then s else
    failwith "invalid input"
  end;

  val encode_byte = encode_hex 2;

  fun decode_byte (s:string) =
    if (String.size s <> 2) then failwith "invalid input" else
       (fromHexString s);

  val combine_bytes = let
      val bs = fromInt 256
    in
      foldl (fn (b, a) => (a*bs + b)) (fromInt 0)
    end;


  (*****************)
  (* Main datatype *)
  (*****************)

  datatype ihex_record_type =
     IHEX_data of num * num list
   | IHEX_eof
   | IHEX_extended_segment_address of num
   | IHEX_start_segment_address of num
   | IHEX_extended_linear_address of num
   | IHEX_start_linear_address of num



  (**********************************)
  (* encoding / decoding to strings *)
  (**********************************)

  fun compute_checksum_of_string s =
  let
    val s_len = String.size s
    val _ = if (Int.mod (s_len, 2) = 0) then () else fail()

    fun compute_sum acc 0 = acc
      | compute_sum acc n = let
          val n' = Int.- (n, 2);
          val b = decode_byte (String.substring (s, n', 2))
          val acc' = b + acc;
        in compute_sum acc' n' end
    val sum = compute_sum (fromInt 0) s_len
    val res = (Arbnum.mod ((fromInt 256) - (Arbnum.mod (sum, fromInt 256)), (fromInt 256)))
  in
    res
  end;


  fun decode_ihex s = let
    val s_len = String.size s

    (* Sanity check: long enough, odd length and starts with #":" *)
    val _ = if (Int.mod (s_len, 2) = 1) andalso (Int.<= (11, s_len)) then ()
               else fail()
    val _ = if (String.sub (s, 0) = #":") then () else fail ()

    (* Decode size and check right amount of data is present *)
    val size = decode_byte (String.substring (s, 1, 2))
    val _ = if (fromInt s_len = fromInt 11 + (size+size)) then () else fail()

    (* decode rest *)
    val addr = fromHexString (String.substring (s, 3, 4))
    val ty = decode_byte (String.substring (s, 7, 2))
    val data = List.tabulate (toInt size, fn n =>
       decode_byte (String.substring (s, Int.+(9, Int.+(n, n)), 2)));

    (* checksum *)
    val check_sum = decode_byte (String.substring (s, Int.-(s_len, 2), 2))
    val check_sum_compute = compute_checksum_of_string (String.substring (s, 1, Int.-(s_len, 3)))
    val _ = if check_sum = check_sum_compute then () else fail ()
  in
    case toInt ty of
        0 => IHEX_data (addr, data)
      | 1 => if (List.null data) then IHEX_eof else fail()
      | 2 => if (List.length data = 2) then IHEX_extended_segment_address (combine_bytes data) else fail ()
      | 3 => if (List.length data = 4) then IHEX_start_segment_address (combine_bytes data) else fail ()
      | 4 => if (List.length data = 2) then IHEX_extended_linear_address (combine_bytes data) else fail ()
      | 5 => if (List.length data = 4) then IHEX_start_linear_address (combine_bytes data) else fail ()
      | _ => fail ()
  end handle HOL_ERR _ => raise (ERR "decode_ihex" ("decoding of '"^s^"' failed"));

  fun encode_ihex_add_cs sl = let
    val s = String.concat sl
    val cs = encode_byte (compute_checksum_of_string s)
  in (":" ^ s ^ cs) end;

  fun encode_ihex (IHEX_eof) = ":00000001FF"
    | encode_ihex (IHEX_data (addr, data)) =
       encode_ihex_add_cs ([encode_byte (fromInt (List.length data)),
                  (encode_hex 4 addr), "00"] @ (List.map encode_byte data))
    | encode_ihex (IHEX_extended_segment_address d) =
        encode_ihex_add_cs ["02000002", encode_hex 4 d]
    | encode_ihex (IHEX_start_segment_address d) =
        encode_ihex_add_cs ["04000003", encode_hex 8 d]
    | encode_ihex (IHEX_extended_linear_address d) =
        encode_ihex_add_cs ["02000004", encode_hex 4 d]
    | encode_ihex (IHEX_start_linear_address d) =
        encode_ihex_add_cs ["04000005", encode_hex 8 d]


  (*******************)
  (* File Operations *)
  (*******************)

  fun write_to_ihex_file file_name add_eof ihl = let
    val strs = map encode_ihex ihl
    val s = String.concat strs
    val outstream = TextIO.openOut file_name
    val ihl' = if add_eof then ihl@[IHEX_eof] else ihl;

    fun do_output [] = ()
      | do_output (ih::ihl) =
         (TextIO.output (outstream, encode_ihex ih);
          TextIO.output (outstream, "\n");
          do_output ihl)

    val _ = do_output ihl' before TextIO.closeOut outstream
  in
    ()
  end;


  fun read_from_ihex_file file_name = let
    val instream = TextIO.openIn file_name
    fun read_it acc =
      case TextIO.inputLine instream of
          NONE => List.rev acc
        | SOME s' => read_it (decode_ihex (String.substring (s', 0, Int.- (String.size s', 1)))::acc)
    val input = read_it [] before TextIO.closeIn instream
  in input end;


  (*************)
  (* Semantics *)
  (*************)

  fun decode_ihex_list_step (ih, (offset:num, acc: (num * num list) list, (cb : num), (ce:num), (dl : num list list))) =
    case ih of
        IHEX_eof => (offset, acc, cb, ce, dl)
      | IHEX_start_linear_address _ => (offset, acc, cb, ce, dl)
      | IHEX_start_segment_address _ => (offset, acc, cb, ce, dl)
      | IHEX_extended_segment_address d => (d * fromInt 16, acc, cb, ce, dl)
      | IHEX_extended_linear_address d => (d * fromInt 65536, acc, cb, ce, dl)
      | IHEX_data (addr, data) => let
          val addr' = addr + offset;
          val addr'_e = addr' + fromInt (List.length data)
        in
          if (addr' = ce) then (offset, acc, cb, addr'_e, data::dl) else
          (offset, (cb, (Lib.flatten (List.rev dl)))::acc, addr', addr'_e, [data])
        end;


  fun decode_ihex_list ihl = let
     val (_, acc, cb, _, dl) = foldl decode_ihex_list_step (fromInt 0, [], fromInt 0, fromInt 0, [])  ihl
     val acc' = tl (List.rev ((cb, (Lib.flatten (List.rev dl)))::acc))
  in acc' end;



  local
    (* val ((addr, data)::adata) = acc'
       val offset = zero
       val offset = addr_offset
    *)
    val offset_sz = Arbnum.pow (two, Arbnum.fromInt 16)
    val max_byte_count = 16 (* Adapt to your wishes, common is 16 or 32, everything up to 255 should be valid *)

    fun encode_ihex_list_aux acc offset [] = List.rev acc
      | encode_ihex_list_aux acc offset ((addr, data)::adata) =
        let
           val (addr_offset, addr_base) = Arbnum.divmod (addr, offset_sz)
        in
        if (addr_offset <> offset) then (
          encode_ihex_list_aux ((IHEX_extended_linear_address addr_offset)::acc) addr_offset ((addr, data)::adata)

        ) else (
          let
            (* How much do we encode *)
            val sz = List.length data;
            val (sz, take_all) = if (Int.> (sz, max_byte_count)) then (max_byte_count, false) else
                                    (sz, true);
            val elems_to_next_offset = toInt (offset_sz - addr_base);
            val (sz, take_all) = if (Int.> (sz, elems_to_next_offset)) then (elems_to_next_offset, false) else (sz, take_all);

            (* encode the ihex *)
            val data' = if take_all then data else List.take (data, sz)
            val ihex = IHEX_data (addr_base, data')
            val adata' = if take_all then adata else (addr+fromInt sz, List.drop(data, sz))::adata
          in
            encode_ihex_list_aux (ihex::acc) offset adata'
          end
        )
        end
  in
    val encode_ihex_list = encode_ihex_list_aux [] zero
  end;



  fun encode_hex_list bc little_end (addr:num, hl:string list) = let
    fun decode_aux s = let
       val bl = List.tabulate (bc, fn n =>
           decode_byte (String.substring (s, Int.+(0, Int.+(n, n)), 2)));
     in if little_end then List.rev bl else bl end;
  in
    (addr, Lib.flatten (map decode_aux hl))
  end

  fun encode_ihex_list_hex (bc, little_end) hcl =
    encode_ihex_list (map (encode_hex_list bc little_end) hcl)


  fun decode_hex_list bc little_end (addr:num, bl:num list) = let
    fun decode_aux acc [] = List.rev acc
      | decode_aux acc bl = let
       val bl_start = List.take (bl, bc)
       val _ = if (Int.< (List.length bl_start, bc)) then fail() else ()
       val bl' = List.drop (bl, bc)
       val bl_start' = if little_end then List.rev bl_start else bl_start
       val hs = String.concat (map encode_byte bl_start')
     in decode_aux (hs::acc) bl' end;
  in
    (addr, decode_aux [] bl)
  end

  fun decode_ihex_list_hex (bc, little_end) ihl =
    map (decode_hex_list bc little_end) (decode_ihex_list ihl);

end
