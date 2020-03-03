structure binariesMemLib =
struct

local

open binariesDefsLib;


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


              fun find_two _   _     _ []     = NONE
		| find_two acc true  c (x::l) = if (c = x) then SOME (acc-1)
                                                           else find_two (acc+1) false c l
		| find_two acc false c (x::l) = if (c = x) then find_two (acc+1) true  c l
                                                           else find_two (acc+1) false c l;
              fun split_at_two c cl =
                case find_two 0 false c cl of
		   NONE   => raise ERR "binariesMemLib" "couldn't find the two characters"
	         | SOME i => i;

          fun split_string_byte s =
            let
              val _ = if (String.size s) mod 2 = 0 then () else
                        raise ERR "split_string_byte" ("bug: string length is wrong: " ^ s);
              val len = (String.size s) div 2;
            in
              (Arbnum.fromHexString (String.substring(s, (len*2) - 2, 2)),
                                     String.substring(s, 0, (len*2) - 2))
            end;
          fun rev_hs_to_num acc "" = acc
	    | rev_hs_to_num acc s  =
                let
                  val sp = split_string_byte s;
                  val n  = Arbnum.+(Arbnum.*(acc, Arbnum.fromInt 256), fst sp);
                in
                  rev_hs_to_num n (snd sp)
                end;

val endianrev_hs_to_num = rev_hs_to_num (Arbnum.fromInt 0);

fun endianrev_hs_to_bytes s =
  let val len = String.size s in
  if len mod 2 <> 0 then
    raise ERR "endianrev_hs_to_bytes" "unexpected string length"
  else if len = 0 then [] else
    (Arbnum.fromHexString (String.substring(s, 0, 2)))
    ::
    (endianrev_hs_to_bytes (String.substring(s, 2, len - 2)))
  end;

fun listsplit_ acc []   _ []     = acc
  | listsplit_ acc accw _ []     = accw::acc
  | listsplit_ acc accw p (x::l) = 
      if p x then
        listsplit_ (accw::acc) [] p l
      else
        listsplit_ acc (x::accw) p l;

fun listsplit p l = listsplit_ [] [] p l;

fun parse_line_acc (s, l) =
  let val cl = explode s; in
  if String.isPrefix "Contents of section " s then
    l (* skip line *)
  else
    if hd cl = #" " then
      let
        (* split data line in base address and values *)
        val (cl_a, cl_d_t) = list_split_pred #" " (tl cl);
        val cl_d_t_i = split_at_two #" " (cl_d_t);
        val (cl_d_, _) = (List.take (cl_d_t, cl_d_t_i), List.drop (cl_d_t, cl_d_t_i));
        val cl_ds = List.filter (fn x => x <> #" ") cl_d_;

        (* process and parse to arbnums *)
        val d_a  = (Arbnum.fromHexString o implode) cl_a;
        val d_ds = (endianrev_hs_to_bytes o implode) cl_ds;
        val dat  = (d_a, d_ds);
      in
        dat::l
      end
    else
      l (* skip line *)
  end;

fun parse_file mem_file =
  let
    val lines   = read_file_lines mem_file;
    val data    = List.foldr parse_line_acc [] lines;
    val data_uf = List.concat (List.map (fn (base, dl) =>
          List.tabulate (List.length dl, fn i => (Arbnum.+(base, Arbnum.fromInt i), List.nth(dl, i)))
      ) data);
  in
    data_uf
  end;

val binary_mem = parse_file mem_file;

in (* local *)

(*
val addr = Arbnum.fromInt (0x10000018);
val hs   = (Option.map Arbnum.toHexString) (mem_read_byte binary_mem addr)
*)
fun mem_read_byte binary_mem addr =
  Option.map snd (List.find (fn (a, _) => a = addr) binary_mem);

end (* local *)

end (* struct *)
