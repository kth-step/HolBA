structure experimentsLib :> experimentsLib =
struct
local
  open HolKernel Parse boolLib bossLib;

  open bir_miscLib;

  (* error handling *)
  val libname = "experimentsLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname
in

  (* TODO: put this in a more general HolBA place... *)
      fun term_to_string_wtypes t =
        let
          val trace_val = Feedback.get_tracefn "types" ();
          val _ = Feedback.set_trace "types" 1;
          val s = term_to_string t;
          val _ = Feedback.set_trace "types" trace_val;
        in s end;

  (* machine states *)
  (* ======================================== *)
  (* machine state definition from the signature *)
  datatype machineState = MACHSTATE of (((string, num) Redblackmap.dict) * (int * num * ((num, num) Redblackmap.dict)));
  fun machstate_empty defval = MACHSTATE ((Redblackmap.mkDict String.compare), (8, defval, Redblackmap.mkDict Arbnum.compare));

  fun machstate_print (MACHSTATE (regmap, (wsz, defval, memmap))) =
      let
	  val _ = print ("MACHSTATE = (\n");
	  val _ = print ("  mem := " ^ (Arbnum.toString defval) ^ ", otherwise {\n");
	  val _ = List.map (fn (a,v) =>  print ("\t(0x"^(Arbnum.toHexString(a))^"\t-> 0x"^(Arbnum.toHexString(v))^")\n"))
                           (Redblackmap.listItems memmap);
	  val _ = print "  }\n  regs := {\n";
	  val _ = List.map (fn (n,v) => print ("\t(" ^ n ^ "\t-> 0x" ^(Arbnum.toHexString( v))^ ")\n"))
                           (Redblackmap.listItems regmap);
	  val _ = print "  }\n)\n";
      in () end;

  fun machstate_add_reg (rn, rv) (MACHSTATE (rm, m)) =
    (MACHSTATE (Redblackmap.insert (rm, rn, rv), m));
  fun machstate_replace_mem newm (MACHSTATE (rm, m)) =
    (MACHSTATE (rm, newm));

  (* convert to json state *)
  fun machstate_to_Json (MACHSTATE (regmap, (wsz, defval, memmap))) =
    let
      open Json;

      val _ = if wsz = 8 then () else
              raise ERR "gen_json_state" "word size has to be one byte";

      fun rkv_to_json (k,v) =
        let
          (* TODO: Stack pointer needs to be handled *)
          (* TODO: maybe want to check that we indeed get R0-R29 or whatever *) 
          val _ = if String.isPrefix "R" k then () else
                    raise ERR "gen_json_state" "input not as exptected";

          val regname = "x" ^ (String.extract(k, 1, NONE));
          val value   = "0x" ^ (Arbnumcore.toHexString v);
        in
          (regname, STRING value)
        end;

      fun mentry_to_json (k,v) =
        let
          val addr  = "0x" ^ (Arbnumcore.toHexString k);
	  val value = "0x" ^ (Arbnumcore.toHexString v);
        in
          (addr, STRING value)
        end;

      val regmap_json  = List.map rkv_to_json    (Redblackmap.listItems regmap);
      val memmap_json_ = List.map mentry_to_json (Redblackmap.listItems memmap);
      val memmap_json  = ("default", STRING ("0x" ^ (Arbnumcore.toHexString defval)))::memmap_json_;

      val json_obj = OBJECT (regmap_json@[("mem", OBJECT memmap_json)])
    in
      json_obj
    end;

  (* convert from json state *)
  fun Json_to_machstate json_obj =
    let
      open Json;
      open wordsSyntax;

      val topl_objlist =
        case json_obj of
           OBJECT l => l
         | _        => raise ERR "Json_to_machstate" "format error, top level is not an OBJECT";

      val memname  = "mem";
      fun is_memmap (n,_) = n = memname;

      val mems_ = List.filter (is_memmap) topl_objlist;
      val mems  = if List.length mems_ = 1 then
                    mems_
                  else
                    [(memname, OBJECT [])]

      val memmap =
        case snd (List.hd mems) of
           OBJECT l => l
         | _        => raise ERR "Json_to_machstate" "format error, 'mem' is not an OBJECT";

      val regmap = List.filter (not o is_memmap) topl_objlist;

      fun parseReg (k_s, v) =
        let
          val v_s =
            case v of
               STRING s => s
             | _        => raise ERR "Json_to_machstate" "format error, register value is not STRING";
          val _ = if List.hd (String.explode k_s) = #"x" then () else
                  raise ERR "Json_to_machstate" "format error, expect register name";
          val regnum_s = (String.implode o List.tl o String.explode) k_s;
          val regnum = case Int.fromString regnum_s of
                          SOME x => x
                        | _ => raise ERR "Json_to_machstate" "format error, cannot parse register number";

          val value    = Arbnum.fromHexString v_s;
          val regname  = "R" ^ (Int.toString regnum);
        in
          (regname, value)
        end;

      fun parseMemVal v =
        let
          val v_s =
            case v of
               STRING s => s
             | _        => raise ERR "Json_to_machstate" "format error, memory value is not STRING";

          val value = Arbnum.fromHexString v_s;

          val _ = if
                    Arbnum.<= (Arbnum.fromInt 0, value) orelse
                    Arbnum.<= (value, Arbnum.fromInt 255)
                  then () else
                    raise ERR "Json_to_machstate" "memory value out of range";
        in
          value
        end;

      fun parseMementry (k_s, v) =
          (Arbnum.fromHexString k_s, parseMemVal v);

      val regmap = Redblackmap.fromList String.compare (List.map parseReg regmap);

      fun is_default (n, _) = n = "default";
      val mem_default_o = List.find is_default memmap;
      val mem_default =
        case mem_default_o of
           SOME (_, v) => parseMemVal v
         | _ => raise ERR "Json_to_machstate" "couldn't find memory default value as expected";

      val memmap_wo_default = List.filter (not o is_default) memmap;
      val mem    = (8, mem_default, Redblackmap.fromList Arbnum.compare (List.map parseMementry memmap_wo_default));
    in
      MACHSTATE (regmap, mem)
    end;


  (* programs *)
  (* ======================================== *)

(*
  (* conversion from asm program (asm lines) to "normal program" *)
  val bir_embexp_prog_to_code : string list -> string
  (* and the other direction *)
  val bir_embexp_code_to_prog : string -> string list

(*
  val bir_embexp_code_to_prog_raw : (string list -> string list) -> string -> string list
  val bir_embexp_prog_std_preproc : string list -> string list
*)
*)

  type experiment_prog = string list;
  fun bir_embexp_prog_to_code asm_lines =
    let
      fun is_colon x = x = #":";
      fun is_ws x = x = #" " orelse x = #"\t" orelse x = #"\n";
      fun is_asm_line l = let val ls = String.explode l in
                            if List.exists is_colon ls then false else
                            if length ls < 1 then false else
                            not (is_ws (hd ls)) andalso not (is_ws (last ls))
                          end;
      val _ = if List.all is_asm_line asm_lines then () else
                raise ERR "bir_embexp_prog_to_code" "some lines are not valid asm lines"
    in
      List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "" asm_lines
    end;

  fun bir_embexp_prog_std_preproc asm_lines =
    let
(*
      val asm_lines = if List.last asm_lines = "\n" then
                        List.take (asm_lines, (length asm_lines) - 1)
                      else
                        raise ERR "bir_embexp_prog_std_preproc" "no final newline";
*)
      val asm_lines = List.map (fn line =>
         let val fixedline = strip_ws_off true line; in
           if line = "\t" ^ fixedline then
             fixedline
           else
             raise ERR "bir_embexp_prog_std_preproc" "lines are not as expected"
         end
       ) asm_lines;
    in
      asm_lines
    end;

  fun bir_embexp_prog_cleanup asm_lines =
    let
      val asm_lines = List.map (strip_ws_off true) asm_lines;
      val asm_lines = List.filter (fn x => not (x = "")) asm_lines;
    in
      asm_lines
    end;

  fun bir_embexp_code_to_prog_raw preproc_fun code_asm =
    let
      val asm_lines = String.tokens (fn c => c = #"\n") code_asm;
      val asm_lines = preproc_fun asm_lines;

      val asm_lines_p = List.exists (fn x =>
            x <> (strip_ws_off true x) orelse
            x = ""
        ) asm_lines;
      val _ = if not asm_lines_p then () else
              raise ERR "bir_embexp_code_to_prog_raw" "unexpected asm formatting";
    in
      asm_lines
    end;
  
  fun bir_embexp_code_to_prog code_asm =
    bir_embexp_code_to_prog_raw bir_embexp_prog_cleanup code_asm;

  (* just input validation *)
  fun mk_experiment_prog asm_lines =
    let
      fun is_colon x = x = #":";
      fun is_ws x = x = #" " orelse x = #"\t" orelse x = #"\n";
      fun is_asm_line l = let val ls = String.explode l in
                            if List.exists is_colon ls then false else
                            if length ls < 1 then false else
                            not (is_ws (hd ls)) andalso not (is_ws (last ls))
                          end;
      val _ = if List.all is_asm_line asm_lines then () else
                raise ERR "mk_experiment_prog" "some lines are not valid asm lines"
    in
      asm_lines
    end;

  (* check expectation and parse input *)
  fun prog_from_asm_code asm_code =
    bir_embexp_code_to_prog asm_code;

  (* simple output functions *)
  fun prog_length asm_lines = length asm_lines;
  fun dest_experiment_prog asm_lines = asm_lines;
  fun prog_to_asm_code asm_lines =
    List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "" asm_lines;


  (* additional structured data *)
  (* ======================================== *)
  datatype experiment_arch = ArchARM8;
  fun exp_arch_to_string ArchARM8 = "arm8";

  datatype experiment_type = ExperimentTypeStdTwo;
  fun exp_type_to_string ExperimentTypeStdTwo = "exps2";

  (* embexp platform parameters *)
  (* ======================================== *)
  val embexp_params_code   = Arbnum.fromHexString    "0x2000";
  val embexp_params_memory = (Arbnum.fromHexString "0x100000",
                                  Arbnum.fromHexString  "0x40000");

  fun embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);


end (* local *)
end (* struct *)
