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

  (* machine states *)
  (* ======================================== *)
  (* machine state definition from the signature *)
  datatype machineState = MACHSTATE of (((string, num) Redblackmap.dict) * (int * ((num, num) Redblackmap.dict)));
  val machstate_empty = MACHSTATE ((Redblackmap.mkDict String.compare), (8, Redblackmap.mkDict Arbnum.compare));

  fun machstate_print (MACHSTATE (regmap, (wsz, memmap))) =
      let
	  val _ = print ("MACHSTATE = (\n");
	  val _ = print ("  mem := {\n");
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
  fun machstate_to_Json (MACHSTATE (regmap, (wsz, memmap))) =
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

      val regmap_json = List.map rkv_to_json    (Redblackmap.listItems regmap);
      val memmap_json = List.map mentry_to_json (Redblackmap.listItems memmap);

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

      fun parseMementry (k_s, v) =
        let
          val v_s =
            case v of
               STRING s => s
             | _        => raise ERR "Json_to_machstate" "format error, register value is not STRING";

          val addr  = Arbnum.fromHexString k_s;
          val value = Arbnum.fromHexString v_s;

          val _ = if
                    Arbnum.<= (Arbnum.fromInt 0, value) orelse
                    Arbnum.<= (value, Arbnum.fromInt 255)
                  then () else
                    raise ERR "Json_to_machstate" "memory value out of range";
        in
          (addr, value)
        end;

      val regmap = Redblackmap.fromList String.compare (List.map parseReg regmap);
      val mem    = (8, Redblackmap.fromList Arbnum.compare (List.map parseMementry memmap));
    in
      MACHSTATE (regmap, mem)
    end;


  (* programs *)
  (* ======================================== *)
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


  (* additional structured data *)
  (* ======================================== *)
  datatype experiment_arch = ArchARM8;
  datatype experiment_type = ExperimentTypeExps2;

  (* embexp platform parameters *)
  (* ======================================== *)
  val bir_embexp_params_code   = Arbnum.fromHexString    "0x2000";
  val bir_embexp_params_memory = (Arbnum.fromHexString "0x100000",
                                  Arbnum.fromHexString  "0x40000");

  fun bir_embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);


end (* local *)
end (* struct *)
