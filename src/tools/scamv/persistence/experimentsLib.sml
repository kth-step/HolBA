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


  (* embexp platform parameters *)
  (* ======================================== *)
  val bir_embexp_params_code   = Arbnum.fromHexString    "0x2000";
  val bir_embexp_params_memory = (Arbnum.fromHexString "0x100000",
                                  Arbnum.fromHexString  "0x40000");

  fun bir_embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);


end (* local *)
end (* struct *)
