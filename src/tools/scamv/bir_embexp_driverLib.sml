structure bir_embexp_driverLib :> bir_embexp_driverLib =
struct

  local

  open HolKernel Parse boolLib bossLib;

  val libname = "bir_embexp_driverLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  val embexp_basedir_ref = ref (NONE:string option);

  fun embexp_basedir_read () =
      case OS.Process.getEnv("HOLBA_EMBEXP_DIR") of
          NONE => raise ERR "embexp_basedir" "the environment variable HOLBA_EMBEXP_DIR is not set"
        | SOME p => p;

  fun embexp_basedir () =
    case !embexp_basedir_ref of
        NONE =>
          let
            val dir_path = embexp_basedir_read();
            val _ = embexp_basedir_ref := SOME dir_path;
          in
            dir_path
          end
      | SOME p => p;

  val logfile_basedir_ref = ref (NONE:string option);

  fun logfile_basedir_read () =
      case OS.Process.getEnv("HOLBA_SCAMV_LOGS") of
          NONE => raise ERR "logfile_basedir" "the environment variable HOLBA_SCAMV_LOGS is not set"
        | SOME p => p;

  fun logfile_basedir () =
    case !logfile_basedir_ref of
        NONE =>
          let
            val dir_path = logfile_basedir_read();
            val _ = logfile_basedir_ref := SOME dir_path;
          in
            dir_path
          end
      | SOME p => p;

  in

(*
  val s = [("R1", 0x30000 + 0x80000000+70), ("R2", 32*1024)];

  val s1 = [("R1", 0x8003B000)];
  val s2 = [("R1", 0x80033000)];

  val test_asm = "ldr x2, [x1]";

  bir_embexp_run_cache_distinguishability test_asm s1 s2;

  val s1 = [("R1", 0x80033005)];
  val s2 = [("R1", 0x80033000)];
*)

  fun write_to_file filename str =
    let
      val file = TextIO.openOut (filename);
      val _    = TextIO.output (file, str);
      val _    = TextIO.closeOut file;
    in
      ()
    end;

  fun set_cache_input_setupi idx s =
    let
      val s_assign = List.map (fn (k,v) =>
             let
               val _ = if String.isPrefix "R" k then () else
                        raise ERR "set_cache_input_setupi" "input not as exptected";
               val regname = "x" ^ (String.extract(k, 1, NONE));
               val regname = if String.isSuffix "_" regname then
                               (String.extract(regname, 0, SOME((String.size regname) - 1)))
                             else regname;
               val v_0 = Int.mod(v,                           0x10000);
               val v_1 = Int.mod(Int.div(v, 0x10000),         0x10000);
               val v_2 = Int.mod(Int.div(v, 0x100000000),     0x10000);
               val v_3 = Int.mod(Int.div(v, 0x1000000000000), 0x10000);
               val line0 = "\tmovz " ^ regname ^ ", #0x" ^ (Int.fmt StringCvt.HEX v_0);
               val line1 = "\tmovk " ^ regname ^ ", #0x" ^ (Int.fmt StringCvt.HEX v_1) ^ ", lsl #16";
               val line2 = "\tmovk " ^ regname ^ ", #0x" ^ (Int.fmt StringCvt.HEX v_2) ^ ", lsl #32";
               val line3 = "\tmovk " ^ regname ^ ", #0x" ^ (Int.fmt StringCvt.HEX v_3) ^ ", lsl #48";
             in
               "\n" ^ line0 ^ "\n" ^ line1 ^ "\n" ^ line2 ^ "\n" ^ line3 ^ "\n"
             end) s;

      val str = List.foldl (op^) "" s_assign;

      val _ = write_to_file ((embexp_basedir()) ^ "/EmbExp-ProgPlatform/inc/experiment/cache_run_input_setup" ^ (Int.toString idx) ^ ".h") str;
    in
      ()
    end;
  
  fun set_cache_input_setup s1 s2 =
    let
      val _ = set_cache_input_setupi 1 s1;
      val _ = set_cache_input_setupi 2 s2;
    in
      ()
    end;

  (* make connect has to be run before and must be complete *)
  fun bir_embexp_run_cache_indistinguishability test_asm s1 s2 =
    let
      (* write the input code *)
      val _ = write_to_file ((embexp_basedir()) ^ "/EmbExp-ProgPlatform/inc/experiment/cache_run_input.h") test_asm;

      (* write the input state preparation code *)
      val _ = set_cache_input_setup s1 s2;

      (* set embexp compilation environment EMBEXP_CROSS, EMBEXP_GDB *)
      val eeenv_str = case OS.Process.getEnv("HOLBA_GCC_ARM8_CROSS") of
                          NONE => ""
                        | SOME p => "EMBEXP_CROSS=" ^ p ^ " " ^ "EMBEXP_GDB=" ^ p ^ "gdb";

      (* make runlog *)
      val _ = if OS.Process.isSuccess (OS.Process.system (eeenv_str ^ " " ^
                                                          "make --directory=" ^
                                                          (embexp_basedir()) ^
                                                          "/EmbExp-ProgPlatform runlog")) then ()
              else raise ERR "bir_embexp_run_cache_indistinguishability" "running \"make runlog\" failed somehow";

      (* create logs: asm/config1/config2 *)
      val date = Date.fromTimeLocal (Time.now ());
      val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
      val logdir = (logfile_basedir()) ^ "/embexp/arm8/cache2/" ^ datestr;
      val _ = OS.Process.system ("mkdir -p " ^ logdir);
      val _ = OS.Process.system ("cp " ^ ((embexp_basedir()) ^ "/EmbExp-ProgPlatform/inc/experiment/cache_run_inp*.h") ^ " " ^ (logdir ^ "/"));

      (* evaluate uart.log *)
      val file = TextIO.openIn ((embexp_basedir()) ^ "/EmbExp-ProgPlatform/temp/uart.log");
      fun allLinesRevFun acc = case TextIO.inputLine file of
			    NONE => acc
			  | SOME l => allLinesRevFun (l::acc);
      val uart_output_strs = List.rev (allLinesRevFun []);
      val _    = TextIO.closeIn file;

      (* skip until init complete *)
      fun skipUntilInit [] = raise ERR "bir_embexp_run_cache_distinguishability" "init never completed"
	| skipUntilInit (x::l) = if x = "Init complete.\r\n" then (x::l)
                                 else skipUntilInit l;
      val uart_output_strs = skipUntilInit uart_output_strs;

      (* check if we see a full experiment *)
      val uart_output_ok = (List.length uart_output_strs) >= 3 andalso
                           hd uart_output_strs = "Init complete.\r\n" andalso
                           last uart_output_strs = "Experiment complete.\r\n";
      val _ = if uart_output_ok then () else
               raise ERR "bir_embexp_run_cache_distinguishability" "uart experiment seems not complete";

      (* check the result line *)
      val resultline = List.nth(uart_output_strs, (length uart_output_strs) - 2);

      val result = case resultline of
          "RESULT: SUCCESS\r\n" => true
        | "RESULT: FAILED\r\n" => false
        | otherwise => raise ERR "bir_embexp_run_cache_distinguishability"
          ("Unexpected result from test platform: '" ^ otherwise ^ "'")
    in
      result (* return result from evaluation *)
    end;

  end (* local end *)

end

