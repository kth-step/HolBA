structure scamv_llvmLib =
struct

local
    open HolKernel boolLib liteLib simpLib Parse bossLib;
    open bir_fileLib;

    (* error handling *)
    val libname  = "scamv_llvmLib"
    val ERR      = Feedback.mk_HOL_ERR libname
    val wrap_exn = Feedback.wrap_exn libname
in

(*  HOLBA_LLVM_DIR= path of llvm build directory *)
fun llvm_prefix () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_LLVM_DIR")) of
          NONE => raise ERR "llvm_prefix" "the environment variable HOLBA_LLVM_DIR is not set"
        | SOME p => (p ^ "/bin/");

val llvm_scamv_lib =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_LLVM_DIR")) of
          NONE => raise ERR "scamv_llvm_lib" "the environment variable HOLBA_LLVM_DIR is not set"
        | SOME p => (p ^ "/lib/LLVMScamv.so");

val linker_path =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_LLVMSCAMV_DIR")) of
          NONE => raise ERR "scamv_llvm_lib" "the environment variable HOLBA_LLVMSCAMV_DIR is not set"
        | SOME p => (p ^ "/linker.ld");

fun get_exec_output_redirect do_print exec_cmd =
    let
      val outputfile = get_tempfile "exec_output" ".txt";

      val r = OS.Process.system (exec_cmd ^ " > " ^ outputfile ^ " 2>&1");
      val _ = if not do_print then () else
                print (read_from_file outputfile);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "get_exec_output_redirect" ("the following command did not execute successfully: " ^ exec_cmd)
              else
                ();

      val s = read_from_file outputfile;

      val _ = OS.Process.system ("rm " ^ outputfile);
    in
      s
    end;

fun compile_and_link_armv8_llvm_bc binfilename bcfile bt =
    let
      val bt_opt = if bt = "rpi3" then "-target aarch64-linux-gnu -march=armv8-a -mcpu=cortex-a53"
		   else if bt = "rpi4" then "-target aarch64-linux-gnu -march=armv8-a -mcpu=cortex-a72"
		   else raise ERR "compile_and_link_armv8_llvm_bc" "unknown board type"
      val linker_opt = "-Xlinker -T " ^ linker_path;
      val compiler_opt = "-O0 -Wall -g -mgeneral-regs-only -static -nostartfiles -fno-stack-protector -nostdlib -ffreestanding -fno-builtin --specs=nosys.specs";
      val cmd_static_link = (llvm_prefix () ^ "clang " ^
			     bt_opt ^ " " ^ compiler_opt ^ " " ^ linker_opt ^ " " ^
			     bcfile ^ " -o " ^ binfilename);
    in
      if OS.Process.isSuccess (OS.Process.system cmd_static_link)
      then binfilename
      else raise ERR "compile_and_link_armv8_llvm_bc" "cmd_static_link"
    end;

fun compile_llvm_bc binfilename bcfile =
    let
      val bcfile_o = binfilename ^ ".o";
      val cmd_bc_compile = (llvm_prefix () ^ "llc -filetype=obj " ^ bcfile ^ " -o " ^ bcfile_o);
    in
      if OS.Process.isSuccess (OS.Process.system cmd_bc_compile)
      then bcfile_o
      else raise ERR "compile_llvm_bc" "cmd_bc_compile"
    end;

fun link_llvm_bcs filename bcfiles =
    let
      val bcfilename = get_simple_tempfile (filename ^ ".bc");
      val bcfiles_to_link = List.foldl (fn (f1,f2)=> (f2 ^ f1 ^ " ")) "" bcfiles;
      val cmd_llvm_link = (llvm_prefix () ^ "llvm-link " ^
			   bcfiles_to_link ^ " -o " ^ bcfilename);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_llvm_link)
       then bcfilename
       else raise ERR "link_llvm_bcs" "cmd_llvm_link")
    end

fun link_missing_funs filename slicedfunbc beforeslicefilebc =
    let
      val bcfilename = filename ^ "linked.bc";
      val cmd_link_miss_funs = (llvm_prefix () ^ "llvm-link" ^
				" -only-needed " ^ slicedfunbc ^ " " ^ beforeslicefilebc ^ " -o " ^ bcfilename);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_link_miss_funs)
       then bcfilename
       else raise ERR "link_missing_funs" "cmd_link_miss_funs")
    end

fun link_missing_globs filename slicedfunbc beforeslicefilebc glob_names =
    let
      val bcglobs = filename ^ "-globs.bc";
      val bcfilename = filename ^ "-final.bc";
      val globs = List.foldl (fn (g1,g2)=> (g2 ^ " -glob " ^ g1)) "" glob_names;
      val cmd_extract_globs = (llvm_prefix () ^ "llvm-extract " ^
			       globs ^ " " ^ beforeslicefilebc ^ " -o " ^ bcglobs);
      val cmd_link_miss_globs = (llvm_prefix () ^ "llvm-link" ^
				" -only-needed " ^ slicedfunbc ^ " " ^ bcglobs ^ " -o " ^ bcfilename);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_extract_globs)
       then
         if OS.Process.isSuccess (OS.Process.system cmd_link_miss_globs)
	 then bcfilename
	 else raise ERR "link_missing_globs" "cmd_link_miss_globs"
       else raise ERR "link_missing_globs" "cmd_extract_globs")
    end

fun get_fun_names prog_bc =
    let
      val cmd_print_funcs = (llvm_prefix () ^ "opt -enable-new-pm=0 -load " ^
			     llvm_scamv_lib ^ " -print-functions " ^
			     prog_bc ^ " -o " ^ (get_simple_tempfile "delete.bc"));
      val output = get_exec_output_redirect false cmd_print_funcs;
      val _ = OS.Process.system ("rm " ^ (get_simple_tempfile "delete.bc"));
    in
      String.tokens (fn x => x = #"\n") output
    end

fun get_glob_names prog_bc =
    let
      val cmd_print_funcs = (llvm_prefix () ^ "opt -enable-new-pm=0 -load " ^
			     llvm_scamv_lib ^ " -print-globals " ^
			     prog_bc ^ " -o " ^ (get_simple_tempfile "delete.bc"));
      val output = get_exec_output_redirect false cmd_print_funcs;
      val _ = OS.Process.system ("rm " ^ (get_simple_tempfile "delete.bc"));
    in
      String.tokens (fn x => x = #"\n") output
    end

fun metarenamer_fun (fun_name, fun_bc) =
    let
      val fun_ll = get_simple_tempfile (fun_name ^ ".ll");
      val cmd_metarenamer_fun = (llvm_prefix () ^ "opt" ^
			    " -S -metarenamer " ^ fun_bc ^ " -o " ^ fun_ll);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_metarenamer_fun)
       then (fun_name, fun_ll)
       else raise ERR "metarenamer_fun" "cmd_metarenamer_fun")
    end

fun metarenamer_bbs (fun_name, fun_bc) =
    let
      (* val fun_renamed = get_simple_tempfile (fun_name ^ "-renamed.bc"); *)
      val cmd_metarenamer_bbs = (llvm_prefix () ^ "opt -enable-new-pm=0 -load " ^
			     llvm_scamv_lib ^ " -rename-blocks " ^
			     fun_bc ^ " -o " ^ fun_bc);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_metarenamer_bbs)
       then (fun_name, fun_bc)
       else raise ERR "metarenamer_bbs" "cmd_metarenamer_bbs")
    end

fun extract_fun_with_recursive prog_bc fun_name =
    let
      val fun_bc = get_simple_tempfile (fun_name ^ ".bc");
      val cmd_extract_fun = (llvm_prefix () ^ "llvm-extract" ^
			     " -func " ^ fun_name ^ " -recursive < " ^ prog_bc ^ " > " ^ fun_bc);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_extract_fun)
       then (fun_name, fun_bc)
       else raise ERR "extract_fun_with_recursive" "cmd_extract_fun")
    end

fun extract_multi_funs prog_bc fun_names =
    let
      val filebc = get_simple_tempfile ("extracted-" ^ prog_bc);
      val funs_to_extr = List.foldl (fn (f1,f2)=> (f2 ^ " -func " ^ f1)) "" fun_names;
      val cmd_extract_multi_funs = (llvm_prefix () ^ "llvm-extract" ^
				    funs_to_extr ^ " < " ^ prog_bc ^ " > " ^ filebc);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_extract_multi_funs)
       then (fun_names, filebc)
       else raise ERR "extract_multi_funs" "cmd_extract_multi_funs")
    end 

fun analyze_func (fun_name, fun_bc) threshold_ninst =
    let
      val cmd_analyze_func = (llvm_prefix () ^ "opt " ^ fun_bc ^
			      " -enable-new-pm=0 -load " ^ llvm_scamv_lib ^
			      " -analyze-function " ^ fun_name ^ " -o " ^ (get_simple_tempfile "delete.bc"));
      val appx_inst_count = Int.fromString (get_exec_output_redirect false cmd_analyze_func);
      val _ = OS.Process.system ("rm " ^ (get_simple_tempfile "delete.bc"));
    in
      if isSome appx_inst_count then
	if ((valOf appx_inst_count) >= threshold_ninst) then true else false
      else raise ERR "analyze_func" "Instruction counting doesn't work"
    end

 fun peel_and_delete_loops (fun_name, filebc) =
    let
      val cmd_unroll_loops = (llvm_prefix () ^ "opt" ^
			      " -mem2reg -loops -loop-simplify -loop-unroll -unroll-peel-count=2 " ^
			      filebc ^ " -o " ^ filebc);
      val cmd_delete_loops = (llvm_prefix () ^ "opt -reg2mem -enable-new-pm=0 -load " ^
			      llvm_scamv_lib ^ " -extend-loop-deletion " ^
			      filebc ^ " -o " ^ filebc);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_unroll_loops)
       then
         if OS.Process.isSuccess (OS.Process.system cmd_delete_loops)
	 then (fun_name, filebc)
	 else raise ERR "peel_and_delete_loops" "cmd_delete_loops"
       else raise ERR "peel_and_delete_loops" "cmd_unroll_loops")
    end

fun get_extract_options (fun_name, fun_bc) threshold =
    let
      val cmd_slicing = (llvm_prefix () ^ "opt -enable-new-pm=0 -load " ^
			 llvm_scamv_lib ^
			 " -automatic-block-specifier -func " ^ fun_name ^ " -t " ^ (Int.toString threshold) ^ " " ^
			 fun_bc ^ " -o " ^ (get_simple_tempfile "delete.bc"));
      val output = get_exec_output_redirect false cmd_slicing;
      val list_ext_opts = String.tokens (fn x => x = #"\n") output;
      val _ = OS.Process.system ("rm " ^ (get_simple_tempfile "delete.bc"));
    in
      list_ext_opts
    end

fun extract_bbs_from_fun (fun_name, fun_bc) ext_option =
    let
      val opt_str = String.implode (List.map
				   (fn c=> if (c=(#";")) then (#"-") else c)
				   (String.explode ext_option));
      val sliced_fun_bc = get_simple_tempfile (opt_str ^ ".bc");
      val cmd_extract_bbs = (llvm_prefix () ^ "llvm-extract" ^
			     " -bb \"" ^ ext_option ^ "\" -recursive " ^
			     fun_bc ^ " -o " ^ sliced_fun_bc);
    in
      (if OS.Process.isSuccess (OS.Process.system cmd_extract_bbs)
       then ((fun_name, SOME opt_str), sliced_fun_bc)
       else raise ERR "extract_bbs_from_fun" "cmd_extract_bbs")
    end
    
fun slice_func (fun_name, fun_bc) size =
    let
      val to_slice = analyze_func (fun_name, fun_bc) size;
    in
      if to_slice
      then
	let
	  val ext_opts = get_extract_options (fun_name, fun_bc) size;
	in
	  if null ext_opts
	  then [((fun_name, NONE), fun_bc)] (* Note: maybe skip this *)
	  else List.map (fn opt=> extract_bbs_from_fun (fun_name, fun_bc) opt) ext_opts
	end
      else [((fun_name, NONE), fun_bc)]
    end


fun llvm_initial_phase filebc llvm_option =
    let
      val _ = print "LLVM phase...\n";
      val func_names = get_fun_names filebc;
      val extracted_fun_bcs = List.map (fn f => extract_fun_with_recursive filebc f) func_names;
      val fun_w_loops_del_bcs = List.map (fn f => peel_and_delete_loops f) extracted_fun_bcs;
      val fun_renamed_bcs = List.map (fn f => metarenamer_bbs f) fun_w_loops_del_bcs;
      val bt = "rpi4";

      val sliced_fun_bcs = let val manually = isSome llvm_option;
			in
			  if manually
			  then
			    let val (fun_specified, blocks_specified) =
				  case (String.tokens (fn c => c = #":") (valOf llvm_option)) of
				    (f::nil) => (f, NONE)
				  | (f::bbs) => (f, SOME bbs)
				  | _ => raise ERR "llvm_initial_phase" "error in llvm_option parsing"
				val f = List.find (fn (fnm,fbc) => fnm = fun_specified) fun_renamed_bcs;
			    in
			      case f of
				SOME (fnm,fbc) =>
				  if isSome blocks_specified then
				      [extract_bbs_from_fun (fnm,fbc) (valOf llvm_option)]
				  else
				      [((fnm,NONE),fbc)]
			      | NONE =>
				raise ERR "llvm_initial_phase" "the specified function was not found"
			    end
			  else (List.concat (List.map (fn f => slice_func f 150) fun_renamed_bcs))
			end;
      (* val fun_w_loops_del_bcs = List.map (fn f => peel_and_delete_loops f) sliced_fun_bcs; *)

      val binfiles = List.map (fn ((f,fd), fbc) =>
				  let
				    val fd = if isSome fd then (valOf fd) else f;
				    (* val name = String.extract (fbc, ((List.length o String.explode) tempdir)+1, NONE); *)
				    val fname = (String.extract(fbc, 0, SOME (String.size fbc-3)));
				    val linkedfilebc = link_missing_funs fname fbc filebc;
				  in
				    ((f, fd,
				      linkedfilebc,
				      SOME (compile_and_link_armv8_llvm_bc fname linkedfilebc bt))
				     handle HOL_ERR e =>
					    let
					      val globs = get_glob_names filebc;
					      val finalfilebc = link_missing_globs fname linkedfilebc filebc globs;
					    in
					      (f, fd,
					       finalfilebc,
					       SOME (compile_and_link_armv8_llvm_bc fname finalfilebc bt))
					    end
				     handle HOL_ERR e => (print ("Compilation error: " ^ fd ^ " \n\n");
							  (f, fd, fbc, NONE)))
				  end) sliced_fun_bcs;
      val _ = print "LLVM phase finished.\n";
    in
      SOME (List.map (fn (f,fd,fbc,b)=> ((f,fd,fbc),valOf b)) (List.filter (fn (_,_,_,b)=> isSome b) binfiles))
    end;

(* val binfilename = "/home/tiziano/llvm-project/llvm/build/tiziano-tests/tea/tea-arm.bc"; *)
(* val binfilename = "/home/tiziano/llvm-project/llvm/build/tiziano-tests/libsodium-aarch64/crypto_onetimeauth_poly1305_donna/poly1305-donna/poly1305_update-O1.bc"; *)
(* val filebc = binfilename; *)


fun llvm_insert_fence fun_name filebc =
    let
      val _ = print "Adding fence...\n";
      (* val fenced_prog_bc = get_simple_tempfile ("fenced_" ^ filebc); *)
      val cmd_insert_fence = (llvm_prefix () ^ "opt -enable-new-pm=0 -load " ^
			      llvm_scamv_lib ^ " -fence-insertion -func_to_fence " ^
			      fun_name ^ " " ^  filebc ^ " -o " ^ filebc);
      val res = Int.fromString (get_exec_output_redirect false cmd_insert_fence);
    in
      if isSome res
      then
	(case (valOf res) of
	    1 => (print "fence added\n"; SOME filebc)
	  | 0 => (print "no fence added (you may have reached the maximum fencing)\n"; NONE)
	  | 23 => (case get_fun_names filebc of
		    fnm::nil => if String.isSubstring fun_name fnm
				then llvm_insert_fence fnm filebc
				else raise ERR "llvm_insert_fence" "function name unknown"
		  | (_::_) => raise ERR "llvm_insert_fence" "more than one function name"
		  | _ => raise ERR "llvm_insert_fence" "unknown error")
	  | _ => raise ERR "llvm_insert_fence" "result unknown")
       else raise ERR "llvm_insert_fence" "cmd_insert_fence"
    end


end


end
