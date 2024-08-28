open HolKernel Parse;

open holba_fileLib;
open holba_z3Lib;

(*
val endi  = SMTMEM_LittleEndian;
val szadi = 32;
val szci  = 8;
val szi   = 16;
val opparam = (endi, szadi, szci, szi);
*)
val mem_params = (List.concat o List.map (fn szadi => (List.concat o List.map (fn szci => List.map (fn endi => (endi, szadi, szci)) gen_smt_as_funcall_endis)) gen_smt_as_funcall_szcis)) gen_smt_as_funcall_szadis;

fun gen_type_array (endi, szadi, szci, szi) =
  (SMTTY_ARR (szadi, szci));
fun gen_type_address (endi, szadi, szci, szi) =
  (SMTTY_BV szadi);
fun gen_type_value (endi, szadi, szci, szi) =
  (SMTTY_BV szi);
fun gen_fun_param vn vt =
  "(" ^ vn ^ " " ^ vt ^ ")";

fun gen_define_fun_load opparam =
  let
    val arrname = "a";
    val addname = "ad";
    val arrtype = gen_type_array opparam;
    val addtype = gen_type_address opparam;
    val valtype = gen_type_value opparam;
    val valm = (arrname, arrtype);
    val valad = (addname, addtype);
    
    val funname = gen_smt_loadstore_funname "load" opparam;
    val params = "(" ^ gen_fun_param arrname (smt_type_to_smtlib arrtype) ^
                 " " ^ gen_fun_param addname (smt_type_to_smtlib addtype) ^ ")";
    val rettype = smt_type_to_smtlib valtype;
    val exp = fst (gen_smt_load_as_exp valm valad opparam);
  in
    "(define-fun " ^ funname ^ "\n" ^
    "  " ^ params ^ "\n" ^
    "  " ^ rettype ^ "\n" ^
    "  " ^ exp ^ "\n" ^
    ")\n"
  end;

fun gen_define_fun_store opparam =
  let
    val arrname = "a";
    val addname = "ad";
    val valname = "v";
    val arrtype = gen_type_array opparam;
    val addtype = gen_type_address opparam;
    val valtype = gen_type_value opparam;
    val valm = (arrname, arrtype);
    val valad = (addname, addtype);
    val valv = (valname, valtype);
    
    val funname = gen_smt_loadstore_funname "store" opparam;
    val params = "(" ^ gen_fun_param arrname (smt_type_to_smtlib arrtype) ^
                 " " ^ gen_fun_param addname (smt_type_to_smtlib addtype) ^
                 " " ^ gen_fun_param valname (smt_type_to_smtlib valtype) ^ ")";
    val rettype = smt_type_to_smtlib arrtype;
    val exp = fst (gen_smt_store_as_exp valm valad valv opparam);
  in
    "(define-fun " ^ funname ^ "\n" ^
    "  " ^ params ^ "\n" ^
    "  " ^ rettype ^ "\n" ^
    "  " ^ exp ^ "\n" ^
    ")\n"
  end;

(*
val _ = print ("\n\n" ^ gen_define_fun_load opparam ^ "\n\n");
val _ = print ("\n\n" ^ gen_define_fun_store opparam ^ "\n\n");
*)

val str = foldl (fn ((endi, szadi, szci), acc) =>
  let
    fun genopparam szi = (endi, szadi, szci, szi);

    val str = "";
    val str = str ^ "; memory " ^ Int.toString szadi ^ "->" ^ Int.toString szci ^ " (" ^ bir_smt_mem_endianness_to_string endi ^ ")\n";
    val str = str ^ "; ----------------------\n";
    
    val str = foldl (fn (szi,acc) => acc ^ (gen_define_fun_load (genopparam szi))) str gen_smt_as_funcall_szis;
    val str = str ^ "\n";
    val str = foldl (fn (szi,acc) => acc ^ (gen_define_fun_store (genopparam szi))) str gen_smt_as_funcall_szis;
    val str = str ^ "\n";
  in
    acc ^ str
  end
) "" mem_params;
val str = str ^ "; --------------------------------------------------------------------------------------------\n";

(*
val _ = print ("\n\n" ^ str ^ "\n\n");
*)

val _ = write_to_file "holba_z3Lib_prelude.z3" str;

(* check whether the result is different *)
val _ =
  if OS.Process.isSuccess (OS.Process.system ("git diff --exit-code holba_z3Lib_prelude.z3"))
  then ()
  else
    raise Fail ("test-holba_z3Lib_preludez3_gen::The generated z3 prelude is not the same as in the git repostioriy")
