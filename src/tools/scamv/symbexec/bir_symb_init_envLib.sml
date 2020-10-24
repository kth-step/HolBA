(********************************************************)
(* Functions definied within this file are use to       *)
(* initialize the environment / memory                  *)
(* This is mostly SML -- not HOL definitions!           *)
(********************************************************)

(* 
app load ["bir_symb_envTheory", "bir_symb_execTheory", "stringLib"]
*)

structure bir_symb_init_envLib :> bir_symb_init_envLib = 
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

local

open HolKernel;
open bir_expTheory;
open bir_symb_execTheory 
open bir_symb_envTheory;
open bir_valuesTheory;
open bir_immTheory;
open finite_mapTheory;
open bitstringTheory;
open stringLib;
open bir_exp_memTheory;


open bir_exec_typingLib;
open stringSyntax;

open bir_immSyntax;
open bir_valuesSyntax;
open bir_expSyntax;
open wordsSyntax;

  (* error handling *)
  val libname  = "bir_symb_init_envLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

(* Initialize all the Registers / Variables we have *)

fun update_env ((name, genf), env) =
  let
    val name_hol = fromMLstring name;
    val (tval, ttype) = genf name;
  in
    (rhs o concl o EVAL) ``bir_symb_env_update ^name_hol ^tval ^ttype ^env``
  end;

fun genf_reg_n n name =
  let
    val r = mk_var(name, mk_int_word_type n);
    val tva = mk_BExp_Const (gen_mk_Imm r);

    val tybb = bir_immtype_t_of_size n;
    val tty = mk_BType_Imm tybb;
  in
    (tva, tty)
  end;

fun genf_mem_a_n a n name =
  let
    val mem = mk_var ("MEM",Type`:num |-> num`);
    val tybba = bir_immtype_t_of_size a;
    val tybbn = bir_immtype_t_of_size n;
    val tva = mk_BExp_MemConst (tybba, tybbn, mem);

    val tty = mk_BType_Mem (tybba, tybbn);
  in
    (tva, tty)
  end;


fun init_env bir_program accept_regsuffix_o = 
    let
      fun bvar_tovarname t = (fromHOLstring o snd o dest_eq o concl o EVAL) ``bir_var_name ^t``;
      fun regs n = List.tabulate (n, fn x => "R" ^ (Int.toString x));
      fun gen_genf_list genf nl =
        List.map (fn n => (n, genf)) nl;
      fun gen_temp sl = List.map (fn s => "tmp_" ^ s) sl;

      (* 64 Bit Registers *)
      val regs_64 = ["SP_EL0"]@(regs 31);
      val regs_64 = regs_64@(gen_temp regs_64);

      (* 1 Bit flags *)
      val regs_1 = ["ProcState_N", "ProcState_Z", "ProcState_C", "ProcState_V"];
      val regs_1 = regs_1@(gen_temp regs_1);

      (* 64->8 bit memory *)
      val mems_64_8 = ["MEM"];

      (* collect all variables *)
      val bir_vars = (gen_genf_list (genf_reg_n 64) regs_64)@
                     (gen_genf_list (genf_reg_n 1) regs_1)@
                     (gen_genf_list (genf_mem_a_n 64 8) mems_64_8);

      val vars_in_prog = List.map bvar_tovarname (gen_vars_of_prog bir_program);
      val bir_vars = List.filter (fn (x, _) => List.exists (fn y => x = y) vars_in_prog) bir_vars;
      val env = List.foldl (update_env) ``BEnv FEMPTY`` bir_vars;

      (* TODO: think about changing the initialization to just take all variables from the program, with their corresponding types, and check for type mismatches *)
      val vars_in_env = List.map fst bir_vars;
      val missing_vars = List.foldr (fn (x,l) => if not (List.exists (fn y => x = y) vars_in_env) then x::l else l) [] vars_in_prog;

      val missing_vars_have_allowed_regsuffix =
        List.all (fn vn =>
           case accept_regsuffix_o of
               NONE => false 
             | SOME suff => (String.isPrefix "R" vn andalso
                             String.isSuffix suff vn)
          ) missing_vars;

      val _ = if missing_vars_have_allowed_regsuffix then () else (
              print "\n";
              print (if isSome accept_regsuffix_o then
                       "accepted register suffix: " ^ (valOf accept_regsuffix_o) ^ "\n"
                     else
                       "no register suffix is allowed\n");
              print "some variables are not allowed. all unexpected variables:\n";
              map PolyML.print missing_vars;
              print "\n";
              print_term bir_program;
              print "\n";
              raise ERR "init_env" "the symbolic environment doesn't contain all variables of the program");
    in
      List.foldl update_env env (gen_genf_list (genf_reg_n 64) missing_vars)
    end;

end (* local *)

end (* struct *)
