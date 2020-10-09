open bir_embexp_driverLib;

open bir_prog_genLib;

open bir_scamv_driverLib;

(* copy and paste code duplication *)
(* ============================================== *)
local
  open pred_setTheory;
in
  val conv_to_varset = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss)
                                 ([INSERT_UNION_EQ,UNION_EMPTY]@HolBASimps.common_exp_defs);
end;

fun simpleholset_to_list t =
  if pred_setSyntax.is_empty t then [] else
  if not (pred_setSyntax.is_insert t) then
    raise ERR "simpleholset_to_list" ("cannot handle syntax: " ^ (term_to_string t))
  else
    let val (x, rset) = pred_setSyntax.dest_insert t in
      x::(simpleholset_to_list rset)
    end;
fun get_birexp_vars exp =
  let
    val exp_vars = (snd o dest_eq o concl o conv_to_varset) ``(bir_vars_of_exp ^exp)``;
    val vars = (simpleholset_to_list) exp_vars;
  in
    vars
  end;
fun get_birprog_vars prog =
  let
    val exp_vars = (snd o dest_eq o concl o conv_to_varset) ``(bir_vars_of_program ^prog)``;
    val vars = (simpleholset_to_list) exp_vars;
  in
    vars
  end;
(* ============================================== *)



(*
=================================== script starts here ====================================
*)

val listname = "hamed1";

(* loading *)
val progs = bir_embexp_load_progs listname;
val prog = hd progs;

(* lifting *)
val prog_preproc_o = lift_prog_preproc (fn x => raise ERR "script" "preproc failed") prog;
val prog_preproc = valOf prog_preproc_o
                   handle _ => raise ERR "script" "this shouldn't happen";

val (asm_code, lifted_prog, prog_len) = lift_prog_lift (fn x => raise ERR "script" "lifting failed") prog_preproc;

(* symbolic execution *)
val (_, all_exps) = symb_exec_phase lifted_prog;

(* collect variables in programs, and [path condition and observation list] per path *)
val varlist_prog_raw = bir_execLib.gen_vars_of_prog lifted_prog;
val vars_prog = Redblackset.fromList Term.compare varlist_prog_raw;

(* NOTE: freevar hack, there is also always MEM *)
val bv_mem = ``BVar "MEM" (BType_Mem Bit64 Bit8)``;
val varlist_exp_raw = (bv_mem::(flatten (List.map get_birexp_vars all_exps)));
val vars_exp = Redblackset.fromList Term.compare varlist_exp_raw;
