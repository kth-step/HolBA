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
(* ============================================== *)



(*
=================================== script starts here ====================================
*)

(* branch: tacas_29_09_01_cache_addr_pc *)
val listname = "M1_zeroedstate_160";

val exp_ids = bir_embexp_load_exp_ids listname;
val exp_id = List.nth(exp_ids,1);

val _ = List.map (fn exp_id =>
  let
val (asm_lines, s) = bir_embexp_load_exp exp_id;

(*
val asm_code = bir_embexp_prog_to_code asm_lines;
*)

(* lifting *)
val prog_preproc_o = lift_prog_preproc (fn x => raise ERR "script" "preproc failed") asm_lines;
val prog_preproc = valOf prog_preproc_o
                   handle _ => raise ERR "script" "this shouldn't happen";

val (asm_code, lifted_prog, prog_len) = lift_prog_lift (fn x => raise ERR "script" "lifting failed") prog_preproc;

(* symbolic execution *)
val prog = lifted_prog
val (paths, all_exps) = symb_exec_phase prog;

(*
(* collect variables in programs, and [path condition and observation list] per path *)
val varlist_prog_raw = bir_execLib.gen_vars_of_prog lifted_prog;
val vars_prog = Redblackset.fromList Term.compare varlist_prog_raw;
*)

(*
(* NOTE: freevar hack, there is also always MEM *)
val bv_mem = ``BVar "MEM" (BType_Mem Bit64 Bit8)``;
val varlist_exp_raw = (bv_mem::(flatten (List.map get_birexp_vars all_exps)));
val vars_exp = Redblackset.fromList Term.compare varlist_exp_raw;
*)

(*
val (pcond, obss) = List.nth (paths, 0);
length paths
List.map snd paths

fun pathtocondvars (pcond, obss) =
  let
    val obs_exps = List.map (fn (_,x,y) => [x,y])
                      (flatten (List.map ((fn x =>
                        case x of NONE => [] 
                         | SOME y => y)) obss));

    val vars = 
  in
    (pcond, vars)
  end;

val pathcondvarsmap = List.map pathtocondvars paths;

val path_conds = List.map fst paths;
*)
  in
    ()
  end) exp_ids;
