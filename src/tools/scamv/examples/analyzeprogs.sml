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

(* add halt statement in the end *)
val lifted_prog_w_halt = add_halt_to_prog prog_len lifted_prog;

(* obs augmentation *)
val current_obs_model_id = "mem_address_pc_trace";

val add_obs = #add_obs (bir_obs_modelLib.get_obs_model (current_obs_model_id));
val lifted_prog_w_obs = add_obs lifted_prog_w_halt;

(* symbolic execution *)
val prog = lifted_prog_w_obs;
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
length paths
List.map snd paths

val (pcond, obss) = hd paths_i;
*)

val paths_i = List.foldr (fn (p, l) => if isSome (#2 p) then (#1 p, valOf (#2 p))::l else l) [] paths;
val _ = if length paths_i = 2 then () else
        raise ERR "script" "expecting two interesting paths";

fun pathtocondvars (pcond, obss:(term * term * term) list) =
  let
    val bir_obs_ch0 = ``0:num``;
    val bir_true = ``BExp_Const (Imm1 1w)``;

    val obs_ch   = List.map #1 obss;
    val _ = if List.all (identical bir_obs_ch0) obs_ch then () else
            raise ERR "script" "expecting always obs channel 0";
    val obs_cond = List.map #2 obss;
    val _ = if List.all (identical bir_true) obs_cond  then () else
            raise ERR "script" "expecting always obs condition true";

    val obs_exps = List.map #3 obss;
    fun scan_for_vars t =
      if not (is_comb t) then
        if not (is_var t) then false else
        (print ("found var: " ^ (term_to_string t) ^ "\n"); true)
      else
      let
        val (t1, t2) = dest_comb t;
      in
        scan_for_vars t1 orelse scan_for_vars t2
      end;
    val foundMem = List.exists scan_for_vars obs_exps;
    val _ = if foundMem then print ("found MEM!\n") else ();

    (* NOTE: freevar hack, there is also always MEM *)
    val bv_mem = ``BVar "MEM" (BType_Mem Bit64 Bit8)``;
    val bv_mem_l = if foundMem then [bv_mem] else [];
    val varlist_exp_raw = flatten (List.map get_birexp_vars (pcond::obs_exps));
    val vars = Redblackset.fromList Term.compare (bv_mem_l@varlist_exp_raw);
  in
    (pcond, vars)
  end;

val pathcondvarsmap = List.map pathtocondvars paths_i;

val path_conds = List.map fst paths;

  in
    ()
  end) exp_ids;
