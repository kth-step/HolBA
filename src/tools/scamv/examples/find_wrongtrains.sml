
(* branch: tacas_29_09_01_cache_addr_pc *)
val listname = "test123";

(*
=================================== general stuff starts here ====================================
*)

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

val (arch_id, exp_type_id, state_gen_id) =
    ("arm8", "cache_multiw", "regen_for_hypothesis");
val prog_gen_id = "regen_for_hypothesis_this_prog_should_exist_already";

val exp_ids = bir_embexp_load_exp_ids listname;
val exp_id = List.nth(exp_ids,1);
(*
val exp_id = "arm8/exps2/cache_multiw/96092ba1f752f2e06ffefb9a186575c6351bf9ab";
*)
val exp_id = List.last exp_ids;

val file_train_ok   = bir_embexp_create_list_open "exps" (listname ^ "_train_ok"  );
val file_train_bad  = bir_embexp_create_list_open "exps" (listname ^ "_train_bad" );
val file_train_fail = bir_embexp_create_list_open "exps" (listname ^ "_train_fail");

val n_exps = length exp_ids;
val iref = ref 0;
val _ = List.map (fn exp_id =>
  let

val i = !iref;
val _ = iref := i + 1;

val p10k = Real.round ((Real.fromInt i) / (Real.fromInt n_exps) * 10000.0);
val pb = p10k div 100;
val pa = p10k mod 100;
val percent_s = (Int.toString pb) ^ "." ^ (Int.toString pa) ^ "%";
val _ = print ("progress: " ^ percent_s);

val _ = print ("\n=========================================================\n");
val _ = print (exp_id ^ "\n");

val (asm_lines, (s1,s2), traino) = bir_embexp_load_exp exp_id;
val s_train = valOf traino
              handle _ => raise ERR "script" "no training data";

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
    (pcond,obs_exps, vars)
  end;

val pathcondvarsmap = List.map pathtocondvars paths_i;
val _ = if length pathcondvarsmap = 2 then () else
        raise ERR "script" "was checked before";

(*
val s_ = s2;
*)

val memtype = inst [Type.alpha |-> ``:num``, Type.beta |-> ``:num``] finite_mapSyntax.fempty_t;
fun modelVal_to_expmap (regT (n, v)) =
      (n, ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordi (v, 64)))``)
  | modelVal_to_expmap (memT (n, l)) =
      (n, List.foldr (fn ((a,v), t) => finite_mapSyntax.mk_fupdate
                (t, pairSyntax.mk_pair (numSyntax.mk_numeral a, numSyntax.mk_numeral v))
            ) memtype l);

val sm1 = Redblackmap.fromList String.compare (List.map modelVal_to_expmap s1);
val sm2 = Redblackmap.fromList String.compare (List.map modelVal_to_expmap s2);
val sm_train = Redblackmap.fromList String.compare (List.map modelVal_to_expmap s_train);

(*
val sm_ = sm1;
val sm_ = sm2;
val (pcond_,obs_exps_, vars_) = hd (tl pathcondvarsmap);
val (pcond_,obs_exps_, vars_) = hd pathcondvarsmap;
val e_ = pcond_;
*)

fun substvars_scamv_hack sm_ e_ =
  if bir_expSyntax.is_BExp_Den e_ then
    let
      val (vn,vt) = (bir_envSyntax.dest_BVar_string o bir_expSyntax.dest_BExp_Den) e_;

      val bexp = Redblackmap.find (sm_, vn)
                 handle _ => raise ERR "script" ("coudln't find state variable for substitution: " ^ vn);

      val _ = if vt = ``BType_Imm Bit64`` then () else
              raise ERR "script" "check type of bexp";
    in
      bexp
    end
  else if not (is_comb e_) then
    if is_var e_ then
      let
        val (vn,vt) = dest_var e_;

        val hexp = Redblackmap.find (sm_, vn)
                   handle _ => raise ERR "script" ("coudln't find state variable for substitution: " ^ vn);

        val _ = if vt = ``:(num |-> num)`` then () else
                raise ERR "script" "check type of hexp";
      in
        hexp
      end
    else
      e_
  else
  let
    val (e1,e2) = dest_comb e_;
  in
    mk_comb (substvars_scamv_hack sm_ e1, substvars_scamv_hack sm_ e2)
  end;

(*
(snd o dest_eq o concl o EVAL) ``bir_eval_exp ^(substvars_scamv_hack sm_ pcond_) (bir_env$BEnv (K NONE))``
*)

(* returns some if eval succeeded to eval to a bir value *)
fun eval_to_bval sm_ e_ =
  let
    val substexp = substvars_scamv_hack sm_ e_;
    val res = (snd o dest_eq o concl o EVAL) ``bir_eval_exp ^(substexp) (bir_env$BEnv (K NONE))``;
  in
    if optionSyntax.is_some res then
      SOME (optionSyntax.dest_some res)
    else
      NONE
  end;

fun pcond_evals_to_birtrue pcond_ sm_ =
  let
    val reso = eval_to_bval sm_ pcond_;
  in
    reso = SOME ``(BVal_Imm (Imm1 1w))``
  end
  handle _ => false;

fun is_validpath sm (pcond_, _, _) =
  pcond_evals_to_birtrue pcond_ sm;

fun is_validpath2 (sm1, sm2) (pcond_, _, _) =
  pcond_evals_to_birtrue pcond_ sm1 andalso
  pcond_evals_to_birtrue pcond_ sm2;

val validpath_l = List.filter (is_validpath2 (sm1, sm2)) pathcondvarsmap;
val _ = if length validpath_l = 1 then () else
        raise ERR "script" "should be exactly one valid path";

val validpath_train_l = List.filter (is_validpath sm_train) pathcondvarsmap;
val _ = if length validpath_train_l = 1 then () else
        raise ERR "script" "should be exactly one valid path (training)";

val validpath = hd validpath_l;
val validpath_train = hd validpath_train_l;

(* pathconditions of the valid paths *)
val (pathcond, _, _) = validpath;
val (pathcond_train, _, _) = validpath_train;

val trainsSamePath = identical pathcond pathcond_train;

(* store exp_id during operation: ok, bad and fail *)
val _ = if trainsSamePath then (
          TextIO.output  (file_train_bad, exp_id ^ "\n");
          TextIO.flushOut file_train_bad
        ) else (
          TextIO.output  (file_train_ok, exp_id ^ "\n");
          TextIO.flushOut file_train_ok
        );

  in
    ()
  end
  handle _=> (
    TextIO.output  (file_train_fail, exp_id ^ "\n");
    TextIO.flushOut file_train_fail;
    print ("!!!!!!!!!! ERROR !!!!!!!!!!!\n")
  )) exp_ids;

val _ = TextIO.closeOut file_train_ok;
val _ = TextIO.closeOut file_train_bad;
val _ = TextIO.closeOut file_train_fail;

(* done *)
val _ = print ("\n\n");
val _ = print ("=================================================\n");
val _ = print (":::::::::::::::::::   done   ::::::::::::::::::::\n");
val _ = print ("=================================================\n");
val _ = print ("\n");

(*
(* process *)
val exp_ids_new = List.map valOf (List.filter isSome exp_ids_opts);

(* print summary *)
val _ = print ("Number of items in list before: " ^
          (Int.toString (List.length exp_ids)) ^
          "\n");
val _ = print ("Number of items in list afterwards: " ^
          (Int.toString (List.length exp_ids_new)) ^
           "\n");

(* store in file *)
val filename = get_tempfile "exps_analyzeoutput" "wrongtrain.txt";
val str = List.foldl (fn (x, s) => s ^ (x ^ "\n")) "" exp_ids_new;
val _ = write_to_file filename str;
val _ = print("output file: " ^ filename ^ "\n");
*)


(*
val _ = print ("\n\n");
val _ = print ("=================================================\n");
val _ = print (":::::::::::::::::::::::::::::::::::::::::::::::::\n");
val _ = print ("=================================================\n");
val _ = print ("\n");

val _ = List.map (fn exp_id =>
  let
    val _ = print (exp_id ^ "\n");
  in () end
) exp_ids_new;

val _ = print ("\n");
val _ = print ("=================================================\n");
val _ = print (":::::::::::::::::::::::::::::::::::::::::::::::::\n");
val _ = print ("=================================================\n");
*)
