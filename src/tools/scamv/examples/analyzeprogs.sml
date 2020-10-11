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
(*
val exp_id = "arm8/exps2/cache_multiw/96092ba1f752f2e06ffefb9a186575c6351bf9ab";
*)

val _ = List.map (fn exp_id =>
  let

val _ = print ("\n=========================================================\n");
val _ = print (exp_id ^ "\n");

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
    (pcond,obs_exps, vars)
  end;

val pathcondvarsmap = List.map pathtocondvars paths_i;
val _ = if length pathcondvarsmap = 2 then () else
        raise ERR "script" "was checked before";

val (s1,s2) = s;
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

val (sm1,sm2) = (Redblackmap.fromList String.compare (List.map modelVal_to_expmap s1),
                 Redblackmap.fromList String.compare (List.map modelVal_to_expmap s2));

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

fun is_validpath (sm1, sm2) (pcond_, _, _) =
  pcond_evals_to_birtrue pcond_ sm1 andalso
  pcond_evals_to_birtrue pcond_ sm2;

val validpath_l = List.filter (is_validpath (sm1, sm2)) pathcondvarsmap;
val _ = if length validpath_l = 1 then () else
        raise ERR "script" "should be exactly one valid path";
val validpath = hd validpath_l;

(* found the observation expressions of the valid path *)
val (_, obs_exps, vars) = validpath;

val mem_hvar_tm = mk_var ("MEM", ``:num |-> num``);
(*
val obs_exp = List.nth (obs_exps, 0);
val obs_exp = List.nth (obs_exps, 6);
val e_ = obs_exp;
val e_ =
``
BExp_Load (BExp_MemConst Bit64 Bit8 ^(mem_hvar_tm))
         (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R25" (BType_Imm Bit64)))
            (BExp_Den (BVar "R12" (BType_Imm Bit64)))) BEnd_LittleEndian
         Bit64
``;
val e_ =
``
BExp_Load (BExp_MemConst Bit64 Bit8 ^(mem_hvar_tm))
         (BExp_BinExp BIExp_Plus (

BExp_Load (BExp_MemConst Bit64 Bit8 ^(mem_hvar_tm))
         (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R25" (BType_Imm Bit64)))
            (BExp_Den (BVar "R12" (BType_Imm Bit64)))) BEnd_LittleEndian
         Bit64

)
            (BExp_Den (BVar "R12" (BType_Imm Bit64)))) BEnd_LittleEndian
         Bit64
``;
*)
fun find_state_access_deps e_ =
  if bir_expSyntax.is_BExp_Den e_ then
    let
      val bv = bir_expSyntax.dest_BExp_Den e_;
    in
      [bv]
    end
  else if bir_expSyntax.is_BExp_Load e_ then
    let
      val (be_m, be_a, be_endi, be_sz) = bir_expSyntax.dest_BExp_Load e_;

      val _ = if identical be_m ``BExp_MemConst Bit64 Bit8 ^mem_hvar_tm`` then () else
              raise ERR "script" "memory not as expected";
      val _ = if identical be_endi ``BEnd_LittleEndian`` then () else
              raise ERR "script" "endianness not as expected";
      val _ = if identical be_sz ``Bit64`` then () else
              raise ERR "script" "size not as expected";

      val deps = find_state_access_deps be_a;
    in
      be_a::deps
    end
  else if not (is_comb e_) then
    []
  else
  let
    val (e1,e2) = dest_comb e_;
  in
    (find_state_access_deps e1)@(find_state_access_deps e2)
  end;

fun compute_addr sm_ e_ =
  if bir_envSyntax.is_BVar e_ then
    e_
  else
    let val bvo = eval_to_bval sm_ e_; in
      if isSome bvo then valOf bvo else
      raise ERR "script" "coudln't evaluate address, why?"
    end;

(*
(List.map (compute_addr sm1) o find_state_access_deps) e_
*)

(*
val obs_exps_ = obs_exps;
val sm_ = sm1;
val sm_ = sm2;
*)
fun get_state_deps sm_ obs_exps_ =
  let
    val deps_terms_hack = flatten (List.map (List.map (compute_addr sm_) o find_state_access_deps) obs_exps_);
    val (bvs, addrs) = List.partition (bir_envSyntax.is_BVar) deps_terms_hack;

    val addrs_nums = List.map (wordsSyntax.dest_word_literal o bir_valuesSyntax.dest_BVal_Imm64) addrs;
    (* NOTICE: everything is fixed to 64bit accesses -> memory addresses + {0-7} *)
    val addr_multlist = List.tabulate (8, Arbnum.fromInt);
    val addrs_nums_bytes = flatten (List.map (fn x => List.map (fn y => Arbnum.+ (x,y)) addr_multlist) addrs_nums);
    val addrs_set = Redblackset.fromList Arbnum.compare addrs_nums_bytes;

    val vns = List.map (fst o bir_envSyntax.dest_BVar_string) bvs;
    val vns_set = Redblackset.fromList String.compare vns;
  in
    (vns_set, addrs_set)
  end;

(*
val obs_exps_ = obs_exps;
val sm_ = sm1;
val s_ = s1;
*)

fun filter_state s_ (sm_, obs_exps_) =
  let
    val (vns_set_, addrs_set_) = get_state_deps sm_ obs_exps_;

    fun memlistentry_in_set set (a,_) =
      Redblackset.member (set, a);

    fun transformmapping (regT (n,v)) =
          if Redblackset.member (vns_set_, n) then
            SOME (regT (n,v))
          else
            NONE
      | transformmapping (memT (n,l)) =
          if n = "MEM" then
            SOME (memT (n, List.filter (memlistentry_in_set addrs_set_) l))
          else
            raise ERR "script" "unexpected memory name";
  in
    List.map valOf (List.filter isSome (List.map transformmapping s_))
  end;

fun get_state_size s_ =
  let
    fun modelValueSize (regT _) = 1
      | modelValueSize (memT (_, l)) = length l;
  in
    List.foldr (op+) 0 (List.map modelValueSize s_)
  end;

val s1_filtered = filter_state s1 (sm1, obs_exps);
val s2_filtered = filter_state s2 (sm2, obs_exps);

val _ = print ("\n");
val _ = print ("shrinked s1 from " ^ (Int.toString (get_state_size s1)) ^ " to " ^ (Int.toString (get_state_size s1_filtered)) ^ "\n");
val _ = print ("shrinked s2 from " ^ (Int.toString (get_state_size s2)) ^ " to " ^ (Int.toString (get_state_size s2_filtered)) ^ "\n");
val _ = print ("\n");

  in
    ()
  end) exp_ids;
