structure bir_exec_auxLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open bir_envSyntax;

  val debug_trace = ref (1:int)
  val _ = register_trace ("bir_exec.DEBUG_LEVEL", debug_trace, 2)


  fun timer_start level = if ((!debug_trace) > level) then SOME (Time.now()) else NONE;
  fun timer_stop NONE = ""
    | timer_stop (SOME tm) = let
       val d_time = Time.- (Time.now(), tm);
       in (Time.toString d_time) end;


  fun GEN_check_thm check_thm_fun extract_print_tm_fun thm =
    if not (check_thm_fun thm) then (
        print "\n----------------\n";
        print_term (extract_print_tm_fun thm);
        print "\n----------------\n";
        raise ERR "GEN_check_thm" "theorem is not as expected"
    ) else thm;


  fun GEN_check_conv check_tm_fun conv tm =
    let
      val thm = conv tm;
      val result = (snd o dest_eq o concl) thm;
    in
      if not (check_tm_fun result) then (
        print "\n----------------\n";
        print_term tm;
        print "\n----------------\n";
        print_term result;
        print "\n----------------\n";
        raise ERR "GEN_check_conv" "conversion result is not as expected"
      ) else
        thm
    end;


  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else
      raise UNCHANGED
    ;

  fun GEN_find_subterm is_tm_fun tm =
    if is_tm_fun tm then
      tm
    else if is_comb tm then
      let
        val (l,r) = dest_comb tm;
      in
        GEN_find_subterm is_tm_fun l
        handle UNCHANGED =>
        GEN_find_subterm is_tm_fun r
      end
    else
      raise UNCHANGED
    ;

  fun GEN_find_all_subterm is_tm_fun tm =
    if is_tm_fun tm then
      [tm]
    else if is_comb tm then
      let
        val (l,r) = dest_comb tm;
      in
        (GEN_find_all_subterm is_tm_fun l)@
        (GEN_find_all_subterm is_tm_fun r)
      end
    else
      []
    ;


  fun GEN_selective_conv is_tm_fun check_tm_fun conv =
    GEN_match_conv is_tm_fun (GEN_check_conv check_tm_fun conv);





  fun gen_var_eq_thms vars =
        let
          val vars_ = List.map (fst o dest_BVar) vars;
        in
          (List.foldl (fn (tm,thms) => (((if ((!debug_trace) > 0) then (print "!") else ());
                                         ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o (EVAL THENC (REWRITE_CONV thms)))
                      ) tm)::thms) []
            (List.foldl (fn (v,l) => (List.map (fn v2 => mk_eq(v,v2)) vars_)@l) [] vars_)
          )
        end;



  fun gen_label_eq_thms labels =
    let
      val eq_list = (List.foldl (fn (v,ls) => (List.map (fn v2 => mk_eq(v,v2)) labels)@ls) [] labels);
      val eq_list_len = length eq_list;

      val eval_conv = ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL);
    in
          List.foldl (fn (t,(i,l)) => (if ((!debug_trace) > 0 andalso (i >= (eq_list_len div 100))) then (print "!";0) else (i+1),
                                       (eval_conv t)::l)
                     ) (0:int,[]) eq_list
    end;



end
