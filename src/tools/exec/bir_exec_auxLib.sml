open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_envSyntax;

structure bir_exec_auxLib =
struct


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


  fun GEN_selective_conv is_tm_fun check_tm_fun conv =
    GEN_match_conv is_tm_fun (GEN_check_conv check_tm_fun conv);





  fun gen_var_eq_thm vars =
        let
          val vars = List.map (fst o dest_BVar) vars;
        in
          LIST_CONJ (List.map ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL)
                     (List.foldl (fn (v,l) => (List.map (fn v2 => mk_eq(v,v2)) vars)@l) [] vars)
                    )
        end;



  fun gen_label_eq_thms labels =
          List.map ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL)
             (List.foldl (fn (v,ls) => (List.map (fn v2 => mk_eq(v,v2)) labels)@ls) [] labels)
          ;



end
