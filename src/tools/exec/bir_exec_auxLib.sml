open HolKernel boolLib liteLib simpLib Parse bossLib;

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


  fun GEN_selective_conv is_tm_fun check_tm_fun conv =
    GEN_match_conv is_tm_fun (GEN_check_conv check_tm_fun conv);


end
