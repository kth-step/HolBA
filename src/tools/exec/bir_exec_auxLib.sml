open HolKernel boolLib liteLib simpLib Parse bossLib;

structure bir_exec_auxLib =
struct


  fun GEN_check_conv check_tm_fun conv tm =
    let
      val thm = conv tm;
      val result = (snd o dest_eq o concl) thm;
    in
      if not (check_tm_fun result) then (
        print "----------------";
        print_term tm;
        print "----------------";
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
