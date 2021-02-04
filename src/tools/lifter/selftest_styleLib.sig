signature selftest_styleLib = sig

  include PPBackEnd;

  (* TODO: Put test instances here? *)
  val sty_OK     : pp_style list
  val sty_CACHE  : pp_style list
  val sty_FAIL   : pp_style list
  val sty_HEADER : pp_style list

end;
