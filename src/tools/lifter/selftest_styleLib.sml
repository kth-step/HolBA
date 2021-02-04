structure selftest_styleLib :> selftest_styleLib = struct

  open PPBackEnd;

  (* TODO: Put test instances here? *)

  (* Styles for success, fail and header *)
  val sty_OK     = [FG Green];
  val sty_CACHE  = [FG Yellow];
  val sty_FAIL   = [FG OrangeRed];
  val sty_HEADER = [Bold, Underline];

end;
