signature pretty_exnLib =
sig

  (****************************************************************************)
  (* This library is designed for user facing code. It enables to easily show *)
  (* exceptions in an easy-to-read way.                                       *)
  (*                                                                          *)
  (* Usage:                                                                   *)
  (*   some_code (that "can_raise" an exn)                                    *)
  (*   handle e => pp_exn e;                                                  *)
  (*                                                                          *)
  (****************************************************************************)

  val pp_exn: exn -> exn
  val pp_exn_s: string -> exn -> exn

end