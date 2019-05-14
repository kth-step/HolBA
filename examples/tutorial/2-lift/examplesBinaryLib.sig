signature examplesBinaryLib =
sig
  include Abbrev

  val bir_prog_tm : term

  (* The greatest common divisor function *)
  val gcd_prog_tm : term

  (* The square root function *)
  val sqrt_prog_tm : term

  (* The modular exponentiation function *)
  val modexp_prog_tm : term

  (* The buggy binary search function *)
  val binsearch_bad_prog_tm : term

  (* The hopefully non-buggy binary search function *)
  val binsearch_ok_prog_tm : term

end
