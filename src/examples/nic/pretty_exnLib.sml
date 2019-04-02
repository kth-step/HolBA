structure pretty_exnLib :> pretty_exnLib =
struct

  local

  open HolKernel Parse boolLib bossLib;

  val ERR = mk_HOL_ERR "pretty_exnLib";
  val wrap_exn = Feedback.wrap_exn "pretty_exnLib";

  (* This is from HOL/Parse *)
  local
    fun checkterm pfx s =
      case OS.Process.getEnv "TERM" of
          NONE => s
        | SOME term =>
          if String.isPrefix "xterm" term then
            pfx ^ s ^ "\027[0m"
          else
            s
  in
    val bold = checkterm "\027[1m"
    val boldred = checkterm "\027[31m\027[1m"
    val boldgreen = checkterm "\027[32m\027[1m"
    val boldyellow = checkterm "\027[33m\027[1m"
    val boldblue = checkterm "\027[34m\027[1m"
    val boldmagenta = checkterm "\027[35m\027[1m"
    val boldcyan = checkterm "\027[36m\027[1m"
    val red = checkterm "\027[31m"
    val green = checkterm "\027[32m"
    val yellow = checkterm "\027[33m"
    val blue = checkterm "\027[34m"
    val magenta = checkterm "\027[35m"
    val cyan = checkterm "\027[36m"
    val dim = checkterm "\027[2m"
    val clear = checkterm "\027[0m"
  end

  fun pp_any_exn exn =
    print (
      boldred "- Exception:\n"
       ^ boldcyan " - Name: " ^ yellow (exnName exn) ^ "\n"
       ^ boldcyan " - Message: " ^ yellow (exnMessage exn) ^ "\n"
     );

  fun pp_HOL_exn {origin_structure, origin_function, message} =
    print (
      boldred "HOL_ERR:\n"
       ^ boldcyan " - Structure: " ^ yellow origin_structure ^ "\n"
       ^ boldcyan " - Function: " ^ yellow origin_function ^ "\n"
       ^ boldcyan " - Message: " ^ yellow message ^ "\n"
     );

  in

  fun pp_exn exn =
    let
      val _ = (case exn of
          Feedback.HOL_ERR hol_exn => pp_HOL_exn hol_exn
        | exn => pp_any_exn exn)
        handle e => raise wrap_exn "pp_exn" e;
      in
        exn
      end;

  fun pp_exn_s message exn
    = (print (boldred "Handled exception: " ^ yellow message ^ "\n"); pp_exn exn);

  end (* local *)

end (* pretty_exnLib *)