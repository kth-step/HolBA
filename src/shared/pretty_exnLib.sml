structure pretty_exnLib :> pretty_exnLib =
struct

  local

  open HolKernel Parse PPBackEnd boolLib bossLib;

  val ERR = mk_HOL_ERR "pretty_exnLib";
  val wrap_exn = Feedback.wrap_exn "pretty_exnLib";

  val yellow = add_style_to_string [FG Yellow]
  val boldcyan = add_style_to_string [FG BlueGreen, Bold]
  val boldred = add_style_to_string [FG RedBrown, Bold]

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
       ^ boldcyan " - Message: " ^ message ^ "\n"
       ^ "\n"
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

  fun pp_exn_s message exn =
    (print (boldred "Handled exception: " ^ yellow message ^ "\n"); pp_exn exn);

  end (* local *)

end (* pretty_exnLib *)
