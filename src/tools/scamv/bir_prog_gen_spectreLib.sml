structure bir_prog_gen_spectreLib : bir_prog_gen_spectreLib =
struct

open asm_genLib;
infix 5 <$>;
infix 5 >>=;

(* ======Spectre Generator======== *)

fun prog_gen_spectre n =
    let
      val g = bir_scamv_helpersLib.rand_gen_get ()
      val (p, _) = run_step n g arb_program_spectre
    in
       pp_program p
    end;

end

