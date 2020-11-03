structure bir_randLib =
struct

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

(* error handling *)
  val libname = "bir_randLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

(* central random number generator *)
local
  fun getrealtime () =
     let
        val t = Time.now ()
        val micro_s = Time.toMicroseconds t
        val sec = micro_s div 1000000
        val usec = micro_s mod 1000000
     in
        {sec = sec, usec = usec}
     end
  fun seedgen_real () =
    let
      val {sec, usec} = getrealtime ();
    in
      Real.fromLargeInt sec + Real.fromLargeInt usec
    end;

  fun gen_seed isfresh =
            if isfresh then
              seedgen_real ()
            else
              3141592.654;

  val rand_isfresh_ref = ref (NONE: bool option);
  val rand_seed_ref    = ref (NONE: real option);
  val rand_gen_ref     = ref (NONE: Random.generator option);
in
  fun rand_isfresh_set isfresh =
    case !rand_isfresh_ref of
       NONE   => rand_isfresh_ref := SOME isfresh
     | SOME x => if x = isfresh then () else
                 raise ERR "rand_isfresh_set"
                    ("random freshness has already been set to " ^
                       (if x then "true" else "false"));

  fun rand_isfresh_get () =
    case !rand_isfresh_ref of
       SOME v => v
     | NONE   => (rand_isfresh_ref := SOME false; rand_isfresh_get());

  fun rand_seed_get () =
    case !rand_seed_ref of
       SOME v => v
     | NONE   => (rand_seed_ref := SOME (gen_seed (rand_isfresh_get())); rand_seed_get());

  fun rand_gen_get () =
    case !rand_gen_ref of
       SOME v => v
     | NONE   => (rand_gen_ref := SOME (Random.newgenseed (rand_seed_get())); rand_gen_get());
end


end (* local *)

end (* struct *)
