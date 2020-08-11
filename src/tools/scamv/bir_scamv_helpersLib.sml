structure bir_scamv_helpersLib =
struct

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

(* error handling *)
  val libname = "bir_scamv_helpersLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

(* Data type for memory constraint generation *)
datatype modelValues = memT of (string * (num*num) list)
		       | regT of (string * num)
(* script input helper *)
  local
    val script_args_data = ref (NONE: string option);
    fun setdata data x =
      if String.isPrefix "--extra=" x then
        if !data = NONE then
          data := SOME (String.extract (x, 8, NONE))
        else raise ERR "scamv_helper" "use the extra argument only once"
      else
        ();
    fun assign_args_data () =
      (List.foldl (fn (x, _) => setdata script_args_data x)
                  ()
                  (Portable.getArgs());
       if !script_args_data = NONE then
         script_args_data := SOME ""
       else
         ()
       );
  in
    fun get_script_args () =
      case !script_args_data of
	  SOME x => x
	| NONE => (assign_args_data (); valOf (!script_args_data));
  end

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
    rand_isfresh_ref := SOME isfresh;
(*    case !rand_isfresh_ref of
       NONE   => rand_isfresh_ref := SOME isfresh
     | SOME _ => raise ERR "rand_isfresh_set" "freshness has been set already"; *)

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

  open bir_miscLib;
  open bir_fileLib;
  open bir_exec_wrapLib;

end (* local *)
  
end
