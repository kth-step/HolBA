structure bir_scamv_helpersLib =
struct

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

(* error handling *)
  val libname = "bir_scamv_helpersLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

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

end (* local *)

end
