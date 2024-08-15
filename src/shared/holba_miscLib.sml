structure holba_miscLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "holba_miscLib"
  val wrap_exn = Feedback.wrap_exn "holba_miscLib"

  open HolKernel boolLib liteLib simpLib Parse bossLib;

in

  (* datestring helper *)
  fun get_datestring () =
    let
      val date = Date.fromTimeLocal (Time.now ());
      val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
    in
      datestr
    end;

(*
val s = ""
*)
  fun strip_ws_off accept_empty_string s =
    let
      fun is_ws x = x = #" " orelse x = #"\t" orelse x = #"\n";
      fun find_first_idx p l = List.foldl (fn ((idx,x),r) => if r >= 0 then r else if p x then idx else r)
                                          (~1)
                                          (snd (List.foldr (fn (x,(i,l)) => (i-1,(i,x)::l)) ((List.length l) - 1, []) l));

      val l = String.explode s;
      val first_c = find_first_idx (not o is_ws) l;
      val last_c = (List.length l) - 1 - (find_first_idx (not o is_ws) (List.rev l));
    in
      if first_c < 0 then
        if accept_empty_string then "" else raise ERR "strip_ws_off" "here we don't accept empty assembly lines"
      else
        String.extract (String.substring (s, 0, last_c + 1), first_c, NONE)
    end;

(* timers *)
  fun timer_start level = if (1 >= level) then SOME (Time.now()) else NONE;
  fun timer_stop f NONE = ()
    | timer_stop f (SOME tm) = let
       val d_time = Time.- (Time.now(), tm);
       in f ((Time.toString d_time) ^ "s") end;

end (* local *)
end (* struct *)
