structure scamv_testsLib =
struct
exception TestsFailed of string list;

fun run_tests ts =
    let fun test [] failed = failed
          | test ((name,func)::ts) failed =
            if func ()
            then test ts failed
            else test ts (name :: failed)
    in
      case test ts [] of
          [] => ()
        | fs => raise (TestsFailed (rev fs))
    end;
end

