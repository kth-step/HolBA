let
open scamv_enumLib;
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

fun test1 () =
    let val e = range_from_to 1 5
    in
      (take 5 e = [1,2,3,4,5]) andalso (peek e = 5)
    end;

fun test_rr () =
    let val e = roundrobin_list [4,2,12,66]
        val _ = take 4 e
    in
      next e = 4 andalso next e = 2
      andalso next e = 12 andalso next e = 66
    end;

fun test_peek () =
    let val e = range_from_to 1 5
    in
      peek e = peek e
    end;

fun test_zip_cartesian () =
    let fun zip [] _ = []
          | zip _ [] = []
          | zip (x::xs) (y::ys) = (x,y) :: zip xs ys
        val p = range_from_to 1 5
        val q = range_from_to 6 10
    in
      take 5 (cartesian p q) = zip [1,2,3,4,5] [6,7,8,9,10]
    end;

fun test_interleave () =
    let fun ileave [] ys = ys
          | ileave xs [] = xs
          | ileave (x::xs) (y::ys) = x :: y :: ileave xs ys
        val e = interleave (range_from_to 1 5) (range_from_to 6 10)
    in
      take 10 e = ileave [1,2,3,4,5] [6,7,8,9,10]
    end;
in
run_tests
        [("test1",test1)
        ,("test_rr",test_rr)
        ,("test_peek",test_peek)
        ,("test_interleave",test_interleave)]
end;
