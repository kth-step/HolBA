
open scamv_enumLib;

fun test1 () =
    let val e = range_from_to 1 5
    in
      (take 10 e = [1,2,3,4,5]) andalso (peek e = 6)
    end;
