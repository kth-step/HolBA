structure UtilLib =
struct

fun span _ [] = ([],[])
  | span p (x::xs) = 
    if p x
    then let val (ys, zs) = span p xs in (x::ys, zs) end
    else ([], x::xs)
	   
fun break p = span (not o p)

fun takeWhile _ [] = []
  | takeWhile p (x::xs) = 
    if p x
    then x::takeWhile p xs
    else []

fun dropWhile _ [] = []
  | dropWhile p (x::xs) = 
    if p x
    then dropWhile p xs
    else (x::xs) 

fun split p xs =
    let val (ys, zs) = break p xs in
	(ys, dropWhile p zs)
    end

fun groupBy _ [] = []
  | groupBy eq (x::xs) =
    let
	val (ys, zs) = span (fn y => eq(x,y)) xs
    in
	(x::ys)::groupBy eq zs
    end

fun deleteBy _ _ [] = []
  | deleteBy eq x (y::ys) = if eq(x, y) then ys else y::deleteBy eq x ys 

fun nubBy _ [] = []
  | nubBy eq (x::xs) = x::(nubBy eq (List.filter (fn y => not(eq(x, y))) xs))

fun unionBy eq xs ys = xs @ foldl (fn (x,ys) => deleteBy eq x ys) ys xs

fun intersectBy eq _ [] = []
  | intersectBy eq [] _ = []
  | intersectBy eq xs ys = List.filter (fn x => List.exists (fn y => eq(x,y)) ys) xs 

fun transpose xs def = 
    let 
	fun hd' [] = def
	  | hd' (x::xs) = x
	fun tl' [] = []
	  | tl' (x::xs) = xs
    in 
	if List.all null xs then []
	else map hd' xs :: transpose (map tl' xs) def
    end

fun trim p s =
    let
	val i = ref 0
	val j = ref (String.size s)
    in
	while (!i < !j andalso p (String.sub(s,!i))) do i := !i + 1;
	while (!i < !j andalso p (String.sub(s,!j - 1))) do j := !j - 1;
	String.substring(s, !i, !j - !i)
    end

fun split p s =
    let
	val i = ref 0
	val size = String.size s
    in
	while (!i < size andalso not (p (String.sub(s, !i)))) do i := !i + 1;
	if !i < size then
	    SOME (String.substring(s, 0, !i),
		  String.extract(s,!i + 1, NONE))
	else 
	    NONE
    end

fun fst (x,_) = x
fun member (x,l) = List.exists (fn y => x = y) l

local
    open HolKernel wordsSyntax numSyntax bir_immSyntax
in

fun word_of_string s =
    case Int.fromString s
     of SOME n => mk_word(Arbnum.fromInt n,Arbnum.fromInt 64)
      | NONE => mk_var(s, mk_int_word_type 64)
    
end

fun eq a b = (a = b)
end
