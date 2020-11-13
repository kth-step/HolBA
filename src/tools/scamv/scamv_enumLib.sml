structure scamv_enumLib :> scamv_enumLib =
struct

(* An enumeration is represented by a pair of a reference to the current value
and a 'step' function that returns the next value. This step function usually
contains in its closure the real state of the enumeration, whereas the current
value can be interpreted as a cache.

Invariants:
- Enumerations are infinite sequences, usually cyclic
- The step function always terminates
*)
datatype 'a enumeration = mk_enum of ('a option) ref * (unit -> 'a);

exception InvalidRange;
exception EmptyList;

fun enum f = mk_enum (ref NONE, f);

(* Steps the enumeration forward and returns new value.
 *)
fun next (mk_enum (curr,step)) =
    let val new_a = step ()
        val _ = curr := SOME new_a;
    in
      new_a
    end;

(* Returns the current value of the enumeration.
 *)
fun peek (e as mk_enum (curr,_)) =
    case !curr of
        NONE => next e
        | SOME c => c

(* Skips (n-1) elements from enumeration e and returns the nth value from the
current position *)
fun nth 0 e = peek e
  | nth n e = (next e; nth (n-1) e);

fun constant x = enum (fn _ => x);
fun unfold head tail seed =
    let val r = ref seed
    in
      enum (fn _ =>
               let val s = !r
               in
                 (r := tail s; head s)
               end
           )
    end;
fun iterate f x = unfold (fn y => y) f x;
fun prefix xs e =
    let val r = ref xs
    in
      enum (fn _ => let val ys = !r
                        val z = peek e
                    in
                      case ys of
                          [] => (next e; z)
                        | x::xs => (r := xs; x)
                    end)
    end;
fun map f e = enum (fn _ => f (next e));
fun zipWith f (mk_enum (c1,s1)) (mk_enum (c2,s2)) =
    enum (fn _ => f (s1 ()) (s2 ()));
fun cartesian e1 e2 = zipWith (fn a => fn b => (a,b)) e1 e2;
fun roundrobin_list [] = raise EmptyList
  | roundrobin_list xs =
    let val curr = ref xs
    in
      enum (fn _ => let val ys = !curr
                    in
                      case ys of
                          [] => (curr := tl xs; hd xs)
                        | z::zs => (curr := zs; z)
                    end)
    end;

fun range_from_to a b =
    if a <= b
    then iterate (fn v => if v >= b then a else v + 1) a
    else raise InvalidRange;
fun interleave e1 e2 =
    map (fn n => if n mod 2 = 0 then next e2 else next e1) (range_from_to 1 2);

fun take 0 e = []
  | take n e = next e :: take (n-1) e;
fun takeWhile f e =
    let val x = next e
    in
      if f x
      then x :: takeWhile f e
      else []
    end;
fun skipWhile f e =
    let val x = next e
    in
      if f x
      then skipWhile f e
      else x
    end;

(* unused for now *)
fun mk_round_robin n =
    let val counter = ref 0;
    in fn (ys : term list) =>
          let val c = !counter;
          in
            (if c = n
             then counter := 0
             else counter := c + 1) ;
            List.nth (ys, c)
          end
    end

fun mk_round_robin_every s n =
    let val counter = ref n;
        val step = ref 0;
    in fn (ys : term list) =>
          let val c = !counter;
          in
            (if c = n
             then (counter := 0; step := 0)
             else (if (!step = s)
                   then (counter := c + 1;
                         step := 0)
                   else (step := !step + 1));
             printv 1 ("Path counter: " ^ PolyML.makestring (!counter) ^ "\n");
             List.nth (ys, c))
          end
    end


end
