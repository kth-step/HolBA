structure bir_rel_synthLib : sig
              include bir_rel_synthLib;
              val test1 : (exp * (cobs list) option) list;
          end = 
struct

open HolKernel Parse boolLib bossLib;
open stringSyntax;
open bir_programTheory;

open bslSyntax;

type exp = term;
type cobs = term * term;

fun bir_free_vars exp =
    if is_comb exp then
        let val (con,args) = strip_comb exp
        in if con = ``BExp_Den`` then
               let val v = case strip_comb (hd args) of
                                     (_,v::_) => v
                                   | _ => raise ERR "bir_free_vars" "not expected"
               in [v]
               end
           else
               List.concat (map bir_free_vars args)
        end
    else [];

val bir_true = bconst1 1;
val bir_false = bconst1 0;

exception ListMkBir of string

val mk_bir_eq = curry beq;
fun mk_bir_impl a b = bor (bnot a, b);

fun primed_subst exp =
    map (fn v =>
            let val vp = lift_string string_ty (fromHOLstring v ^ "'")
            in
            ``BVar ^v`` |-> ``BVar ^vp`` end)
        (bir_free_vars exp);

fun primed_vars exp = map (#residue) (primed_subst exp);

fun primed_term exp =
    let val psub = primed_subst exp
    in subst psub exp
    end;

fun cartesianWith f xs ys =
    let fun go [] _ = []
          | go _ [] = []
          | go (x::xs) (y::ys) =
            (map (fn p => f x p) (y::ys)) @
            (map (fn p => f y p) xs) @
            go xs ys
    in go xs ys
    end;

(* Symbolic execution of conditional observation lists *)

fun buildLeaves [] = []
  | buildLeaves [(c,e)] = [(c,[e]),(bnot c, [])]
  | buildLeaves ((c,e)::cobs) =
    let val cobs' = buildLeaves cobs;
        val cHolds    = map (fn (c',es) => (band (c, c'), e :: es)) cobs';
        val cNotHolds = map (fn (c',es) => (band (bnot c, c'), es)) cobs';
    in cHolds @ cNotHolds
    end


(* Relation synthesis functions *)

(* list equality as a conjunction of pairwise equality *)
fun mk_bir_list_eq l1 l2 =
    if length l1 <> length l2
    then bir_false
    else let fun list_eq [] [] = bir_true
               | list_eq _ []  = bir_false
               | list_eq [] _  = bir_false
               | list_eq [x] [y] = mk_bir_eq x y
               | list_eq (x::xs) (y::ys) =
                 band (mk_bir_eq x y, list_eq xs ys)
         in list_eq l1 l2
         end

fun nonridiculous_zip [] ys = []
  | nonridiculous_zip xs [] = []
  | nonridiculous_zip (x::xs) (y::ys) = (x,y) :: nonridiculous_zip xs ys

val internal_counter = ref 0;
(* unpacks xs = ys where xs and ys are lists of conditional observations
   returns a HOL term of HOL type bir_exp_t that represents
   all possible ways of making xs = ys
*)
fun mk_bir_cond_obs_eq xs ys =
    let fun go (l1,l2) = 
            let val l1leaves = buildLeaves l1;
                val l2leaves = buildLeaves l2;
                fun processList (c,es1) (c',es2) =
                    let val t = mk_bir_list_eq es1 es2
                    in (band (c, c'), t) end
                val xs = cartesianWith processList l1leaves l2leaves
                val _ = if length xs = 0
                        then print ("nullifier index found " ^ PolyML.makestring (!internal_counter))
                        else (internal_counter := (!internal_counter) + 1)
            in (* if length xs > 0 then bandl xs else bir_true *)
                xs
            end
        val (trivial, nontrivial) =
            partition (fn ((c,x),(c',y)) => (c = bir_true)
                                            andalso (c' = bir_true))
                      (nonridiculous_zip xs ys);
    in
        case trivial of
            [] => go (unzip nontrivial)
         |  _  =>
            let val _ = print(PolyML.makestring (length trivial));
                val trivial_eq =
                    List.map (fn ((_,x),(_,y)) => (btrue, mk_bir_eq x y))
                             trivial;
            in
                (*        go (xs,ys) *)
                trivial_eq @ go (unzip nontrivial)
(*                band (bandl trivial_eq, go (unzip nontrivial)) *)
            end
    end

fun mapPair f (c, oCobs) = (f c, f oCobs);

exception MkRel;

(* input type : (bir_exp * (cobs list) option) list *)
(*              path condition * ((list of conditional observations) or bottom if error) *)
fun mkRel_conds xs =
    let val _ = print("Relation synthesis: " ^ PolyML.makestring (length xs) ^ " paths ");
        fun primed ys =
            map (fn (x,y) => (primed_term x, Option.map (map (mapPair primed_term)) y)) ys;
        val (somes, nones) = partition (is_some o snd) xs;
        val _ = print("("
                      ^ (PolyML.makestring (length somes))
                      ^ " valid, "
                      ^ (PolyML.makestring (length nones))
                      ^ " invalid)\n");
        val (somes_primed, nones_primed) = (primed somes, primed nones);

        fun processImpl (c, l1) (c', l2) = 
            let val eqRel =
                    case (l1,l2) of
(*                       (NONE, NONE) => bir_true
                     | (NONE,_) => bir_false
                     | (_,NONE) => bir_false
                     | *) (SOME l1,SOME l2)  => 
                          mk_bir_cond_obs_eq l1 l2
                        | _ => raise ERR "mkRel_conds" "this should really not happen :)"
                val _ = print (".");
            in List.map
                   (fn (cond,rel) => (band (band (c, c'),cond), rel))
                   eqRel
            end;
        val xs2 = List.concat (cartesianWith processImpl somes somes_primed);

        fun smart_bandl xs = if null xs then btrue else bandl xs;
        val negCond = smart_bandl o List.map (bnot o fst);
        val unfoldCondObs =  smart_bandl o List.map (uncurry mk_bir_impl);
        val _ = print ("Done!\n");
    in (List.map fst xs2,
        band (unfoldCondObs xs2, band (negCond nones, negCond nones_primed)))
    end

fun mkRel xs = snd (mkRel_conds xs);


(*    let fun partitionOption [] = ([],[])
          | partitionOption ((pathCond,NONE)::ps) =
            let val (v,e) = partitionOption ps
            in (v,pathCond::e) end
          | partitionOption ((pathCond,SOME cObs)::ps) =
            let val (v,e) = partitionOption ps
            in ((pathCond,cObs)::v,e) end;
        val (valid,nones) = partitionOption xs;
        val errors = map (fn x => mk_bir_impl x bir_false) nones;
    in case (valid,errors) of
           ([],_) => borl errors
         | (_,[]) => mkRelConj valid
         | _ =>
           band (mkRelConj valid, borl errors)
    end;
*)
fun bool_var s = ``BExp_Den (BVar ^(lift_string string_ty s) (BType_Imm Bit1))``;
val varA = bool_var "a"
val varB = bool_var "b"
val varC = bool_var "c"

val cObsList1 = [(bir_true, varA), (bir_true, varB)];
val cObsList1' = map (mapPair primed_term) cObsList1;

val test1 : (term * ((term * term) list) option) list = [
    (mk_bir_eq varA varB, SOME [(bir_true, varC), (bir_true, varB)]
    ) (*,
    (``BExp_UnaryExp BIExp_Not ^(mk_bir_eq varA varA)``, NONE) *)
        ];

end
