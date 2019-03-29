structure bir_relSynth : sig
              include bir_relSynth;
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
               let val (_,v::_) = strip_comb (hd args)
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

fun triangleWith f xs ys =
    let fun go [] _ = []
          | go _ [] = []
          | go (x::xs) (y::ys) =
            (map (fn p => f x p) (y::ys)) @ go xs ys
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

(* unpacks l1 = l2 where l1 and l2 are lists of conditional observations
   returns a HOL term of HOL type bir_exp_t that represents
   all possible ways of making l1 = l2
*)
fun mk_bir_cond_obs_eq l1 l2 =
    let val l1leaves = buildLeaves l1;
        val l2leaves = buildLeaves l2;
        fun processList (c,es1) (c',es2) =
            mk_bir_impl (band (c, c')) (mk_bir_list_eq es1 es2)
        val xs = triangleWith processList l1leaves l2leaves
    in bandl xs
    end

fun mapPair f (c, oCobs) = (f c, f oCobs);

fun mkRelConj xs =
    let val primed =
            map (fn (x,y) => (primed_term x, map (mapPair primed_term) y)) xs;
        fun processImpl (c, l1) (c', l2) =
            let val eqRel = mk_bir_cond_obs_eq l1 l2;
            in mk_bir_impl (band (c, c')) eqRel end;
        val xs2 = triangleWith processImpl xs primed
    in bandl xs2
    end

exception MkRel

(* input type : (bir_exp * (cobs list) option) list *)
(*              path condition * ((list of conditional observations) or bottom if error) *)
fun mkRel [] = ``T``
  | mkRel xs =
    let fun partitionOption [] = ([],[])
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
