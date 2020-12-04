structure bir_rel_synthLib : bir_rel_synthLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

  (* error handling *)
  val libname  = "bir_rel_synthLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

local
open HolKernel Parse boolLib bossLib;
open stringSyntax;
open bir_programTheory;
open bir_utilLib;
open scamv_path_structLib;
open scamv_enumLib;

open bslSyntax;
open numSyntax;
in

type exp = term;
type cobs = term * term * term;

datatype enum_strategy = enum_extensional of int list
                       | enum_range of int * int;
type enum_env = (term * enum_strategy) list;

exception ListMkBir of string

fun primed_subst exp =
    let 
	val (mfvs, rfvs) = List.partition (fn el =>  Term.term_eq el ``"MEM"``)(bir_free_vars exp)
	val regs =
	    List.map (fn v =>
		    let val vp = lift_string string_ty (fromHOLstring v ^ "'")
		    in
			``BVar ^v`` |-> ``BVar ^vp`` end) rfvs
	val mem  = mk_var ("MEM" ,Type`:num |-> num`)
	val mem' = mk_var ("MEM'",Type`:num |-> num`)
    in
	if List.null mfvs
	then regs
	else [mem |-> mem']@regs
    end
	
fun primed_vars exp = List.map (#residue) (primed_subst exp);

fun primed_term exp =
    let val psub = primed_subst exp
    in
	subst psub exp
    end;

fun primed ys =
    map (fn (x,y) => (primed_term x,
                      Option.map (List.map (mapPair primed_term)) y)) ys;

fun primed_obs (cos : cobs_repr list) =
    let fun primed_cobs (cobs (id, oid, c, t)) =
            cobs (id, oid, primed_term c, primed_term t);
    in List.map primed_cobs cos
    end;
(*
val fresh_id =
    stateful_tabulate
        (fn n =>
            let fun onechar n =
                    (Char.chr (Char.ord (#"A") + (n mod 26)));
                fun c m =
                    if m < 26
                    then [onechar m]
                    else #"Z" :: (String.explode (Int.toString (n-25)));
            in
                String.implode (c n)
            end);

fun mk_fresh_gen () =
    stateful_tabulate (fn n => n);
*)
fun todo () = raise ERR "todo" "unimplemented";

fun split_obs_list n xs =
    let val (refs, base) = Portable.partition (fn (oid,_) => oid = n) xs;
    in
      (List.map snd refs, List.map snd base)
    end

fun triangleWith f xs ys =
(*  full product: List.concat (map (fn a => map (fn b => f a b) xs) ys);*)
    let fun go g [] _ = []
          | go g _ [] = []
          | go g (x::xs) (y::ys) =
            (List.map (fn p => g x p) (y::ys)) @
            go g xs ys
    in
        if length ys < length xs
        then (* take upper triangle *)
            go (fn x => fn y => f y x) ys xs
        else (* take lower triangle *)
            go f xs ys
    end;

fun buildLeavesIds [] = []
  | buildLeavesIds [oid] = [[(true, oid)], [(false,oid)]]
  | buildLeavesIds (oid::rest) =
    let val cobs' = buildLeavesIds rest;
        val oHolds    = List.map (fn spec => (true, oid) :: spec) cobs';
        val oNotHolds = List.map (fn spec => (false, oid) :: spec) cobs';
    in oHolds @ oNotHolds
    end

fun enumFromTo a b =
    let fun go n xs =
            if n = a then (a :: xs)
            else go (n-1) (n :: xs)
    in go b []
    end;

fun enumerate_domain (a_term, strategy) =
    case strategy of
        enum_range (a,b) =>
        enumerate_domain (a_term, enum_extensional (enumFromTo a b))
      | enum_extensional xs =>
        let val b_term = primed_term a_term;
            fun apply_pair v1 v2 =
                band (beq (a_term, bconst64 v1), beq (b_term, bconst64 v2))
            val prod = triangleWith apply_pair xs xs;
(*            val len = length prod;
            fun next_constraint n =
                SOME (List.nth (prod, n mod len))
                     handle _ => NONE; *)
        in (prod, roundrobin_list prod)
        end;

fun enumerate_domains [] = ([], constant btrue)
  | enumerate_domains env =
    let val (prods, enums) = unzip (List.map enumerate_domain env)
        (* fun nexts () =
             (*let fun go [] = [] *)
            (*       | go (NONE :: xs) = go xs *)
            (*       | go (SOME x :: xs) = x :: (go xs) *)
            (* in
            bandl (List.map next enums)
            handle _ => btrue
            end; *) *)
    in (prods, list_reduce bandl enums)
    end;

fun enumerate_relation path_dom static_obs_dom dynamic_obs_dom =
    let (* compute all interesting path pairs *)
        val paths = triangleWith (fn x => fn y => { a_run = x, b_run = y})
                                 path_dom path_dom;
        (* compute all interesting dynamic observation traces *)
        val obs_specs = buildLeavesIds dynamic_obs_dom;
        val dyn_spec = triangleWith (fn x => fn y => { a_run = x, b_run = y })
                                    obs_specs obs_specs;

        (* static obs always occur in their respective path *)
        val static_obs = List.map (fn id => (true,id)) static_obs_dom;

        (* add the static observations (always true) to the dyn ones *)
        val spec =
            if null dyn_spec (* no dynamic observations *)
            then [{a_run = static_obs, b_run = static_obs}]
            else
                List.map (fn spec => {a_run = static_obs @ (#a_run spec),
                                      b_run = static_obs @ (#b_run spec) })
                         dyn_spec;

        (* compute pairs of path * observation spec *)
        val specs =
            triangleWith (fn path_spec => fn obs_spec =>
                             { a_run = (#a_run path_spec,
                                        #a_run obs_spec),
                               b_run = (#b_run path_spec,
                                        #b_run obs_spec)})
                         paths spec;
        fun effective_length xs =
            length (List.filter (fn (b,x) => b) xs);

        (* discard specs with different number of observations *)
        val full_specs =
            List.filter (fn spec =>
                            effective_length (snd (#a_run spec)) =
                            effective_length (snd (#b_run spec)))
                        specs;

        (* iterator *)
(*        val len = length full_specs;
        fun next_test_case n =
            SOME (List.nth (full_specs, n mod len))
                     handle _ => NONE; *)
    in
        (full_specs, roundrobin_list full_specs)
    end;

fun trace_cobs_jit [] obs_list = ([],[])
  | trace_cobs_jit ((b,id) :: ids) obs_list  =
    let val (SOME (cobs (_, oid, cond, obs_term))) = lookup_obs id obs_list;
        val (conds, obs) = trace_cobs_jit ids obs_list;
    in
        if b
        then (cond :: conds, (int_of_term oid,obs_term) :: obs)
        else (bnot cond :: conds, obs)
    end handle Bind =>
               raise ERR "trace_cobs_jit"
                     ("invalid cobs id " ^ PolyML.makestring id);

val example_bir_path_struct =
    [path (1, blt (bden (bvarimm64 "A"), bconst64 0),
           [cobs (2, term_of_int 0, blt (bden (bvarimm64 "B"), bconst64 64),
                     bden(bvarimm64 "A"))])
           ,path (3, bnot (blt (bden (bvarimm64 "A"), bconst64 0)), [])];

val example_bir_initial_ps =
    [(blt (bden (bvarimm64 "A"), bconst64 0),
      SOME [(btrue, bden(bvarimm64 "A")),(blt (bden (bvarimm64 "B"), bconst64 64),bden(bvarimm64 "A"))])
    ,(bnot (blt (bden (bvarimm64 "A"), bconst64 0)), SOME [])];


val example_enum_env = [(bden (bvarimm64 "line"), enum_range (0,3))];

(* list equality as a conjunction of pairwise equality *)
fun mk_bir_list_eq l1 l2 =
    if length l1 <> length l2
    then bfalse
    else let fun list_eq [] [] = btrue
               | list_eq _ []  = bfalse
               | list_eq [] _  = bfalse
               | list_eq [x] [y] = beq (x, y)
               | list_eq (x::xs) (y::ys) =
                 band (beq (x, y), list_eq xs ys)
         in list_eq l1 l2
         end

fun op  mem (x, xs) =
    is_some (List.find (fn y => x = y) xs);

infix 5 mem;

fun rel_synth_jit
        (spec as {a_run = (a_path, a_obs_spec), b_run = (b_path, b_obs_spec)})
        obs_projection
        path_struct =
    let val SOME (path (_,a_cond,a_obs)) = lookup_path a_path path_struct;
        val SOME (path (_,b_cond_unprimed,b_obs_unprimed)) =
            lookup_path b_path path_struct;
        val (b_cond, b_obs) = (primed_term b_cond_unprimed,
                               primed_obs b_obs_unprimed);
        fun project obs_list obs_spec =
            List.filter
                (fn (_,id) => id mem (obs_domain_path obs_list))
                obs_spec;
        val (a_obs_cond, a_obs_terms) =
            trace_cobs_jit (project a_obs a_obs_spec) a_obs;
        val (b_obs_cond, b_obs_terms) =
            trace_cobs_jit (project b_obs b_obs_spec) b_obs;
        val (a_obs_terms_refined, a_obs_terms_base) =
            split_obs_list obs_projection a_obs_terms;
        val (b_obs_terms_refined, b_obs_terms_base) =
            split_obs_list obs_projection b_obs_terms;
        fun bandl' xs =
            case xs of
                [] => btrue
              | xs => bandl xs;
    in
        band (a_cond,
              band (b_cond,
                    bandl' [bandl' a_obs_cond, bandl' b_obs_cond,
                            band (mk_bir_list_eq a_obs_terms_base b_obs_terms_base
                                 ,bnot (if null a_obs_terms_refined andalso null b_obs_terms_refined then bfalse else mk_bir_list_eq a_obs_terms_refined b_obs_terms_refined))]))
    end
    handle Bind =>
           raise ERR "rel_synth_jit"
                 ("invalid id in arg " ^
                  PolyML.makestring spec);

val example_initial_ps = [(``A``, SOME [(``0``,``B``,``C``)]), (``D``,NONE)];

fun partition_domains (ps : path_struct) : int list * int list =
    let fun partition_obs_list xs =
            List.partition (fn (cobs (id,oid,cond,term)) => identical cond btrue) xs;
        fun go [] = ([],[])
          | go (path (_,_,xs)::ps) =
            let val (static, dyn) = partition_obs_list xs;
                val static' = List.map cobs_id_of static;
                val dyn' = List.map cobs_id_of dyn;
                val (rec_static, rec_dyn) = go ps
            in (static' @ rec_static, dyn' @ rec_dyn)
            end;
    in go ps
    end;

val max_guard_tries = 10000;
(* input: path_struct *)
fun rel_synth_init ps obs_projection (env : enum_env) =
    let
      val validity = btrue;
      val (static_obs_domain, dynamic_obs_domain) = partition_domains ps;
      val (full_specs, relation) =
          enumerate_relation (path_domain ps)
                             static_obs_domain dynamic_obs_domain;
      val (full_enums, constraints) =
          enumerate_domains env;
      fun next_test guard_path_spec =
          let open bir_expLib;
              fun try_spec () =
                  let fun go 0 = raise ERR "next_test" "guard_path_spec failed too many times in a row"
                        | go n =
                          let val p = next relation;
                          in if guard_path_spec p
                             then (print "\n"; p)
                             else (print "~"; go (n-1))
                          end;
                  in go max_guard_tries
                  end
                  handle Bind => raise ERR "next_test" "no next relation found";
              val spec = try_spec ();
              val constraint = next constraints;
              val _ = if not (identical constraint btrue)
                      then (print ("Selected constraint: ");
                            bir_exp_pretty_print constraint;
                            print "\n")
                      else ();
          in SOME (spec, band (band (rel_synth_jit spec obs_projection ps, constraint)
                              ,validity))
             handle e => (print (PolyML.makestring e ^ "\n");
                          print (PolyML.makestring spec ^ "\n");
                          NONE)
          end
          handle Bind => NONE;
    in
      (full_specs, validity, next_test)
    end

end

end
