structure bir_utilLib =
struct

local
  open HolKernel Parse;
  open bslSyntax;
  open bir_exp_to_wordsLib stringSyntax wordsSyntax 
  
  (* error handling *)
  val libname  = "bir_utilLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname
  (* C like macros *)
  val endif__ = (fn id => id);
  fun ifdef__else__ x c c' e = (if x then c else c') |> e;
  fun ifdef__ x c e = case x of true => c |> e;
  fun force f = f ();

  val SPECTRE = false;
  val DISTINCT_MEM = false;
  exception NoObsInPath;

in

fun stateful_tabulate f =
    let val current = ref 0;
        fun next () =
            let val result = f (!current);
            in (current := !current + 1;
                result)
            end
    in
      next
    end;

fun mapPair f (c, oCobs) = (f c, f oCobs);

fun nub_with eq [] = []
	| nub_with eq (x::xs) = x::(nub_with eq (List.filter (fn y => not (eq (y, x))) xs))

fun nub xs = nub_with (op=);

fun to_sml_Arbnums model =
    let open bir_embexp_driverLib wordsSyntax;
    in
    List.foldl (fn ((name, tm), mst) => 
                   if finite_mapSyntax.is_fupdate tm
	                 then
	                   let val bitvec = (can o find_term) (fn x => identical ``(BitVec: 64 word)`` x )
		                     val vlsW = (snd o finite_mapSyntax.strip_fupdate) tm
		                     val vlsN = map (fn p =>
				                                    let
				                                      val (ad, vl) = pairSyntax.dest_pair p
				                                    in
				                                      (* Sometime Z3 returns a function like K(BitVec(64), 0) instead of explicitly assigning values to memory addresses. *)
				                                      (* To mark such cases I used an out of range address 0xFFFFFFFF. This is also the magic number which showes up in bir_conc_execLib. *)

				                                      if bitvec ad
				                                      then (Arbnum.fromInt 4294967295, dest_word_literal vl)
				                                      else (dest_word_literal ad, dest_word_literal vl)
				                                    end) vlsW
	                   in
		                   machstate_replace_mem (8, Redblackmap.fromList Arbnum.compare vlsN) mst
	                   end
	                 else
	                   machstate_add_reg (name, dest_word_literal tm) mst) machstate_empty model
    end;

fun remove_prime str =
    if String.isSuffix "_" str then
      (String.extract(str, 0, SOME((String.size str) - 1)))
    else
      raise ERR "remove_prime" "there was no prime where there should be one";

fun isPrimedRun s = String.isSuffix "_" s;

fun bir_free_vars exp =
    let
      open stringSyntax;
      fun var_to_str v =
          let val (name,_) = dest_var v
          in
            fromMLstring name
          end
	    val fvs =
	        if is_comb exp then
		        let val (con,args) = strip_comb exp
		        in
		          if identical con ``BExp_MemConst``
		          then [var_to_str (List.nth(args, 2))]
		          else if identical con ``BExp_Den``
		          then
		            let val v = case strip_comb (hd args) of
				                        (_,v::_) => v
				                      | _ => raise ERR "bir_free_vars" "not expected"
		            in
			            [v]
		            end
		          else
		            List.concat (map bir_free_vars args)
		        end
	        else []
    in
	    nub_with (fn (x,y) => identical x y) fvs
    end;

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x);
fun dest_mem_load size tm =
    if size = 7 
    then tm |> (finite_mapSyntax.dest_fapply  o  (n_times  7 (#2 o dest_word_concat))) 
    else tm |> (#1 o dest_word_lsr o #1 o dest_w2w)
	    |> (finite_mapSyntax.dest_fapply o (n_times size (#2 o dest_word_concat)));


fun member x ys = exists (fn y => y = x) ys;

fun intersection [] ys = []
  | intersection (x::xs) ys =
    if member x ys
    then x::intersection xs ys
    else intersection xs ys;

(*
This function not only converts the BIR relation into a words HOL term but
also adds constraints that force the variables from different runs to be
distinct.
 *)
fun make_word_relation relation =
    let
	open boolSyntax;

        fun primed_subst exp =
            List.map (fn v =>
                    let val vp = lift_string string_ty (fromHOLstring v ^ "'")
                    in ``BVar ^v`` |-> ``BVar ^vp`` end)
                (bir_free_vars exp)

        fun primed_vars exp = List.map (#residue) (primed_subst exp);
        val vars =
            sort (curry String.<=)
                 (List.map fromHOLstring
                           (nub_with (fn (x,y) => identical x y) (bir_free_vars relation)));
        val (primed,unprimed) = List.partition (String.isSuffix "'") vars;
        val primed_base = List.map (fn s => substring(s,0,size(s)-1)) primed;
        val paired_vars = intersection primed_base unprimed;

        fun add_prime s = s^"'";

        val pairs = zip paired_vars (List.map add_prime paired_vars);
	      val (mpair, rpair) = List.partition (fn el =>  (String.isSubstring (#1 el) "MEM")) pairs

        fun mk_distinct_reg (a,b) =
            let val va = mk_var (a,``:word64``);
                val vb = mk_var (b,``:word64``);
		val in_range = (fn x => ``(0x80100000w <= ^x /\ ^x < 0x8013FE80w)``);
            in
		ifdef__else__ SPECTRE
		    (``(^va <> ^vb) /\ (^(in_range(``^va``))) /\ (^(in_range(``^vb``))) /\ (^va && 0xffw = ^vb && 0xefw) ``)
		    (``(^va <> ^vb)``)
		endif__
            end;
	val rel2w = (bir2bool relation)

	fun mk_distinct_mem (a, b) rel = 
	    let 
		    open finite_mapSyntax;
        open List;
		val va = mk_var (a, ``:word64 |-> word8``)
		val vb = mk_var (b, ``:word64 |-> word8``)
		fun split_mem  tms m = filter (fn tm => (identical (#1 (dest_fapply(find_term is_fapply tm))) m)) tms
		fun extract_mem_load n rel = ((nub_with (fn (x,y) => identical x y) o find_terms (can (dest_mem_load n))) rel);
		val memop  = (extract_mem_load 7 rel)@(extract_mem_load 3 rel)@(extract_mem_load 1 rel)@(extract_mem_load 0 rel)
		val m1 = zip (split_mem  memop va) (split_mem memop vb)
		val res = if List.null m1 then T else list_mk_disj (map (fn (tm, tm') => ``^tm <> ^tm'`` ) m1)
	    in 
		res
	    end;

        val distinct = force (ifdef__else__ DISTINCT_MEM
	                      (fn () => if null pairs 
			          then raise NoObsInPath 
			          else if List.null mpair
			          then list_mk_disj (map mk_distinct_reg rpair)
		                  else mk_conj (list_mk_disj ((map mk_distinct_reg rpair)), (mk_distinct_mem (hd mpair) rel2w)))

		  	      (fn () => if null pairs 
			          then raise NoObsInPath 
			          else list_mk_disj (map mk_distinct_reg rpair))
		             endif__)
    in
       ``^rel2w /\ ^distinct``
    end

end

end
