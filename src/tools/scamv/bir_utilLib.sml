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
    let open experimentsLib wordsSyntax;
    in
    List.foldl (fn ((name, tm), mst) => 
                   if finite_mapSyntax.is_fupdate tm
	           then let val bitvec = (can o find_term) (fn x => identical ``(BitVec: 64 word)`` x )
		            val vlsW = (snd o finite_mapSyntax.strip_fupdate) tm
		            val vlsN = map (fn p => let val (ad, vl) = pairSyntax.dest_pair p
				                    in
(* Sometime Z3 returns a function like K(BitVec(64), 0) instead of explicitly assigning values to memory *)
(* To mark such cases I used an out of range address 0xFFFFFFFF.*) 
(* This is also the magic number which showes up in bir_conc_execLib. *)					
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
            in
		(``(^va <> ^vb)``)
            end;
	val rel2w = (bir2bool relation)

        val distinct = if null pairs 
		       then raise NoObsInPath 
		       else list_mk_disj (map mk_distinct_reg rpair)

    in
       ``^rel2w /\ ^distinct``
    end

end

end
