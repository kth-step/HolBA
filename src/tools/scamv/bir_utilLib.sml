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

(*
val tm = ``(FUN_FMAP (K ((0x0w: 8 word))) (UNIV) : 64 word |-> 8 word) |+ (0x80100000w, 0x0w) |+ (0x80100001w, 0x0w) |+ (0x80100002w, 0x10w) |+ (0x80100003w, 0x0w) |+ (0x80100004w, 0x0w) |+ (0x80100005w, 0x0w) |+ (0x80100006w, 0x0w) |+ (0x80100007w, 0x0w)``;

val tm = ``(FUN_FMAP (K 0w) 𝕌(:word64) |+ (2148532224w,1w) |+ (2148532225w,0w) |+
(2148532226w,0w) |+ (2148532227w,0w) |+ (2148532228w,0w) |+
(2148532229w,0w) |+ (2148532230w,0w) |+ (2148532231w,0w)) : 64 word |-> 8 word``

val tm = ``(FUN_FMAP (K 0w) 𝕌(:word64) |+ (2148532224w,0w) |+ (2148532225w,0w) |+
(2148532226w,0w) |+ (2148532227w,0w) |+ (2148532228w,0w) |+
(2148532229w,0w) |+ (2148532230w,0w) |+ (2148532231w,0w)) : 64 word |-> 8 word``


val tm = fst (finite_mapSyntax.strip_fupdate tm)

is_FUN_FMAP tm

to_sml_Arbnums_mem8 tm
*)

local
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "finite_map";

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;

val (FUN_FMAP_tm, mk_FUN_FMAP, dest_FUN_FMAP, is_FUN_FMAP)  = syntax_fns2 "FUN_FMAP";

val expected_mem_type = ``:word64 |-> word8``;
val expected_K_tm = ``K : 8 word -> 64 word -> 8 word``;
val expected_U_tm = ``UNIV :word64->bool``;
in
  fun is_valid_to_sml_Arbnums_mem tm =
    finite_mapSyntax.is_fupdate tm orelse
    finite_mapSyntax.is_fempty tm orelse
    is_FUN_FMAP tm;

  fun to_sml_Arbnum_map tm =
    if finite_mapSyntax.is_fupdate tm then
      let
        val (tm_base, vlsW) = finite_mapSyntax.strip_fupdate tm;

        val (mem_dict, mem_default) = to_sml_Arbnum_map tm_base;
        val mem_updates = List.map (fn p =>
          let val (ad, vl) = pairSyntax.dest_pair p
          in (dest_word_literal ad, dest_word_literal vl)
          end) vlsW;
      in
        (Redblackmap.insertList (mem_dict, mem_updates), mem_default)
      end
    else if finite_mapSyntax.is_fempty tm then
      (Redblackmap.fromList Arbnum.compare [], Arbnum.zero)
    else if is_FUN_FMAP tm then
      let
        val (map_f, map_P) = dest_FUN_FMAP tm;
      in
        if identical map_P expected_U_tm andalso
           is_comb map_f andalso
           identical ((fst o dest_comb) map_f) expected_K_tm then
          let
            val (_, default_val) = dest_comb map_f;
          in
            (Redblackmap.fromList Arbnum.compare [], (dest_word_literal default_val))
          end
        else raise ERR "to_sml_Arbnum_map" "unexpected base map"
      end
    else
      raise ERR "to_sml_Arbnum_map" "unexpected fmap";

  fun to_sml_Arbnums_mem8 tm =
    if (type_of tm) = expected_mem_type then
      let
        val (mem_dict, default_val) = to_sml_Arbnum_map tm;
      in
        (8, mem_dict, default_val)
      end
    else
      raise ERR "to_sml_Arbnums_mem8" "unexpected memory type";
end;


fun to_sml_Arbnums model =
  let
    open experimentsLib wordsSyntax;
    fun fold_reg ((name, tm), mst) =
      machstate_add_reg (name, dest_word_literal tm) mst;
    fun fold_mem ((name, tm), mst) =
      if name <> "MEM" then raise ERR "to_sml_Arbnums" "memory should be called MEM" else
      let
        val (wordsz, mem_dict, default_val) = to_sml_Arbnums_mem8 tm;
      in
        machstate_replace_mem (wordsz, default_val, mem_dict) mst
      end;
  in
    List.foldl (fn ((name, tm), mst) =>
      if is_word_literal tm then
        fold_reg ((name, tm), mst)
      else if is_valid_to_sml_Arbnums_mem tm then
        fold_mem ((name, tm), mst)
      else
        raise ERR "to_sml_Arbnums" "unknown syntax"
      ) (machstate_empty Arbnum.zero) model
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
distinct if the require_distinctness parameter is true.
 *)
fun make_word_relation relation require_distinctness =
    let val rel2w = (bir2bool relation)
    in
      if require_distinctness
      then 
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
          
          val distinct = if null pairs 
		       then raise NoObsInPath 
		                     else list_mk_disj (map mk_distinct_reg rpair)
                                           
        in
``^rel2w /\ ^distinct``
        end
      else
        rel2w
    end;
end

end
