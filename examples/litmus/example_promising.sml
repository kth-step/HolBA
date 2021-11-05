open litmusInterfaceLib;
open bir_promisingTheory;
open wordsTheory;
open computeLib;
open bslSyntax;
open herdLitmusRegLib;

fun term_EVAL tm = (rand o concl) (EVAL tm);

exception WrongType;

fun bir_type exp =
    let open bir_typing_expTheory optionSyntax;
        val ty = term_EVAL “type_of_bir_exp ^exp”;
    in
      if is_some ty
      then dest_some ty
      else raise WrongType
    end;

fun combin [] = []
  | combin (x::xs) = List.map (fn y => (x,y)) xs @ combin xs 

fun assume_cheat tm = prove(tm,cheat);
fun mk_assums var =
    map assume_cheat [
      (* alignment *)
      “^var && 3w = 0w”,
      (* range *)
      “^var ≤₊ 0xFFFFFFFFFFFFFFFBw”,
      “0w <₊ ^var”,
      “4w + ^var ≤₊ 0w”,
      “1000w ≤₊ ^var”,
      (* other *)
      “~(^var <₊ 0w)”,
      “0w + ^var = ^var”,
      “^var + 0w = ^var”
    ];

fun extend_compset () =
    let 
	val var = [“x:word64”,“y:word64”]
    in
	add_thms (flatten (map mk_assums var)) the_compset;
	add_thms (CONJUNCTS LITMUS_CONSTANT_THM) the_compset
    end

fun process_transform to_compset (clauses.RRules thms) = add_thms thms to_compset
  | process_transform to_compset (clauses.Conversion f) = add_conv (“T”,1,fn tm => fst (f tm)) to_compset;
fun process_item to_compset (_,ts) = List.app (process_transform to_compset) ts;
fun copy_items items to_compset = List.app (process_item to_compset) items;

val litmus_compset = bool_compset ();
val _ = copy_items (listItems the_compset) litmus_compset;
val _ = add_thms (flatten (map mk_assums [“x:word64”,“y:word64”])) litmus_compset;
val LITMUS_CONV = CBV_CONV litmus_compset;
fun term_LITMUS_CONV tm = term_EVAL ((rand o concl) (LITMUS_CONV tm));

fun typed_prog p = inst [alpha |-> Type`:string`] p;
fun fix_types ps = map typed_prog ps;

fun mk_st_from_env prog env = term_EVAL “bir_state_init ^prog with <| bst_environ := BEnv ^env |>”;
fun extend_env mem env = term_EVAL “case ^env of BEnv f => BEnv (\s . (if s = "MEM8" then bir_env_lookup "MEM8" ^mem else f s))”;
fun core_st_promised n st promises = term_EVAL “^st with <| bst_prom := [(^n)] |>”;

exception WrongType;
val term_EVAL = rhs o concl o EVAL

fun bir_type exp =
    let open bir_typing_expTheory optionSyntax;
        val ty = term_EVAL “type_of_bir_exp ^exp”;
    in
      if is_some ty
      then dest_some ty
      else raise WrongType
    end;

open bir_programSyntax listSyntax;

val get_TS = “\ts.
	      MAP (\t. case t of (Core cid p s) => 
				 case s.bst_environ of BEnv f => f) ts
	      ”;
val get_M = “\m.
	     FOLDR (\m t. t (|m.loc |-> SOME m.val|)) (K NONE) m
	     ”;
fun run_litmus_2thread filename =
   let 
       val _ = print filename
       val test = load_litmus filename;
       val (progs as [prog1,prog2]) = fix_types (#progs test);
       val (mem,envs) = #inits test; (* mem is assumed to be empty for now *)
       val [st1,st2] = map (uncurry mk_st_from_env) (zip progs envs);
       val cores = “[(Core 0 ^prog1 ^st1);
                     (Core 1 ^prog2 ^st2)]”;
       val _ = extend_compset ();
       val final_states = term_EVAL “eval_promising 16 (^cores, [])”;
       val TS = term_EVAL “MAP (^get_TS o FST) ^final_states”
       val M = term_EVAL “MAP (^get_M o SND) ^final_states”
       val final = #final test
       val finals = term_EVAL “ZIP (^M, ^TS)”
       val res = term_EVAL “^final ^finals”
   in res end;

(* 
fun find_tests () =
    let
	val proc = Unix.execute("/usr/bin/find", ["-iname", "*.litmus.json"])
	val inStream = Unix.textInstreamOf proc
    in
	String.tokens Char.isSpace (TextIO.inputAll inStream) before TextIO.closeIn inStream
    end

val filenames = find_tests ()
val basic = List.filter (String.isSubstring "size/BASIC") filenames
val res = map run_litmus_2thread basic;

val filename = "./tests/non-mixed-size/BASIC_2_THREAD/S+fence.rw.rws.litmus.json"
run_litmus_2thread filename
*)
