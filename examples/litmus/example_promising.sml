open litmusInterfaceLib;
open bir_promisingTheory;
open wordsTheory;
open computeLib;

fun term_EVAL tm = (rand o concl) (EVAL tm);

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
      “~(^var <₊ 0w)”
    ];

fun extend_compset () =
    add_thms (flatten (map mk_assums [“x:word64”,“y:word64”])) the_compset;

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

fun mk_st_from_env prog env = term_EVAL “bir_state_init ^prog with <| bst_environ := ^env |>”;
fun extend_env mem env = term_EVAL “case ^env of BEnv f => BEnv (\s . (if s = "MEM8" then bir_env_lookup "MEM8" ^mem else f s))”;
fun core_st_promised n st promises = term_EVAL “^st with <| bst_prom := [(^n)] |>”;

(* val filename = "tests/non-mixed-size/BASIC_2_THREAD/R.litmus.json" *)
fun run_litmus_2thread filename =
   let val test = load_litmus filename;
       val (progs as [prog1,prog2]) = fix_types (#progs test);
       val (mem,envs) = #inits test; (* mem is assumed to be empty for now *)
       val envs_with_mem = map (extend_env mem) envs
       val [st1,st2] = map (uncurry mk_st_from_env) (zip progs envs_with_mem);
       val cores = “[(core 0 ^prog1 ^st1);
                     (core 1 ^prog2 ^st2)]”;
       (* val _ = extend_compset (); *)
       val promised_mem = term_EVAL “core_promises 7 (core 0 ^prog1 ^st1)”;
       val core1_st_promised = core_st_promised “1:num” st1 promised_mem;
       val core2_st_promised = core_st_promised “2:num” st1 promised_mem;
       val cores_promised = “[(core 0 ^prog1 ^core1_st_promised);
                              (core 1 ^prog2 ^core2_st_promised)]”;
       (*val final_states = term_EVAL “eval_parsteps 8 ^cores_promised ^promised_mem”; *)
       (*val _ = restore_compset (); *)
   in promised_mem end;

fun test () = run_litmus_2thread "tests/non-mixed-size/BASIC_2_THREAD/R.litmus.json";
