open HolKernel Parse boolLib bossLib
open wordsLib wordsSyntax
open cv_transLib cv_primTheory cv_stdTheory
open cv_computeLib cv_stdTheory
open Random

open cv_wordTheory;

structure cv_wordLib :> cv_wordLib =
struct

fun power (x : int) (n : int) : int =
    if n = 0 then 1
    else 
        if (n mod 2) = 0 then 
            let val r = power x (n div 2) in r * r end
        else
            let val r = power x (n div 2) in r * r * x end

fun getNewTerm (th : thm) : term = rhs (concl th)

fun getCVWord (t : term) : term = getNewTerm (EVAL ``from_word ^t``)

fun randomWord64 (gen:generator) :term =
    mk_wordii (range (0,power 2 10) gen,64)

(** TODO : Maybe output a correction theorem when building *)
fun word64_to_cv (t:term) : term =
    if is_word_literal t then 
        getCVWord t
    else if is_word_and t then
        let val (t1,t2) = dest_word_and t
        in ``cv_word_and ^(word64_to_cv t1) ^(word64_to_cv t2)`` end
    else if is_word_add t then
        let val (t1,t2) = dest_word_add t
        in ``cv_word64_add ^(word64_to_cv t1) ^(word64_to_cv t2)`` end
    else 
        failwith "Not a word."

(* TODO : Output a theorem instead *)
(** This function eval a term using a DFS to convert it and then using * `cv_compute`*)
fun cv_eval_word (t:term) = 
    let 
        val thm_list = [cv_word_and_def, cv_word_and_loop_def, cv_word64_add_def]
        val translated = word64_to_cv t
        val cvIntermediateValue = getNewTerm (cv_compute thm_list translated)
        val cvValue = getNewTerm (EVAL ``(to_word ^cvIntermediateValue) :word64``)
    in 
        cvValue
    end


fun addOperationLinear (term_op: term) (gen:generator) (t : term) (n:int) = 
    if n = 0 then t
    else 
        let val randomWord = randomWord64 gen
        in
            addOperationLinear term_op gen ``^term_op ^randomWord ^t`` (n-1)
        end

fun addOperationSequentially (term_op : term) (gen:generator) (l : term list )(list_size : int) =
    let fun aux (n:int) (acc:term list) = 
        if n = 0 then acc
        else
            let val w1 = randomWord64 gen
                val w2 = randomWord64 gen
            in 
                aux (n - 1) (``^term_op ^w1 ^w2``::acc)
            end
    in
        aux list_size l
    end


(** Computes the time for `EVAL`ing the term and `cv_eval`ing it and `cv_eval_word`
 ** Returns a tuple with `EVAL` time first, then `cv_eval` time  then `cv eval_word` *)
fun time_term_evaluation (t:term) : (Time.time * Time.time * Time.time) =
    let val evalStart = Time.now ()
        val evalValue = getNewTerm (EVAL t)
        val evalEnd = Time.now ()

        val cvStart = Time.now ()
        val cvValue = getNewTerm (cv_eval t)
        val cvEnd = Time.now ()

        val _ = assert (fn x => (Term.compare (x, cvValue)) = EQUAL) evalValue 


        val customStart = Time.now ()
        val customValue  = (cv_eval_word t)
        val customEnd = Time.now ()

        val _ = assert (fn x => (Term.compare (x, cvValue)) = EQUAL) customValue 

    in (evalEnd - evalStart, cvEnd - cvStart, customEnd - customStart) end


fun time_sequence_evaluation (l :term list) : (Time.time * Time.time * Time.time) =
    let val evalStart = Time.now ()
        val evalValue = List.map (fn x => getNewTerm (EVAL x)) l
        val evalEnd = Time.now ()

        val cvStart = Time.now ()
        val cvValue = List.map (fn x => getNewTerm (cv_eval x)) l
        val cvEnd = Time.now ()

        (* val _ = assert (fn x => (Term.compare (x, cvValue)) = EQUAL) evalValue  *)


        val customStart = Time.now ()
        val customValue = List.map (fn x => cv_eval_word x) l
        val customEnd = Time.now ()

        (* val _ = assert (fn x => (Term.compare (x, cvValue)) = EQUAL) customValue *)

    in (evalEnd - evalStart, cvEnd - cvStart, customEnd - customStart) end


fun pp_time_tuple ((evalTime, cvTime, customTime) : Time.time * Time.time * Time.time) : unit = 
    let val _ = print ("EVAL : "^ Time.fmt 3 evalTime ^"\n")
        val _ = print ("cv_eval : "^ Time.fmt 3 cvTime ^"\n")
        val _ = print ("cv_eval_word : "^ Time.fmt 3 customTime ^"\n")
    in () end


fun pp_benchmark (times : (int * (Time.time * Time.time * Time.time)) list) : unit =
    let fun aux ((n, time_tuple) : int * (Time.time * Time.time * Time.time)) = 
        let 
            val _ = print "\n"
            val _ = print ("For n = "^ Int.toString n ^" words : \n")
            val _ = pp_time_tuple time_tuple
        in () end
    in 
        List.app aux (List.rev times)
    end

fun word_benchmark () = let
    val gen = newgen ()
    val next_op = fn x => x

    fun generateRandomOperation (term_op : term) (term_size:int) = 
        addOperationLinear term_op gen ``0w:word64`` term_size

    fun generateSequentialOperation (term_op : term) (list_size : int) =
        addOperationSequentially term_op gen [] list_size


    (* NB : term_size is the size of the input old_term *)
    fun measure_one (term_op : term) (iter_num:int) (term_size:int) (old_term:term)
                        (acc: (int * (Time.time * Time.time * Time.time)) list) =
        if iter_num = 0 then acc 
        else 
            let 
                (* We generate a new term twice the size (always (around) 2 ** n nodes) *)
                (* cf 2^(n+1) - 2^n = 2^n *)
                val _ = print ("Iters left : " ^Int.toString iter_num ^"\n")

                val n = term_size (* div 2 *)

                val _ = print ("Adding " ^ Int.toString n ^ " nested operations...\n")
                val new_term = addOperationLinear term_op gen old_term n

                val _ = print ("Timing Evaluations...\n")
                val times = time_term_evaluation new_term
            in
                measure_one (next_op term_op) (iter_num - 1) (term_size * 2) new_term ((term_size * 2,times)::acc)
            end

    fun measure_sequentially (term_op : term) (iter_num:int) (list_size)
                    (old_list : term list) (acc : (int * (Time.time * Time.time * Time.time)) list) = 
        if iter_num = 0 then acc 
        else 
            let 
                (* We generate a new term twice the size (always (around) 2 ** n nodes) *)
                (* cf 2^(n+1) - 2^n = 2^n *)
                val _ = print ("Iters left : " ^Int.toString iter_num ^"\n")

                val n = list_size (* div 2 *)

                val _ = print ("Adding " ^ Int.toString n ^ " operations sequentially...\n")
                val new_term_list = addOperationSequentially term_op gen old_list n 

                val _ = print ("Timing Sequential Evaluations...\n")
                val times = time_sequence_evaluation new_term_list
            in
                measure_sequentially (next_op term_op) (iter_num - 1) (list_size * 2)
                    new_term_list ((list_size * 2,times)::acc)
            end


    val startAndNestedSize = power 2 11
    val startAndSequentialSize = power 2 12
    val startSumNestedSize = power 2 10
    val startSumSequentialSize = power 2 12
    val iter_num = 1

    val and_op = ``$&& : word64 -> word64 -> word64``
    val sum_op = ``$+ : word64 -> word64 -> word64``

    val _ = print ("Generating the first terms\n")
    val startAndNestedTerm = generateRandomOperation and_op startAndNestedSize
    val startAndSequentialTerm = generateSequentialOperation and_op startAndSequentialSize
    val startSumNestedTerm = generateRandomOperation sum_op startSumNestedSize
    val startSumSequentialTerm = generateSequentialOperation sum_op startSumSequentialSize

    (* measure is op -> iter_num -> start_size -> start_term -> time list *)
    val time_and_nested = measure_one and_op iter_num startAndNestedSize startAndNestedTerm [(startAndNestedSize,time_term_evaluation startAndNestedTerm)]
    val time_and_sequential = measure_sequentially and_op iter_num startAndSequentialSize startAndSequentialTerm [(startAndSequentialSize,time_sequence_evaluation startAndSequentialTerm)]
    val time_sum_nested = measure_one sum_op iter_num startSumNestedSize startSumNestedTerm [(startSumNestedSize,time_term_evaluation startSumNestedTerm)]
    val time_sum_sequential = measure_sequentially sum_op iter_num startSumSequentialSize startSumSequentialTerm [(startSumSequentialSize,time_sequence_evaluation startSumSequentialTerm)]
in 
    print "************** Nested AND : **************\n";
    pp_benchmark time_and_nested ;
    print "************** Sequential AND : **************\n";
    pp_benchmark time_and_sequential ;
    print "************** Nested SUM : **************\n";
    pp_benchmark time_sum_nested ;
    print "************** Sequential SUM : **************\n";
    pp_benchmark time_sum_sequential
end (* fun *)

end (* struct *)
