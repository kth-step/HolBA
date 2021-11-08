structure herdLitmusValuesLib =
struct
    
local
    open HolKernel bossLib boolLib Parse;
    open computeLib;
    open numSyntax bir_immSyntax wordsSyntax wordsLib;
    
    fun mk_constant_aux_thm n =
      let
        val vars = List.tabulate(n, fn i => mk_var("x" ^ (Int.toString i), “:word64”));
        fun mk_distinct [] = []
          | mk_distinct (x::xs) = map (fn y => “(^x <> ^y) /\ (^y <> ^x)”) xs @ mk_distinct xs;
        fun mk_addr_constraint var = [
          (* alignment *)
          “^var && 3w = 0w”,
          (* range *)
          “(if ^var ≤₊ 0xFFFFFFFFFFFFFFFBw then (1w:word1)
          else 0w) &&
          ((if 0w <₊ ^var then 1w else 0w) ‖
            if 4w + ^var ≤₊ 0w then 1w else 0w) &&
          ((if ^var <₊ 0w then 1w else 0w) ‖
          if 1000w ≤₊ ^var then 1w else 0w) 
          = 1w”];
        val terms = mk_distinct vars @ List.concat (map mk_addr_constraint vars);
        val final_term = list_mk_exists (vars, list_mk_conj terms);
        fun mk_exists i = EXISTS_TAC (mk_wordii(1000+4*i, 64));
        val word_ss = bool_ss ++ WORD_ss
        val tactics = List.foldl (op>>)
                          (simp_tac word_ss [])
                          (List.tabulate(n, mk_exists));
      in
        TAC_PROOF (([],final_term), tactics)
      end;
    
    fun mk_constants_thm name l =
      new_specification(name, l, mk_constant_aux_thm (List.length l))

in
val LITMUS_CONSTANT_THM = mk_constants_thm "LitmusConstants" ["x", "y", "z"]

fun word_of_string s sz =
    case Int.fromString s
     of SOME n => mk_wordii(n, sz)
      | NONE => mk_const(s, mk_int_word_type sz)
end

end		     
