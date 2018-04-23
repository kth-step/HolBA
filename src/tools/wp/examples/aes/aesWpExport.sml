open aesSimpWpTheory;

open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;
open bir_wp_simpTheory;
open bir_expSyntax bir_immSyntax bir_envSyntax bir_imm_expSyntax bir_mem_expSyntax;

(* look at core/bir_expLib *)

val prop = (snd o dest_eq o concl) aes_wp_taut_thm;
val wp = List.nth((snd o strip_comb o snd o dest_comb) prop, 1);

fun writeFile filename content =
    let val fd = TextIO.openOut filename
        val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
        val _ = TextIO.closeOut fd
    in () end;

writeFile "/tmp/aaa.z3" "(declare-const a (_ BitVec 4)) (declare-const b (_ BitVec 4)) (assert (not (= (bvule a b) (bvsle a b)))) (check-sat) (get-model)";


writeFile "/tmp/aaa.z3" "(declare-const SP (_ BitVec 64)) (assert (not (and (= (bvand SP (_ bv3 64)) 0) true))) (check-sat) (get-model)";


fun bop_to_smt bop = if is_BIExp_And bop then
                         "and"
                     else if is_BIExp_Or bop then
                         "or"
                     else if is_BIExp_Xor bop then
                         "xor"
                     else
                         raise (ERR "bop_to_string" "don't know how to print BIR binop")
;

fun bbv_to_smt bop = if is_BIExp_And bop then
                         "bvand"
                     else if is_BIExp_Or bop then
                         "bvor"
                     else if is_BIExp_Xor bop then
                         "bvxor"
                     else if is_BIExp_Plus bop then
                         "bvadd"
                     else if is_BIExp_Minus bop then
                         "bvsub"
                     else if is_BIExp_Mult bop then
                         "bvmul"
                     else if is_BIExp_Div bop then
                         "bvdiv"
                     else if is_BIExp_SignedDiv bop then
                         "bvsdiv"
                     else if is_BIExp_Mod bop then
                         "bvmod"
                     else if is_BIExp_SignedMod bop then
                         "bvsmod"
                     else if is_BIExp_LeftShift bop then
                         "bvshl"
                     else if is_BIExp_RightShift bop then
                         "bvlshr"
                     else if is_BIExp_SignedRightShift bop then
                         "bvashr"
                     else
                         raise (ERR "bop_to_string" "don't know how to print BIR binop")
;

(* https://z3prover.github.io/api/html/ml/Z3.BitVector.html *)

fun bpredop_to_smt bpredop = if is_BIExp_Equal bpredop then
                                 "="
                             else if is_BIExp_NotEqual bpredop then
                                 "<>"
                             else if is_BIExp_LessThan bpredop then
                                 "bvult"
                             else if is_BIExp_SignedLessThan bpredop then
                                 "bvslt"
                             else if is_BIExp_LessOrEqual bpredop then
                                 "bvule"
                             else if is_BIExp_SignedLessOrEqual bpredop then
                                 "bvsle"
                             else
                                 raise (ERR "bpredop_to_string" "don't know how to print BIR binpredop")
;

fun uop_to_smt uop = if is_BIExp_Not uop then
                         "not"
                     else
                         raise (ERR "uop_to_string" "don't know how to print BIR unaryop");

fun export_to_smt exp =
    if is_BExp_Const exp then
	if exp = ``BExp_Const (Imm1 1w)`` then ("true", ``:word1``)
	else if exp = ``BExp_Const (Imm1 0w)`` then ("false", ``:word1``)
	else 
	    let val (s,w) =(gen_dest_Imm o dest_BExp_Const) exp
	    in
		(String.concat[
		 "(_ bv", 
		 Arbnumcore.toString(wordsSyntax.dest_word_literal w), 
		 " ", Int.toString s, ")"], type_of w)
	    end
    else if is_BExp_Den exp then
        ((fst o dest_BVar_string o dest_BExp_Den) exp, ``:word64``)
    else if is_BExp_UnaryExp exp then
        let
            val (uop, exp) = (dest_BExp_UnaryExp) exp;
            val uopstr = uop_to_smt uop;
	    val e1 = (export_to_smt exp)
        in
	    (String.concat ["(", uopstr, " ", 
			    (fst e1), ")"],
	     snd e1)
        end
    else if is_BExp_BinExp exp then
        let
            val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
	    val e1 = (export_to_smt exp1)
	    val e2 = (export_to_smt exp2)
            val bpredopstr = if (snd e1) = ``:word1`` then bop_to_smt bop
			     else bbv_to_smt bop;
        in
	    (String.concat ["(", bpredopstr, " ", 
			    (fst e1), " ", 
			    (fst e2), ")"],
	     snd e1)
        end
    else if is_BExp_BinPred exp then
        let
            val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
	    val e1 = (export_to_smt exp1)
	    val e2 = (export_to_smt exp2)
            val bpredopstr = bpredop_to_smt bpredop;
        in
	    (String.concat ["(", bpredopstr, " ", 
			    (fst e1), " ", 
			    (fst e2), ")"],
	     ``:word1``)
        end
    else if is_BExp_Load exp then
        let
            val (expm, expad, endi, sz) = (dest_BExp_Load) exp
	    val em = (export_to_smt expm)
	    val ead = (export_to_smt expad)
            val szn = (size_of_bir_immtype_t) sz
        in
	    if is_BEnd_LittleEndian endi then
		if szn = 64 then
		    let val selects = List.map (fn n => String.concat ["(select ", fst em, " (bvadd ", fst ead, " (_ bv", n," 64)))"]) (List.tabulate (8, Int.toString))
		    in
			(List.foldl (fn (a,b) => String.concat ["(concat ", a, b, " )"])
				   (hd selects) (tl selects),
			 ``:word64``)	 
		    end
		else
		    raise (ERR "castt_to_string" (term_to_string exp))
	    else
		raise (ERR "castt_to_string" (term_to_string exp))
        end
    else
	raise (ERR "castt_to_string" (term_to_string exp))
;


fun bir_exp_vars_in_exp exp =
    if is_BExp_Const exp then
        []
    else if is_BExp_Den exp then
        [(dest_BVar_string o dest_BExp_Den) exp]
    else if is_BExp_Cast exp then
        let
            val (castt, exp, sz) = (dest_BExp_Cast) exp;
        in
            bir_exp_vars_in_exp exp
        end
    else if is_BExp_UnaryExp exp then
        let
            val (uop, exp) = (dest_BExp_UnaryExp) exp;
        in
            bir_exp_vars_in_exp exp
        end
    else if is_BExp_BinExp exp then
        let
            val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
        in
            (bir_exp_vars_in_exp exp1) @ (bir_exp_vars_in_exp exp2)
        end
    else if is_BExp_BinPred exp then
        let
            val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
        in
            (bir_exp_vars_in_exp exp1) @ (bir_exp_vars_in_exp exp2)
        end
    else if is_BExp_IfThenElse exp then
        let
            val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
            (bir_exp_vars_in_exp expc) @ (bir_exp_vars_in_exp expt) @ (bir_exp_vars_in_exp expf)
        end
    else if is_BExp_Load exp then
        let
            val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
        in
            (bir_exp_vars_in_exp expm) @ (bir_exp_vars_in_exp expad)
        end
    else if is_BExp_Store exp then
        let
            val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
        in
            (bir_exp_vars_in_exp expm) @ (bir_exp_vars_in_exp expad) @ (bir_exp_vars_in_exp expv)
        end
    else
        raise (ERR "bir_exp_vars_in_exp" "don't know BIR expression")
;
fun bir_exp_dist_vars_in_exp exp =
    let
	val vars = bir_exp_vars_in_exp exp;
    in
	List.foldr (fn (var, vl) => if List.exists (fn x => x = var) vl then vl else var::vl) [] vars
    end;

fun var_to_smt (v, t) =
    if t = ``BType_Mem Bit64 Bit8`` then
	String.concat ["(declare-const ", v, "(Array (_ BitVec 64) (_ BitVec 8))) \n"]
    else
	String.concat ["(declare-const ", v, "(_ BitVec 64)) \n"];

val thm1 = SIMP_CONV std_ss [bir_wp_simpTheory.bir_exp_and_def,
			     bir_wp_simpTheory.bir_exp_imp_def,
			     bir_wp_simpTheory.bir_exp_or_def,
			     bir_wp_simpTheory.bir_exp_not_def] wp;
val wp1 = (snd o dest_eq o concl) thm1;



val pre = " (and (and (= (bvand SP_EL0 (_ bv7 64)) (_ bv0 64)) (bvugt SP_EL0 (_ bv33554432 64))) (bvult SP_EL0 (_ bv43554432 64)))";
(* val pre = " (= SP_EL0 (_ bv16777216 64) )"; *)
(* val pre = " (= (bvand SP_EL0 (_ bv3 64)) (_ bv0 64))"; *)
val pre = (String.concat [
	  "(and (= (bvand R0_wp_0  (_ bv3 64)) (_ bv0 64)) ",
	  pre,
	  ")"]);
    
writeFile "/tmp/aaa.z3" (String.concat
 ((List.map var_to_smt (bir_exp_dist_vars_in_exp wp1)) @
[
  "(assert (not ",
  "(=>", pre,
  fst (export_to_smt wp1),
  ")", 
  "))\n",
  "(check-sat) (get-model)"]));




