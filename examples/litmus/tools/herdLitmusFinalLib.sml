signature herdLitmusFinalLib =
sig
    include Abbrev
    (* Argument: Final/Constraint section
       Returns: Predicate on bir_environments *)
    val parse_final : string -> term
end

structure herdLitmusFinalLib : herdLitmusFinalLib =
struct
open HolKernel Parse boolLib bossLib;

open stringSyntax numSyntax wordsSyntax listSyntax;

open bir_immSyntax bir_envSyntax bir_valuesSyntax;

open UtilLib herdLitmusValuesLib;

(* The tokenizer and parser is based on the functional parser
   from 'ML for the Working Programmer, Chapter 9'. *)

(* TOKENIZER *)
datatype token = SYM of string | ID of string | NUM of int
val alphas = ["forall", "exists", "not"]
and symbols = ["/\\", "\\/", "(", ")", ":", "="]

(* Make an alphanumeric token *)
fun alphaTok a =
    if member (a, alphas)
    then SYM a
    else ID a

(* Make numeric token *)
val numTok = NUM o valOf o Int.fromString

(* Make symbolic token *)
fun symbolic (sy, ss) =
    case Substring.getc ss
     of NONE => (SYM sy, ss)
      | SOME(c, ss1) =>
	if member (sy, symbols) orelse not (Char.isPunct c)
	then (SYM sy, ss)
	else symbolic (sy ^ String.str c, ss1)

(* Scan substring and making token list *)
fun scanning (toks, ss) =
    case Substring.getc ss
     of NONE => rev toks (* Done. *)
      | SOME (c,ss1) => 
	if Char.isDigit c
	then (* number *)
	    let val (num, ss2) = Substring.splitl Char.isDigit ss
		val tok = numTok (Substring.string num)
	    in scanning (tok::toks, ss2)
	    end
	else if Char.isAlphaNum c
	then (* identifier or keyword *)
	    let val (id, ss2) = Substring.splitl Char.isAlphaNum ss
		val tok = alphaTok (Substring.string id)
	    in scanning (tok::toks, ss2)
	    end
	else if Char.isPunct c
	then (* special symbol *)
	    let val (tok, ss2) = symbolic (String.str c, ss1)
	    in scanning (tok::toks, ss2)
	    end
	else (* non-printable characters *)
	    scanning (toks, Substring.dropl (not o Char.isGraph) ss)

fun scan a = scanning([], Substring.full a)

(* PARSER *)
exception SyntaxErr of string
infixr 6 $--
infixr 5 --
infix 3 >>
infix 0 ||

(* Identifier *)
fun id (ID x::xs) = (x, xs)
  | id _ = raise SyntaxErr("Expected id")
(* Number *)
fun num (NUM x::xs) = (x, xs)
  | num _ = raise SyntaxErr("Expected num")
(* Symbol *)
fun sym a (SYM x::xs) =
    if a = x then (x, xs) else raise SyntaxErr ("Expected "^a)
  | sym a _ = raise SyntaxErr ("Expected "^a)
(* Concatenation *)
fun (ph1 -- ph2) xs =
    let val (x, xs') = ph1 xs
	val (y, xs'') = ph2 xs'
    in ((x,y), xs'') end
(* Alternative *)
fun (ph1 || ph2) xs = ph1 xs
		      handle SyntaxErr _ => ph2 xs
(* Application *)
fun (ph >> f) xs =
    let val (x, xs') = ph xs
    in (f x, xs') end
(* Must satisfy *)
fun !!ph xs = ph xs
	      handle SyntaxErr msg => raise Fail ("Syntax error: " ^msg)
(* Symbol followed by some expression *)
fun (a $-- ph) xs = ((sym a -- !!ph) >> snd) xs

fun empty a xs = (a, xs)

(* Scan the token stream ‘a’ with grammar ‘ph’ *)
fun reader ph a =
    case ph (scan a)
     of (x, []) => x
      | (_, l) => raise SyntaxErr "Extra characters in phrase"

(* Make terms *)
val mk_AND = mk_conj
val mk_OR = mk_disj
fun mk_FORALL x = 
	“EVERY  (\ (M:bir_val_t -> bir_val_t option, 
		    TS:(string -> bir_val_t option) list). ^x)”
fun mk_EXISTS x = 
	“EXISTS (\ (M:bir_val_t -> bir_val_t option, 
	            TS:(string -> bir_val_t option) list). ^x)”
fun mk_MEM (a, v) =
    let
	(* vars are word type by default, memory has num type *)
	fun f v n = mk_BVal_Imm $ gen_mk_Imm $ word_of_string v n
	val ha = f a 64
	val hv = f v 32
    in
	“M ^ha = SOME ^hv”
    end
fun mk_REG (t,(r,v)) =
    let val ht = term_of_int t
	val hr = fromMLstring r
	val hv = mk_Imm64 (word_of_string v 64)
    in
	“(EL ^ht TS) ^hr = SOME (BVal_Imm ^hv)”
    end
(* FORALL || EXISTS *)
fun quant xs = ("forall" $-- expr >> mk_FORALL
			 || "exists" $-- expr >> mk_EXISTS) xs
(* OR *)
and expr xs = (term -- ("\\/" $-- expr || empty “F”) >> mk_OR) xs
(* AND *)
and term xs = (factor -- ("/\\" $-- term || empty “T”) >> mk_AND) xs
(* NOT || () *)
and factor xs = ("(" $-- expr -- (sym ")") >> fst
		     || "not" $-- expr >> mk_neg
		     || atom) xs
(* MEM || REG *)
and atom xs = ((id -- "=" $-- var >> mk_MEM)
		   || num -- ":" $-- id -- "=" $-- var >> mk_REG) xs
(* Variable (will become word type) *)
and var xs = (id || num >> Int.toString) xs

(* Parse the final expression *)
fun parse_final final_sec =
    let val t = reader quant final_sec
    in (rhs o concl o EVAL) t end
end

(*
val x = "exists (not (x=1 /\\ (2:x7=0 /\\ (2:x8=0 /\\ (1:x5=0 /\\ (1:x8=0 /\\ (2:x9=1 /\\ (1:x7=0 \\/ 1:x7=1 \\/ 1:x7=2) \\/ 2:x9=2 /\\ (1:x7=2 \\/ 1:x7=1 \\/ 1:x7=0)) \\/ 1:x8=1 /\\ (2:x9=1 /\\ (1:x7=2 \\/ 1:x7=1 \\/ 1:x7=0) \\/ 2:x9=2 /\\ (1:x7=0 \\/ 1:x7=1 \\/ 1:x7=2))) \\/ 1:x5=2 /\\ (1:x7=1 /\\ (1:x8=0 /\\ (2:x9=2 \\/ 2:x9=1) \\/ 1:x8=1 /\\ (2:x9=1 \\/ 2:x9=2)) \\/ 1:x7=2 /\\ (1:x8=0 /\\ (2:x9=1 \\/ 2:x9=2) \\/ 1:x8=1 /\\ (2:x9=2 \\/ 2:x9=1))) \\/ 1:x5=1 /\\ 1:x7=1 /\\ (1:x8=0 /\\ (2:x9=1 \\/ 2:x9=2) \\/ 1:x8=1 /\\ (2:x9=2 \\/ 2:x9=1))) \\/ 2:x8=1 /\\ (1:x5=0 /\\ (1:x7=0 /\\ (1:x8=0 /\\ (2:x9=1 \\/ 2:x9=0) \\/ 1:x8=1 /\\ (2:x9=0 \\/ 2:x9=1)) \\/ 1:x7=1 /\\ (1:x8=0 /\\ (2:x9=0 \\/ 2:x9=1) \\/ 1:x8=1 /\\ (2:x9=1 \\/ 2:x9=0))) \\/ 1:x5=1 /\\ 1:x7=1 /\\ (1:x8=0 /\\ (2:x9=0 \\/ 2:x9=1) \\/ 1:x8=1 /\\ (2:x9=1 \\/ 2:x9=0)))) \\/ 2:x7=1 /\\ 2:x8=1 /\\ 2:x9=1 /\\ (1:x5=0 /\\ (1:x7=0 /\\ (1:x8=1 \\/ 1:x8=0) \\/ 1:x7=1 /\\ (1:x8=0 \\/ 1:x8=1)) \\/ 1:x5=1 /\\ 1:x7=1 /\\ (1:x8=0 \\/ 1:x8=1))) \\/ 2:x7=1 /\\ 2:x8=0 /\\ 2:x9=2 /\\ x=2 /\\ (1:x5=0 /\\ (1:x8=0 /\\ (1:x7=2 \\/ 1:x7=1 \\/ 1:x7=0) \\/ 1:x8=1 /\\ (1:x7=0 \\/ 1:x7=1 \\/ 1:x7=2)) \\/ 1:x5=1 /\\ (1:x7=1 /\\ (1:x8=0 \\/ 1:x8=1) \\/ 1:x7=2 /\\ (1:x8=1 \\/ 1:x8=0)) \\/ 1:x5=2 /\\ 1:x7=2 /\\ (1:x8=1 \\/ 1:x8=0))))"

val t = parse_final "exists (1:x1=3)"
*)
