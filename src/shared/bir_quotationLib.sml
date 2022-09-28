(*
BIR quotation library for HolBA
===============================

Based on mlibTerm in HOL4's metis implementation by Joe Hurd.

The reference expr_infixes contains infix operator precedence and associativity.
Should be easy to change to suit your needs.

Known issues and limitations:

- Antiquoting is not supported. Unfortunately this hinders usability in proofs.
  It could be implemented but it's a lot more work.

- When a jump target is a string, it is interpreted as a static string label.
  This means the following program may not parse as one expects:

val not_indirect_jump = BIR‘
a:
  X1 = 0x8000004
  jmp X1
’

  The jump becomes a direct jump to a non-existing label X1. In order to express
  an indirect jump properly we need to force the parser to interpret the jump
  target as an expression, as follows:

val indirect_jump = BIR‘
a:
  X1 = 0x8000004
  jmp (X1+0)
’

- Error reporting is very limited.

This library is released under the standard BSD-3-Clause license.

Copyright 2022 Pablo Buiras

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors
may be used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)
structure bir_quotationLib :> bir_quotationLib =
struct

open HolKernel Parse boolLib;

open mlibParser mlibUseful;
open bslSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_envSyntax;
open bir_valuesSyntax;
open bir_exp_immSyntax;

infixr 8 ++
infixr 7 >>
infixr 6 ||

(* error handling *)
val libname = "bir_quotationLib"
val ERR = Feedback.mk_HOL_ERR libname
val wrap_exn = Feedback.wrap_exn libname

val quotation_default_size = ref 64;
val quotation_default_size_byte = ref 8;
val quotation_memory_prefixes = ref ["MEM", "_MEM"];

val expr_infixes : infixities ref = ref
  [{tok = " / ",   prec = 7,  left_assoc = true},
   {tok = " % ", prec = 7,  left_assoc = true},
   {tok = " * ",   prec = 7,  left_assoc = true},
   {tok = " + ",   prec = 6,  left_assoc = true},
   {tok = " - ",   prec = 6,  left_assoc = true},
   {tok = " & ",   prec = 6,  left_assoc = true},
   {tok = " ^ ",   prec = 6,  left_assoc = true},
   {tok = " | ",   prec = 6,  left_assoc = true},
   {tok = " << ",  prec = 5,  left_assoc = true},
   {tok = " >> ",   prec = 5,  left_assoc = true},
   {tok = " == ",  prec = 4,  left_assoc = true},
   {tok = " <> ",  prec = 4,  left_assoc = true},
   {tok = " <= ",  prec = 4,  left_assoc = true},
   {tok = " < ",   prec = 4,  left_assoc = true},
   {tok = " >= ",  prec = 4,  left_assoc = true},
   {tok = " > ",   prec = 4,  left_assoc = true},
   {tok = " : ",   prec = 8,  left_assoc = true}
   ];

val reserved = ["(", ")", ".", "~", "assert", "assume",
                "observe", "halt", "jmp", "cjmp",
                "if", "then", "else"];
val keywords = ["ld", "ld8", "ld16", "ld32", "ld64",
                "st", "st8", "st16", "st32", "st64",
                "chsign", "clz", "cls",
                "ucast",  "scast", "hcast", "lcast",
                "sdiv", "smod", "srsh", "slt", "sle", "memeq"];

local
  val initials = explode "_rxw";
in
  val var_string = ref (C mem initials o Char.toLower o hd o explode);
end;

val lexer =
    (fn ((_, (toks, _)), _) => toks) o
    (many (some space) ++
          (many
            ((((atleastone (some alphanum) ||
                           (some (fn c => symbol c andalso c <> #"~") ++
                            many (some symbol)) >>
                           op ::) >> implode
                                  || some (fn c => c = #"~" orelse punct c) >> str) ++
                                     many (some space)) >> fst)) ++
          finished);


val lex_str = lexer o mlibStream.from_list o explode;

fun filter_comment [] = []
  | filter_comment (";" :: ts) = []
  | filter_comment (tok :: ts) =  tok :: filter_comment ts

datatype fo_term =
         Var of string
         | Imm of string
         | Fn  of string * fo_term list;

fun is_memory_var s =
    List.exists (fn prefix => String.isPrefix prefix s)
                (!quotation_memory_prefixes);

fun dest_imm (Imm n) = n
  | dest_imm _ = raise Error "dest_imm: not an Imm"

val is_imm = can dest_imm;

fun dest_var (Var v) = v
  | dest_var _ = raise Error "dest_var: not a Var"

val is_var = can dest_var;

fun dest_fn (Fn f) = f
  | dest_fn _ = raise Error "dest_fn: not a Fn";

val is_fn = can dest_fn;

val fn_name = fst o dest_fn;

val fn_args = snd o dest_fn;

val fn_arity = length o fn_args;

fun fn_function tm = (fn_name tm, fn_arity tm);

fun dest_const (Fn (c, [])) = c
  | dest_const _ = raise Error "dest_const: not a const";

val is_const = can dest_const;

fun dest_binop f (Fn (x, [a, b])) =
    if x = f then (a, b) else raise Error "dest_binop: wrong binop"
  | dest_binop _ _ = raise Error "dest_binop: not a binop";

fun is_binop f = can (dest_binop f);

val vname_parser = some (fn tok => not (mem tok reserved)
                                   andalso not (digit (hd (explode tok)))
                                   andalso not (mem tok (optoks (!expr_infixes))));

val imm_parser =
    some (fn tok =>
             let val cs = explode tok;
                 fun hex_digit c =
                     digit c
                     orelse
                     String.isSubstring (implode [(Char.toLower c)]) "abcdef";
             in
               case cs of
                   #"0" :: #"x" ::rest =>
                   List.all hex_digit rest
                 | _ => List.all digit cs
             end
         );

fun literal_from_string str =
    if String.isPrefix "0x" str
    then Arbnumcore.toInt (Arbnumcore.fromHexString str)
    else valOf (Int.fromString str)

val imm_term_parser =
    let open wordsSyntax numSyntax;
        fun to_term str =
            mk_wordii (literal_from_string str,
                       64);
    in
      (imm_parser >> (fn str => “Imm64 ^(to_term str)”)
       handle Overflow =>
              raise (ERR "imm_term_parser" "integer overflow"))
    end;

fun term_parser ops =
    let
      val iparser = parse_infixes ops
      val itoks = optoks ops
      val avoid = itoks @ reserved
      fun fname tok = mem tok keywords andalso not (mem tok avoid)
      val fname_parser = some fname
          || (exact "(" ++ any ++ exact ")") >> (fst o snd)
      fun basic inp =
          ((exact "if" ++ tm_parser ++ exact "then" ++ tm_parser ++ exact "else" ++ tm_parser) >> (fn (_,(cond,(_,(left,(_,right))))) =>
               Fn ("__ite", [cond,left,right])) ||
            vname_parser >> Var ||
           imm_parser >> Imm ||
           fname_parser >> (fn f => Fn (f,[])) ||
           (exact "(" ++ tm_parser ++ exact ")") >> (fn (_,(t,_)) => t)
          ) inp
      and molecule inp =
          ((many (exact "~")
            ++ ((fname_parser ++ many basic) >> Fn || basic))
               >> (fn (l, t) => funpow (length l)
                    (fn x => Fn ("~", [x])) t)) inp
      and tm_parser inp =
          iparser (fn (f, a, b) => Fn (f, [a, b])) molecule inp
    in
      tm_parser
    end;

local
  fun ty_to_int ty_str =
      case ty_str of
          "Bit8" => 8
        | "Bit16" => 16
        | "Bit32" => 32
        | "Bit64" => 64
        | _ => raise (ERR "ty_to_int" "invalid bit type")
  fun lift n t =
      case t of
          Fn ("~", [a]) =>
          bnot (lift n a)
        | Fn ("clz", [a]) =>
          bclz (lift n a)
        | Fn ("cls", [a]) =>
          bcls (lift n a)
        | Fn ("chsign", [a]) =>
          bchsign (lift n a)
        | Fn ("+", [a,b]) =>
          bplus (lift n a, lift n b)
        | Fn ("-", [a,b]) =>
          bminus (lift n a, lift n b)
        | Fn ("*", [a,b]) =>
          bmult (lift n a, lift n b)
        | Fn ("/", [a,b]) =>
          bdiv (lift n a, lift n b)
        | Fn ("sdiv", [a,b]) =>
          bsdiv (lift n a, lift n b)
        | Fn ("%", [a,b]) =>
          bmod (lift n a, lift n b)
        | Fn ("smod", [a,b]) =>
          bsmod (lift n a, lift n b)
        | Fn ("srsh", [a,b]) =>
          bsrshift (lift n a, lift n b)
        | Fn ("<<", [a,b]) =>
          blshift (lift n a, lift n b)
        | Fn (">>", [a,b]) =>
          brshift (lift n a, lift n b)
        | Fn ("ld", [a,b]) =>
          bloadi_le (lift n a)
                    (lift (!quotation_default_size) b)
                    n
        | Fn ("ld8", [a,b]) =>
          bloadi_le (lift n a)
                    (lift (!quotation_default_size) b)
                    8
        | Fn ("ld16", [a,b]) =>
          bloadi_le (lift n a)
                    (lift (!quotation_default_size) b)
                    16
        | Fn ("ld32", [a,b]) =>
          bloadi_le (lift n a)
                    (lift (!quotation_default_size) b)
                    32
        | Fn ("ld64", [a,b]) =>
          bloadi_le (lift n a)
                    (lift (!quotation_default_size) b)
                    64
        | Fn ("st", [a,b,c]) =>
          bstore_le (lift n a)
                    (lift (!quotation_default_size) b)
                    (lift n c)
        | Fn ("st8", [a,b,c]) =>
          bstore_le (lift n a)
                    (lift (!quotation_default_size) b)
                    (lift 8 c)
        | Fn ("st16", [a,b,c]) =>
          bstore_le (lift n a)
                    (lift (!quotation_default_size) b)
                    (lift 16 c)
        | Fn ("st32", [a,b,c]) =>
          bstore_le (lift n a)
                    (lift (!quotation_default_size) b)
                    (lift 32 c)
        | Fn ("st64", [a,b,c]) =>
          bstore_le (lift n a)
                    (lift (!quotation_default_size) b)
                    (lift 64 c)
        | Fn ("==", [a,b]) =>
          beq (lift n a, lift n b)
        | Fn ("memeq", [a,b]) =>
          bmemeq (lift n a, lift n b)
        | Fn ("<>", [a,b]) =>
          bneq (lift n a, lift n b)
        | Fn ("<", [a,b]) =>
          blt (lift n a, lift n b)
        | Fn ("slt", [a,b]) =>
          bslt (lift n a, lift n b)
        | Fn (">", [a,b]) =>
          bgt (lift n a, lift n b)
        | Fn ("<=", [a,b]) =>
          ble (lift n a, lift n b)
        | Fn ("sle", [a,b]) =>
          bsle (lift n a, lift n b)
        | Fn (">=", [a,b]) =>
          bge (lift n a, lift n b)
        | Fn ("&", [a, b]) =>
          band (lift n a, lift n b)
        | Fn ("|", [a,b]) =>
          bor (lift n a, lift n b)
        | Fn ("^", [a,b]) =>
          bxor (lift n a, lift n b)
        | Fn ("ucast", [a, Var ty]) =>
          bucasti (ty_to_int ty) (lift n a)
        | Fn ("scast", [a, Var ty]) =>
          bscasti (ty_to_int ty) (lift n a)
        | Fn ("hcast", [a, Var ty]) =>
          bhighcasti (ty_to_int ty) (lift n a)
        | Fn ("lcast", [a, Var ty]) =>
          blowcasti (ty_to_int ty) (lift n a)
        | Fn ("__ite", [cond,left,right]) =>
          bite (lift n cond, lift n left, lift n right)
        | Fn (":", [a, Var ty]) =>
          lift (ty_to_int ty) a
        | Fn (fname, args) =>
          raise ERR "lift"
                ("parse error in function application: "
                     ^ fname ^ ", arguments: " ^ PolyML.makestring args)
        | Var s =>
          if is_memory_var s
          then
            bden (bvarmem ((!quotation_default_size)
                          ,(!quotation_default_size_byte)) s)
          else bden (bvarimm n s)
        | Imm s => bconstii n (literal_from_string s)
                   handle Overflow =>
                          raise (ERR "lift" "integer overflow")
in
val bir_expr_parser = term_parser (!expr_infixes) >> lift 64;
end;

fun string_to_term' ops =
    fst o ((term_parser ops ++ finished) >> fst) o mlibStream.from_list o lex_str;
fun string_to_term  s = string_to_term' (!expr_infixes) s;
val string_to_expr =
    fst o ((bir_expr_parser ++ finished) >> fst) o mlibStream.from_list o lex_str;

fun basic_stmt_parser obs_ty =
    let
      open bir_programSyntax numSyntax;
      val hd_func = inst [Lib.|->(Type‘:'a’,obs_ty)] “HD”;
      val obs_stmt_mono =
          inst [Lib.|->(Type‘:'a’,obs_ty)] “BStmt_Observe”;
      val parser =
          (exact "assert" ++ bir_expr_parser)
                >> (fn (_,exp) => bassert exp) ||
          (exact "assume" ++ bir_expr_parser)
                >> (fn (_,exp) => bassume exp) ||
          (exact "observe" ++ imm_parser
                 ++ bir_expr_parser ++ bir_expr_parser)
                >> (fn (_,(oid,(cnd,exp))) =>
                       “^obs_stmt_mono (^(term_of_int (valOf (Int.fromString oid)))) ^cnd [^exp] ^hd_func”) ||
          (vname_parser ++ exact "=" ++ bir_expr_parser)
          >> (fn (var,(_,exp)) =>
                 let val lvalue =
                         if String.isPrefix "MEM" var
                         then bvarmem (!quotation_default_size,!quotation_default_size_byte) var
                         else bvarimm (!quotation_default_size) var
                 in
                   bassign (lvalue,exp)
                 end
             )
    in
      parser >> inst [Lib.|->(Type‘:'a’,obs_ty)]
    end;

fun mklabel exp =
    if is_BExp_Den exp
    then
      let val (var,ty) = dest_BVar_string (dest_BExp_Den exp)
      in
        belabel_str var
      end
    else if is_BExp_Const exp
    then
      let open wordsSyntax;
        val (sz,c) = gen_dest_Imm (dest_BExp_Const exp)
      in
        belabel_addrii sz (uint_of_word c)
      end
    else
      belabel_expr exp

val end_stmt_parser =
    ((exact "jmp" ++ bir_expr_parser)
         >> (fn (_,exp) => bjmp (mklabel exp)) ||
    (exact "cjmp" ++ bir_expr_parser
           ++ bir_expr_parser ++ bir_expr_parser)
         >> (fn (_,(cnd,(left,right))) =>
                bcjmp (cnd, mklabel left,
                            mklabel right)) ||
     (exact "halt" ++ bir_expr_parser)
         >> (fn (_,exp) => bhalt exp))

val parse_expr =
    fst o ((bir_expr_parser ++ finished) >> fst);

fun lift_parse p (inp: 'a stream stream) =
    case inp of
        mlibStream.NIL => raise mlibParser.Noparse
      | mlibStream.CONS (s,ss) =>
        case p s of
            (b,mlibStream.NIL) => (b,ss ())
          | _ => raise mlibParser.Noparse;

fun bir_program_parser obs_ty =
    let
      open listSyntax;
      val label_parser =
          lift_parse (
            (((vname_parser >> blabel_str)
              || (imm_term_parser >> blabel_addrimm))
              ++ exact ":" ++ finished)
                >> (fn (t,_) => t)
            );
      val stmt_parser =
          lift_parse ((basic_stmt_parser obs_ty ++ finished) >> fst);
      val end_stmt_parser_finished =
          lift_parse ((end_stmt_parser ++ finished) >> fst);
      fun block_parser inp =
          ((label_parser
               ++ many stmt_parser
               ++ end_stmt_parser_finished)
               >> (fn (lbl,(stmts,end_stmt))
                      => bblock obs_ty (lbl, stmts, end_stmt)))
              inp
      fun prog_parser inp =
          (many block_parser >>
                (fn blocks =>
                    case blocks of
                        [] => “BirProgram []”
                      | _ => “BirProgram ^(mk_list (blocks,type_of (List.hd blocks)))”
                    ))inp
    in
      prog_parser
    end;

val line_tokenise = String.tokens (fn x => x = #"\n");
val default_obs_ty = (Type`:bir_val_t`);
val parse_program =
    fst o ((bir_program_parser default_obs_ty ++ finished) >> fst)
    o (mlibStream.partial_map
           (fn line =>
               let val tokens = filter_comment (lex_str line)
               in
                 if null tokens
                 then NONE
                 else SOME (mlibStream.from_list tokens)
               end)
      )
    o mlibStream.from_list o line_tokenise;

val loc_parser =
    (fn ((_,(_,(_,(line,(col,(_,_)))))),rest)
        => (line,col,rest)) o
    (exact "(" ++
           exact "*#" ++
           exact "loc" ++
           imm_parser ++
           imm_parser ++
           exact "*" ++
           exact ")");

val parse_loc =
    loc_parser o mlibStream.from_list o lex_str

fun BExp [QUOTE str] =
    let val (line,col,body) = parse_loc str;
    in
      parse_expr body
      handle e =>
             raise (wrap_exn
                        ("BExp (line "^line
                         ^", col "^col^")") e)
    end;

fun parse_loc_prog str =
    let val first_line::lines = line_tokenise  str;
        val (line,col,body) = parse_loc first_line;
    in
      (line,col,
       String.concatWith "\n"
       (String.concatWith " " (mlibStream.to_list body)
       :: lines))
    end;

fun BIR [QUOTE str] =
    let val (line,col,prog_body) = parse_loc_prog str;
    in
      parse_program prog_body
      handle e =>
             raise (wrap_exn
                        ("BIR (line "^line
                         ^", col "^col^")") e)
    end;

val pp_vname = pp_string;

fun pp_term' ops =
  let
    fun iprinter des = pp_infixes ops des
    val itoks = optoks ops
    fun specialf s = mem s itoks orelse !var_string s
    val pp_fname = pp_map (fn s=>if specialf s then "("^s^")" else s) pp_string
    fun idest (Fn (f, [a, b])) = SOME (f, a, b) | idest _ = NONE
    fun is_op t = case idest t of SOME (f, _, _) => mem f itoks | NONE => false
    fun negs (Fn ("~", [a])) = (curry op+ 1 ## I) (negs a) | negs tm = (0, tm)
    open PP
    fun basic (Var v) = pp_vname v
      | basic (Imm v) = pp_string v
      | basic (Fn ("__ite", [cond,left,right])) =
        block INCONSISTENT 0 [
          add_string "if", add_break (1,0),
          argument cond, add_break (1,0),
          add_string "then", add_break (1,0),
          argument left, add_break (1,0),
          add_string "else", add_break (1,0),
          argument right]
      | basic (Fn (f, a)) =
        block INCONSISTENT 0
              (pp_fname f ::
               List.concat (map (fn x => [add_break (1,0), argument x]) a))
    and argument (tm: fo_term) =
        if is_var tm orelse is_const tm orelse is_imm tm
        then basic tm else pp_btm tm
    and molecule (tm, r) =
      let
        val (n, x) = negs tm
      in
        block INCONSISTENT n [
          add_string (CharVector.tabulate(n, fn _ => #"~")),
          if is_op x then pp_btm x else basic x
        ]
      end
    and pp_btm tm = pp_bracket "(" ")" pp_tm (tm, false)
    and pp_tm tmr = iprinter idest molecule tmr
  in
    pp_map (C pair false) pp_tm
  end;

local
  open bir_expSyntax bir_immSyntax bir_valuesSyntax wordsSyntax;
  open bir_exp_immSyntax;
  fun ty_to_string imm_type =
      if is_Bit64 imm_type
      then "64"
      else if is_Bit32 imm_type
      then "32"
      else if is_Bit16 imm_type
      then "16"
      else if is_Bit8 imm_type
      then "8"
      else raise (ERR "immtype_to_string" "invalid imm type")
  fun immtype_to_string imm_type =
      if is_Bit64 imm_type
      then "Bit64"
      else if is_Bit32 imm_type
      then "Bit32"
      else if is_Bit16 imm_type
      then "Bit16"
      else if is_Bit8 imm_type
      then "Bit8"
      else raise (ERR "immtype_to_string" "invalid imm type")
  fun unop_to_string oper =
      if is_BIExp_Not oper then "~"
      else if is_BIExp_ChangeSign oper then "chsign"
      else if is_BIExp_CLZ oper then "clz"
      else if is_BIExp_CLS oper then "cls"
      else raise (ERR "unop_to_string" "invalid unary op")
  fun binop_to_string oper =
      if is_BIExp_Plus oper then "+"
      else if is_BIExp_Minus oper then "-"
      else if is_BIExp_Mult oper then "*"
      else if is_BIExp_Div oper then "/"
      else if is_BIExp_SignedDiv oper then "sdiv"
      else if is_BIExp_And oper then "&"
      else if is_BIExp_Or oper then "|"
      else if is_BIExp_Xor oper then "^"
      else if is_BIExp_Mod oper then "%"
      else if is_BIExp_SignedMod oper then "smod"
      else if is_BIExp_LeftShift oper then "<<"
      else if is_BIExp_RightShift oper then ">>"
      else if is_BIExp_SignedRightShift oper then "srsh"
      else if is_BIExp_Equal oper then "=="
      else if is_BIExp_NotEqual oper then "<>"
      else if is_BIExp_LessThan oper then "<"
      else if is_BIExp_LessOrEqual oper then "<="
      else if is_BIExp_SignedLessThan oper then "slt"
      else if is_BIExp_SignedLessOrEqual oper then "sle"
      else if is_BIExp_UnsignedCast oper then "ucast"
      else if is_BIExp_SignedCast oper then "scast"
      else if is_BIExp_HighCast oper then "hcast"
      else if is_BIExp_LowCast oper then "lcast"
      else raise (ERR "binop_to_string" "invalid binop")
  fun unlift_expr expr =
      if is_BExp_Const expr
      then let val (sz,c) = gen_dest_Imm (dest_BExp_Const expr)
               val str = Int.toString (uint_of_word c)
           in
             if sz = 64
             then Imm str
             else Fn (":", [Imm str, Var ("Bit"^Int.toString sz)])
           end
      else if is_BExp_Den expr
      then let val (var,ty) = dest_BVar_string (dest_BExp_Den expr)
           in
             if is_BType_Imm ty
             then if is_BType_Imm64 ty
                  then Var var
                  else let val wty = dest_BType_Imm ty
                       in
                         Fn (":",[Var var, Var (immtype_to_string wty)])
                       end
             else Var var
           end
      else if is_BExp_UnaryExp expr
      then let val (oper,a) = dest_BExp_UnaryExp expr
           in
             Fn (unop_to_string oper, [unlift_expr a])
           end
      else if is_BExp_BinExp expr
      then let val (oper,a,b) = dest_BExp_BinExp expr
           in
             Fn (binop_to_string oper, [unlift_expr a, unlift_expr b])
           end
      else if is_BExp_BinPred expr
      then let val (oper,a,b) = dest_BExp_BinPred expr
           in
             Fn (binop_to_string oper, [unlift_expr a, unlift_expr b])
           end
      else if is_BExp_IfThenElse expr
      then let val (cond,left,right) = dest_BExp_IfThenElse expr
           in
             Fn ("__ite", [unlift_expr cond, unlift_expr left, unlift_expr right])
           end
      else if is_BExp_MemEq expr
      then let val (a,b) = dest_BExp_MemEq expr
           in
             Fn ("memeq", [unlift_expr a, unlift_expr b])
           end
      else if is_BExp_Load expr
      then let val (mem,addr,_,sz) = dest_BExp_Load expr
           in
             Fn ("ld" ^ (ty_to_string sz), [unlift_expr mem, unlift_expr addr])
           end
      else if is_BExp_Store expr
      then let val (mem,addr,_,value) = dest_BExp_Store expr
           in
             Fn ("st", [unlift_expr mem, unlift_expr addr, unlift_expr value])
           end
      else if is_BExp_Cast expr
      then let val (a,b,c) = dest_BExp_Cast expr
           in
             Fn (binop_to_string a, [unlift_expr b, Var (immtype_to_string c)])
           end
      else
        raise ERR "unlift_expr" "cannot pp this BExp"
in
  fun pp_expr' ops = pp_map unlift_expr (pp_term' ops);
end;

fun term_to_string'    ops len tm = PP.pp_to_string len (pp_term'    ops) tm;
fun expr_to_string' ops len fm = PP.pp_to_string len (pp_expr' ops) fm;

(* Pretty-printing using !infixes and !LINE_LENGTH *)

fun pp_term tm = pp_term' (!expr_infixes) tm;
fun pp_expr expr = pp_expr' (!expr_infixes) expr;
fun term_to_string tm = term_to_string' (!expr_infixes) (!LINE_LENGTH) tm;
fun expr_to_string expr = expr_to_string' (!expr_infixes) (!LINE_LENGTH) expr;

local
  open PP listSyntax bir_programSyntax;
in
fun pp_bracket pp tm =
    if is_BLE_Label tm orelse is_BExp_Den tm orelse is_BExp_Const tm
    then pp tm
    else
      block INCONSISTENT 0 [
        add_string "(", pp tm, add_string ")"
      ];
fun pp_bexpr expr = pp_bracket pp_expr expr;
fun pp_lbl lbl =
    if is_BL_Label lbl
    then PP.add_string (stringSyntax.fromHOLstring (dest_BL_Label lbl))
    else
      let val (sz,c) = gen_dest_Imm (dest_BL_Address lbl)
      in
        PP.add_string (PolyML.makestring (wordsSyntax.uint_of_word c))
      end;
fun pp_lblexpr lblexpr =
    if is_BLE_Label lblexpr
    then let val lbl = dest_BLE_Label lblexpr
         in
           pp_lbl lbl
         end
    else
      pp_expr (dest_BLE_Exp lblexpr)

fun pp_app str pp =
    block INCONSISTENT 0 [
      add_string str, add_break (1,0),
      pp
    ]

fun pp_stmt stmt =
    if is_BStmt_Assert stmt
    then let val expr = dest_BStmt_Assert stmt
         in
           pp_app "assert" (pp_bexpr expr)
         end
    else if is_BStmt_Assume stmt
    then let val expr = dest_BStmt_Assume stmt
         in
           pp_app "assume" (pp_bexpr expr)
         end
    else if is_BStmt_Assign stmt
    then let open PP
             val (var,expr) = dest_BStmt_Assign stmt
             val (str,_) = dest_BVar_string var
         in
           block INCONSISTENT 0 [
             add_string str, add_break (1,0),
             add_string "=", add_break (1,0),
             pp_expr expr
           ]
         end
    else if is_BStmt_Halt stmt
    then let val expr = dest_BStmt_Halt stmt
         in
           pp_app "halt" (pp_bexpr expr)
         end
    else if is_BStmt_Jmp stmt
    then let val lblexpr = dest_BStmt_Jmp stmt
         in
           pp_app "jmp" (pp_bracket pp_lblexpr lblexpr)
         end
    else if is_BStmt_CJmp stmt
    then let val (cond,left,right) = dest_BStmt_CJmp stmt
         in
           block INCONSISTENT 0 [
             add_string "cjmp", add_break (1,0),
             pp_bexpr cond, add_break (1,0),
             pp_bracket pp_lblexpr left, add_break (1,0),
             pp_bracket pp_lblexpr right
           ]
         end
    else raise ERR "pp_stmt" "cannot pp this BIR statement"
fun pp_prog prog =
    let val (block_list,_) = dest_list (dest_BirProgram prog)
        fun pp_block bl =
            let val (lbl,stmts_tm,end_stmt) = dest_bir_block bl
                val (stmts,_) = dest_list stmts_tm;
            in
              PP.block INCONSISTENT 0 [
                pp_lbl lbl, add_string ":\n",
                block INCONSISTENT 0
                      (List.concat
                           (List.map (fn stmt =>
                                         [pp_stmt stmt, add_string "\n"]) stmts)),
                pp_stmt end_stmt, add_string "\n"
              ]
            end
    in
      PP.block INCONSISTENT 0
               (List.map pp_block block_list)
    end
end

fun prog_to_string' len fm = PP.pp_to_string len pp_prog fm;
fun prog_to_string prog = prog_to_string' (!LINE_LENGTH) prog;

(* Some examples *)
val exp = BExp‘ucast (1 : Bit32) Bit8’

val prog =
BIR‘
a:
assert (X1 > 0) ; this is a comment
X1 = sdiv X2 4 + ld MEM X4 + 3
jmp b
b:
halt X1
’;

end
