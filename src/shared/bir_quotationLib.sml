structure bir_quotationLib =
struct

open HolKernel Parse boolLib;

open monadic_parserLib;
open bslSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_envSyntax;
open bir_valuesSyntax;
open bir_exp_immSyntax;

infix 9 <?>
infix 8 <|>

(* error handling *)
val libname = "bir_quotationLib"
val ERR = Feedback.mk_HOL_ERR libname
val wrap_exn = Feedback.wrap_exn libname

val default_size = 64;
val default_size_byte = 8;

val imm_type =
    seq (string "Bit")
    (token dec) <?> "BIR imm type"

fun annotated p typ constr default_ty =
    let val ann =
            bind p (fn x =>
            seq (char #":")
            (bind typ (fn ty =>
            return (constr ty x))))  <?> "type-annotated token"
    in
      choicel [try ann, fmap (constr default_ty) p]
    end

fun gen_bir_imm sz =
    annotated (token number) imm_type mk_Imm_of_int sz;

val bir_imm = gen_bir_imm default_size;
val bir_imm_byte = gen_bir_imm default_size_byte;

val bir_type =
    fmap gen_mk_BType_Imm imm_type <?> "BIR type"

val variable = fmap implode (many1 (sat Char.isAlphaNum)) <?> "variable"

fun gen_bir_var sz =
    annotated (token variable) bir_type (fn ty => fn s => mk_BVar_string (s,ty)) (gen_mk_BType_Imm sz)

val bir_var = gen_bir_var default_size;

(* TODO complete with missing operators *)
val unary_op =
    choicel [seq (char #"~") (return bnot)] <?> "unary op";

(* TODO complete with missing operators *)
val binary_op_bitwise =
    choicel [seq (char #"&") (return band)
             ,seq (char #"|") (return bor)
             ,seq (string ">>") (return brshift)
             ,seq (string "<<") (return blshift)] <?> "binary op";

val binary_op_factor =
   choicel [seq (char #"*") (return bmult)
           ,seq (char #"/") (return bdiv)
           ,seq (char #"%") (return bmod)] <?> "multiplication or division operator";

val binary_op_term =
    choicel [seq (char #"+") (return bplus)
            ,seq (char #"-") (return bminus)] <?> "addition or subtraction operator";

val binary_pred =
    choicel [seq (string "==") (return beq)
            ,seq (string "/=") (return bneq)
            ,seq (char #"<") (return blt)
            ,seq (string "<=") (return ble)
            ,seq (char #">") (return bgt)
            ,seq (string ">=") (return bge)] <?> "binary predicate operator";

fun binop p =
    bind (token p) (fn oper =>
    return (curry oper));

val default_mem_var = bvarmem64_8 "MEM";
val default_mem = bden default_mem_var;

fun gen_bir_exp sz =
    fix (fn bir_exp =>
            let val mem_load =
                    seq (string "MEM")
                        (bind (bracket (char #"[") bir_exp (char #"]")) (fn addr =>
                        (return (bload8_le default_mem addr))))
                val logical = choicel [bracket (char #"(") bir_exp (char #")")
                                      ,bind unary_op
                                            (fn oper => fmap oper bir_exp)
                                      ,try mem_load
                                      ,fmap bconstimm (gen_bir_imm sz)
                                      ,fmap bden bir_var]
                                      <?> "logical expression"
                val factor = chainr1 logical (binop binary_op_bitwise)
                                     <?> "factor"
                val term = chainr1 factor (binop binary_op_factor) <?> "term"
                val binexp = chainl1 term (binop binary_op_term)
                                     <?> "BIR binary expression"
                val binpred = bind (token binexp) (fn e1 =>
                              bind (binop binary_pred) (fn oper =>
                              bind (token binexp) (fn e2 =>
                              return (oper e1 e2))))
                                   <?> "BIR binary predicate"
            in
             try binpred <|> binexp
            end
        ) <?> "BIR expression";

val bir_exp = gen_bir_exp default_size;

val bir_assign =
    bind bir_var (fn v =>
    seq (token (string "=")) (
    bind bir_exp (fn exp =>
    return (bassign (v,exp)))))

val bir_assign_mem_store =
    let
      val bir_exp_byte = gen_bir_exp default_size_byte
      val mapping = bind (try bir_exp) (fn addr =>
                    seq (token (string ":="))
                    (bind bir_exp_byte (fn v =>
                    return (bstore_le default_mem addr v))))
    in
    seq (token (string "MEM"))
    (seq (token (string "="))
    (seq (token (string ("MEM")))
    (bind (bracket (char #"{") mapping (char #"}")) (fn store_exp =>
    return (bassign (default_mem_var,store_exp))))))
    end;

val bir_stmtb =
    choicel [try (seq (string "assert") (fmap bassert bir_exp))
             ,try (seq (string "assume") (fmap bassume bir_exp))
             ,try bir_assign_mem_store
             ,bir_assign
             ] <?> "BIR basic statement";

val bir_label = fmap blabel_str variable <?> "label";
val bir_label_exp = fmap belabel_str variable <?> "label expression";

val bir_cjmp_stmt =
    bind bir_exp (fn exp =>
    seq (token (char #",")) (
    bind bir_label_exp (fn lbl1 =>
    seq (token (char #",")) (
    bind bir_label_exp (fn lbl2 =>
    return (bcjmp (exp,lbl1,lbl2)))))))

val bir_stmte =
    choicel [seq (token (string "jmp")) (fmap bjmp bir_label_exp)
            ,seq (token (string "cjmp")) bir_cjmp_stmt
            ,seq (token (string "halt")) (fmap bhalt bir_exp)
            ] <?> "BIR end statement";

fun end_by p sep =
    many (bind p (fn x => seq sep (return x)))

(* TODO: Fix these with new bir_block syntax
val bir_block =
    bind bir_label (fn lbl =>
    seq (seq (string ":") (many (char #"\n"))) (
    bind (end_by (try bir_stmtb) (char #"\n")) (fn stmts =>
    seq (many (char #"\n")) (
    bind bir_stmte (fn stmte =>
    return (lbl, is_atomic, stmts, stmte)))))) <?> "BIR block";

val bir_prog =
    bind (sep_by1 bir_block (seq (string ";") (many1 (char #"\n")))) (fn blocks =>
    return (bprog_list (Type`:'a`) blocks)) <?> "BIR program";


fun BIR [QUOTE str] = parse (seq junk bir_prog) str
                            handle e => raise (ERR "BIR" (make_string_parse_error e))
fun BExp [QUOTE str] = parse (seq junk bir_exp) str
                       handle e => raise (ERR "BExp" (make_string_parse_error e))
*)
end
