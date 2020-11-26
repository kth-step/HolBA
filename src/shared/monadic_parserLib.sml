structure monadic_parserLib (*:> monadic_parserLib *) =
struct

type location = int * int;
type pstring = location * string;
datatype message = message of pstring * string list;
datatype  'a reply = ok of 'a * pstring * message
         | error of message
datatype 'a consumed = consumed of 'a reply
                     | empty of 'a reply
datatype 'a parser = mk_p of pstring -> 'a consumed;
exception ParseError of location * string * string list;
exception Foldr1;

fun inc c (lin,col) =
    if c = #"\n"
    then (lin+1,0)
    else (lin,col+1);
fun inc_str s loc = foldr (fn (a,b) => inc a b) loc (String.explode s);
fun expect (message (ps,_)) exp = message (ps,[exp]);
fun loc_of (l,_) = l;

fun make_string_parse_error (ParseError ((lin,col),msg,exp)) =
    let fun render [] = ""
          | render [e] = e
          | render [e1,e2] = e1 ^ " or " ^ e2
          | render (e::es) = e ^ ", " ^ render es
    in
    "parse error (line " ^ PolyML.makestring lin ^ ", col " ^ PolyML.makestring col ^ ")\n"
    ^ "unexpected " ^ msg ^ "\n"
    ^ "expecting " ^ render exp
    end;

fun print_parse_error err =
    (print (make_string_parse_error err); ());

fun foldr1 f [] = raise Foldr1
  | foldr1 f [x] = x
  | foldr1 f (x::y::xs) = f x (foldr1 f (y::xs))

fun unConsume (consumed r) = r
  | unConsume (empty r) = r;

fun unParse (mk_p p) s = p s;

fun return a = mk_p (fn ps => empty (ok (a,ps,message ((loc_of ps,""),[]))));
fun bind (mk_p m) f =
    mk_p
        (fn s =>
            case m s of
                empty (ok (x,rest,msg)) => unParse (f x) rest
              | empty (error err) => empty (error err)
              | consumed reply1 =>
                consumed (case reply1 of
                              ok (x,rest,msg) => unConsume (unParse (f x) rest)
                            | error err => error err));

fun seq p q = bind p (fn _ => q);
fun fmap f p = bind p (return o f);


fun merge (message (ps,exp1)) (message (_,exp2)) =
    message (ps,exp1 @ exp2);
fun merge_ok x rest msg1 msg2 =
    empty (ok (x,rest,merge msg1 msg2));
fun merge_error msg1 msg2 =
    empty (error (merge msg1 msg2));

infixr 8 <|>

fun (mk_p p) <|> (mk_p q) =
    mk_p (fn s =>
             case p s of
                 empty (error msg1) =>
                 (case q s of
                      empty (error msg2) =>
                      merge_error msg1 msg2
                    | empty (ok (x,rest,msg2)) =>
                      merge_ok x rest msg1 msg2
                    | c => c)
               | empty (ok (x,rest,msg1)) =>
                 (case q s of
                      empty (error msg2) =>
                      merge_ok x rest msg1 msg2
                    | empty (ok (_,_,msg2)) =>
                      merge_ok x rest msg1 msg2
                    | c => c)
               | c => c);
fun choicel xs = foldr1 (fn x => fn y => x <|> y) xs

fun sat pred =
    mk_p (fn (l,s) =>
             if String.size s = 0
             then empty (error (message ((l,"end of input"),[])))
             else let val (c,cs) = (String.sub (s,0), String.extract(s,1,NONE))
                  in if pred c
                     then consumed (ok (c,(inc c l,cs),message ((inc c l,""),[])))
                     else empty (error (message ((l,str c),[])))
                  end);
val zero = mk_p (fn s => empty (error (message ((loc_of s,"parse error"),[]))));

fun many p =
    (many1 p) <|> (return [])
and many1 p =
    bind p (fn x => bind (many p) (fn xs => return (x::xs)));

fun fix f = mk_p (fn s =>
                     unParse (f (fix f)) s)

infix 9 <?>;

fun p <?> msg =
    mk_p (fn s =>
             case unParse p s of
                 empty (error old_msg) => empty (error (expect old_msg msg))
               | empty (ok (x,rest,old_msg)) => empty (ok (x,rest,expect old_msg msg))
               | other => other);

fun char c = sat (fn x => x = c) <?> (str c)
fun string a = mk_p (fn (l,s) => if String.isPrefix a s
                             then consumed (ok (a,(inc_str a l, String.extract (s,String.size a,NONE)),message ((inc_str a l,""),[])))
                             else empty (error (message ((l,s),["\""^a^"\""]))));
val digit = sat Char.isDigit <?> "digit";
val hexdigit = sat Char.isHexDigit <?> "hex digit";
val letter = sat Char.isAlpha <?> "letter";
val item = sat (fn _ => true);

val identifier
    = many1 (letter <|> digit <|> char #"_") <?> "identifier";

val literal = mk_p (fn (l,s) =>
                       let val toks = String.tokens Char.isSpace s
                       in case toks of
                              [] => empty (error (message ((l,"token"),[])))
                           |  (t::ts) => consumed (ok (t, (inc_str t l, String.concat ts),message ((inc_str t l, ""),[])))
                       end) <?> "literal";

fun try p =
    mk_p (fn s =>
             case unParse p s of
                 consumed (error err) => empty (error err)
               | other => other);

fun bracket begin p close =
    seq begin (bind p (fn x => seq close (return x)));

val spaces = many1 (sat (fn c => (not (c = #"\n") andalso Char.isSpace c)))
val comment = bracket (string "(*") (many (sat (fn c => not (c = #"*")))) (string "*)")
val junk = seq (many (try spaces <|> comment)) (return ())
fun token p = bind p (fn x => seq junk (return x))

fun sep_by1 p sep =
    bind p (fn x =>
    bind (many (seq sep p)) (fn xs =>
    return (x::xs)));

fun chainl1 p oper =
    let fun rest x = (bind oper (fn f =>
                      bind p (fn y =>
                      rest (f x y)))) <|> (return x)
    in bind p rest
    end;
fun chainr1 p oper =
    bind p (fn x =>
               (bind oper (fn f =>
                bind (chainr1 p oper) (fn y =>
                return (f x y)))) <|> (return x));

fun parse p s =
    case unConsume (unParse p ((0,0),s)) of
        error (message ((l,msg),expected)) =>
        raise (ParseError (l,msg,expected))
      | ok (x,(_,""),_) => x
      | ok (_,(l,rest),message (_,exp)) =>
        raise (ParseError (l, "unparsed input", exp));

val dec = chainl1 (bind digit (fn d => return (Char.ord d - Char.ord #"0")))
                         (return (fn m => fn n => 10*m + n)) <?> "decimal number"
val hex = seq (string "0x")
              (bind (many1 hexdigit) (fn n =>
                                case StringCvt.scanString (Int.scan StringCvt.HEX) (String.implode n) of
                                    NONE => zero
                                  | SOME n => return n))
val number = (hex <|> dec) <?> "number";
val addop = seq (char #"+") (return (fn n => fn m => n+m)) <?> "operator";
val multop = seq (char #"*") (return (fn n => fn m => n*m))<?> "operator";

val expr_fix =
    fix (fn expr =>
            let val factor = (bracket (char #"(") expr (char #")")) <|> number
                                    <?> "factor"
                val term = chainr1 factor multop <?> "term"
            in
              chainl1 term addop <?> "expression"
            end);

end
