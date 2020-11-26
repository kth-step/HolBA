signature monadic_parserLib =
sig
  type 'a parser;
  type location = int * int;
  exception ParseError of location * string * string list;

  (* functor *)
  val fmap : ('a -> 'b) -> 'a parser -> 'b parser

  (* monad *)
  val return : 'a -> 'a parser
  val bind : 'a parser -> ('a -> 'b parser) -> 'b parser
  val seq : 'a parser -> 'b parser -> 'b parser

  (* MonadPlus *)
  val zero : 'a parser
  val <|> : 'a parser * 'a parser -> 'a parser
                                         
  (* effect basis *)
  val parse : 'a parser -> string -> 'a

  (* base tokens *)
  val sat : (char -> bool) -> char parser
  val item : char parser
  val char : char -> char parser
  val string : string -> string parser
  val literal : string parser
  val comment : char list parser
  val spaces : char list parser
  val junk : unit parser
  val token : 'a parser -> 'a parser

  (* combinators *)
  val many : 'a parser -> 'a list parser
  val many1 : 'a parser -> 'a list parser
  val bracket : 'a parser -> 'b parser -> 'c parser -> 'b parser
  val chainl1 : 'a parser -> ('a -> 'a -> 'a) parser -> 'a parser
  val chainr1 : 'a parser -> ('a -> 'a -> 'a) parser -> 'a parser
  val sep_by1 : 'a parser -> 'b parser -> 'a list parser
  val fix : ('a parser -> 'a parser) -> 'a parser
  val choicel : 'a parser list -> 'a parser
  val try : 'a parser -> 'a parser
  val <?> : 'a parser * string -> 'a parser

  (* numeric parsers *)
  val dec : int parser
  val digit : char parser
  val hex : int parser
  val hexdigit : char parser
  val number : int parser

  (* error processing *)
  val make_string_parse_error : exn -> string
  val print_parse_error : exn -> unit
end

