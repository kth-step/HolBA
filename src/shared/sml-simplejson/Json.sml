
(* Simple Standard ML JSON parser
   ==============================

   https://hg.sr.ht/~cannam/sml-simplejson

   An RFC-compliant JSON parser in one SML file with no dependency 
   on anything outside the Basis library. Also includes a simple
   serialiser.

   Tested with MLton, Poly/ML, and SML/NJ compilers.

   Parser notes:

   * Complies with RFC 7159, The JavaScript Object Notation (JSON)
     Data Interchange Format

   * Passes all of the JSONTestSuite parser accept/reject tests that
     exist at the time of writing, as listed in "Parsing JSON is a
     Minefield" (http://seriot.ch/parsing_json.php)
 
   * Two-pass parser using naive exploded strings, therefore not
     particularly fast and not suitable for large input files

   * Only supports UTF-8 input, not UTF-16 or UTF-32. Doesn't check
     that JSON strings are valid UTF-8 -- the caller must do that --
     but does handle \u escapes

   * Converts all numbers to type "real". If that is a 64-bit IEEE
     float type (common but not guaranteed in SML) then we're pretty
     standard for a JSON parser
     (A. Lindner: modified this locally to be Arbnum.num)

   * For simplicity this implementation returns object fields in the
     order in which they appear in the input, without checking for
     duplicates. But JSON object fields are unordered, so callers
     should take care not to accidentally rely on this

   Copyright 2017 Chris Cannam.
   Parts based on the JSON parser in the Ponyo library by Phil Eaton.

   Permission is hereby granted, free of charge, to any person
   obtaining a copy of this software and associated documentation
   files (the "Software"), to deal in the Software without
   restriction, including without limitation the rights to use, copy,
   modify, merge, publish, distribute, sublicense, and/or sell copies
   of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be
   included in all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR
   ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
   CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
   WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

   Except as contained in this notice, the names of Chris Cannam and
   Particular Programs Ltd shall not be used in advertising or
   otherwise to promote the sale, use or other dealings in this
   Software without prior written authorization.
*)

signature JSON = sig

    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of Arbnum.num
                  | STRING of string
                  | BOOL of bool
                  | NULL

    datatype 'a result = OK of 'a
                       | ERROR of string

    val parse : string -> json result
    val serialise : json -> string
    val serialiseIndented : json -> string

end

structure Json :> JSON = struct

    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of Arbnum.num
                  | STRING of string
                  | BOOL of bool
                  | NULL

    datatype 'a result = OK of 'a
                       | ERROR of string

    structure T = struct
        datatype token = NUMBER of char list
                       | STRING of string
                       | BOOL of bool
                       | NULL
                       | CURLY_L
                       | CURLY_R
                       | SQUARE_L
                       | SQUARE_R
                       | COLON
                       | COMMA

        fun toString t =
            case t of NUMBER digits => implode digits
                    | STRING s => s
                    | BOOL b => Bool.toString b
                    | NULL => "null"
                    | CURLY_L => "{"
                    | CURLY_R => "}"
                    | SQUARE_L => "["
                    | SQUARE_R => "]"
                    | COLON => ":"
                    | COMMA => ","
    end

    fun bmpToUtf8 cp =  (* convert a codepoint in Unicode BMP to utf8 bytes *)
        let open Word
	    infix 6 orb andb >>
        in
            map (Char.chr o toInt)
                (if cp < 0wx80 then
                     [cp]
                 else if cp < 0wx800 then
                     [0wxc0 orb (cp >> 0w6), 0wx80 orb (cp andb 0wx3f)]
                 else if cp < 0wx10000 then
                     [0wxe0 orb (cp >> 0w12),
                      0wx80 orb ((cp >> 0w6) andb 0wx3f),
		      0wx80 orb (cp andb 0wx3f)]
                 else raise Fail ("Invalid BMP point " ^ (Word.toString cp)))
        end
                      
    fun error pos text = ERROR (text ^ " at character position " ^
                                Int.toString (pos - 1))
    fun token_error pos = error pos ("Unexpected token")

    fun lexNull pos acc (#"u" :: #"l" :: #"l" :: xs) =
        lex (pos + 3) (T.NULL :: acc) xs
      | lexNull pos acc _ = token_error pos

    and lexTrue pos acc (#"r" :: #"u" :: #"e" :: xs) =
        lex (pos + 3) (T.BOOL true :: acc) xs
      | lexTrue pos acc _ = token_error pos

    and lexFalse pos acc (#"a" :: #"l" :: #"s" :: #"e" :: xs) =
        lex (pos + 4) (T.BOOL false :: acc) xs
      | lexFalse pos acc _ = token_error pos

    and lexChar tok pos acc xs =
        lex pos (tok :: acc) xs
        
    and lexString pos acc cc =
        let datatype escaped = ESCAPED | NORMAL
            fun lexString' pos text ESCAPED [] =
                error pos "End of input during escape sequence"
              | lexString' pos text NORMAL [] = 
                error pos "End of input during string"
              | lexString' pos text ESCAPED (x :: xs) =
                let fun esc c = lexString' (pos + 1) (c :: text) NORMAL xs
                in case x of
                       #"\"" => esc x
                     | #"\\" => esc x
                     | #"/"  => esc x
                     | #"b"  => esc #"\b"
                     | #"f"  => esc #"\f"
                     | #"n"  => esc #"\n"
                     | #"r"  => esc #"\r"
                     | #"t"  => esc #"\t"
                     | _     => error pos ("Invalid escape \\" ^
                                           Char.toString x)
                end
              | lexString' pos text NORMAL (#"\\" :: #"u" ::a::b::c::d:: xs) =
                if List.all Char.isHexDigit [a,b,c,d]
                then case Word.fromString ("0wx" ^ (implode [a,b,c,d])) of
                         SOME w => (let val utf = rev (bmpToUtf8 w) in
                                        lexString' (pos + 6) (utf @ text)
                                                   NORMAL xs
                                    end
                                    handle Fail err => error pos err)
                       | NONE => error pos "Invalid Unicode BMP escape sequence"
                else error pos "Invalid Unicode BMP escape sequence"
              | lexString' pos text NORMAL (x :: xs) =
                if Char.ord x < 0x20
                then error pos "Invalid unescaped control character"
                else
                    case x of
                        #"\"" => OK (rev text, xs, pos + 1)
                      | #"\\" => lexString' (pos + 1) text ESCAPED xs
                      | _     => lexString' (pos + 1) (x :: text) NORMAL xs
        in
            case lexString' pos [] NORMAL cc of
                OK (text, rest, newpos) =>
                lex newpos (T.STRING (implode text) :: acc) rest
              | ERROR e => ERROR e
        end

    and lexNumber firstChar pos acc cc =
        let val valid = explode "-"
            fun lexNumber' pos digits [] = (rev digits, [], pos)
              | lexNumber' pos digits (x :: xs) =
                if x = #"E" then lexNumber' (pos + 1) (#"e" :: digits) xs
                else if Char.isDigit x orelse List.exists (fn c => x = c) valid
                then lexNumber' (pos + 1) (x :: digits) xs
                else (rev digits, x :: xs, pos)
            val (digits, rest, newpos) =
                lexNumber' (pos - 1) [] (firstChar :: cc)
        in
            case digits of
                [] => token_error pos
              | _ => lex newpos (T.NUMBER digits :: acc) rest
        end
                                           
    and lex pos acc [] = OK (rev acc)
      | lex pos acc (x::xs) = 
        (case x of
             #" "  => lex
           | #"\t" => lex
           | #"\n" => lex
           | #"\r" => lex
           | #"{"  => lexChar T.CURLY_L
           | #"}"  => lexChar T.CURLY_R
           | #"["  => lexChar T.SQUARE_L
           | #"]"  => lexChar T.SQUARE_R
           | #":"  => lexChar T.COLON
           | #","  => lexChar T.COMMA
           | #"\"" => lexString
           | #"t"  => lexTrue
           | #"f"  => lexFalse
           | #"n"  => lexNull
           | x     => lexNumber x) (pos + 1) acc xs

    fun show [] = "end of input"
      | show (tok :: _) = T.toString tok

    fun parseNumber digits =
        (* Note lexNumber already case-insensitised the E for us *)
        let open Char
            fun okPosTrailing [] = true
              | okPosTrailing (c :: cs) =
                isDigit c andalso okPosTrailing cs
                                                      
            fun okPositive [] = false
              | okPositive (#"0" :: []) = true
              | okPositive (#"0" :: cs) = false
              | okPositive (c :: cs) = isDigit c andalso okPosTrailing cs
                    
            fun okNumber (#"-" :: cs) = okPositive cs
              | okNumber cc = okPositive cc
        in
            if okNumber digits
            then OK (Arbnum.fromString (implode digits))
            else ERROR ("Invalid number \"" ^ (implode digits) ^ "\"")
        end
                                     
    fun parseObject (T.CURLY_R :: xs) = OK (OBJECT [], xs)
      | parseObject tokens =
        let fun parsePair (T.STRING key :: T.COLON :: xs) =
                (case parseTokens xs of
                     ERROR e => ERROR e
                   | OK (j, xs) => OK ((key, j), xs))
              | parsePair other =
                ERROR ("Object key/value pair expected around \"" ^
                       show other ^ "\"")
            fun parseObject' acc [] = ERROR "End of input during object"
              | parseObject' acc tokens =
                case parsePair tokens of
                    ERROR e => ERROR e
                  | OK (pair, T.COMMA :: xs) =>
                    parseObject' (pair :: acc) xs
                  | OK (pair, T.CURLY_R :: xs) =>
                    OK (OBJECT (rev (pair :: acc)), xs)
                  | OK (_, _) => ERROR "Expected , or } after object element"
        in
            parseObject' [] tokens
        end

    and parseArray (T.SQUARE_R :: xs) = OK (ARRAY [], xs)
      | parseArray tokens =
        let fun parseArray' acc [] = ERROR "End of input during array"
              | parseArray' acc tokens =
                case parseTokens tokens of
                    ERROR e => ERROR e
                  | OK (j, T.COMMA :: xs) => parseArray' (j :: acc) xs
                  | OK (j, T.SQUARE_R :: xs) => OK (ARRAY (rev (j :: acc)), xs)
                  | OK (_, _) => ERROR "Expected , or ] after array element"
        in
            parseArray' [] tokens
        end

    and parseTokens [] = ERROR "Value expected"
      | parseTokens (tok :: xs) =
        (case tok of
             T.NUMBER d => (case parseNumber d of
                                OK r => OK (NUMBER r, xs)
                              | ERROR e => ERROR e)
           | T.STRING s => OK (STRING s, xs)
           | T.BOOL b   => OK (BOOL b, xs)
           | T.NULL     => OK (NULL, xs)
           | T.CURLY_L  => parseObject xs
           | T.SQUARE_L => parseArray xs
           | _ => ERROR ("Unexpected token " ^ T.toString tok ^
                         " before " ^ show xs))
                                   
    fun parse str =
        case lex 1 [] (explode str) of
           ERROR e => ERROR e
         | OK tokens => case parseTokens tokens of
                            OK (value, []) => OK value
                          | OK (_, _) => ERROR "Extra data after input"
                          | ERROR e => ERROR e

    fun stringEscape s =
        let fun esc x = [x, #"\\"]
            fun escape' acc [] = rev acc
              | escape' acc (x :: xs) =
                escape' (case x of
                             #"\"" => esc x @ acc
                           | #"\\" => esc x @ acc
                           | #"\b" => esc #"b" @ acc
                           | #"\f" => esc #"f" @ acc
                           | #"\n" => esc #"n" @ acc
                           | #"\r" => esc #"r" @ acc
                           | #"\t" => esc #"t" @ acc
                           | _ =>
                             let val c = Char.ord x
                             in
                                 if c < 0x20
                                 then let val hex = Word.toString (Word.fromInt c)
                                      in (rev o explode) (if c < 0x10
                                                          then ("\\u000" ^ hex)
                                                          else ("\\u00" ^ hex))
                                      end @ acc
                                 else 
                                     x :: acc
                             end)
                        xs
        in
            implode (escape' [] (explode s))
        end
        
    fun serialise json =
        case json of
            OBJECT pp => "{" ^ String.concatWith
                                   "," (map (fn (key, value) =>
                                                serialise (STRING key) ^ ":" ^
                                                serialise value) pp) ^
                         "}"
          | ARRAY arr => "[" ^ String.concatWith "," (map serialise arr) ^ "]"
          | NUMBER n => implode (map (fn #"~" => #"-" | c => c) 
                                     (explode (Arbnum.toString n)))
          | STRING s => "\"" ^ stringEscape s ^ "\""
          | BOOL b => Bool.toString b
          | NULL => "null"
        
    fun serialiseIndented json =
        let fun indent 0 = ""
              | indent i = "  " ^ indent (i - 1)
            fun serialiseIndented' i json =
                let val ser = serialiseIndented' (i + 1)
                in
                    case json of
                        OBJECT [] => "{}"
                      | ARRAY [] => "[]"
                      | OBJECT pp => "{\n" ^ indent (i + 1) ^
                                     String.concatWith
                                         (",\n" ^ indent (i + 1))
                                         (map (fn (key, value) =>
                                                  ser (STRING key) ^ ": " ^
                                                  ser value) pp) ^
                                     "\n" ^ indent i ^ "}"
                      | ARRAY arr => "[\n" ^ indent (i + 1) ^
                                     String.concatWith
                                         (",\n" ^ indent (i + 1))
                                         (map ser arr) ^
                                     "\n" ^ indent i ^ "]"
                      | other => serialise other
                end
        in
            serialiseIndented' 0 json ^ "\n"
        end
                                             
end

