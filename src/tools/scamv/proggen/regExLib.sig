signature regEx_lib = sig
    datatype regex =
        ALTERNATION of regex list
      | CONCATENATION of regex list
      | END
      | LITERAL of char
      | STAR of regex
    val evalRegex:
       regex -> (char, 'a) StringCvt.reader -> 'a -> (string * 'a) option
    val literalList: string -> regex list
    val stringLiteral: string -> regex
    val testResults: string list
end
