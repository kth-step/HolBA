structure regExLib =
struct
  datatype regex =
      (* No support for matching the null string *)
      LITERAL of char
    | END
    | CONCATENATION of regex list
    | ALTERNATION of regex list
    | STAR of regex


  fun evalRegex (pattern : regex)
           (reader: (char, 'strm) StringCvt.reader)
           (strm: 'strm)
         : (string * 'strm) option =
    let
      fun nextChar (f : (char * 'strm) -> (string * 'strm) option)
                 : (string * 'strm) option =
        Option.mapPartial f (reader strm)
      fun eval' s p = evalRegex p reader s
    in
      case pattern of
           END => if isSome (reader strm) then NONE else SOME ("", strm)
         | LITERAL (p) =>
             nextChar (
               fn (c, strm) => if c = p
                               then SOME (Char.toString c, strm)
                               else NONE
             )
         | CONCATENATION (nil)  => SOME ("", strm)
         | CONCATENATION (h::t) =>
             let
               fun combine ((str, strm) : (string * 'strm))
                         : (string * 'strm) option =
                 Option.compose ((
                   fn (str', strm) => (str ^ str', strm)
                 ), (eval' strm)) (CONCATENATION (t))
             in
               Option.composePartial (combine, (eval' strm)) h
             end
         | ALTERNATION (pl) =>
             let
               val (matches : (string * 'strm) list) =
                 List.mapPartial (eval' strm) pl
             in
               foldr (
                 fn ((str, strm), b) =>
                   SOME (
                     case b of
                          NONE => (str, strm)
                        | SOME (str', strm') =>
                            if (size str) > (size str')
                            then (str, strm)
                            else (str', strm')
                   )
               ) NONE matches
             end
         | STAR (p) =>
             let
               val m = eval' strm p
             in
               if not (isSome m)
               then SOME ("", strm)
               else
                 let
                   val (str, strm') = valOf m
                   val (str', strm'') = valOf (eval' strm' pattern)
                 in
                   SOME (str ^ str', strm'')
                 end
             end
    end

  fun literalList s =
    let
      fun literalList' (s : char list) : regex list =
        case s of
             nil    => nil
           | (h::t) => (LITERAL (h)) :: (literalList' t)
    in
      literalList' (String.explode s)
    end

  fun stringLiteral s = CONCATENATION (literalList s)

  local
    fun runTest ((name, pattern, str, expect)
               : (string * regex * string * bool))
              : string =
      let
        fun reader nil    = NONE
          | reader (h::t) = SOME (h, t)
        val result = Option.map (fn (str, strm) => str) (
          evalRegex pattern reader (String.explode str)
        )
        val resultStr = if (isSome result) = expect then "pass" else "fail"
      in
        name ^ ": " ^ resultStr
      end

    val whitespace_r =
      STAR (ALTERNATION [LITERAL #" ", LITERAL #"\t", LITERAL #"\n"])
    val alphabet_r =
      ALTERNATION (
        literalList "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
      )

    val tests = [
      ("literal", LITERAL #"a", "a", true),
      ("concat", stringLiteral "and", "and", true),
      ("alternation 1", ALTERNATION (literalList "yx"), "y", true),
      ("alternation 2", ALTERNATION (literalList "yx"), "x", true),
      ("end", END, "", true),
      ("star", STAR (LITERAL #"a"), "aaaa", true),
      (
        "whitespace",
        whitespace_r,
        "  " ^ (Char.toString #"\n") ^ (Char.toString #"\t"),
        true
      ),
      (
        "and with whitespace",
        CONCATENATION [whitespace_r, stringLiteral "and", whitespace_r, END],
        "   and",
        true
      ),
      (
        "ambiguous",
        CONCATENATION [
          ALTERNATION [
            stringLiteral "if",
            stringLiteral "ifc"
          ],
          END
        ],
        "ifc",
        true
      ),
      (
        "ambiguous 2",
        CONCATENATION [
          ALTERNATION [
            stringLiteral "if",
            stringLiteral "ifc"
          ],
          END
        ],
        "if",
        true
      ),
      (
        "ambiguous 3",
        CONCATENATION [
          ALTERNATION [
            stringLiteral "and",
            STAR (alphabet_r)
          ],
          END
        ],
        "andothers",
        true
      )
    ]
  in
    val testResults = map (runTest) tests
  end
end
