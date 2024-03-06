open HolKernel Parse boolLib bossLib;

open wordsTheory;
open bir_valuesTheory;
open bir_programTheory;

(*
val _ = load "sml-simplejson/jsonparse";
*)

fun readFile filename =
  String.concat (bir_fileLib.read_file_lines filename);

fun parseJson input =
    let
    val serialise = Json.serialiseIndented
    in
        case Json.parse input of
            Json.ERROR e =>
            raise Fail ("Error: " ^ e ^ "\n")
          | Json.OK json =>
            (print (serialise json ^ "\n");
             json)
    end;

fun tryJsonParseSerialize jsonstr =
  let
    val parsed = parseJson jsonstr;
    val jsonstr2 = Json.serialise parsed;
    val _ = print (jsonstr2 ^ "\n");
  in
    if jsonstr = jsonstr2
    then ()
    else raise Fail ("Json str does not come out the same: " ^ jsonstr)
  end;


val path = "../sml-simplejson/testfiles/test_parsing/";

val filename = "y_object_duplicated_key_and_value.json";

val _ =
  case (parseJson o readFile) (path ^ filename) of
     Json.OBJECT [("a", Json.STRING "b"), ("a", Json.STRING "b")] => ()
   | _ => raise Fail "unexpected outcome 1";

val _ =
  case parseJson "[\"hello\", 21, null]" of
     Json.ARRAY [Json.STRING "hello", Json.NUMBER a21, Json.NULL] =>
        if Arbnum.compare(a21, Arbnum.fromInt 21) = EQUAL then () else
        raise Fail "unexpected outcome 2_1"
   | _ => raise Fail "unexpected outcome 2_2";

val _ = tryJsonParseSerialize "[21]";
val _ = tryJsonParseSerialize "[21,25]";
val _ = tryJsonParseSerialize "{\"hallo\":21,\"o\":null,\"m\":[true,false]}";

(* try a big hol term, through string and json, and bring it back *)
val prog_1_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 0w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 4w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R17" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 8w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 12w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_Den (BVar "R9" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 2148532224w))
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 2148794240w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R9*" (BType_Imm Bit64))] HD;
            BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 16w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 76w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 20w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assign (BVar "R26*" (BType_Imm Bit64))
              (BExp_Den (BVar "R26" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 2148532224w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 2148794240w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 76w))] HD;
            BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 24w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R9" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 28w)]
              HD]; bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;
val simpleterm =
``
  3w:word64 = 5w
``;

val t = 3;
local
  val t = prog_1_cache_speculation;
  val t_ = simpleterm;
in
(* Feedback.traces () *)
val _ = Feedback.set_trace "types" 1;
val jsonarg = Json.STRING (term_to_string t);

val command = "./try_deserialize_serialize_json.py";
val operation = "test";
val jsonback = bir_json_execLib.call_json_exec (command, ["-v", operation], jsonarg);

val stringback = case jsonback of
                    Json.STRING s => s
                  | _ => raise Fail "this should not be: not parse back to a json-string";
val termback = Term [QUOTE stringback];

val _ = if identical termback t then () else
        raise Fail "printing and parsing did not go well";
val _ = print "printing an parsing did go well.\n";
end

(* what happens if we get an exception or similar? *)
val command = "./try_deserialize_serialize_json.py";
val operation = "wrong";
val jsonarg = Json.STRING "";
val r = (bir_json_execLib.call_json_exec (command, ["-v", operation], jsonarg); true)
        handle _ => false;

val _ = if not r then () else
        raise Fail "command errors must cause an exception";

