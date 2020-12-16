let
open bir_utilLib;
open scamv_testsLib;

val example_relation =
   ``BExp_BinExp BIExp_And
      (BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessThan
               (BExp_Den (BVar "A" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0w)))
            (BExp_BinExp BIExp_And
               (BExp_BinPred BIExp_LessThan
                  (BExp_Den (BVar "A'" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 0w)))
               (BExp_BinExp BIExp_And
                  (BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
                     (BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
                        (BExp_Const (Imm1 1w))))
                  (BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
                        (BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
                           (BExp_Const (Imm1 1w))))
                     (BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
                        (BExp_UnaryExp BIExp_Not
                           (BExp_BinExp BIExp_And
                              (BExp_BinPred BIExp_Equal
                                 (BExp_Den (BVar "D" (BType_Imm Bit64)))
                                 (BExp_Den (BVar "A'" (BType_Imm Bit64))))
                              (BExp_BinExp BIExp_And
                                 (BExp_BinPred BIExp_Equal
                                    (BExp_Den (BVar "E" (BType_Imm Bit64)))
                                    (BExp_Den (BVar "B'" (BType_Imm Bit64))))
                                 (BExp_BinPred BIExp_Equal
                                    (BExp_Den (BVar "F" (BType_Imm Bit64)))
                                    (BExp_Den (BVar "C'" (BType_Imm Bit64))))))))))))
         (BExp_Const (Imm1 1w))) (BExp_Const (Imm1 1w))``;

(* simple test just to check that make_word_relation doesn't throw an exception
for now *)
fun test1 () = (make_word_relation example_relation; true);

in
  run_tests [("test1",test1)]
end;
