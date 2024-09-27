open HolKernel Parse boolLib bossLib;


(*
open aes_symb_execTheory;

val state = (snd o dest_comb o fst o dest_comb o snd o dest_comb o snd o dest_comb o snd o dest_comb o snd o dest_comb o concl) aes_symb_analysis_thm;

val birs_state_t_ty = mk_type ("birs_state_t", []);
fun dest_birs_state tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if ty = birs_state_t_ty then () else fail()
  val pc = Lib.assoc "bsst_pc" l
  val env = Lib.assoc "bsst_environ" l
  val status = Lib.assoc "bsst_status" l
  val pcond = Lib.assoc "bsst_pcond" l
in
  (pc, env, status, pcond) end;


val (_,env,_,_) = dest_birs_state state;

val mem_sval = (snd o pairSyntax.dest_pair o (fn x => List.nth(x,1)) o fst o listSyntax.dest_list o snd o dest_comb) env;
(*
val t = ``                      BExp_Store
                        (BExp_Store
                           (BExp_Store
                              (BExp_Store
                                 (BExp_Store
                                    (BExp_Store
                                       (BExp_Den
                                          (BVar "sy_MEM8"
                                             (BType_Mem Bit64 Bit8)))
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_Den
                                             (BVar "sy_x2"
                                                (BType_Imm Bit64)))
                                          (BExp_Const (Imm64 8w)))
                                       BEnd_LittleEndian
                                       (BExp_Den
                                          (BVar "sy_x1" (BType_Imm Bit64))))
                                    (BExp_BinExp BIExp_Minus
                                       (BExp_Den
                                          (BVar "sy_x2" (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 16w)))
                                    BEnd_LittleEndian
                                    (BExp_Den
                                       (BVar "sy_x8" (BType_Imm Bit64))))
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_Den
                                       (BVar "sy_x2" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 24w)))
                                 BEnd_LittleEndian
                                 (BExp_Const (Imm64 1984w)))
                              (BExp_BinExp BIExp_Minus
                                 (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w)))
                              BEnd_LittleEndian
                              (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))))
                           (BExp_BinExp BIExp_Plus
                              (BExp_BinExp BIExp_LeftShift
                                 (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                                 (BExp_Const (Imm64 32w)))
                              (BExp_Const (Imm64 16w))) BEnd_LittleEndian
                           (BExp_Cast BIExp_LowCast
                              (BExp_Cast BIExp_SignedCast
                                 (BExp_BinExp BIExp_Plus
                                    (BExp_BinExp BIExp_Mult
                                       (BExp_Const (Imm32 0xFFFFFFFFw))
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_BinExp BIExp_Minus
                                             (BExp_Const (Imm64 4096w))
                                             (BExp_Const (Imm64 1366w)))
                                          Bit32))
                                    (BExp_Cast BIExp_LowCast
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_Const (Imm64 32768w))
                                          (BExp_Const (Imm64 2w))) Bit32))
                                 Bit64) Bit32))
                        (BExp_BinExp BIExp_Plus
                           (BExp_BinExp BIExp_LeftShift
                              (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                              (BExp_Const (Imm64 32w)))
                           (BExp_Const (Imm64 32w))) BEnd_LittleEndian
                        (BExp_Cast BIExp_LowCast
                           (BExp_Cast BIExp_SignedCast
                              (BExp_Cast BIExp_LowCast
                                 (BExp_BinExp BIExp_Plus
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Load
                                          (BExp_Den
                                             (BVar "sy_MEM8"
                                                (BType_Mem Bit64 Bit8)))
                                          (BExp_BinExp BIExp_LeftShift
                                             (BExp_Const
                                                (Imm64 0xFFFFFFFFFFFFFFFFw))
                                             (BExp_Const (Imm64 32w)))
                                          BEnd_LittleEndian Bit32) Bit64)
                                    (BExp_Const (Imm64 1w))) Bit32) Bit64)
                           Bit32)``
val a = [];
*)
fun dest_store_rec t a =
  if not (bir_expSyntax.is_BExp_Store t) then (print_term t; a) else
  let
    val (mem_t, addr_t, end_t, val_t) = bir_expSyntax.dest_BExp_Store t;
  in
    dest_store_rec mem_t ((addr_t)::a)
  end;

val addrs = dest_store_rec mem_sval [];
val t = hd addrs;

fun mapfun t =
  (Arbnum.toInt o wordsLib.dest_word_literal o  snd o bir_immSyntax.gen_dest_Imm o bir_expSyntax.dest_BExp_Const o snd o dest_comb) t;

val addrs_vals = List.map mapfun addrs;

val origlen = length addrs_vals;

fun makeunique []     a = a
  | makeunique (h::t) a = makeunique (List.filter (fn x => not (x = h)) t) (h::a);

val unique_addrs_vals = makeunique addrs_vals [];

val maxlen = length unique_addrs_vals;
*)

val bir_aespart_prog_def = Define `
   bir_aespart_prog =
        BirProgram
          [<|bb_label :=
               BL_Address_HC (Imm64 2796w) "FCC42783 (lw a5,-52(s0))";
             bb_statements :=
               [BStmt_Assert
                  (BExp_Aligned Bit64 2
                     (BExp_Den (BVar "x8" (BType_Imm Bit64))));
                BStmt_Assign (BVar "x15" (BType_Imm Bit64))
                  (BExp_Cast BIExp_SignedCast
                     (BExp_Load
                        (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "x8" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                        Bit32) Bit64)];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm64 2800w)))|>]
`;


local
  val state = ``
         <|bsst_pc :=
                  <|bpc_label := BL_Address (Imm64 2804w); bpc_index := 0|>;
                bsst_environ :=
                  birs_gen_env
                    [("MEM8",
                      BExp_Store
                        (BExp_Store
                           (BExp_Store
                              (BExp_Store
                                 (BExp_Store
                                    (BExp_Store
                                       (BExp_Store
                                          (BExp_Store
                                             (BExp_Store
                                                (BExp_Store
                                                   (BExp_Store
                                                      (BExp_Store
                                                         (BExp_Store
                                                            (BExp_Store
                                                               (BExp_Store
                                                                  (BExp_Store
                                                                     (BExp_Store
                                                                        (BExp_Store
                                                                           (BExp_Store
                                                                              (BExp_Store
                                                                                 (BExp_Store
                                                                                    (BExp_Store
                                                                                       (BExp_Store
                                                                                          (BExp_Store
                                                                                             (BExp_Store
                                                                                                (BExp_Store
                                                                                                   (BExp_Store
                                                                                                      (BExp_Store
                                                                                                         (BExp_Store
                                                                                                            (BExp_Store
                                                                                                               (BExp_Store
                                                                                                                  (BExp_Store
                                                                                                                     (BExp_Store
                                                                                                                        (BExp_Store
                                                                                                                           (BExp_Store
                                                                                                                              (BExp_Store
                                                                                                                                 (BExp_Store
                                                                                                                                    (BExp_Store
                                                                                                                                       (BExp_Store
                                                                                                                                          (BExp_Store
                                                                                                                                             (BExp_Store
                                                                                                                                                (BExp_Store
                                                                                                                                                   (BExp_Store
                                                                                                                                                      (BExp_Store
                                                                                                                                                         (BExp_Store
                                                                                                                                                            (BExp_Store
                                                                                                                                                               (BExp_Store
                                                                                                                                                                  (BExp_Store
                                                                                                                                                                     (BExp_Store
                                                                                                                                                                        (BExp_Store
                                                                                                                                                                           (BExp_Store
                                                                                                                                                                              (BExp_Store
                                                                                                                                                                                 (BExp_Store
                                                                                                                                                                                    (BExp_Store
                                                                                                                                                                                       (BExp_Store
                                                                                                                                                                                          (BExp_Store
                                                                                                                                                                                             (BExp_Store
                                                                                                                                                                                                (BExp_Den
                                                                                                                                                                                                   (BVar
                                                                                                                                                                                                      "sy_MEM8"
                                                                                                                                                                                                      (BType_Mem
                                                                                                                                                                                                         Bit64
                                                                                                                                                                                                         Bit8)))
                                                                                                                                                                                                (BExp_BinExp
                                                                                                                                                                                                   BIExp_Minus
                                                                                                                                                                                                   (BExp_Den
                                                                                                                                                                                                      (BVar
                                                                                                                                                                                                         "sy_x2"
                                                                                                                                                                                                         (BType_Imm
                                                                                                                                                                                                            Bit64)))
                                                                                                                                                                                                   (BExp_Const
                                                                                                                                                                                                      (Imm64
                                                                                                                                                                                                         8w)))
                                                                                                                                                                                                BEnd_LittleEndian
                                                                                                                                                                                                (BExp_Den
                                                                                                                                                                                                   (BVar
                                                                                                                                                                                                      "sy_x8"
                                                                                                                                                                                                      (BType_Imm
                                                                                                                                                                                                         Bit64))))
                                                                                                                                                                                             (BExp_BinExp
                                                                                                                                                                                                BIExp_Minus
                                                                                                                                                                                                (BExp_Den
                                                                                                                                                                                                   (BVar
                                                                                                                                                                                                      "sy_x2"
                                                                                                                                                                                                      (BType_Imm
                                                                                                                                                                                                         Bit64)))
                                                                                                                                                                                                (BExp_Const
                                                                                                                                                                                                   (Imm64
                                                                                                                                                                                                      104w)))
                                                                                                                                                                                             BEnd_LittleEndian
                                                                                                                                                                                             (BExp_Den
                                                                                                                                                                                                (BVar
                                                                                                                                                                                                   "sy_x10"
                                                                                                                                                                                                   (BType_Imm
                                                                                                                                                                                                      Bit64))))
                                                                                                                                                                                          (BExp_BinExp
                                                                                                                                                                                             BIExp_Minus
                                                                                                                                                                                             (BExp_Den
                                                                                                                                                                                                (BVar
                                                                                                                                                                                                   "sy_x2"
                                                                                                                                                                                                   (BType_Imm
                                                                                                                                                                                                      Bit64)))
                                                                                                                                                                                             (BExp_Const
                                                                                                                                                                                                (Imm64
                                                                                                                                                                                                   120w)))
                                                                                                                                                                                          BEnd_LittleEndian
                                                                                                                                                                                          (BExp_Den
                                                                                                                                                                                             (BVar
                                                                                                                                                                                                "sy_x12"
                                                                                                                                                                                                (BType_Imm
                                                                                                                                                                                                   Bit64))))
                                                                                                                                                                                       (BExp_BinExp
                                                                                                                                                                                          BIExp_Minus
                                                                                                                                                                                          (BExp_Den
                                                                                                                                                                                             (BVar
                                                                                                                                                                                                "sy_x2"
                                                                                                                                                                                                (BType_Imm
                                                                                                                                                                                                   Bit64)))
                                                                                                                                                                                          (BExp_Const
                                                                                                                                                                                             (Imm64
                                                                                                                                                                                                128w)))
                                                                                                                                                                                       BEnd_LittleEndian
                                                                                                                                                                                       (BExp_Den
                                                                                                                                                                                          (BVar
                                                                                                                                                                                             "sy_x13"
                                                                                                                                                                                             (BType_Imm
                                                                                                                                                                                                Bit64))))
                                                                                                                                                                                    (BExp_BinExp
                                                                                                                                                                                       BIExp_Minus
                                                                                                                                                                                       (BExp_Den
                                                                                                                                                                                          (BVar
                                                                                                                                                                                             "sy_x2"
                                                                                                                                                                                             (BType_Imm
                                                                                                                                                                                                Bit64)))
                                                                                                                                                                                       (BExp_Const
                                                                                                                                                                                          (Imm64
                                                                                                                                                                                             136w)))
                                                                                                                                                                                    BEnd_LittleEndian
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x14"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64))))
                                                                                                                                                                                 (BExp_BinExp
                                                                                                                                                                                    BIExp_Minus
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x2"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    (BExp_Const
                                                                                                                                                                                       (Imm64
                                                                                                                                                                                          108w)))
                                                                                                                                                                                 BEnd_LittleEndian
                                                                                                                                                                                 (BExp_Cast
                                                                                                                                                                                    BIExp_LowCast
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x11"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    Bit32))
                                                                                                                                                                              (BExp_BinExp
                                                                                                                                                                                 BIExp_Minus
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_x2"
                                                                                                                                                                                       (BType_Imm
                                                                                                                                                                                          Bit64)))
                                                                                                                                                                                 (BExp_Const
                                                                                                                                                                                    (Imm64
                                                                                                                                                                                       52w)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              (BExp_Cast
                                                                                                                                                                                 BIExp_LowCast
                                                                                                                                                                                 (BExp_BinExp
                                                                                                                                                                                    BIExp_Minus
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x11"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    (BExp_Const
                                                                                                                                                                                       (Imm64
                                                                                                                                                                                          1w)))
                                                                                                                                                                                 Bit32))
                                                                                                                                                                           (BExp_BinExp
                                                                                                                                                                              BIExp_Minus
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x2"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              (BExp_Const
                                                                                                                                                                                 (Imm64
                                                                                                                                                                                    20w)))
                                                                                                                                                                           BEnd_LittleEndian
                                                                                                                                                                           (BExp_Cast
                                                                                                                                                                              BIExp_LowCast
                                                                                                                                                                              (BExp_Cast
                                                                                                                                                                                 BIExp_SignedCast
                                                                                                                                                                                 (BExp_Load
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_MEM8"
                                                                                                                                                                                          (BType_Mem
                                                                                                                                                                                             Bit64
                                                                                                                                                                                             Bit8)))
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x12"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    BEnd_LittleEndian
                                                                                                                                                                                    Bit32)
                                                                                                                                                                                 Bit64)
                                                                                                                                                                              Bit32))
                                                                                                                                                                        (BExp_BinExp
                                                                                                                                                                           BIExp_Minus
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_x2"
                                                                                                                                                                                 (BType_Imm
                                                                                                                                                                                    Bit64)))
                                                                                                                                                                           (BExp_Const
                                                                                                                                                                              (Imm64
                                                                                                                                                                                 24w)))
                                                                                                                                                                        BEnd_LittleEndian
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_LowCast
                                                                                                                                                                           (BExp_Cast
                                                                                                                                                                              BIExp_SignedCast
                                                                                                                                                                              (BExp_Load
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_MEM8"
                                                                                                                                                                                       (BType_Mem
                                                                                                                                                                                          Bit64
                                                                                                                                                                                          Bit8)))
                                                                                                                                                                                 (BExp_BinExp
                                                                                                                                                                                    BIExp_Plus
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x12"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    (BExp_Const
                                                                                                                                                                                       (Imm64
                                                                                                                                                                                          4w)))
                                                                                                                                                                                 BEnd_LittleEndian
                                                                                                                                                                                 Bit32)
                                                                                                                                                                              Bit64)
                                                                                                                                                                           Bit32))
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Minus
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x2"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        (BExp_Const
                                                                                                                                                                           (Imm64
                                                                                                                                                                              28w)))
                                                                                                                                                                     BEnd_LittleEndian
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_LowCast
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_BinExp
                                                                                                                                                                                 BIExp_Plus
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_x12"
                                                                                                                                                                                       (BType_Imm
                                                                                                                                                                                          Bit64)))
                                                                                                                                                                                 (BExp_Const
                                                                                                                                                                                    (Imm64
                                                                                                                                                                                       8w)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64)
                                                                                                                                                                        Bit32))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Minus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x2"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           32w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_LowCast
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_SignedCast
                                                                                                                                                                        (BExp_Load
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_MEM8"
                                                                                                                                                                                 (BType_Mem
                                                                                                                                                                                    Bit64
                                                                                                                                                                                    Bit8)))
                                                                                                                                                                           (BExp_BinExp
                                                                                                                                                                              BIExp_Plus
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x12"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              (BExp_Const
                                                                                                                                                                                 (Imm64
                                                                                                                                                                                    12w)))
                                                                                                                                                                           BEnd_LittleEndian
                                                                                                                                                                           Bit32)
                                                                                                                                                                        Bit64)
                                                                                                                                                                     Bit32))
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_Minus
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_x2"
                                                                                                                                                                        (BType_Imm
                                                                                                                                                                           Bit64)))
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm64
                                                                                                                                                                        20w)))
                                                                                                                                                               BEnd_LittleEndian
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_LowCast
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Xor
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_SignedCast
                                                                                                                                                                        (BExp_Load
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_MEM8"
                                                                                                                                                                                 (BType_Mem
                                                                                                                                                                                    Bit64
                                                                                                                                                                                    Bit8)))
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_x10"
                                                                                                                                                                                 (BType_Imm
                                                                                                                                                                                    Bit64)))
                                                                                                                                                                           BEnd_LittleEndian
                                                                                                                                                                           Bit32)
                                                                                                                                                                        Bit64)
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_SignedCast
                                                                                                                                                                        (BExp_Load
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_MEM8"
                                                                                                                                                                                 (BType_Mem
                                                                                                                                                                                    Bit64
                                                                                                                                                                                    Bit8)))
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_x12"
                                                                                                                                                                                 (BType_Imm
                                                                                                                                                                                    Bit64)))
                                                                                                                                                                           BEnd_LittleEndian
                                                                                                                                                                           Bit32)
                                                                                                                                                                        Bit64))
                                                                                                                                                                  Bit32))
                                                                                                                                                            (BExp_BinExp
                                                                                                                                                               BIExp_Minus
                                                                                                                                                               (BExp_Den
                                                                                                                                                                  (BVar
                                                                                                                                                                     "sy_x2"
                                                                                                                                                                     (BType_Imm
                                                                                                                                                                        Bit64)))
                                                                                                                                                               (BExp_Const
                                                                                                                                                                  (Imm64
                                                                                                                                                                     24w)))
                                                                                                                                                            BEnd_LittleEndian
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_LowCast
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_Xor
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_SignedCast
                                                                                                                                                                     (BExp_Load
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_MEM8"
                                                                                                                                                                              (BType_Mem
                                                                                                                                                                                 Bit64
                                                                                                                                                                                 Bit8)))
                                                                                                                                                                        (BExp_BinExp
                                                                                                                                                                           BIExp_Plus
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_x10"
                                                                                                                                                                                 (BType_Imm
                                                                                                                                                                                    Bit64)))
                                                                                                                                                                           (BExp_Const
                                                                                                                                                                              (Imm64
                                                                                                                                                                                 4w)))
                                                                                                                                                                        BEnd_LittleEndian
                                                                                                                                                                        Bit32)
                                                                                                                                                                     Bit64)
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_SignedCast
                                                                                                                                                                     (BExp_Load
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_MEM8"
                                                                                                                                                                              (BType_Mem
                                                                                                                                                                                 Bit64
                                                                                                                                                                                 Bit8)))
                                                                                                                                                                        (BExp_BinExp
                                                                                                                                                                           BIExp_Plus
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_x12"
                                                                                                                                                                                 (BType_Imm
                                                                                                                                                                                    Bit64)))
                                                                                                                                                                           (BExp_Const
                                                                                                                                                                              (Imm64
                                                                                                                                                                                 4w)))
                                                                                                                                                                        BEnd_LittleEndian
                                                                                                                                                                        Bit32)
                                                                                                                                                                     Bit64))
                                                                                                                                                               Bit32))
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_Minus
                                                                                                                                                            (BExp_Den
                                                                                                                                                               (BVar
                                                                                                                                                                  "sy_x2"
                                                                                                                                                                  (BType_Imm
                                                                                                                                                                     Bit64)))
                                                                                                                                                            (BExp_Const
                                                                                                                                                               (Imm64
                                                                                                                                                                  28w)))
                                                                                                                                                         BEnd_LittleEndian
                                                                                                                                                         (BExp_Cast
                                                                                                                                                            BIExp_LowCast
                                                                                                                                                            (BExp_BinExp
                                                                                                                                                               BIExp_Xor
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_SignedCast
                                                                                                                                                                  (BExp_Load
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_MEM8"
                                                                                                                                                                           (BType_Mem
                                                                                                                                                                              Bit64
                                                                                                                                                                              Bit8)))
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Plus
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x10"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        (BExp_Const
                                                                                                                                                                           (Imm64
                                                                                                                                                                              8w)))
                                                                                                                                                                     BEnd_LittleEndian
                                                                                                                                                                     Bit32)
                                                                                                                                                                  Bit64)
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_SignedCast
                                                                                                                                                                  (BExp_Load
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_MEM8"
                                                                                                                                                                           (BType_Mem
                                                                                                                                                                              Bit64
                                                                                                                                                                              Bit8)))
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Plus
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x12"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        (BExp_Const
                                                                                                                                                                           (Imm64
                                                                                                                                                                              8w)))
                                                                                                                                                                     BEnd_LittleEndian
                                                                                                                                                                     Bit32)
                                                                                                                                                                  Bit64))
                                                                                                                                                            Bit32))
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_Minus
                                                                                                                                                         (BExp_Den
                                                                                                                                                            (BVar
                                                                                                                                                               "sy_x2"
                                                                                                                                                               (BType_Imm
                                                                                                                                                                  Bit64)))
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               32w)))
                                                                                                                                                      BEnd_LittleEndian
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_LowCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_Xor
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_Load
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_MEM8"
                                                                                                                                                                        (BType_Mem
                                                                                                                                                                           Bit64
                                                                                                                                                                           Bit8)))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Plus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x10"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           12w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  Bit32)
                                                                                                                                                               Bit64)
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_Load
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_MEM8"
                                                                                                                                                                        (BType_Mem
                                                                                                                                                                           Bit64
                                                                                                                                                                           Bit8)))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Plus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x12"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           12w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  Bit32)
                                                                                                                                                               Bit64))
                                                                                                                                                         Bit32))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Minus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x2"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            104w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x10"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            16w))))
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_Minus
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_x2"
                                                                                                                                                         (BType_Imm
                                                                                                                                                            Bit64)))
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         56w)))
                                                                                                                                                BEnd_LittleEndian
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_LowCast
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_And
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            255w))
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_SignedCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_RightShift
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_LowCast
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_Xor
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_SignedCast
                                                                                                                                                                     (BExp_Load
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_MEM8"
                                                                                                                                                                              (BType_Mem
                                                                                                                                                                                 Bit64
                                                                                                                                                                                 Bit8)))
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x10"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        BEnd_LittleEndian
                                                                                                                                                                        Bit32)
                                                                                                                                                                     Bit64)
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_SignedCast
                                                                                                                                                                     (BExp_Load
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_MEM8"
                                                                                                                                                                              (BType_Mem
                                                                                                                                                                                 Bit64
                                                                                                                                                                                 Bit8)))
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x12"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        BEnd_LittleEndian
                                                                                                                                                                        Bit32)
                                                                                                                                                                     Bit64))
                                                                                                                                                               Bit32)
                                                                                                                                                            (BExp_Const
                                                                                                                                                               (Imm32
                                                                                                                                                                  24w)))
                                                                                                                                                         Bit64))
                                                                                                                                                   Bit32))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Minus
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_x2"
                                                                                                                                                      (BType_Imm
                                                                                                                                                         Bit64)))
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      60w)))
                                                                                                                                             BEnd_LittleEndian
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_LowCast
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_And
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         255w))
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_SignedCast
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_RightShift
                                                                                                                                                         (BExp_Cast
                                                                                                                                                            BIExp_LowCast
                                                                                                                                                            (BExp_BinExp
                                                                                                                                                               BIExp_Xor
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_SignedCast
                                                                                                                                                                  (BExp_Load
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_MEM8"
                                                                                                                                                                           (BType_Mem
                                                                                                                                                                              Bit64
                                                                                                                                                                              Bit8)))
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Plus
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x10"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        (BExp_Const
                                                                                                                                                                           (Imm64
                                                                                                                                                                              4w)))
                                                                                                                                                                     BEnd_LittleEndian
                                                                                                                                                                     Bit32)
                                                                                                                                                                  Bit64)
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_SignedCast
                                                                                                                                                                  (BExp_Load
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_MEM8"
                                                                                                                                                                           (BType_Mem
                                                                                                                                                                              Bit64
                                                                                                                                                                              Bit8)))
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Plus
                                                                                                                                                                        (BExp_Den
                                                                                                                                                                           (BVar
                                                                                                                                                                              "sy_x12"
                                                                                                                                                                              (BType_Imm
                                                                                                                                                                                 Bit64)))
                                                                                                                                                                        (BExp_Const
                                                                                                                                                                           (Imm64
                                                                                                                                                                              4w)))
                                                                                                                                                                     BEnd_LittleEndian
                                                                                                                                                                     Bit32)
                                                                                                                                                                  Bit64))
                                                                                                                                                            Bit32)
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm32
                                                                                                                                                               16w)))
                                                                                                                                                      Bit64))
                                                                                                                                                Bit32))
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Minus
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_x2"
                                                                                                                                                   (BType_Imm
                                                                                                                                                      Bit64)))
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   64w)))
                                                                                                                                          BEnd_LittleEndian
                                                                                                                                          (BExp_Cast
                                                                                                                                             BIExp_LowCast
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_And
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      255w))
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_SignedCast
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_RightShift
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_LowCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_Xor
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_Load
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_MEM8"
                                                                                                                                                                        (BType_Mem
                                                                                                                                                                           Bit64
                                                                                                                                                                           Bit8)))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Plus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x10"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           8w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  Bit32)
                                                                                                                                                               Bit64)
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_Load
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_MEM8"
                                                                                                                                                                        (BType_Mem
                                                                                                                                                                           Bit64
                                                                                                                                                                           Bit8)))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Plus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x12"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           8w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  Bit32)
                                                                                                                                                               Bit64))
                                                                                                                                                         Bit32)
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm32
                                                                                                                                                            8w)))
                                                                                                                                                   Bit64))
                                                                                                                                             Bit32))
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_Minus
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_x2"
                                                                                                                                                (BType_Imm
                                                                                                                                                   Bit64)))
                                                                                                                                          (BExp_Const
                                                                                                                                             (Imm64
                                                                                                                                                68w)))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_LowCast
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_And
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   255w))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Xor
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_SignedCast
                                                                                                                                                   (BExp_Load
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_MEM8"
                                                                                                                                                            (BType_Mem
                                                                                                                                                               Bit64
                                                                                                                                                               Bit8)))
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_Plus
                                                                                                                                                         (BExp_Den
                                                                                                                                                            (BVar
                                                                                                                                                               "sy_x10"
                                                                                                                                                               (BType_Imm
                                                                                                                                                                  Bit64)))
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               12w)))
                                                                                                                                                      BEnd_LittleEndian
                                                                                                                                                      Bit32)
                                                                                                                                                   Bit64)
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_SignedCast
                                                                                                                                                   (BExp_Load
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_MEM8"
                                                                                                                                                            (BType_Mem
                                                                                                                                                               Bit64
                                                                                                                                                               Bit8)))
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_Plus
                                                                                                                                                         (BExp_Den
                                                                                                                                                            (BVar
                                                                                                                                                               "sy_x12"
                                                                                                                                                               (BType_Imm
                                                                                                                                                                  Bit64)))
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               12w)))
                                                                                                                                                      BEnd_LittleEndian
                                                                                                                                                      Bit32)
                                                                                                                                                   Bit64)))
                                                                                                                                          Bit32))
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_Minus
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_x2"
                                                                                                                                             (BType_Imm
                                                                                                                                                Bit64)))
                                                                                                                                       (BExp_Const
                                                                                                                                          (Imm64
                                                                                                                                             72w)))
                                                                                                                                    BEnd_LittleEndian
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_LowCast
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_SignedCast
                                                                                                                                          (BExp_Load
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_MEM8"
                                                                                                                                                   (BType_Mem
                                                                                                                                                      Bit64
                                                                                                                                                      Bit8)))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_LeftShift
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_UnsignedCast
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_LowCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_And
                                                                                                                                                            (BExp_Const
                                                                                                                                                               (Imm64
                                                                                                                                                                  255w))
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_RightShift
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_LowCast
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Xor
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x10"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64)
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x12"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64))
                                                                                                                                                                     Bit32)
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm32
                                                                                                                                                                        24w)))
                                                                                                                                                               Bit64))
                                                                                                                                                         Bit32)
                                                                                                                                                      Bit64)
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         2w)))
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_x14"
                                                                                                                                                      (BType_Imm
                                                                                                                                                         Bit64))))
                                                                                                                                             BEnd_LittleEndian
                                                                                                                                             Bit32)
                                                                                                                                          Bit64)
                                                                                                                                       Bit32))
                                                                                                                                 (BExp_BinExp
                                                                                                                                    BIExp_Minus
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_x2"
                                                                                                                                          (BType_Imm
                                                                                                                                             Bit64)))
                                                                                                                                    (BExp_Const
                                                                                                                                       (Imm64
                                                                                                                                          76w)))
                                                                                                                                 BEnd_LittleEndian
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_LowCast
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_SignedCast
                                                                                                                                       (BExp_Load
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_MEM8"
                                                                                                                                                (BType_Mem
                                                                                                                                                   Bit64
                                                                                                                                                   Bit8)))
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Plus
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_LeftShift
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_Plus
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_UnsignedCast
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_LowCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_And
                                                                                                                                                            (BExp_Const
                                                                                                                                                               (Imm64
                                                                                                                                                                  255w))
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_RightShift
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_LowCast
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Xor
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_BinExp
                                                                                                                                                                                 BIExp_Plus
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_x10"
                                                                                                                                                                                       (BType_Imm
                                                                                                                                                                                          Bit64)))
                                                                                                                                                                                 (BExp_Const
                                                                                                                                                                                    (Imm64
                                                                                                                                                                                       4w)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64)
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_BinExp
                                                                                                                                                                                 BIExp_Plus
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_x12"
                                                                                                                                                                                       (BType_Imm
                                                                                                                                                                                          Bit64)))
                                                                                                                                                                                 (BExp_Const
                                                                                                                                                                                    (Imm64
                                                                                                                                                                                       4w)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64))
                                                                                                                                                                     Bit32)
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm32
                                                                                                                                                                        16w)))
                                                                                                                                                               Bit64))
                                                                                                                                                         Bit32)
                                                                                                                                                      Bit64)
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         256w)))
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      2w)))
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_x14"
                                                                                                                                                   (BType_Imm
                                                                                                                                                      Bit64))))
                                                                                                                                          BEnd_LittleEndian
                                                                                                                                          Bit32)
                                                                                                                                       Bit64)
                                                                                                                                    Bit32))
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_Minus
                                                                                                                                 (BExp_Den
                                                                                                                                    (BVar
                                                                                                                                       "sy_x2"
                                                                                                                                       (BType_Imm
                                                                                                                                          Bit64)))
                                                                                                                                 (BExp_Const
                                                                                                                                    (Imm64
                                                                                                                                       80w)))
                                                                                                                              BEnd_LittleEndian
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_LowCast
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_Load
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_MEM8"
                                                                                                                                             (BType_Mem
                                                                                                                                                Bit64
                                                                                                                                                Bit8)))
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_Plus
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_LeftShift
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_UnsignedCast
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_LowCast
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_And
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               255w))
                                                                                                                                                         (BExp_Cast
                                                                                                                                                            BIExp_SignedCast
                                                                                                                                                            (BExp_BinExp
                                                                                                                                                               BIExp_RightShift
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_LowCast
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Xor
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_SignedCast
                                                                                                                                                                        (BExp_Load
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_MEM8"
                                                                                                                                                                                 (BType_Mem
                                                                                                                                                                                    Bit64
                                                                                                                                                                                    Bit8)))
                                                                                                                                                                           (BExp_BinExp
                                                                                                                                                                              BIExp_Plus
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x10"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              (BExp_Const
                                                                                                                                                                                 (Imm64
                                                                                                                                                                                    8w)))
                                                                                                                                                                           BEnd_LittleEndian
                                                                                                                                                                           Bit32)
                                                                                                                                                                        Bit64)
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_SignedCast
                                                                                                                                                                        (BExp_Load
                                                                                                                                                                           (BExp_Den
                                                                                                                                                                              (BVar
                                                                                                                                                                                 "sy_MEM8"
                                                                                                                                                                                 (BType_Mem
                                                                                                                                                                                    Bit64
                                                                                                                                                                                    Bit8)))
                                                                                                                                                                           (BExp_BinExp
                                                                                                                                                                              BIExp_Plus
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x12"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              (BExp_Const
                                                                                                                                                                                 (Imm64
                                                                                                                                                                                    8w)))
                                                                                                                                                                           BEnd_LittleEndian
                                                                                                                                                                           Bit32)
                                                                                                                                                                        Bit64))
                                                                                                                                                                  Bit32)
                                                                                                                                                               (BExp_Const
                                                                                                                                                                  (Imm32
                                                                                                                                                                     8w)))
                                                                                                                                                            Bit64))
                                                                                                                                                      Bit32)
                                                                                                                                                   Bit64)
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      512w)))
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   2w)))
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_x14"
                                                                                                                                                (BType_Imm
                                                                                                                                                   Bit64))))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       Bit32)
                                                                                                                                    Bit64)
                                                                                                                                 Bit32))
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_Minus
                                                                                                                              (BExp_Den
                                                                                                                                 (BVar
                                                                                                                                    "sy_x2"
                                                                                                                                    (BType_Imm
                                                                                                                                       Bit64)))
                                                                                                                              (BExp_Const
                                                                                                                                 (Imm64
                                                                                                                                    84w)))
                                                                                                                           BEnd_LittleEndian
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_LowCast
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_SignedCast
                                                                                                                                 (BExp_Load
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_MEM8"
                                                                                                                                          (BType_Mem
                                                                                                                                             Bit64
                                                                                                                                             Bit8)))
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_Plus
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_LeftShift
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Plus
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_UnsignedCast
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_LowCast
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_And
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            255w))
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_Xor
                                                                                                                                                         (BExp_Cast
                                                                                                                                                            BIExp_SignedCast
                                                                                                                                                            (BExp_Load
                                                                                                                                                               (BExp_Den
                                                                                                                                                                  (BVar
                                                                                                                                                                     "sy_MEM8"
                                                                                                                                                                     (BType_Mem
                                                                                                                                                                        Bit64
                                                                                                                                                                        Bit8)))
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_Plus
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_x10"
                                                                                                                                                                        (BType_Imm
                                                                                                                                                                           Bit64)))
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm64
                                                                                                                                                                        12w)))
                                                                                                                                                               BEnd_LittleEndian
                                                                                                                                                               Bit32)
                                                                                                                                                            Bit64)
                                                                                                                                                         (BExp_Cast
                                                                                                                                                            BIExp_SignedCast
                                                                                                                                                            (BExp_Load
                                                                                                                                                               (BExp_Den
                                                                                                                                                                  (BVar
                                                                                                                                                                     "sy_MEM8"
                                                                                                                                                                     (BType_Mem
                                                                                                                                                                        Bit64
                                                                                                                                                                        Bit8)))
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_Plus
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_x12"
                                                                                                                                                                        (BType_Imm
                                                                                                                                                                           Bit64)))
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm64
                                                                                                                                                                        12w)))
                                                                                                                                                               BEnd_LittleEndian
                                                                                                                                                               Bit32)
                                                                                                                                                            Bit64)))
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64)
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   768w)))
                                                                                                                                          (BExp_Const
                                                                                                                                             (Imm64
                                                                                                                                                2w)))
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_x14"
                                                                                                                                             (BType_Imm
                                                                                                                                                Bit64))))
                                                                                                                                    BEnd_LittleEndian
                                                                                                                                    Bit32)
                                                                                                                                 Bit64)
                                                                                                                              Bit32))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Minus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x2"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 36w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_LowCast
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_Xor
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_SignedCast
                                                                                                                                 (BExp_Load
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_MEM8"
                                                                                                                                          (BType_Mem
                                                                                                                                             Bit64
                                                                                                                                             Bit8)))
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_Plus
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_x10"
                                                                                                                                             (BType_Imm
                                                                                                                                                Bit64)))
                                                                                                                                       (BExp_Const
                                                                                                                                          (Imm64
                                                                                                                                             16w)))
                                                                                                                                    BEnd_LittleEndian
                                                                                                                                    Bit32)
                                                                                                                                 Bit64)
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_Xor
                                                                                                                                 (BExp_BinExp
                                                                                                                                    BIExp_Xor
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_Xor
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_SignedCast
                                                                                                                                          (BExp_Load
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_MEM8"
                                                                                                                                                   (BType_Mem
                                                                                                                                                      Bit64
                                                                                                                                                      Bit8)))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_LeftShift
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_UnsignedCast
                                                                                                                                                         (BExp_Cast
                                                                                                                                                            BIExp_LowCast
                                                                                                                                                            (BExp_BinExp
                                                                                                                                                               BIExp_And
                                                                                                                                                               (BExp_Const
                                                                                                                                                                  (Imm64
                                                                                                                                                                     255w))
                                                                                                                                                               (BExp_Cast
                                                                                                                                                                  BIExp_SignedCast
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_RightShift
                                                                                                                                                                     (BExp_Cast
                                                                                                                                                                        BIExp_LowCast
                                                                                                                                                                        (BExp_BinExp
                                                                                                                                                                           BIExp_Xor
                                                                                                                                                                           (BExp_Cast
                                                                                                                                                                              BIExp_SignedCast
                                                                                                                                                                              (BExp_Load
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_MEM8"
                                                                                                                                                                                       (BType_Mem
                                                                                                                                                                                          Bit64
                                                                                                                                                                                          Bit8)))
                                                                                                                                                                                 (BExp_BinExp
                                                                                                                                                                                    BIExp_Plus
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x10"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    (BExp_Const
                                                                                                                                                                                       (Imm64
                                                                                                                                                                                          4w)))
                                                                                                                                                                                 BEnd_LittleEndian
                                                                                                                                                                                 Bit32)
                                                                                                                                                                              Bit64)
                                                                                                                                                                           (BExp_Cast
                                                                                                                                                                              BIExp_SignedCast
                                                                                                                                                                              (BExp_Load
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_MEM8"
                                                                                                                                                                                       (BType_Mem
                                                                                                                                                                                          Bit64
                                                                                                                                                                                          Bit8)))
                                                                                                                                                                                 (BExp_BinExp
                                                                                                                                                                                    BIExp_Plus
                                                                                                                                                                                    (BExp_Den
                                                                                                                                                                                       (BVar
                                                                                                                                                                                          "sy_x12"
                                                                                                                                                                                          (BType_Imm
                                                                                                                                                                                             Bit64)))
                                                                                                                                                                                    (BExp_Const
                                                                                                                                                                                       (Imm64
                                                                                                                                                                                          4w)))
                                                                                                                                                                                 BEnd_LittleEndian
                                                                                                                                                                                 Bit32)
                                                                                                                                                                              Bit64))
                                                                                                                                                                        Bit32)
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm32
                                                                                                                                                                           16w)))
                                                                                                                                                                  Bit64))
                                                                                                                                                            Bit32)
                                                                                                                                                         Bit64)
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            256w)))
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         2w)))
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_x14"
                                                                                                                                                      (BType_Imm
                                                                                                                                                         Bit64))))
                                                                                                                                             BEnd_LittleEndian
                                                                                                                                             Bit32)
                                                                                                                                          Bit64)
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_SignedCast
                                                                                                                                          (BExp_Load
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_MEM8"
                                                                                                                                                   (BType_Mem
                                                                                                                                                      Bit64
                                                                                                                                                      Bit8)))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_LeftShift
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_UnsignedCast
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_LowCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_And
                                                                                                                                                            (BExp_Const
                                                                                                                                                               (Imm64
                                                                                                                                                                  255w))
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_RightShift
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_LowCast
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Xor
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x10"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64)
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_x12"
                                                                                                                                                                                    (BType_Imm
                                                                                                                                                                                       Bit64)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64))
                                                                                                                                                                     Bit32)
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm32
                                                                                                                                                                        24w)))
                                                                                                                                                               Bit64))
                                                                                                                                                         Bit32)
                                                                                                                                                      Bit64)
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         2w)))
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_x14"
                                                                                                                                                      (BType_Imm
                                                                                                                                                         Bit64))))
                                                                                                                                             BEnd_LittleEndian
                                                                                                                                             Bit32)
                                                                                                                                          Bit64))
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_SignedCast
                                                                                                                                       (BExp_Load
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_MEM8"
                                                                                                                                                (BType_Mem
                                                                                                                                                   Bit64
                                                                                                                                                   Bit8)))
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Plus
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_LeftShift
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_Plus
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_UnsignedCast
                                                                                                                                                      (BExp_Cast
                                                                                                                                                         BIExp_LowCast
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_And
                                                                                                                                                            (BExp_Const
                                                                                                                                                               (Imm64
                                                                                                                                                                  255w))
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_BinExp
                                                                                                                                                                  BIExp_RightShift
                                                                                                                                                                  (BExp_Cast
                                                                                                                                                                     BIExp_LowCast
                                                                                                                                                                     (BExp_BinExp
                                                                                                                                                                        BIExp_Xor
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_BinExp
                                                                                                                                                                                 BIExp_Plus
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_x10"
                                                                                                                                                                                       (BType_Imm
                                                                                                                                                                                          Bit64)))
                                                                                                                                                                                 (BExp_Const
                                                                                                                                                                                    (Imm64
                                                                                                                                                                                       8w)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64)
                                                                                                                                                                        (BExp_Cast
                                                                                                                                                                           BIExp_SignedCast
                                                                                                                                                                           (BExp_Load
                                                                                                                                                                              (BExp_Den
                                                                                                                                                                                 (BVar
                                                                                                                                                                                    "sy_MEM8"
                                                                                                                                                                                    (BType_Mem
                                                                                                                                                                                       Bit64
                                                                                                                                                                                       Bit8)))
                                                                                                                                                                              (BExp_BinExp
                                                                                                                                                                                 BIExp_Plus
                                                                                                                                                                                 (BExp_Den
                                                                                                                                                                                    (BVar
                                                                                                                                                                                       "sy_x12"
                                                                                                                                                                                       (BType_Imm
                                                                                                                                                                                          Bit64)))
                                                                                                                                                                                 (BExp_Const
                                                                                                                                                                                    (Imm64
                                                                                                                                                                                       8w)))
                                                                                                                                                                              BEnd_LittleEndian
                                                                                                                                                                              Bit32)
                                                                                                                                                                           Bit64))
                                                                                                                                                                     Bit32)
                                                                                                                                                                  (BExp_Const
                                                                                                                                                                     (Imm32
                                                                                                                                                                        8w)))
                                                                                                                                                               Bit64))
                                                                                                                                                         Bit32)
                                                                                                                                                      Bit64)
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         512w)))
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      2w)))
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_x14"
                                                                                                                                                   (BType_Imm
                                                                                                                                                      Bit64))))
                                                                                                                                          BEnd_LittleEndian
                                                                                                                                          Bit32)
                                                                                                                                       Bit64))
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_Load
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_MEM8"
                                                                                                                                             (BType_Mem
                                                                                                                                                Bit64
                                                                                                                                                Bit8)))
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_Plus
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_LeftShift
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_UnsignedCast
                                                                                                                                                   (BExp_Cast
                                                                                                                                                      BIExp_LowCast
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_And
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               255w))
                                                                                                                                                         (BExp_BinExp
                                                                                                                                                            BIExp_Xor
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_Load
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_MEM8"
                                                                                                                                                                        (BType_Mem
                                                                                                                                                                           Bit64
                                                                                                                                                                           Bit8)))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Plus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x10"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           12w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  Bit32)
                                                                                                                                                               Bit64)
                                                                                                                                                            (BExp_Cast
                                                                                                                                                               BIExp_SignedCast
                                                                                                                                                               (BExp_Load
                                                                                                                                                                  (BExp_Den
                                                                                                                                                                     (BVar
                                                                                                                                                                        "sy_MEM8"
                                                                                                                                                                        (BType_Mem
                                                                                                                                                                           Bit64
                                                                                                                                                                           Bit8)))
                                                                                                                                                                  (BExp_BinExp
                                                                                                                                                                     BIExp_Plus
                                                                                                                                                                     (BExp_Den
                                                                                                                                                                        (BVar
                                                                                                                                                                           "sy_x12"
                                                                                                                                                                           (BType_Imm
                                                                                                                                                                              Bit64)))
                                                                                                                                                                     (BExp_Const
                                                                                                                                                                        (Imm64
                                                                                                                                                                           12w)))
                                                                                                                                                                  BEnd_LittleEndian
                                                                                                                                                                  Bit32)
                                                                                                                                                               Bit64)))
                                                                                                                                                      Bit32)
                                                                                                                                                   Bit64)
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      768w)))
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   2w)))
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_x14"
                                                                                                                                                (BType_Imm
                                                                                                                                                   Bit64))))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       Bit32)
                                                                                                                                    Bit64)))
                                                                                                                           Bit32))
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_Minus
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_x2"
                                                                                                                              (BType_Imm
                                                                                                                                 Bit64)))
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              56w)))
                                                                                                                     BEnd_LittleEndian
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_LowCast
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_And
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 255w))
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_SignedCast
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_RightShift
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_LowCast
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_Xor
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_SignedCast
                                                                                                                                          (BExp_Load
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_MEM8"
                                                                                                                                                   (BType_Mem
                                                                                                                                                      Bit64
                                                                                                                                                      Bit8)))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_x10"
                                                                                                                                                      (BType_Imm
                                                                                                                                                         Bit64)))
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      4w)))
                                                                                                                                             BEnd_LittleEndian
                                                                                                                                             Bit32)
                                                                                                                                          Bit64)
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_SignedCast
                                                                                                                                          (BExp_Load
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_MEM8"
                                                                                                                                                   (BType_Mem
                                                                                                                                                      Bit64
                                                                                                                                                      Bit8)))
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Plus
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_x12"
                                                                                                                                                      (BType_Imm
                                                                                                                                                         Bit64)))
                                                                                                                                                (BExp_Const
                                                                                                                                                   (Imm64
                                                                                                                                                      4w)))
                                                                                                                                             BEnd_LittleEndian
                                                                                                                                             Bit32)
                                                                                                                                          Bit64))
                                                                                                                                    Bit32)
                                                                                                                                 (BExp_Const
                                                                                                                                    (Imm32
                                                                                                                                       24w)))
                                                                                                                              Bit64))
                                                                                                                        Bit32))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Minus
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x2"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64)))
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           60w)))
                                                                                                                  BEnd_LittleEndian
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_LowCast
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_And
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              255w))
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_SignedCast
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_RightShift
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_LowCast
                                                                                                                                 (BExp_BinExp
                                                                                                                                    BIExp_Xor
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_SignedCast
                                                                                                                                       (BExp_Load
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_MEM8"
                                                                                                                                                (BType_Mem
                                                                                                                                                   Bit64
                                                                                                                                                   Bit8)))
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Plus
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_x10"
                                                                                                                                                   (BType_Imm
                                                                                                                                                      Bit64)))
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   8w)))
                                                                                                                                          BEnd_LittleEndian
                                                                                                                                          Bit32)
                                                                                                                                       Bit64)
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_SignedCast
                                                                                                                                       (BExp_Load
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_MEM8"
                                                                                                                                                (BType_Mem
                                                                                                                                                   Bit64
                                                                                                                                                   Bit8)))
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Plus
                                                                                                                                             (BExp_Den
                                                                                                                                                (BVar
                                                                                                                                                   "sy_x12"
                                                                                                                                                   (BType_Imm
                                                                                                                                                      Bit64)))
                                                                                                                                             (BExp_Const
                                                                                                                                                (Imm64
                                                                                                                                                   8w)))
                                                                                                                                          BEnd_LittleEndian
                                                                                                                                          Bit32)
                                                                                                                                       Bit64))
                                                                                                                                 Bit32)
                                                                                                                              (BExp_Const
                                                                                                                                 (Imm32
                                                                                                                                    16w)))
                                                                                                                           Bit64))
                                                                                                                     Bit32))
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Minus
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_x2"
                                                                                                                        (BType_Imm
                                                                                                                           Bit64)))
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        64w)))
                                                                                                               BEnd_LittleEndian
                                                                                                               (BExp_Cast
                                                                                                                  BIExp_LowCast
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_And
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           255w))
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_SignedCast
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_RightShift
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_LowCast
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_Xor
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_Load
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_MEM8"
                                                                                                                                             (BType_Mem
                                                                                                                                                Bit64
                                                                                                                                                Bit8)))
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_Plus
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_x10"
                                                                                                                                                (BType_Imm
                                                                                                                                                   Bit64)))
                                                                                                                                          (BExp_Const
                                                                                                                                             (Imm64
                                                                                                                                                12w)))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       Bit32)
                                                                                                                                    Bit64)
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_Load
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_MEM8"
                                                                                                                                             (BType_Mem
                                                                                                                                                Bit64
                                                                                                                                                Bit8)))
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_Plus
                                                                                                                                          (BExp_Den
                                                                                                                                             (BVar
                                                                                                                                                "sy_x12"
                                                                                                                                                (BType_Imm
                                                                                                                                                   Bit64)))
                                                                                                                                          (BExp_Const
                                                                                                                                             (Imm64
                                                                                                                                                12w)))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       Bit32)
                                                                                                                                    Bit64))
                                                                                                                              Bit32)
                                                                                                                           (BExp_Const
                                                                                                                              (Imm32
                                                                                                                                 8w)))
                                                                                                                        Bit64))
                                                                                                                  Bit32))
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_Minus
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_x2"
                                                                                                                     (BType_Imm
                                                                                                                        Bit64)))
                                                                                                               (BExp_Const
                                                                                                                  (Imm64
                                                                                                                     68w)))
                                                                                                            BEnd_LittleEndian
                                                                                                            (BExp_Cast
                                                                                                               BIExp_LowCast
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_And
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        255w))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Xor
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_SignedCast
                                                                                                                        (BExp_Load
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_MEM8"
                                                                                                                                 (BType_Mem
                                                                                                                                    Bit64
                                                                                                                                    Bit8)))
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x10"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           BEnd_LittleEndian
                                                                                                                           Bit32)
                                                                                                                        Bit64)
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_SignedCast
                                                                                                                        (BExp_Load
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_MEM8"
                                                                                                                                 (BType_Mem
                                                                                                                                    Bit64
                                                                                                                                    Bit8)))
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x12"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           BEnd_LittleEndian
                                                                                                                           Bit32)
                                                                                                                        Bit64)))
                                                                                                               Bit32))
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Minus
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x2"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64)))
                                                                                                            (BExp_Const
                                                                                                               (Imm64
                                                                                                                  72w)))
                                                                                                         BEnd_LittleEndian
                                                                                                         (BExp_Cast
                                                                                                            BIExp_LowCast
                                                                                                            (BExp_Cast
                                                                                                               BIExp_SignedCast
                                                                                                               (BExp_Load
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_MEM8"
                                                                                                                        (BType_Mem
                                                                                                                           Bit64
                                                                                                                           Bit8)))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_LeftShift
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_UnsignedCast
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_LowCast
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_And
                                                                                                                                 (BExp_Const
                                                                                                                                    (Imm64
                                                                                                                                       255w))
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_RightShift
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_LowCast
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Xor
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x10"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            4w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64)
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x12"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            4w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64))
                                                                                                                                          Bit32)
                                                                                                                                       (BExp_Const
                                                                                                                                          (Imm32
                                                                                                                                             24w)))
                                                                                                                                    Bit64))
                                                                                                                              Bit32)
                                                                                                                           Bit64)
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              2w)))
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x14"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64))))
                                                                                                                  BEnd_LittleEndian
                                                                                                                  Bit32)
                                                                                                               Bit64)
                                                                                                            Bit32))
                                                                                                      (BExp_BinExp
                                                                                                         BIExp_Minus
                                                                                                         (BExp_Den
                                                                                                            (BVar
                                                                                                               "sy_x2"
                                                                                                               (BType_Imm
                                                                                                                  Bit64)))
                                                                                                         (BExp_Const
                                                                                                            (Imm64
                                                                                                               76w)))
                                                                                                      BEnd_LittleEndian
                                                                                                      (BExp_Cast
                                                                                                         BIExp_LowCast
                                                                                                         (BExp_Cast
                                                                                                            BIExp_SignedCast
                                                                                                            (BExp_Load
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_MEM8"
                                                                                                                     (BType_Mem
                                                                                                                        Bit64
                                                                                                                        Bit8)))
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Plus
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_LeftShift
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_Plus
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_UnsignedCast
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_LowCast
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_And
                                                                                                                                 (BExp_Const
                                                                                                                                    (Imm64
                                                                                                                                       255w))
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_RightShift
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_LowCast
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Xor
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x10"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            8w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64)
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x12"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            8w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64))
                                                                                                                                          Bit32)
                                                                                                                                       (BExp_Const
                                                                                                                                          (Imm32
                                                                                                                                             16w)))
                                                                                                                                    Bit64))
                                                                                                                              Bit32)
                                                                                                                           Bit64)
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              256w)))
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           2w)))
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_x14"
                                                                                                                        (BType_Imm
                                                                                                                           Bit64))))
                                                                                                               BEnd_LittleEndian
                                                                                                               Bit32)
                                                                                                            Bit64)
                                                                                                         Bit32))
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_Minus
                                                                                                      (BExp_Den
                                                                                                         (BVar
                                                                                                            "sy_x2"
                                                                                                            (BType_Imm
                                                                                                               Bit64)))
                                                                                                      (BExp_Const
                                                                                                         (Imm64
                                                                                                            80w)))
                                                                                                   BEnd_LittleEndian
                                                                                                   (BExp_Cast
                                                                                                      BIExp_LowCast
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_Load
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_MEM8"
                                                                                                                  (BType_Mem
                                                                                                                     Bit64
                                                                                                                     Bit8)))
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_Plus
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_LeftShift
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_UnsignedCast
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_LowCast
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_And
                                                                                                                              (BExp_Const
                                                                                                                                 (Imm64
                                                                                                                                    255w))
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_SignedCast
                                                                                                                                 (BExp_BinExp
                                                                                                                                    BIExp_RightShift
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_LowCast
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_Xor
                                                                                                                                          (BExp_Cast
                                                                                                                                             BIExp_SignedCast
                                                                                                                                             (BExp_Load
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_MEM8"
                                                                                                                                                      (BType_Mem
                                                                                                                                                         Bit64
                                                                                                                                                         Bit8)))
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_Plus
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_x10"
                                                                                                                                                         (BType_Imm
                                                                                                                                                            Bit64)))
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         12w)))
                                                                                                                                                BEnd_LittleEndian
                                                                                                                                                Bit32)
                                                                                                                                             Bit64)
                                                                                                                                          (BExp_Cast
                                                                                                                                             BIExp_SignedCast
                                                                                                                                             (BExp_Load
                                                                                                                                                (BExp_Den
                                                                                                                                                   (BVar
                                                                                                                                                      "sy_MEM8"
                                                                                                                                                      (BType_Mem
                                                                                                                                                         Bit64
                                                                                                                                                         Bit8)))
                                                                                                                                                (BExp_BinExp
                                                                                                                                                   BIExp_Plus
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_x12"
                                                                                                                                                         (BType_Imm
                                                                                                                                                            Bit64)))
                                                                                                                                                   (BExp_Const
                                                                                                                                                      (Imm64
                                                                                                                                                         12w)))
                                                                                                                                                BEnd_LittleEndian
                                                                                                                                                Bit32)
                                                                                                                                             Bit64))
                                                                                                                                       Bit32)
                                                                                                                                    (BExp_Const
                                                                                                                                       (Imm32
                                                                                                                                          8w)))
                                                                                                                                 Bit64))
                                                                                                                           Bit32)
                                                                                                                        Bit64)
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           512w)))
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        2w)))
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_x14"
                                                                                                                     (BType_Imm
                                                                                                                        Bit64))))
                                                                                                            BEnd_LittleEndian
                                                                                                            Bit32)
                                                                                                         Bit64)
                                                                                                      Bit32))
                                                                                                (BExp_BinExp
                                                                                                   BIExp_Minus
                                                                                                   (BExp_Den
                                                                                                      (BVar
                                                                                                         "sy_x2"
                                                                                                         (BType_Imm
                                                                                                            Bit64)))
                                                                                                   (BExp_Const
                                                                                                      (Imm64
                                                                                                         84w)))
                                                                                                BEnd_LittleEndian
                                                                                                (BExp_Cast
                                                                                                   BIExp_LowCast
                                                                                                   (BExp_Cast
                                                                                                      BIExp_SignedCast
                                                                                                      (BExp_Load
                                                                                                         (BExp_Den
                                                                                                            (BVar
                                                                                                               "sy_MEM8"
                                                                                                               (BType_Mem
                                                                                                                  Bit64
                                                                                                                  Bit8)))
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Plus
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_LeftShift
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Plus
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_UnsignedCast
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_LowCast
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_And
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 255w))
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_Xor
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_SignedCast
                                                                                                                                 (BExp_Load
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_MEM8"
                                                                                                                                          (BType_Mem
                                                                                                                                             Bit64
                                                                                                                                             Bit8)))
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_x10"
                                                                                                                                          (BType_Imm
                                                                                                                                             Bit64)))
                                                                                                                                    BEnd_LittleEndian
                                                                                                                                    Bit32)
                                                                                                                                 Bit64)
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_SignedCast
                                                                                                                                 (BExp_Load
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_MEM8"
                                                                                                                                          (BType_Mem
                                                                                                                                             Bit64
                                                                                                                                             Bit8)))
                                                                                                                                    (BExp_Den
                                                                                                                                       (BVar
                                                                                                                                          "sy_x12"
                                                                                                                                          (BType_Imm
                                                                                                                                             Bit64)))
                                                                                                                                    BEnd_LittleEndian
                                                                                                                                    Bit32)
                                                                                                                                 Bit64)))
                                                                                                                        Bit32)
                                                                                                                     Bit64)
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        768w)))
                                                                                                               (BExp_Const
                                                                                                                  (Imm64
                                                                                                                     2w)))
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x14"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64))))
                                                                                                         BEnd_LittleEndian
                                                                                                         Bit32)
                                                                                                      Bit64)
                                                                                                   Bit32))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Minus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x2"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      40w)))
                                                                                             BEnd_LittleEndian
                                                                                             (BExp_Cast
                                                                                                BIExp_LowCast
                                                                                                (BExp_BinExp
                                                                                                   BIExp_Xor
                                                                                                   (BExp_Cast
                                                                                                      BIExp_SignedCast
                                                                                                      (BExp_Load
                                                                                                         (BExp_Den
                                                                                                            (BVar
                                                                                                               "sy_MEM8"
                                                                                                               (BType_Mem
                                                                                                                  Bit64
                                                                                                                  Bit8)))
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Plus
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x10"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64)))
                                                                                                            (BExp_Const
                                                                                                               (Imm64
                                                                                                                  20w)))
                                                                                                         BEnd_LittleEndian
                                                                                                         Bit32)
                                                                                                      Bit64)
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_Xor
                                                                                                      (BExp_BinExp
                                                                                                         BIExp_Xor
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Xor
                                                                                                            (BExp_Cast
                                                                                                               BIExp_SignedCast
                                                                                                               (BExp_Load
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_MEM8"
                                                                                                                        (BType_Mem
                                                                                                                           Bit64
                                                                                                                           Bit8)))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_LeftShift
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_UnsignedCast
                                                                                                                              (BExp_Cast
                                                                                                                                 BIExp_LowCast
                                                                                                                                 (BExp_BinExp
                                                                                                                                    BIExp_And
                                                                                                                                    (BExp_Const
                                                                                                                                       (Imm64
                                                                                                                                          255w))
                                                                                                                                    (BExp_Cast
                                                                                                                                       BIExp_SignedCast
                                                                                                                                       (BExp_BinExp
                                                                                                                                          BIExp_RightShift
                                                                                                                                          (BExp_Cast
                                                                                                                                             BIExp_LowCast
                                                                                                                                             (BExp_BinExp
                                                                                                                                                BIExp_Xor
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_SignedCast
                                                                                                                                                   (BExp_Load
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_MEM8"
                                                                                                                                                            (BType_Mem
                                                                                                                                                               Bit64
                                                                                                                                                               Bit8)))
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_Plus
                                                                                                                                                         (BExp_Den
                                                                                                                                                            (BVar
                                                                                                                                                               "sy_x10"
                                                                                                                                                               (BType_Imm
                                                                                                                                                                  Bit64)))
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               8w)))
                                                                                                                                                      BEnd_LittleEndian
                                                                                                                                                      Bit32)
                                                                                                                                                   Bit64)
                                                                                                                                                (BExp_Cast
                                                                                                                                                   BIExp_SignedCast
                                                                                                                                                   (BExp_Load
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_MEM8"
                                                                                                                                                            (BType_Mem
                                                                                                                                                               Bit64
                                                                                                                                                               Bit8)))
                                                                                                                                                      (BExp_BinExp
                                                                                                                                                         BIExp_Plus
                                                                                                                                                         (BExp_Den
                                                                                                                                                            (BVar
                                                                                                                                                               "sy_x12"
                                                                                                                                                               (BType_Imm
                                                                                                                                                                  Bit64)))
                                                                                                                                                         (BExp_Const
                                                                                                                                                            (Imm64
                                                                                                                                                               8w)))
                                                                                                                                                      BEnd_LittleEndian
                                                                                                                                                      Bit32)
                                                                                                                                                   Bit64))
                                                                                                                                             Bit32)
                                                                                                                                          (BExp_Const
                                                                                                                                             (Imm32
                                                                                                                                                16w)))
                                                                                                                                       Bit64))
                                                                                                                                 Bit32)
                                                                                                                              Bit64)
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 256w)))
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              2w)))
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x14"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64))))
                                                                                                                  BEnd_LittleEndian
                                                                                                                  Bit32)
                                                                                                               Bit64)
                                                                                                            (BExp_Cast
                                                                                                               BIExp_SignedCast
                                                                                                               (BExp_Load
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_MEM8"
                                                                                                                        (BType_Mem
                                                                                                                           Bit64
                                                                                                                           Bit8)))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_LeftShift
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_UnsignedCast
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_LowCast
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_And
                                                                                                                                 (BExp_Const
                                                                                                                                    (Imm64
                                                                                                                                       255w))
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_RightShift
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_LowCast
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Xor
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x10"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            4w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64)
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x12"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            4w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64))
                                                                                                                                          Bit32)
                                                                                                                                       (BExp_Const
                                                                                                                                          (Imm32
                                                                                                                                             24w)))
                                                                                                                                    Bit64))
                                                                                                                              Bit32)
                                                                                                                           Bit64)
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              2w)))
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x14"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64))))
                                                                                                                  BEnd_LittleEndian
                                                                                                                  Bit32)
                                                                                                               Bit64))
                                                                                                         (BExp_Cast
                                                                                                            BIExp_SignedCast
                                                                                                            (BExp_Load
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_MEM8"
                                                                                                                     (BType_Mem
                                                                                                                        Bit64
                                                                                                                        Bit8)))
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Plus
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_LeftShift
                                                                                                                     (BExp_BinExp
                                                                                                                        BIExp_Plus
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_UnsignedCast
                                                                                                                           (BExp_Cast
                                                                                                                              BIExp_LowCast
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_And
                                                                                                                                 (BExp_Const
                                                                                                                                    (Imm64
                                                                                                                                       255w))
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_BinExp
                                                                                                                                       BIExp_RightShift
                                                                                                                                       (BExp_Cast
                                                                                                                                          BIExp_LowCast
                                                                                                                                          (BExp_BinExp
                                                                                                                                             BIExp_Xor
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x10"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            12w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64)
                                                                                                                                             (BExp_Cast
                                                                                                                                                BIExp_SignedCast
                                                                                                                                                (BExp_Load
                                                                                                                                                   (BExp_Den
                                                                                                                                                      (BVar
                                                                                                                                                         "sy_MEM8"
                                                                                                                                                         (BType_Mem
                                                                                                                                                            Bit64
                                                                                                                                                            Bit8)))
                                                                                                                                                   (BExp_BinExp
                                                                                                                                                      BIExp_Plus
                                                                                                                                                      (BExp_Den
                                                                                                                                                         (BVar
                                                                                                                                                            "sy_x12"
                                                                                                                                                            (BType_Imm
                                                                                                                                                               Bit64)))
                                                                                                                                                      (BExp_Const
                                                                                                                                                         (Imm64
                                                                                                                                                            12w)))
                                                                                                                                                   BEnd_LittleEndian
                                                                                                                                                   Bit32)
                                                                                                                                                Bit64))
                                                                                                                                          Bit32)
                                                                                                                                       (BExp_Const
                                                                                                                                          (Imm32
                                                                                                                                             8w)))
                                                                                                                                    Bit64))
                                                                                                                              Bit32)
                                                                                                                           Bit64)
                                                                                                                        (BExp_Const
                                                                                                                           (Imm64
                                                                                                                              512w)))
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           2w)))
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_x14"
                                                                                                                        (BType_Imm
                                                                                                                           Bit64))))
                                                                                                               BEnd_LittleEndian
                                                                                                               Bit32)
                                                                                                            Bit64))
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_Load
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_MEM8"
                                                                                                                  (BType_Mem
                                                                                                                     Bit64
                                                                                                                     Bit8)))
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_Plus
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_LeftShift
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_UnsignedCast
                                                                                                                        (BExp_Cast
                                                                                                                           BIExp_LowCast
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_And
                                                                                                                              (BExp_Const
                                                                                                                                 (Imm64
                                                                                                                                    255w))
                                                                                                                              (BExp_BinExp
                                                                                                                                 BIExp_Xor
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_Load
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_MEM8"
                                                                                                                                             (BType_Mem
                                                                                                                                                Bit64
                                                                                                                                                Bit8)))
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_x10"
                                                                                                                                             (BType_Imm
                                                                                                                                                Bit64)))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       Bit32)
                                                                                                                                    Bit64)
                                                                                                                                 (BExp_Cast
                                                                                                                                    BIExp_SignedCast
                                                                                                                                    (BExp_Load
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_MEM8"
                                                                                                                                             (BType_Mem
                                                                                                                                                Bit64
                                                                                                                                                Bit8)))
                                                                                                                                       (BExp_Den
                                                                                                                                          (BVar
                                                                                                                                             "sy_x12"
                                                                                                                                             (BType_Imm
                                                                                                                                                Bit64)))
                                                                                                                                       BEnd_LittleEndian
                                                                                                                                       Bit32)
                                                                                                                                    Bit64)))
                                                                                                                           Bit32)
                                                                                                                        Bit64)
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           768w)))
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        2w)))
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_x14"
                                                                                                                     (BType_Imm
                                                                                                                        Bit64))))
                                                                                                            BEnd_LittleEndian
                                                                                                            Bit32)
                                                                                                         Bit64)))
                                                                                                Bit32))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Minus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x2"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   56w)))
                                                                                          BEnd_LittleEndian
                                                                                          (BExp_Cast
                                                                                             BIExp_LowCast
                                                                                             (BExp_BinExp
                                                                                                BIExp_And
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      255w))
                                                                                                (BExp_Cast
                                                                                                   BIExp_SignedCast
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_RightShift
                                                                                                      (BExp_Cast
                                                                                                         BIExp_LowCast
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Xor
                                                                                                            (BExp_Cast
                                                                                                               BIExp_SignedCast
                                                                                                               (BExp_Load
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_MEM8"
                                                                                                                        (BType_Mem
                                                                                                                           Bit64
                                                                                                                           Bit8)))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x10"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64)))
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           8w)))
                                                                                                                  BEnd_LittleEndian
                                                                                                                  Bit32)
                                                                                                               Bit64)
                                                                                                            (BExp_Cast
                                                                                                               BIExp_SignedCast
                                                                                                               (BExp_Load
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_MEM8"
                                                                                                                        (BType_Mem
                                                                                                                           Bit64
                                                                                                                           Bit8)))
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Plus
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x12"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64)))
                                                                                                                     (BExp_Const
                                                                                                                        (Imm64
                                                                                                                           8w)))
                                                                                                                  BEnd_LittleEndian
                                                                                                                  Bit32)
                                                                                                               Bit64))
                                                                                                         Bit32)
                                                                                                      (BExp_Const
                                                                                                         (Imm32
                                                                                                            24w)))
                                                                                                   Bit64))
                                                                                             Bit32))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Minus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x2"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                60w)))
                                                                                       BEnd_LittleEndian
                                                                                       (BExp_Cast
                                                                                          BIExp_LowCast
                                                                                          (BExp_BinExp
                                                                                             BIExp_And
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   255w))
                                                                                             (BExp_Cast
                                                                                                BIExp_SignedCast
                                                                                                (BExp_BinExp
                                                                                                   BIExp_RightShift
                                                                                                   (BExp_Cast
                                                                                                      BIExp_LowCast
                                                                                                      (BExp_BinExp
                                                                                                         BIExp_Xor
                                                                                                         (BExp_Cast
                                                                                                            BIExp_SignedCast
                                                                                                            (BExp_Load
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_MEM8"
                                                                                                                     (BType_Mem
                                                                                                                        Bit64
                                                                                                                        Bit8)))
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Plus
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_x10"
                                                                                                                        (BType_Imm
                                                                                                                           Bit64)))
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        12w)))
                                                                                                               BEnd_LittleEndian
                                                                                                               Bit32)
                                                                                                            Bit64)
                                                                                                         (BExp_Cast
                                                                                                            BIExp_SignedCast
                                                                                                            (BExp_Load
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_MEM8"
                                                                                                                     (BType_Mem
                                                                                                                        Bit64
                                                                                                                        Bit8)))
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Plus
                                                                                                                  (BExp_Den
                                                                                                                     (BVar
                                                                                                                        "sy_x12"
                                                                                                                        (BType_Imm
                                                                                                                           Bit64)))
                                                                                                                  (BExp_Const
                                                                                                                     (Imm64
                                                                                                                        12w)))
                                                                                                               BEnd_LittleEndian
                                                                                                               Bit32)
                                                                                                            Bit64))
                                                                                                      Bit32)
                                                                                                   (BExp_Const
                                                                                                      (Imm32
                                                                                                         16w)))
                                                                                                Bit64))
                                                                                          Bit32))
                                                                                    (BExp_BinExp
                                                                                       BIExp_Minus
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_x2"
                                                                                             (BType_Imm
                                                                                                Bit64)))
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             64w)))
                                                                                    BEnd_LittleEndian
                                                                                    (BExp_Cast
                                                                                       BIExp_LowCast
                                                                                       (BExp_BinExp
                                                                                          BIExp_And
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                255w))
                                                                                          (BExp_Cast
                                                                                             BIExp_SignedCast
                                                                                             (BExp_BinExp
                                                                                                BIExp_RightShift
                                                                                                (BExp_Cast
                                                                                                   BIExp_LowCast
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_Xor
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_Load
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_MEM8"
                                                                                                                  (BType_Mem
                                                                                                                     Bit64
                                                                                                                     Bit8)))
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x10"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64)))
                                                                                                            BEnd_LittleEndian
                                                                                                            Bit32)
                                                                                                         Bit64)
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_Load
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_MEM8"
                                                                                                                  (BType_Mem
                                                                                                                     Bit64
                                                                                                                     Bit8)))
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x12"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64)))
                                                                                                            BEnd_LittleEndian
                                                                                                            Bit32)
                                                                                                         Bit64))
                                                                                                   Bit32)
                                                                                                (BExp_Const
                                                                                                   (Imm32
                                                                                                      8w)))
                                                                                             Bit64))
                                                                                       Bit32))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Minus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x2"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          68w)))
                                                                                 BEnd_LittleEndian
                                                                                 (BExp_Cast
                                                                                    BIExp_LowCast
                                                                                    (BExp_BinExp
                                                                                       BIExp_And
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             255w))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Xor
                                                                                          (BExp_Cast
                                                                                             BIExp_SignedCast
                                                                                             (BExp_Load
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_MEM8"
                                                                                                      (BType_Mem
                                                                                                         Bit64
                                                                                                         Bit8)))
                                                                                                (BExp_BinExp
                                                                                                   BIExp_Plus
                                                                                                   (BExp_Den
                                                                                                      (BVar
                                                                                                         "sy_x10"
                                                                                                         (BType_Imm
                                                                                                            Bit64)))
                                                                                                   (BExp_Const
                                                                                                      (Imm64
                                                                                                         4w)))
                                                                                                BEnd_LittleEndian
                                                                                                Bit32)
                                                                                             Bit64)
                                                                                          (BExp_Cast
                                                                                             BIExp_SignedCast
                                                                                             (BExp_Load
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_MEM8"
                                                                                                      (BType_Mem
                                                                                                         Bit64
                                                                                                         Bit8)))
                                                                                                (BExp_BinExp
                                                                                                   BIExp_Plus
                                                                                                   (BExp_Den
                                                                                                      (BVar
                                                                                                         "sy_x12"
                                                                                                         (BType_Imm
                                                                                                            Bit64)))
                                                                                                   (BExp_Const
                                                                                                      (Imm64
                                                                                                         4w)))
                                                                                                BEnd_LittleEndian
                                                                                                Bit32)
                                                                                             Bit64)))
                                                                                    Bit32))
                                                                              (BExp_BinExp
                                                                                 BIExp_Minus
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x2"
                                                                                       (BType_Imm
                                                                                          Bit64)))
                                                                                 (BExp_Const
                                                                                    (Imm64
                                                                                       72w)))
                                                                              BEnd_LittleEndian
                                                                              (BExp_Cast
                                                                                 BIExp_LowCast
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_BinExp
                                                                                             BIExp_LeftShift
                                                                                             (BExp_Cast
                                                                                                BIExp_UnsignedCast
                                                                                                (BExp_Cast
                                                                                                   BIExp_LowCast
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_And
                                                                                                      (BExp_Const
                                                                                                         (Imm64
                                                                                                            255w))
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_RightShift
                                                                                                            (BExp_Cast
                                                                                                               BIExp_LowCast
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Xor
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x10"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 8w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64)
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x12"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 8w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64))
                                                                                                               Bit32)
                                                                                                            (BExp_Const
                                                                                                               (Imm32
                                                                                                                  24w)))
                                                                                                         Bit64))
                                                                                                   Bit32)
                                                                                                Bit64)
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   2w)))
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x14"
                                                                                                (BType_Imm
                                                                                                   Bit64))))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64)
                                                                                 Bit32))
                                                                           (BExp_BinExp
                                                                              BIExp_Minus
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_x2"
                                                                                    (BType_Imm
                                                                                       Bit64)))
                                                                              (BExp_Const
                                                                                 (Imm64
                                                                                    76w)))
                                                                           BEnd_LittleEndian
                                                                           (BExp_Cast
                                                                              BIExp_LowCast
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_BinExp
                                                                                       BIExp_Plus
                                                                                       (BExp_BinExp
                                                                                          BIExp_LeftShift
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Cast
                                                                                                BIExp_UnsignedCast
                                                                                                (BExp_Cast
                                                                                                   BIExp_LowCast
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_And
                                                                                                      (BExp_Const
                                                                                                         (Imm64
                                                                                                            255w))
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_RightShift
                                                                                                            (BExp_Cast
                                                                                                               BIExp_LowCast
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Xor
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x10"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 12w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64)
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x12"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 12w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64))
                                                                                                               Bit32)
                                                                                                            (BExp_Const
                                                                                                               (Imm32
                                                                                                                  16w)))
                                                                                                         Bit64))
                                                                                                   Bit32)
                                                                                                Bit64)
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   256w)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                2w)))
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_x14"
                                                                                             (BType_Imm
                                                                                                Bit64))))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64)
                                                                              Bit32))
                                                                        (BExp_BinExp
                                                                           BIExp_Minus
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_x2"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 80w)))
                                                                        BEnd_LittleEndian
                                                                        (BExp_Cast
                                                                           BIExp_LowCast
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_BinExp
                                                                                       BIExp_LeftShift
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Cast
                                                                                             BIExp_UnsignedCast
                                                                                             (BExp_Cast
                                                                                                BIExp_LowCast
                                                                                                (BExp_BinExp
                                                                                                   BIExp_And
                                                                                                   (BExp_Const
                                                                                                      (Imm64
                                                                                                         255w))
                                                                                                   (BExp_Cast
                                                                                                      BIExp_SignedCast
                                                                                                      (BExp_BinExp
                                                                                                         BIExp_RightShift
                                                                                                         (BExp_Cast
                                                                                                            BIExp_LowCast
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_Xor
                                                                                                               (BExp_Cast
                                                                                                                  BIExp_SignedCast
                                                                                                                  (BExp_Load
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_MEM8"
                                                                                                                           (BType_Mem
                                                                                                                              Bit64
                                                                                                                              Bit8)))
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x10"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64)))
                                                                                                                     BEnd_LittleEndian
                                                                                                                     Bit32)
                                                                                                                  Bit64)
                                                                                                               (BExp_Cast
                                                                                                                  BIExp_SignedCast
                                                                                                                  (BExp_Load
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_MEM8"
                                                                                                                           (BType_Mem
                                                                                                                              Bit64
                                                                                                                              Bit8)))
                                                                                                                     (BExp_Den
                                                                                                                        (BVar
                                                                                                                           "sy_x12"
                                                                                                                           (BType_Imm
                                                                                                                              Bit64)))
                                                                                                                     BEnd_LittleEndian
                                                                                                                     Bit32)
                                                                                                                  Bit64))
                                                                                                            Bit32)
                                                                                                         (BExp_Const
                                                                                                            (Imm32
                                                                                                               8w)))
                                                                                                      Bit64))
                                                                                                Bit32)
                                                                                             Bit64)
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                512w)))
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             2w)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x14"
                                                                                          (BType_Imm
                                                                                             Bit64))))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)
                                                                           Bit32))
                                                                     (BExp_BinExp
                                                                        BIExp_Minus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x2"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              84w)))
                                                                     BEnd_LittleEndian
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_Load
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_MEM8"
                                                                                    (BType_Mem
                                                                                       Bit64
                                                                                       Bit8)))
                                                                              (BExp_BinExp
                                                                                 BIExp_Plus
                                                                                 (BExp_BinExp
                                                                                    BIExp_LeftShift
                                                                                    (BExp_BinExp
                                                                                       BIExp_Plus
                                                                                       (BExp_Cast
                                                                                          BIExp_UnsignedCast
                                                                                          (BExp_Cast
                                                                                             BIExp_LowCast
                                                                                             (BExp_BinExp
                                                                                                BIExp_And
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      255w))
                                                                                                (BExp_BinExp
                                                                                                   BIExp_Xor
                                                                                                   (BExp_Cast
                                                                                                      BIExp_SignedCast
                                                                                                      (BExp_Load
                                                                                                         (BExp_Den
                                                                                                            (BVar
                                                                                                               "sy_MEM8"
                                                                                                               (BType_Mem
                                                                                                                  Bit64
                                                                                                                  Bit8)))
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Plus
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x10"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64)))
                                                                                                            (BExp_Const
                                                                                                               (Imm64
                                                                                                                  4w)))
                                                                                                         BEnd_LittleEndian
                                                                                                         Bit32)
                                                                                                      Bit64)
                                                                                                   (BExp_Cast
                                                                                                      BIExp_SignedCast
                                                                                                      (BExp_Load
                                                                                                         (BExp_Den
                                                                                                            (BVar
                                                                                                               "sy_MEM8"
                                                                                                               (BType_Mem
                                                                                                                  Bit64
                                                                                                                  Bit8)))
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_Plus
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_x12"
                                                                                                                  (BType_Imm
                                                                                                                     Bit64)))
                                                                                                            (BExp_Const
                                                                                                               (Imm64
                                                                                                                  4w)))
                                                                                                         BEnd_LittleEndian
                                                                                                         Bit32)
                                                                                                      Bit64)))
                                                                                             Bit32)
                                                                                          Bit64)
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             768w)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          2w)))
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x14"
                                                                                       (BType_Imm
                                                                                          Bit64))))
                                                                              BEnd_LittleEndian
                                                                              Bit32)
                                                                           Bit64)
                                                                        Bit32))
                                                                  (BExp_BinExp
                                                                     BIExp_Minus
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_x2"
                                                                           (BType_Imm
                                                                              Bit64)))
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           44w)))
                                                                  BEnd_LittleEndian
                                                                  (BExp_Cast
                                                                     BIExp_LowCast
                                                                     (BExp_BinExp
                                                                        BIExp_Xor
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_Load
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_MEM8"
                                                                                    (BType_Mem
                                                                                       Bit64
                                                                                       Bit8)))
                                                                              (BExp_BinExp
                                                                                 BIExp_Plus
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x10"
                                                                                       (BType_Imm
                                                                                          Bit64)))
                                                                                 (BExp_Const
                                                                                    (Imm64
                                                                                       24w)))
                                                                              BEnd_LittleEndian
                                                                              Bit32)
                                                                           Bit64)
                                                                        (BExp_BinExp
                                                                           BIExp_Xor
                                                                           (BExp_BinExp
                                                                              BIExp_Xor
                                                                              (BExp_BinExp
                                                                                 BIExp_Xor
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_BinExp
                                                                                             BIExp_LeftShift
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Cast
                                                                                                   BIExp_UnsignedCast
                                                                                                   (BExp_Cast
                                                                                                      BIExp_LowCast
                                                                                                      (BExp_BinExp
                                                                                                         BIExp_And
                                                                                                         (BExp_Const
                                                                                                            (Imm64
                                                                                                               255w))
                                                                                                         (BExp_Cast
                                                                                                            BIExp_SignedCast
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_RightShift
                                                                                                               (BExp_Cast
                                                                                                                  BIExp_LowCast
                                                                                                                  (BExp_BinExp
                                                                                                                     BIExp_Xor
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_SignedCast
                                                                                                                        (BExp_Load
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_MEM8"
                                                                                                                                 (BType_Mem
                                                                                                                                    Bit64
                                                                                                                                    Bit8)))
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_Plus
                                                                                                                              (BExp_Den
                                                                                                                                 (BVar
                                                                                                                                    "sy_x10"
                                                                                                                                    (BType_Imm
                                                                                                                                       Bit64)))
                                                                                                                              (BExp_Const
                                                                                                                                 (Imm64
                                                                                                                                    12w)))
                                                                                                                           BEnd_LittleEndian
                                                                                                                           Bit32)
                                                                                                                        Bit64)
                                                                                                                     (BExp_Cast
                                                                                                                        BIExp_SignedCast
                                                                                                                        (BExp_Load
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_MEM8"
                                                                                                                                 (BType_Mem
                                                                                                                                    Bit64
                                                                                                                                    Bit8)))
                                                                                                                           (BExp_BinExp
                                                                                                                              BIExp_Plus
                                                                                                                              (BExp_Den
                                                                                                                                 (BVar
                                                                                                                                    "sy_x12"
                                                                                                                                    (BType_Imm
                                                                                                                                       Bit64)))
                                                                                                                              (BExp_Const
                                                                                                                                 (Imm64
                                                                                                                                    12w)))
                                                                                                                           BEnd_LittleEndian
                                                                                                                           Bit32)
                                                                                                                        Bit64))
                                                                                                                  Bit32)
                                                                                                               (BExp_Const
                                                                                                                  (Imm32
                                                                                                                     16w)))
                                                                                                            Bit64))
                                                                                                      Bit32)
                                                                                                   Bit64)
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      256w)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   2w)))
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x14"
                                                                                                (BType_Imm
                                                                                                   Bit64))))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64)
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_BinExp
                                                                                             BIExp_LeftShift
                                                                                             (BExp_Cast
                                                                                                BIExp_UnsignedCast
                                                                                                (BExp_Cast
                                                                                                   BIExp_LowCast
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_And
                                                                                                      (BExp_Const
                                                                                                         (Imm64
                                                                                                            255w))
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_RightShift
                                                                                                            (BExp_Cast
                                                                                                               BIExp_LowCast
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Xor
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x10"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 8w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64)
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_BinExp
                                                                                                                           BIExp_Plus
                                                                                                                           (BExp_Den
                                                                                                                              (BVar
                                                                                                                                 "sy_x12"
                                                                                                                                 (BType_Imm
                                                                                                                                    Bit64)))
                                                                                                                           (BExp_Const
                                                                                                                              (Imm64
                                                                                                                                 8w)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64))
                                                                                                               Bit32)
                                                                                                            (BExp_Const
                                                                                                               (Imm32
                                                                                                                  24w)))
                                                                                                         Bit64))
                                                                                                   Bit32)
                                                                                                Bit64)
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   2w)))
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x14"
                                                                                                (BType_Imm
                                                                                                   Bit64))))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64))
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_BinExp
                                                                                       BIExp_Plus
                                                                                       (BExp_BinExp
                                                                                          BIExp_LeftShift
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Cast
                                                                                                BIExp_UnsignedCast
                                                                                                (BExp_Cast
                                                                                                   BIExp_LowCast
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_And
                                                                                                      (BExp_Const
                                                                                                         (Imm64
                                                                                                            255w))
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_BinExp
                                                                                                            BIExp_RightShift
                                                                                                            (BExp_Cast
                                                                                                               BIExp_LowCast
                                                                                                               (BExp_BinExp
                                                                                                                  BIExp_Xor
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_x10"
                                                                                                                              (BType_Imm
                                                                                                                                 Bit64)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64)
                                                                                                                  (BExp_Cast
                                                                                                                     BIExp_SignedCast
                                                                                                                     (BExp_Load
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_MEM8"
                                                                                                                              (BType_Mem
                                                                                                                                 Bit64
                                                                                                                                 Bit8)))
                                                                                                                        (BExp_Den
                                                                                                                           (BVar
                                                                                                                              "sy_x12"
                                                                                                                              (BType_Imm
                                                                                                                                 Bit64)))
                                                                                                                        BEnd_LittleEndian
                                                                                                                        Bit32)
                                                                                                                     Bit64))
                                                                                                               Bit32)
                                                                                                            (BExp_Const
                                                                                                               (Imm32
                                                                                                                  8w)))
                                                                                                         Bit64))
                                                                                                   Bit32)
                                                                                                Bit64)
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   512w)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                2w)))
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_x14"
                                                                                             (BType_Imm
                                                                                                Bit64))))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64))
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_BinExp
                                                                                       BIExp_LeftShift
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Cast
                                                                                             BIExp_UnsignedCast
                                                                                             (BExp_Cast
                                                                                                BIExp_LowCast
                                                                                                (BExp_BinExp
                                                                                                   BIExp_And
                                                                                                   (BExp_Const
                                                                                                      (Imm64
                                                                                                         255w))
                                                                                                   (BExp_BinExp
                                                                                                      BIExp_Xor
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_Load
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_MEM8"
                                                                                                                  (BType_Mem
                                                                                                                     Bit64
                                                                                                                     Bit8)))
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_Plus
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_x10"
                                                                                                                     (BType_Imm
                                                                                                                        Bit64)))
                                                                                                               (BExp_Const
                                                                                                                  (Imm64
                                                                                                                     4w)))
                                                                                                            BEnd_LittleEndian
                                                                                                            Bit32)
                                                                                                         Bit64)
                                                                                                      (BExp_Cast
                                                                                                         BIExp_SignedCast
                                                                                                         (BExp_Load
                                                                                                            (BExp_Den
                                                                                                               (BVar
                                                                                                                  "sy_MEM8"
                                                                                                                  (BType_Mem
                                                                                                                     Bit64
                                                                                                                     Bit8)))
                                                                                                            (BExp_BinExp
                                                                                                               BIExp_Plus
                                                                                                               (BExp_Den
                                                                                                                  (BVar
                                                                                                                     "sy_x12"
                                                                                                                     (BType_Imm
                                                                                                                        Bit64)))
                                                                                                               (BExp_Const
                                                                                                                  (Imm64
                                                                                                                     4w)))
                                                                                                            BEnd_LittleEndian
                                                                                                            Bit32)
                                                                                                         Bit64)))
                                                                                                Bit32)
                                                                                             Bit64)
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                768w)))
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             2w)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x14"
                                                                                          (BType_Imm
                                                                                             Bit64))))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)))
                                                                     Bit32))
                                                               (BExp_BinExp
                                                                  BIExp_Minus
                                                                  (BExp_Den
                                                                     (BVar
                                                                        "sy_x2"
                                                                        (BType_Imm
                                                                           Bit64)))
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        56w)))
                                                               BEnd_LittleEndian
                                                               (BExp_Cast
                                                                  BIExp_LowCast
                                                                  (BExp_BinExp
                                                                     BIExp_And
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           255w))
                                                                     (BExp_Cast
                                                                        BIExp_SignedCast
                                                                        (BExp_BinExp
                                                                           BIExp_RightShift
                                                                           (BExp_Cast
                                                                              BIExp_LowCast
                                                                              (BExp_BinExp
                                                                                 BIExp_Xor
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x10"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                12w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64)
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x12"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                12w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64))
                                                                              Bit32)
                                                                           (BExp_Const
                                                                              (Imm32
                                                                                 24w)))
                                                                        Bit64))
                                                                  Bit32))
                                                            (BExp_BinExp
                                                               BIExp_Minus
                                                               (BExp_Den
                                                                  (BVar
                                                                     "sy_x2"
                                                                     (BType_Imm
                                                                        Bit64)))
                                                               (BExp_Const
                                                                  (Imm64
                                                                     60w)))
                                                            BEnd_LittleEndian
                                                            (BExp_Cast
                                                               BIExp_LowCast
                                                               (BExp_BinExp
                                                                  BIExp_And
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        255w))
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_BinExp
                                                                        BIExp_RightShift
                                                                        (BExp_Cast
                                                                           BIExp_LowCast
                                                                           (BExp_BinExp
                                                                              BIExp_Xor
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64)
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64))
                                                                           Bit32)
                                                                        (BExp_Const
                                                                           (Imm32
                                                                              16w)))
                                                                     Bit64))
                                                               Bit32))
                                                         (BExp_BinExp
                                                            BIExp_Minus
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x2"
                                                                  (BType_Imm
                                                                     Bit64)))
                                                            (BExp_Const
                                                               (Imm64 64w)))
                                                         BEnd_LittleEndian
                                                         (BExp_Cast
                                                            BIExp_LowCast
                                                            (BExp_BinExp
                                                               BIExp_And
                                                               (BExp_Const
                                                                  (Imm64
                                                                     255w))
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_BinExp
                                                                     BIExp_RightShift
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_Xor
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          4w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          4w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64))
                                                                        Bit32)
                                                                     (BExp_Const
                                                                        (Imm32
                                                                           8w)))
                                                                  Bit64))
                                                            Bit32))
                                                      (BExp_BinExp
                                                         BIExp_Minus
                                                         (BExp_Den
                                                            (BVar "sy_x2"
                                                               (BType_Imm
                                                                  Bit64)))
                                                         (BExp_Const
                                                            (Imm64 68w)))
                                                      BEnd_LittleEndian
                                                      (BExp_Cast
                                                         BIExp_LowCast
                                                         (BExp_BinExp
                                                            BIExp_And
                                                            (BExp_Const
                                                               (Imm64 255w))
                                                            (BExp_BinExp
                                                               BIExp_Xor
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x10"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              8w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x12"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              8w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64)))
                                                         Bit32))
                                                   (BExp_BinExp BIExp_Minus
                                                      (BExp_Den
                                                         (BVar "sy_x2"
                                                            (BType_Imm
                                                               Bit64)))
                                                      (BExp_Const
                                                         (Imm64 72w)))
                                                   BEnd_LittleEndian
                                                   (BExp_Cast BIExp_LowCast
                                                      (BExp_Cast
                                                         BIExp_SignedCast
                                                         (BExp_Load
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_MEM8"
                                                                  (BType_Mem
                                                                     Bit64
                                                                     Bit8)))
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_BinExp
                                                                  BIExp_LeftShift
                                                                  (BExp_Cast
                                                                     BIExp_UnsignedCast
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_And
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 255w))
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_BinExp
                                                                                 BIExp_RightShift
                                                                                 (BExp_Cast
                                                                                    BIExp_LowCast
                                                                                    (BExp_BinExp
                                                                                       BIExp_Xor
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x10"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      12w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64)
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x12"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      12w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64))
                                                                                    Bit32)
                                                                                 (BExp_Const
                                                                                    (Imm32
                                                                                       24w)))
                                                                              Bit64))
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        2w)))
                                                               (BExp_Den
                                                                  (BVar
                                                                     "sy_x14"
                                                                     (BType_Imm
                                                                        Bit64))))
                                                            BEnd_LittleEndian
                                                            Bit32) Bit64)
                                                      Bit32))
                                                (BExp_BinExp BIExp_Minus
                                                   (BExp_Den
                                                      (BVar "sy_x2"
                                                         (BType_Imm Bit64)))
                                                   (BExp_Const (Imm64 76w)))
                                                BEnd_LittleEndian
                                                (BExp_Cast BIExp_LowCast
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_Load
                                                         (BExp_Den
                                                            (BVar "sy_MEM8"
                                                               (BType_Mem
                                                                  Bit64
                                                                  Bit8)))
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_BinExp
                                                               BIExp_LeftShift
                                                               (BExp_BinExp
                                                                  BIExp_Plus
                                                                  (BExp_Cast
                                                                     BIExp_UnsignedCast
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_And
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 255w))
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_BinExp
                                                                                 BIExp_RightShift
                                                                                 (BExp_Cast
                                                                                    BIExp_LowCast
                                                                                    (BExp_BinExp
                                                                                       BIExp_Xor
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x10"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64)
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x12"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64))
                                                                                    Bit32)
                                                                                 (BExp_Const
                                                                                    (Imm32
                                                                                       16w)))
                                                                              Bit64))
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        256w)))
                                                               (BExp_Const
                                                                  (Imm64 2w)))
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x14"
                                                                  (BType_Imm
                                                                     Bit64))))
                                                         BEnd_LittleEndian
                                                         Bit32) Bit64)
                                                   Bit32))
                                             (BExp_BinExp BIExp_Minus
                                                (BExp_Den
                                                   (BVar "sy_x2"
                                                      (BType_Imm Bit64)))
                                                (BExp_Const (Imm64 80w)))
                                             BEnd_LittleEndian
                                             (BExp_Cast BIExp_LowCast
                                                (BExp_Cast BIExp_SignedCast
                                                   (BExp_Load
                                                      (BExp_Den
                                                         (BVar "sy_MEM8"
                                                            (BType_Mem
                                                               Bit64 Bit8)))
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_BinExp
                                                            BIExp_LeftShift
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_Cast
                                                                  BIExp_UnsignedCast
                                                                  (BExp_Cast
                                                                     BIExp_LowCast
                                                                     (BExp_BinExp
                                                                        BIExp_And
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              255w))
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_BinExp
                                                                              BIExp_RightShift
                                                                              (BExp_Cast
                                                                                 BIExp_LowCast
                                                                                 (BExp_BinExp
                                                                                    BIExp_Xor
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x10"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   4w)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64)
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x12"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   4w)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64))
                                                                                 Bit32)
                                                                              (BExp_Const
                                                                                 (Imm32
                                                                                    8w)))
                                                                           Bit64))
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Const
                                                                  (Imm64
                                                                     512w)))
                                                            (BExp_Const
                                                               (Imm64 2w)))
                                                         (BExp_Den
                                                            (BVar "sy_x14"
                                                               (BType_Imm
                                                                  Bit64))))
                                                      BEnd_LittleEndian
                                                      Bit32) Bit64) Bit32))
                                          (BExp_BinExp BIExp_Minus
                                             (BExp_Den
                                                (BVar "sy_x2"
                                                   (BType_Imm Bit64)))
                                             (BExp_Const (Imm64 84w)))
                                          BEnd_LittleEndian
                                          (BExp_Cast BIExp_LowCast
                                             (BExp_Cast BIExp_SignedCast
                                                (BExp_Load
                                                   (BExp_Den
                                                      (BVar "sy_MEM8"
                                                         (BType_Mem Bit64
                                                            Bit8)))
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_BinExp
                                                         BIExp_LeftShift
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_Cast
                                                               BIExp_UnsignedCast
                                                               (BExp_Cast
                                                                  BIExp_LowCast
                                                                  (BExp_BinExp
                                                                     BIExp_And
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           255w))
                                                                     (BExp_BinExp
                                                                        BIExp_Xor
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_Load
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_MEM8"
                                                                                    (BType_Mem
                                                                                       Bit64
                                                                                       Bit8)))
                                                                              (BExp_BinExp
                                                                                 BIExp_Plus
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x10"
                                                                                       (BType_Imm
                                                                                          Bit64)))
                                                                                 (BExp_Const
                                                                                    (Imm64
                                                                                       8w)))
                                                                              BEnd_LittleEndian
                                                                              Bit32)
                                                                           Bit64)
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_Load
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_MEM8"
                                                                                    (BType_Mem
                                                                                       Bit64
                                                                                       Bit8)))
                                                                              (BExp_BinExp
                                                                                 BIExp_Plus
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x12"
                                                                                       (BType_Imm
                                                                                          Bit64)))
                                                                                 (BExp_Const
                                                                                    (Imm64
                                                                                       8w)))
                                                                              BEnd_LittleEndian
                                                                              Bit32)
                                                                           Bit64)))
                                                                  Bit32)
                                                               Bit64)
                                                            (BExp_Const
                                                               (Imm64 768w)))
                                                         (BExp_Const
                                                            (Imm64 2w)))
                                                      (BExp_Den
                                                         (BVar "sy_x14"
                                                            (BType_Imm
                                                               Bit64))))
                                                   BEnd_LittleEndian Bit32)
                                                Bit64) Bit32))
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_Den
                                             (BVar "sy_x2"
                                                (BType_Imm Bit64)))
                                          (BExp_Const (Imm64 48w)))
                                       BEnd_LittleEndian
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_BinExp BIExp_Xor
                                             (BExp_Cast BIExp_SignedCast
                                                (BExp_Load
                                                   (BExp_Den
                                                      (BVar "sy_MEM8"
                                                         (BType_Mem Bit64
                                                            Bit8)))
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_Den
                                                         (BVar "sy_x10"
                                                            (BType_Imm
                                                               Bit64)))
                                                      (BExp_Const
                                                         (Imm64 28w)))
                                                   BEnd_LittleEndian Bit32)
                                                Bit64)
                                             (BExp_BinExp BIExp_Xor
                                                (BExp_BinExp BIExp_Xor
                                                   (BExp_BinExp BIExp_Xor
                                                      (BExp_Cast
                                                         BIExp_SignedCast
                                                         (BExp_Load
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_MEM8"
                                                                  (BType_Mem
                                                                     Bit64
                                                                     Bit8)))
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_BinExp
                                                                  BIExp_LeftShift
                                                                  (BExp_BinExp
                                                                     BIExp_Plus
                                                                     (BExp_Cast
                                                                        BIExp_UnsignedCast
                                                                        (BExp_Cast
                                                                           BIExp_LowCast
                                                                           (BExp_BinExp
                                                                              BIExp_And
                                                                              (BExp_Const
                                                                                 (Imm64
                                                                                    255w))
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_BinExp
                                                                                    BIExp_RightShift
                                                                                    (BExp_Cast
                                                                                       BIExp_LowCast
                                                                                       (BExp_BinExp
                                                                                          BIExp_Xor
                                                                                          (BExp_Cast
                                                                                             BIExp_SignedCast
                                                                                             (BExp_Load
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_MEM8"
                                                                                                      (BType_Mem
                                                                                                         Bit64
                                                                                                         Bit8)))
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x10"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                BEnd_LittleEndian
                                                                                                Bit32)
                                                                                             Bit64)
                                                                                          (BExp_Cast
                                                                                             BIExp_SignedCast
                                                                                             (BExp_Load
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_MEM8"
                                                                                                      (BType_Mem
                                                                                                         Bit64
                                                                                                         Bit8)))
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x12"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                BEnd_LittleEndian
                                                                                                Bit32)
                                                                                             Bit64))
                                                                                       Bit32)
                                                                                    (BExp_Const
                                                                                       (Imm32
                                                                                          16w)))
                                                                                 Bit64))
                                                                           Bit32)
                                                                        Bit64)
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           256w)))
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        2w)))
                                                               (BExp_Den
                                                                  (BVar
                                                                     "sy_x14"
                                                                     (BType_Imm
                                                                        Bit64))))
                                                            BEnd_LittleEndian
                                                            Bit32) Bit64)
                                                      (BExp_Cast
                                                         BIExp_SignedCast
                                                         (BExp_Load
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_MEM8"
                                                                  (BType_Mem
                                                                     Bit64
                                                                     Bit8)))
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_BinExp
                                                                  BIExp_LeftShift
                                                                  (BExp_Cast
                                                                     BIExp_UnsignedCast
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_And
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 255w))
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_BinExp
                                                                                 BIExp_RightShift
                                                                                 (BExp_Cast
                                                                                    BIExp_LowCast
                                                                                    (BExp_BinExp
                                                                                       BIExp_Xor
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x10"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      12w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64)
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x12"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      12w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64))
                                                                                    Bit32)
                                                                                 (BExp_Const
                                                                                    (Imm32
                                                                                       24w)))
                                                                              Bit64))
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        2w)))
                                                               (BExp_Den
                                                                  (BVar
                                                                     "sy_x14"
                                                                     (BType_Imm
                                                                        Bit64))))
                                                            BEnd_LittleEndian
                                                            Bit32) Bit64))
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_Load
                                                         (BExp_Den
                                                            (BVar "sy_MEM8"
                                                               (BType_Mem
                                                                  Bit64
                                                                  Bit8)))
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_BinExp
                                                               BIExp_LeftShift
                                                               (BExp_BinExp
                                                                  BIExp_Plus
                                                                  (BExp_Cast
                                                                     BIExp_UnsignedCast
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_And
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 255w))
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_BinExp
                                                                                 BIExp_RightShift
                                                                                 (BExp_Cast
                                                                                    BIExp_LowCast
                                                                                    (BExp_BinExp
                                                                                       BIExp_Xor
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x10"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      4w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64)
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x12"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      4w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64))
                                                                                    Bit32)
                                                                                 (BExp_Const
                                                                                    (Imm32
                                                                                       8w)))
                                                                              Bit64))
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        512w)))
                                                               (BExp_Const
                                                                  (Imm64 2w)))
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x14"
                                                                  (BType_Imm
                                                                     Bit64))))
                                                         BEnd_LittleEndian
                                                         Bit32) Bit64))
                                                (BExp_Cast BIExp_SignedCast
                                                   (BExp_Load
                                                      (BExp_Den
                                                         (BVar "sy_MEM8"
                                                            (BType_Mem
                                                               Bit64 Bit8)))
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_BinExp
                                                            BIExp_LeftShift
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_Cast
                                                                  BIExp_UnsignedCast
                                                                  (BExp_Cast
                                                                     BIExp_LowCast
                                                                     (BExp_BinExp
                                                                        BIExp_And
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              255w))
                                                                        (BExp_BinExp
                                                                           BIExp_Xor
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          8w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          8w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)))
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Const
                                                                  (Imm64
                                                                     768w)))
                                                            (BExp_Const
                                                               (Imm64 2w)))
                                                         (BExp_Den
                                                            (BVar "sy_x14"
                                                               (BType_Imm
                                                                  Bit64))))
                                                      BEnd_LittleEndian
                                                      Bit32) Bit64))) Bit32))
                                    (BExp_BinExp BIExp_Minus
                                       (BExp_Den
                                          (BVar "sy_x2" (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 20w)))
                                    BEnd_LittleEndian
                                    (BExp_Cast BIExp_LowCast
                                       (BExp_BinExp BIExp_Xor
                                          (BExp_Cast BIExp_SignedCast
                                             (BExp_Load
                                                (BExp_Den
                                                   (BVar "sy_MEM8"
                                                      (BType_Mem Bit64 Bit8)))
                                                (BExp_BinExp BIExp_Plus
                                                   (BExp_Den
                                                      (BVar "sy_x10"
                                                         (BType_Imm Bit64)))
                                                   (BExp_Const (Imm64 16w)))
                                                BEnd_LittleEndian Bit32)
                                             Bit64)
                                          (BExp_BinExp BIExp_Xor
                                             (BExp_BinExp BIExp_Xor
                                                (BExp_BinExp BIExp_Xor
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_Load
                                                         (BExp_Den
                                                            (BVar "sy_MEM8"
                                                               (BType_Mem
                                                                  Bit64
                                                                  Bit8)))
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_BinExp
                                                               BIExp_LeftShift
                                                               (BExp_BinExp
                                                                  BIExp_Plus
                                                                  (BExp_Cast
                                                                     BIExp_UnsignedCast
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_And
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 255w))
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_BinExp
                                                                                 BIExp_RightShift
                                                                                 (BExp_Cast
                                                                                    BIExp_LowCast
                                                                                    (BExp_BinExp
                                                                                       BIExp_Xor
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x10"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      4w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64)
                                                                                       (BExp_Cast
                                                                                          BIExp_SignedCast
                                                                                          (BExp_Load
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_MEM8"
                                                                                                   (BType_Mem
                                                                                                      Bit64
                                                                                                      Bit8)))
                                                                                             (BExp_BinExp
                                                                                                BIExp_Plus
                                                                                                (BExp_Den
                                                                                                   (BVar
                                                                                                      "sy_x12"
                                                                                                      (BType_Imm
                                                                                                         Bit64)))
                                                                                                (BExp_Const
                                                                                                   (Imm64
                                                                                                      4w)))
                                                                                             BEnd_LittleEndian
                                                                                             Bit32)
                                                                                          Bit64))
                                                                                    Bit32)
                                                                                 (BExp_Const
                                                                                    (Imm32
                                                                                       16w)))
                                                                              Bit64))
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        256w)))
                                                               (BExp_Const
                                                                  (Imm64 2w)))
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x14"
                                                                  (BType_Imm
                                                                     Bit64))))
                                                         BEnd_LittleEndian
                                                         Bit32) Bit64)
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_Load
                                                         (BExp_Den
                                                            (BVar "sy_MEM8"
                                                               (BType_Mem
                                                                  Bit64
                                                                  Bit8)))
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_BinExp
                                                               BIExp_LeftShift
                                                               (BExp_Cast
                                                                  BIExp_UnsignedCast
                                                                  (BExp_Cast
                                                                     BIExp_LowCast
                                                                     (BExp_BinExp
                                                                        BIExp_And
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              255w))
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_BinExp
                                                                              BIExp_RightShift
                                                                              (BExp_Cast
                                                                                 BIExp_LowCast
                                                                                 (BExp_BinExp
                                                                                    BIExp_Xor
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x10"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64)
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x12"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64))
                                                                                 Bit32)
                                                                              (BExp_Const
                                                                                 (Imm32
                                                                                    24w)))
                                                                           Bit64))
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Const
                                                                  (Imm64 2w)))
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x14"
                                                                  (BType_Imm
                                                                     Bit64))))
                                                         BEnd_LittleEndian
                                                         Bit32) Bit64))
                                                (BExp_Cast BIExp_SignedCast
                                                   (BExp_Load
                                                      (BExp_Den
                                                         (BVar "sy_MEM8"
                                                            (BType_Mem
                                                               Bit64 Bit8)))
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_BinExp
                                                            BIExp_LeftShift
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_Cast
                                                                  BIExp_UnsignedCast
                                                                  (BExp_Cast
                                                                     BIExp_LowCast
                                                                     (BExp_BinExp
                                                                        BIExp_And
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              255w))
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_BinExp
                                                                              BIExp_RightShift
                                                                              (BExp_Cast
                                                                                 BIExp_LowCast
                                                                                 (BExp_BinExp
                                                                                    BIExp_Xor
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x10"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   8w)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64)
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x12"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   8w)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64))
                                                                                 Bit32)
                                                                              (BExp_Const
                                                                                 (Imm32
                                                                                    8w)))
                                                                           Bit64))
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Const
                                                                  (Imm64
                                                                     512w)))
                                                            (BExp_Const
                                                               (Imm64 2w)))
                                                         (BExp_Den
                                                            (BVar "sy_x14"
                                                               (BType_Imm
                                                                  Bit64))))
                                                      BEnd_LittleEndian
                                                      Bit32) Bit64))
                                             (BExp_Cast BIExp_SignedCast
                                                (BExp_Load
                                                   (BExp_Den
                                                      (BVar "sy_MEM8"
                                                         (BType_Mem Bit64
                                                            Bit8)))
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_BinExp
                                                         BIExp_LeftShift
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_Cast
                                                               BIExp_UnsignedCast
                                                               (BExp_Cast
                                                                  BIExp_LowCast
                                                                  (BExp_BinExp
                                                                     BIExp_And
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           255w))
                                                                     (BExp_BinExp
                                                                        BIExp_Xor
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_Load
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_MEM8"
                                                                                    (BType_Mem
                                                                                       Bit64
                                                                                       Bit8)))
                                                                              (BExp_BinExp
                                                                                 BIExp_Plus
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x10"
                                                                                       (BType_Imm
                                                                                          Bit64)))
                                                                                 (BExp_Const
                                                                                    (Imm64
                                                                                       12w)))
                                                                              BEnd_LittleEndian
                                                                              Bit32)
                                                                           Bit64)
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_Load
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "sy_MEM8"
                                                                                    (BType_Mem
                                                                                       Bit64
                                                                                       Bit8)))
                                                                              (BExp_BinExp
                                                                                 BIExp_Plus
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_x12"
                                                                                       (BType_Imm
                                                                                          Bit64)))
                                                                                 (BExp_Const
                                                                                    (Imm64
                                                                                       12w)))
                                                                              BEnd_LittleEndian
                                                                              Bit32)
                                                                           Bit64)))
                                                                  Bit32)
                                                               Bit64)
                                                            (BExp_Const
                                                               (Imm64 768w)))
                                                         (BExp_Const
                                                            (Imm64 2w)))
                                                      (BExp_Den
                                                         (BVar "sy_x14"
                                                            (BType_Imm
                                                               Bit64))))
                                                   BEnd_LittleEndian Bit32)
                                                Bit64))) Bit32))
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_Den
                                       (BVar "sy_x2" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 24w)))
                                 BEnd_LittleEndian
                                 (BExp_Cast BIExp_LowCast
                                    (BExp_BinExp BIExp_Xor
                                       (BExp_Cast BIExp_SignedCast
                                          (BExp_Load
                                             (BExp_Den
                                                (BVar "sy_MEM8"
                                                   (BType_Mem Bit64 Bit8)))
                                             (BExp_BinExp BIExp_Plus
                                                (BExp_Den
                                                   (BVar "sy_x10"
                                                      (BType_Imm Bit64)))
                                                (BExp_Const (Imm64 20w)))
                                             BEnd_LittleEndian Bit32) Bit64)
                                       (BExp_BinExp BIExp_Xor
                                          (BExp_BinExp BIExp_Xor
                                             (BExp_BinExp BIExp_Xor
                                                (BExp_Cast BIExp_SignedCast
                                                   (BExp_Load
                                                      (BExp_Den
                                                         (BVar "sy_MEM8"
                                                            (BType_Mem
                                                               Bit64 Bit8)))
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_BinExp
                                                            BIExp_LeftShift
                                                            (BExp_BinExp
                                                               BIExp_Plus
                                                               (BExp_Cast
                                                                  BIExp_UnsignedCast
                                                                  (BExp_Cast
                                                                     BIExp_LowCast
                                                                     (BExp_BinExp
                                                                        BIExp_And
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              255w))
                                                                        (BExp_Cast
                                                                           BIExp_SignedCast
                                                                           (BExp_BinExp
                                                                              BIExp_RightShift
                                                                              (BExp_Cast
                                                                                 BIExp_LowCast
                                                                                 (BExp_BinExp
                                                                                    BIExp_Xor
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x10"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   8w)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64)
                                                                                    (BExp_Cast
                                                                                       BIExp_SignedCast
                                                                                       (BExp_Load
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_MEM8"
                                                                                                (BType_Mem
                                                                                                   Bit64
                                                                                                   Bit8)))
                                                                                          (BExp_BinExp
                                                                                             BIExp_Plus
                                                                                             (BExp_Den
                                                                                                (BVar
                                                                                                   "sy_x12"
                                                                                                   (BType_Imm
                                                                                                      Bit64)))
                                                                                             (BExp_Const
                                                                                                (Imm64
                                                                                                   8w)))
                                                                                          BEnd_LittleEndian
                                                                                          Bit32)
                                                                                       Bit64))
                                                                                 Bit32)
                                                                              (BExp_Const
                                                                                 (Imm32
                                                                                    16w)))
                                                                           Bit64))
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Const
                                                                  (Imm64
                                                                     256w)))
                                                            (BExp_Const
                                                               (Imm64 2w)))
                                                         (BExp_Den
                                                            (BVar "sy_x14"
                                                               (BType_Imm
                                                                  Bit64))))
                                                      BEnd_LittleEndian
                                                      Bit32) Bit64)
                                                (BExp_Cast BIExp_SignedCast
                                                   (BExp_Load
                                                      (BExp_Den
                                                         (BVar "sy_MEM8"
                                                            (BType_Mem
                                                               Bit64 Bit8)))
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_BinExp
                                                            BIExp_LeftShift
                                                            (BExp_Cast
                                                               BIExp_UnsignedCast
                                                               (BExp_Cast
                                                                  BIExp_LowCast
                                                                  (BExp_BinExp
                                                                     BIExp_And
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           255w))
                                                                     (BExp_Cast
                                                                        BIExp_SignedCast
                                                                        (BExp_BinExp
                                                                           BIExp_RightShift
                                                                           (BExp_Cast
                                                                              BIExp_LowCast
                                                                              (BExp_BinExp
                                                                                 BIExp_Xor
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x10"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                4w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64)
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x12"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                4w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64))
                                                                              Bit32)
                                                                           (BExp_Const
                                                                              (Imm32
                                                                                 24w)))
                                                                        Bit64))
                                                                  Bit32)
                                                               Bit64)
                                                            (BExp_Const
                                                               (Imm64 2w)))
                                                         (BExp_Den
                                                            (BVar "sy_x14"
                                                               (BType_Imm
                                                                  Bit64))))
                                                      BEnd_LittleEndian
                                                      Bit32) Bit64))
                                             (BExp_Cast BIExp_SignedCast
                                                (BExp_Load
                                                   (BExp_Den
                                                      (BVar "sy_MEM8"
                                                         (BType_Mem Bit64
                                                            Bit8)))
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_BinExp
                                                         BIExp_LeftShift
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_Cast
                                                               BIExp_UnsignedCast
                                                               (BExp_Cast
                                                                  BIExp_LowCast
                                                                  (BExp_BinExp
                                                                     BIExp_And
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           255w))
                                                                     (BExp_Cast
                                                                        BIExp_SignedCast
                                                                        (BExp_BinExp
                                                                           BIExp_RightShift
                                                                           (BExp_Cast
                                                                              BIExp_LowCast
                                                                              (BExp_BinExp
                                                                                 BIExp_Xor
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x10"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                12w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64)
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x12"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                12w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64))
                                                                              Bit32)
                                                                           (BExp_Const
                                                                              (Imm32
                                                                                 8w)))
                                                                        Bit64))
                                                                  Bit32)
                                                               Bit64)
                                                            (BExp_Const
                                                               (Imm64 512w)))
                                                         (BExp_Const
                                                            (Imm64 2w)))
                                                      (BExp_Den
                                                         (BVar "sy_x14"
                                                            (BType_Imm
                                                               Bit64))))
                                                   BEnd_LittleEndian Bit32)
                                                Bit64))
                                          (BExp_Cast BIExp_SignedCast
                                             (BExp_Load
                                                (BExp_Den
                                                   (BVar "sy_MEM8"
                                                      (BType_Mem Bit64 Bit8)))
                                                (BExp_BinExp BIExp_Plus
                                                   (BExp_BinExp
                                                      BIExp_LeftShift
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_Cast
                                                            BIExp_UnsignedCast
                                                            (BExp_Cast
                                                               BIExp_LowCast
                                                               (BExp_BinExp
                                                                  BIExp_And
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        255w))
                                                                  (BExp_BinExp
                                                                     BIExp_Xor
                                                                     (BExp_Cast
                                                                        BIExp_SignedCast
                                                                        (BExp_Load
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_MEM8"
                                                                                 (BType_Mem
                                                                                    Bit64
                                                                                    Bit8)))
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_x10"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           BEnd_LittleEndian
                                                                           Bit32)
                                                                        Bit64)
                                                                     (BExp_Cast
                                                                        BIExp_SignedCast
                                                                        (BExp_Load
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_MEM8"
                                                                                 (BType_Mem
                                                                                    Bit64
                                                                                    Bit8)))
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_x12"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           BEnd_LittleEndian
                                                                           Bit32)
                                                                        Bit64)))
                                                               Bit32) Bit64)
                                                         (BExp_Const
                                                            (Imm64 768w)))
                                                      (BExp_Const
                                                         (Imm64 2w)))
                                                   (BExp_Den
                                                      (BVar "sy_x14"
                                                         (BType_Imm Bit64))))
                                                BEnd_LittleEndian Bit32)
                                             Bit64))) Bit32))
                              (BExp_BinExp BIExp_Minus
                                 (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 28w)))
                              BEnd_LittleEndian
                              (BExp_Cast BIExp_LowCast
                                 (BExp_BinExp BIExp_Xor
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Load
                                          (BExp_Den
                                             (BVar "sy_MEM8"
                                                (BType_Mem Bit64 Bit8)))
                                          (BExp_BinExp BIExp_Plus
                                             (BExp_Den
                                                (BVar "sy_x10"
                                                   (BType_Imm Bit64)))
                                             (BExp_Const (Imm64 24w)))
                                          BEnd_LittleEndian Bit32) Bit64)
                                    (BExp_BinExp BIExp_Xor
                                       (BExp_BinExp BIExp_Xor
                                          (BExp_BinExp BIExp_Xor
                                             (BExp_Cast BIExp_SignedCast
                                                (BExp_Load
                                                   (BExp_Den
                                                      (BVar "sy_MEM8"
                                                         (BType_Mem Bit64
                                                            Bit8)))
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_BinExp
                                                         BIExp_LeftShift
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_Cast
                                                               BIExp_UnsignedCast
                                                               (BExp_Cast
                                                                  BIExp_LowCast
                                                                  (BExp_BinExp
                                                                     BIExp_And
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           255w))
                                                                     (BExp_Cast
                                                                        BIExp_SignedCast
                                                                        (BExp_BinExp
                                                                           BIExp_RightShift
                                                                           (BExp_Cast
                                                                              BIExp_LowCast
                                                                              (BExp_BinExp
                                                                                 BIExp_Xor
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x10"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                12w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64)
                                                                                 (BExp_Cast
                                                                                    BIExp_SignedCast
                                                                                    (BExp_Load
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_MEM8"
                                                                                             (BType_Mem
                                                                                                Bit64
                                                                                                Bit8)))
                                                                                       (BExp_BinExp
                                                                                          BIExp_Plus
                                                                                          (BExp_Den
                                                                                             (BVar
                                                                                                "sy_x12"
                                                                                                (BType_Imm
                                                                                                   Bit64)))
                                                                                          (BExp_Const
                                                                                             (Imm64
                                                                                                12w)))
                                                                                       BEnd_LittleEndian
                                                                                       Bit32)
                                                                                    Bit64))
                                                                              Bit32)
                                                                           (BExp_Const
                                                                              (Imm32
                                                                                 16w)))
                                                                        Bit64))
                                                                  Bit32)
                                                               Bit64)
                                                            (BExp_Const
                                                               (Imm64 256w)))
                                                         (BExp_Const
                                                            (Imm64 2w)))
                                                      (BExp_Den
                                                         (BVar "sy_x14"
                                                            (BType_Imm
                                                               Bit64))))
                                                   BEnd_LittleEndian Bit32)
                                                Bit64)
                                             (BExp_Cast BIExp_SignedCast
                                                (BExp_Load
                                                   (BExp_Den
                                                      (BVar "sy_MEM8"
                                                         (BType_Mem Bit64
                                                            Bit8)))
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_BinExp
                                                         BIExp_LeftShift
                                                         (BExp_Cast
                                                            BIExp_UnsignedCast
                                                            (BExp_Cast
                                                               BIExp_LowCast
                                                               (BExp_BinExp
                                                                  BIExp_And
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        255w))
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_BinExp
                                                                        BIExp_RightShift
                                                                        (BExp_Cast
                                                                           BIExp_LowCast
                                                                           (BExp_BinExp
                                                                              BIExp_Xor
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_BinExp
                                                                                       BIExp_Plus
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_x10"
                                                                                             (BType_Imm
                                                                                                Bit64)))
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             8w)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64)
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_BinExp
                                                                                       BIExp_Plus
                                                                                       (BExp_Den
                                                                                          (BVar
                                                                                             "sy_x12"
                                                                                             (BType_Imm
                                                                                                Bit64)))
                                                                                       (BExp_Const
                                                                                          (Imm64
                                                                                             8w)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64))
                                                                           Bit32)
                                                                        (BExp_Const
                                                                           (Imm32
                                                                              24w)))
                                                                     Bit64))
                                                               Bit32) Bit64)
                                                         (BExp_Const
                                                            (Imm64 2w)))
                                                      (BExp_Den
                                                         (BVar "sy_x14"
                                                            (BType_Imm
                                                               Bit64))))
                                                   BEnd_LittleEndian Bit32)
                                                Bit64))
                                          (BExp_Cast BIExp_SignedCast
                                             (BExp_Load
                                                (BExp_Den
                                                   (BVar "sy_MEM8"
                                                      (BType_Mem Bit64 Bit8)))
                                                (BExp_BinExp BIExp_Plus
                                                   (BExp_BinExp
                                                      BIExp_LeftShift
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_Cast
                                                            BIExp_UnsignedCast
                                                            (BExp_Cast
                                                               BIExp_LowCast
                                                               (BExp_BinExp
                                                                  BIExp_And
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        255w))
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_BinExp
                                                                        BIExp_RightShift
                                                                        (BExp_Cast
                                                                           BIExp_LowCast
                                                                           (BExp_BinExp
                                                                              BIExp_Xor
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64)
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64))
                                                                           Bit32)
                                                                        (BExp_Const
                                                                           (Imm32
                                                                              8w)))
                                                                     Bit64))
                                                               Bit32) Bit64)
                                                         (BExp_Const
                                                            (Imm64 512w)))
                                                      (BExp_Const
                                                         (Imm64 2w)))
                                                   (BExp_Den
                                                      (BVar "sy_x14"
                                                         (BType_Imm Bit64))))
                                                BEnd_LittleEndian Bit32)
                                             Bit64))
                                       (BExp_Cast BIExp_SignedCast
                                          (BExp_Load
                                             (BExp_Den
                                                (BVar "sy_MEM8"
                                                   (BType_Mem Bit64 Bit8)))
                                             (BExp_BinExp BIExp_Plus
                                                (BExp_BinExp
                                                   BIExp_LeftShift
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_Cast
                                                         BIExp_UnsignedCast
                                                         (BExp_Cast
                                                            BIExp_LowCast
                                                            (BExp_BinExp
                                                               BIExp_And
                                                               (BExp_Const
                                                                  (Imm64
                                                                     255w))
                                                               (BExp_BinExp
                                                                  BIExp_Xor
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_Load
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_MEM8"
                                                                              (BType_Mem
                                                                                 Bit64
                                                                                 Bit8)))
                                                                        (BExp_BinExp
                                                                           BIExp_Plus
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_x10"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 4w)))
                                                                        BEnd_LittleEndian
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_Load
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_MEM8"
                                                                              (BType_Mem
                                                                                 Bit64
                                                                                 Bit8)))
                                                                        (BExp_BinExp
                                                                           BIExp_Plus
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "sy_x12"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 4w)))
                                                                        BEnd_LittleEndian
                                                                        Bit32)
                                                                     Bit64)))
                                                            Bit32) Bit64)
                                                      (BExp_Const
                                                         (Imm64 768w)))
                                                   (BExp_Const (Imm64 2w)))
                                                (BExp_Den
                                                   (BVar "sy_x14"
                                                      (BType_Imm Bit64))))
                                             BEnd_LittleEndian Bit32) Bit64)))
                                 Bit32))
                           (BExp_BinExp BIExp_Minus
                              (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 32w))) BEnd_LittleEndian
                           (BExp_Cast BIExp_LowCast
                              (BExp_BinExp BIExp_Xor
                                 (BExp_Cast BIExp_SignedCast
                                    (BExp_Load
                                       (BExp_Den
                                          (BVar "sy_MEM8"
                                             (BType_Mem Bit64 Bit8)))
                                       (BExp_BinExp BIExp_Plus
                                          (BExp_Den
                                             (BVar "sy_x10"
                                                (BType_Imm Bit64)))
                                          (BExp_Const (Imm64 28w)))
                                       BEnd_LittleEndian Bit32) Bit64)
                                 (BExp_BinExp BIExp_Xor
                                    (BExp_BinExp BIExp_Xor
                                       (BExp_BinExp BIExp_Xor
                                          (BExp_Cast BIExp_SignedCast
                                             (BExp_Load
                                                (BExp_Den
                                                   (BVar "sy_MEM8"
                                                      (BType_Mem Bit64 Bit8)))
                                                (BExp_BinExp BIExp_Plus
                                                   (BExp_BinExp
                                                      BIExp_LeftShift
                                                      (BExp_BinExp
                                                         BIExp_Plus
                                                         (BExp_Cast
                                                            BIExp_UnsignedCast
                                                            (BExp_Cast
                                                               BIExp_LowCast
                                                               (BExp_BinExp
                                                                  BIExp_And
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        255w))
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_BinExp
                                                                        BIExp_RightShift
                                                                        (BExp_Cast
                                                                           BIExp_LowCast
                                                                           (BExp_BinExp
                                                                              BIExp_Xor
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64)
                                                                              (BExp_Cast
                                                                                 BIExp_SignedCast
                                                                                 (BExp_Load
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_MEM8"
                                                                                          (BType_Mem
                                                                                             Bit64
                                                                                             Bit8)))
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    BEnd_LittleEndian
                                                                                    Bit32)
                                                                                 Bit64))
                                                                           Bit32)
                                                                        (BExp_Const
                                                                           (Imm32
                                                                              16w)))
                                                                     Bit64))
                                                               Bit32) Bit64)
                                                         (BExp_Const
                                                            (Imm64 256w)))
                                                      (BExp_Const
                                                         (Imm64 2w)))
                                                   (BExp_Den
                                                      (BVar "sy_x14"
                                                         (BType_Imm Bit64))))
                                                BEnd_LittleEndian Bit32)
                                             Bit64)
                                          (BExp_Cast BIExp_SignedCast
                                             (BExp_Load
                                                (BExp_Den
                                                   (BVar "sy_MEM8"
                                                      (BType_Mem Bit64 Bit8)))
                                                (BExp_BinExp BIExp_Plus
                                                   (BExp_BinExp
                                                      BIExp_LeftShift
                                                      (BExp_Cast
                                                         BIExp_UnsignedCast
                                                         (BExp_Cast
                                                            BIExp_LowCast
                                                            (BExp_BinExp
                                                               BIExp_And
                                                               (BExp_Const
                                                                  (Imm64
                                                                     255w))
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_BinExp
                                                                     BIExp_RightShift
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_Xor
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          12w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          12w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64))
                                                                        Bit32)
                                                                     (BExp_Const
                                                                        (Imm32
                                                                           24w)))
                                                                  Bit64))
                                                            Bit32) Bit64)
                                                      (BExp_Const
                                                         (Imm64 2w)))
                                                   (BExp_Den
                                                      (BVar "sy_x14"
                                                         (BType_Imm Bit64))))
                                                BEnd_LittleEndian Bit32)
                                             Bit64))
                                       (BExp_Cast BIExp_SignedCast
                                          (BExp_Load
                                             (BExp_Den
                                                (BVar "sy_MEM8"
                                                   (BType_Mem Bit64 Bit8)))
                                             (BExp_BinExp BIExp_Plus
                                                (BExp_BinExp
                                                   BIExp_LeftShift
                                                   (BExp_BinExp BIExp_Plus
                                                      (BExp_Cast
                                                         BIExp_UnsignedCast
                                                         (BExp_Cast
                                                            BIExp_LowCast
                                                            (BExp_BinExp
                                                               BIExp_And
                                                               (BExp_Const
                                                                  (Imm64
                                                                     255w))
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_BinExp
                                                                     BIExp_RightShift
                                                                     (BExp_Cast
                                                                        BIExp_LowCast
                                                                        (BExp_BinExp
                                                                           BIExp_Xor
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x10"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          4w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64)
                                                                           (BExp_Cast
                                                                              BIExp_SignedCast
                                                                              (BExp_Load
                                                                                 (BExp_Den
                                                                                    (BVar
                                                                                       "sy_MEM8"
                                                                                       (BType_Mem
                                                                                          Bit64
                                                                                          Bit8)))
                                                                                 (BExp_BinExp
                                                                                    BIExp_Plus
                                                                                    (BExp_Den
                                                                                       (BVar
                                                                                          "sy_x12"
                                                                                          (BType_Imm
                                                                                             Bit64)))
                                                                                    (BExp_Const
                                                                                       (Imm64
                                                                                          4w)))
                                                                                 BEnd_LittleEndian
                                                                                 Bit32)
                                                                              Bit64))
                                                                        Bit32)
                                                                     (BExp_Const
                                                                        (Imm32
                                                                           8w)))
                                                                  Bit64))
                                                            Bit32) Bit64)
                                                      (BExp_Const
                                                         (Imm64 512w)))
                                                   (BExp_Const (Imm64 2w)))
                                                (BExp_Den
                                                   (BVar "sy_x14"
                                                      (BType_Imm Bit64))))
                                             BEnd_LittleEndian Bit32) Bit64))
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Load
                                          (BExp_Den
                                             (BVar "sy_MEM8"
                                                (BType_Mem Bit64 Bit8)))
                                          (BExp_BinExp BIExp_Plus
                                             (BExp_BinExp BIExp_LeftShift
                                                (BExp_BinExp BIExp_Plus
                                                   (BExp_Cast
                                                      BIExp_UnsignedCast
                                                      (BExp_Cast
                                                         BIExp_LowCast
                                                         (BExp_BinExp
                                                            BIExp_And
                                                            (BExp_Const
                                                               (Imm64 255w))
                                                            (BExp_BinExp
                                                               BIExp_Xor
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x10"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              8w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x12"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              8w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64)))
                                                         Bit32) Bit64)
                                                   (BExp_Const (Imm64 768w)))
                                                (BExp_Const (Imm64 2w)))
                                             (BExp_Den
                                                (BVar "sy_x14"
                                                   (BType_Imm Bit64))))
                                          BEnd_LittleEndian Bit32) Bit64)))
                              Bit32))
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "sy_x10" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 32w))));
                     ("x14",
                      BExp_BinExp BIExp_Xor
                        (BExp_BinExp BIExp_Xor
                           (BExp_BinExp BIExp_Xor
                              (BExp_Cast BIExp_SignedCast
                                 (BExp_Load
                                    (BExp_Den
                                       (BVar "sy_MEM8"
                                          (BType_Mem Bit64 Bit8)))
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_BinExp BIExp_LeftShift
                                          (BExp_BinExp BIExp_Plus
                                             (BExp_Cast BIExp_UnsignedCast
                                                (BExp_Cast BIExp_LowCast
                                                   (BExp_BinExp BIExp_And
                                                      (BExp_Const
                                                         (Imm64 255w))
                                                      (BExp_Cast
                                                         BIExp_SignedCast
                                                         (BExp_BinExp
                                                            BIExp_RightShift
                                                            (BExp_Cast
                                                               BIExp_LowCast
                                                               (BExp_BinExp
                                                                  BIExp_Xor
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_Load
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_MEM8"
                                                                              (BType_Mem
                                                                                 Bit64
                                                                                 Bit8)))
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x10"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        BEnd_LittleEndian
                                                                        Bit32)
                                                                     Bit64)
                                                                  (BExp_Cast
                                                                     BIExp_SignedCast
                                                                     (BExp_Load
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_MEM8"
                                                                              (BType_Mem
                                                                                 Bit64
                                                                                 Bit8)))
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x12"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        BEnd_LittleEndian
                                                                        Bit32)
                                                                     Bit64))
                                                               Bit32)
                                                            (BExp_Const
                                                               (Imm32 16w)))
                                                         Bit64)) Bit32)
                                                Bit64)
                                             (BExp_Const (Imm64 256w)))
                                          (BExp_Const (Imm64 2w)))
                                       (BExp_Den
                                          (BVar "sy_x14" (BType_Imm Bit64))))
                                    BEnd_LittleEndian Bit32) Bit64)
                              (BExp_Cast BIExp_SignedCast
                                 (BExp_Load
                                    (BExp_Den
                                       (BVar "sy_MEM8"
                                          (BType_Mem Bit64 Bit8)))
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_BinExp BIExp_LeftShift
                                          (BExp_Cast BIExp_UnsignedCast
                                             (BExp_Cast BIExp_LowCast
                                                (BExp_BinExp BIExp_And
                                                   (BExp_Const (Imm64 255w))
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_BinExp
                                                         BIExp_RightShift
                                                         (BExp_Cast
                                                            BIExp_LowCast
                                                            (BExp_BinExp
                                                               BIExp_Xor
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x10"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              12w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x12"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              12w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64))
                                                            Bit32)
                                                         (BExp_Const
                                                            (Imm32 24w)))
                                                      Bit64)) Bit32) Bit64)
                                          (BExp_Const (Imm64 2w)))
                                       (BExp_Den
                                          (BVar "sy_x14" (BType_Imm Bit64))))
                                    BEnd_LittleEndian Bit32) Bit64))
                           (BExp_Cast BIExp_SignedCast
                              (BExp_Load
                                 (BExp_Den
                                    (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                                 (BExp_BinExp BIExp_Plus
                                    (BExp_BinExp BIExp_LeftShift
                                       (BExp_BinExp BIExp_Plus
                                          (BExp_Cast BIExp_UnsignedCast
                                             (BExp_Cast BIExp_LowCast
                                                (BExp_BinExp BIExp_And
                                                   (BExp_Const (Imm64 255w))
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_BinExp
                                                         BIExp_RightShift
                                                         (BExp_Cast
                                                            BIExp_LowCast
                                                            (BExp_BinExp
                                                               BIExp_Xor
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x10"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              4w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64)
                                                               (BExp_Cast
                                                                  BIExp_SignedCast
                                                                  (BExp_Load
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "sy_MEM8"
                                                                           (BType_Mem
                                                                              Bit64
                                                                              Bit8)))
                                                                     (BExp_BinExp
                                                                        BIExp_Plus
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "sy_x12"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              4w)))
                                                                     BEnd_LittleEndian
                                                                     Bit32)
                                                                  Bit64))
                                                            Bit32)
                                                         (BExp_Const
                                                            (Imm32 8w)))
                                                      Bit64)) Bit32) Bit64)
                                          (BExp_Const (Imm64 512w)))
                                       (BExp_Const (Imm64 2w)))
                                    (BExp_Den
                                       (BVar "sy_x14" (BType_Imm Bit64))))
                                 BEnd_LittleEndian Bit32) Bit64))
                        (BExp_Cast BIExp_SignedCast
                           (BExp_Load
                              (BExp_Den
                                 (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                              (BExp_BinExp BIExp_Plus
                                 (BExp_BinExp BIExp_LeftShift
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_Cast BIExp_UnsignedCast
                                          (BExp_Cast BIExp_LowCast
                                             (BExp_BinExp BIExp_And
                                                (BExp_Const (Imm64 255w))
                                                (BExp_BinExp BIExp_Xor
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_Load
                                                         (BExp_Den
                                                            (BVar "sy_MEM8"
                                                               (BType_Mem
                                                                  Bit64
                                                                  Bit8)))
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x10"
                                                                  (BType_Imm
                                                                     Bit64)))
                                                            (BExp_Const
                                                               (Imm64 8w)))
                                                         BEnd_LittleEndian
                                                         Bit32) Bit64)
                                                   (BExp_Cast
                                                      BIExp_SignedCast
                                                      (BExp_Load
                                                         (BExp_Den
                                                            (BVar "sy_MEM8"
                                                               (BType_Mem
                                                                  Bit64
                                                                  Bit8)))
                                                         (BExp_BinExp
                                                            BIExp_Plus
                                                            (BExp_Den
                                                               (BVar
                                                                  "sy_x12"
                                                                  (BType_Imm
                                                                     Bit64)))
                                                            (BExp_Const
                                                               (Imm64 8w)))
                                                         BEnd_LittleEndian
                                                         Bit32) Bit64)))
                                             Bit32) Bit64)
                                       (BExp_Const (Imm64 768w)))
                                    (BExp_Const (Imm64 2w)))
                                 (BExp_Den
                                    (BVar "sy_x14" (BType_Imm Bit64))))
                              BEnd_LittleEndian Bit32) Bit64));
                     ("x15",
                      BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "sy_x11" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 2w)));
                     ("x8",
                      BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 0w)));
                     ("x2",
                      BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 144w)));
                     ("x11",BExp_Den (BVar "sy_x11" (BType_Imm Bit64)));
                     ("x12",BExp_Den (BVar "sy_x12" (BType_Imm Bit64)));
                     ("x13",BExp_Den (BVar "sy_x13" (BType_Imm Bit64)));
                     ("x10",BExp_Den (BVar "sy_x10" (BType_Imm Bit64)));
                     ("x1",BExp_Den (BVar "sy_x1" (BType_Imm Bit64)))];
                bsst_status := BST_Running;
                bsst_pcond :=
                  BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_Equal
                          (BExp_Den (BVar "sy_x11" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 14w)))
                       (BExp_BinExp BIExp_And
                          (BExp_BinPred BIExp_LessThan
                             (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                             (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))))
                          (BExp_BinExp BIExp_And
                             (BExp_BinPred BIExp_LessThan
                                (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                                (BExp_Den (BVar "sy_x12" (BType_Imm Bit64))))
                             (BExp_BinExp BIExp_And
                                (BExp_BinPred BIExp_LessThan
                                   (BExp_Den
                                      (BVar "sy_x2" (BType_Imm Bit64)))
                                   (BExp_Den
                                      (BVar "sy_x14" (BType_Imm Bit64))))
                                (BExp_BinExp BIExp_And
                                   (BExp_BinExp BIExp_And
                                      (BExp_BinPred BIExp_LessThan
                                         (BExp_Den
                                            (BVar "sy_x10"
                                               (BType_Imm Bit64)))
                                         (BExp_BinExp BIExp_Plus
                                            (BExp_Den
                                               (BVar "sy_x10"
                                                  (BType_Imm Bit64)))
                                            (BExp_Const (Imm64 239w))))
                                      (BExp_BinExp BIExp_And
                                         (BExp_BinPred BIExp_LessThan
                                            (BExp_Den
                                               (BVar "sy_x12"
                                                  (BType_Imm Bit64)))
                                            (BExp_BinExp BIExp_Plus
                                               (BExp_Den
                                                  (BVar "sy_x12"
                                                     (BType_Imm Bit64)))
                                               (BExp_Const (Imm64 15w))))
                                         (BExp_BinExp BIExp_Or
                                            (BExp_BinPred BIExp_LessThan
                                               (BExp_BinExp BIExp_Plus
                                                  (BExp_Den
                                                     (BVar "sy_x10"
                                                        (BType_Imm Bit64)))
                                                  (BExp_Const (Imm64 239w)))
                                               (BExp_Den
                                                  (BVar "sy_x12"
                                                     (BType_Imm Bit64))))
                                            (BExp_BinPred BIExp_LessThan
                                               (BExp_BinExp BIExp_Plus
                                                  (BExp_Den
                                                     (BVar "sy_x12"
                                                        (BType_Imm Bit64)))
                                                  (BExp_Const (Imm64 15w)))
                                               (BExp_Den
                                                  (BVar "sy_x10"
                                                     (BType_Imm Bit64)))))))
                                   (BExp_BinExp BIExp_And
                                      (BExp_BinExp BIExp_And
                                         (BExp_BinPred BIExp_LessThan
                                            (BExp_Den
                                               (BVar "sy_x14"
                                                  (BType_Imm Bit64)))
                                            (BExp_BinExp BIExp_Plus
                                               (BExp_Den
                                                  (BVar "sy_x14"
                                                     (BType_Imm Bit64)))
                                               (BExp_Const (Imm64 4095w))))
                                         (BExp_BinExp BIExp_And
                                            (BExp_BinPred BIExp_LessThan
                                               (BExp_Den
                                                  (BVar "sy_x12"
                                                     (BType_Imm Bit64)))
                                               (BExp_BinExp BIExp_Plus
                                                  (BExp_Den
                                                     (BVar "sy_x12"
                                                        (BType_Imm Bit64)))
                                                  (BExp_Const (Imm64 15w))))
                                            (BExp_BinExp BIExp_Or
                                               (BExp_BinPred BIExp_LessThan
                                                  (BExp_BinExp BIExp_Plus
                                                     (BExp_Den
                                                        (BVar "sy_x14"
                                                           (BType_Imm Bit64)))
                                                     (BExp_Const
                                                        (Imm64 4095w)))
                                                  (BExp_Den
                                                     (BVar "sy_x12"
                                                        (BType_Imm Bit64))))
                                               (BExp_BinPred BIExp_LessThan
                                                  (BExp_BinExp BIExp_Plus
                                                     (BExp_Den
                                                        (BVar "sy_x12"
                                                           (BType_Imm Bit64)))
                                                     (BExp_Const
                                                        (Imm64 15w)))
                                                  (BExp_Den
                                                     (BVar "sy_x14"
                                                        (BType_Imm Bit64)))))))
                                      (BExp_BinExp BIExp_And
                                         (BExp_BinExp BIExp_And
                                            (BExp_BinPred BIExp_LessThan
                                               (BExp_Den
                                                  (BVar "sy_x14"
                                                     (BType_Imm Bit64)))
                                               (BExp_BinExp BIExp_Plus
                                                  (BExp_Den
                                                     (BVar "sy_x14"
                                                        (BType_Imm Bit64)))
                                                  (BExp_Const (Imm64 4095w))))
                                            (BExp_BinExp BIExp_And
                                               (BExp_BinPred BIExp_LessThan
                                                  (BExp_Den
                                                     (BVar "sy_x10"
                                                        (BType_Imm Bit64)))
                                                  (BExp_BinExp BIExp_Plus
                                                     (BExp_Den
                                                        (BVar "sy_x10"
                                                           (BType_Imm Bit64)))
                                                     (BExp_Const
                                                        (Imm64 239w))))
                                               (BExp_BinExp BIExp_Or
                                                  (BExp_BinPred
                                                     BIExp_LessThan
                                                     (BExp_BinExp
                                                        BIExp_Plus
                                                        (BExp_Den
                                                           (BVar "sy_x14"
                                                              (BType_Imm
                                                                 Bit64)))
                                                        (BExp_Const
                                                           (Imm64 4095w)))
                                                     (BExp_Den
                                                        (BVar "sy_x10"
                                                           (BType_Imm Bit64))))
                                                  (BExp_BinPred
                                                     BIExp_LessThan
                                                     (BExp_BinExp
                                                        BIExp_Plus
                                                        (BExp_Den
                                                           (BVar "sy_x10"
                                                              (BType_Imm
                                                                 Bit64)))
                                                        (BExp_Const
                                                           (Imm64 239w)))
                                                     (BExp_Den
                                                        (BVar "sy_x14"
                                                           (BType_Imm Bit64)))))))
                                         (BExp_BinExp BIExp_And
                                            (BExp_BinExp BIExp_And
                                               (BExp_BinPred BIExp_Equal
                                                  (BExp_BinExp BIExp_And
                                                     (BExp_Den
                                                        (BVar "sy_x2"
                                                           (BType_Imm Bit64)))
                                                     (BExp_Const (Imm64 7w)))
                                                  (BExp_Const (Imm64 0w)))
                                               (BExp_BinExp BIExp_And
                                                  (BExp_BinPred
                                                     BIExp_LessOrEqual
                                                     (BExp_Const
                                                        (Imm64 0x20000w))
                                                     (BExp_Den
                                                        (BVar "sy_x2"
                                                           (BType_Imm Bit64))))
                                                  (BExp_BinPred
                                                     BIExp_LessThan
                                                     (BExp_Den
                                                        (BVar "sy_x2"
                                                           (BType_Imm Bit64)))
                                                     (BExp_Const
                                                        (Imm64 0x100000000w)))))
                                            (BExp_BinExp BIExp_And
                                               (BExp_BinExp BIExp_And
                                                  (BExp_BinPred BIExp_Equal
                                                     (BExp_BinExp BIExp_And
                                                        (BExp_Den
                                                           (BVar "sy_x10"
                                                              (BType_Imm
                                                                 Bit64)))
                                                        (BExp_Const
                                                           (Imm64 7w)))
                                                     (BExp_Const (Imm64 0w)))
                                                  (BExp_BinExp BIExp_And
                                                     (BExp_BinPred
                                                        BIExp_LessOrEqual
                                                        (BExp_Const
                                                           (Imm64 0x20000w))
                                                        (BExp_Den
                                                           (BVar "sy_x10"
                                                              (BType_Imm
                                                                 Bit64))))
                                                     (BExp_BinPred
                                                        BIExp_LessThan
                                                        (BExp_Den
                                                           (BVar "sy_x10"
                                                              (BType_Imm
                                                                 Bit64)))
                                                        (BExp_Const
                                                           (Imm64
                                                              0x100000000w)))))
                                               (BExp_BinExp BIExp_And
                                                  (BExp_BinExp BIExp_And
                                                     (BExp_BinPred
                                                        BIExp_Equal
                                                        (BExp_BinExp
                                                           BIExp_And
                                                           (BExp_Den
                                                              (BVar
                                                                 "sy_x12"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64 7w)))
                                                        (BExp_Const
                                                           (Imm64 0w)))
                                                     (BExp_BinExp BIExp_And
                                                        (BExp_BinPred
                                                           BIExp_LessOrEqual
                                                           (BExp_Const
                                                              (Imm64
                                                                 0x20000w))
                                                           (BExp_Den
                                                              (BVar
                                                                 "sy_x12"
                                                                 (BType_Imm
                                                                    Bit64))))
                                                        (BExp_BinPred
                                                           BIExp_LessThan
                                                           (BExp_Den
                                                              (BVar
                                                                 "sy_x12"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64
                                                                 0x100000000w)))))
                                                  (BExp_BinExp BIExp_And
                                                     (BExp_BinPred
                                                        BIExp_Equal
                                                        (BExp_BinExp
                                                           BIExp_And
                                                           (BExp_Den
                                                              (BVar
                                                                 "sy_x14"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64 7w)))
                                                        (BExp_Const
                                                           (Imm64 0w)))
                                                     (BExp_BinExp BIExp_And
                                                        (BExp_BinPred
                                                           BIExp_LessOrEqual
                                                           (BExp_Const
                                                              (Imm64
                                                                 0x20000w))
                                                           (BExp_Den
                                                              (BVar
                                                                 "sy_x14"
                                                                 (BType_Imm
                                                                    Bit64))))
                                                        (BExp_BinPred
                                                           BIExp_LessThan
                                                           (BExp_Den
                                                              (BVar
                                                                 "sy_x14"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64
                                                                 0x100000000w)))))))))))))))
                    (BExp_UnaryExp BIExp_Not
                       (BExp_BinPred BIExp_Equal
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "sy_x11" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 1w)))
                          (BExp_Const (Imm64 0w))))|>
``;

val pc_old = ``<|bpc_label := BL_Address (Imm64 2804w); bpc_index := 0|>``;
val pc_new = ``<|bpc_label := BL_Address (Imm64 0xAECw); bpc_index := 1|>``; (* load *)
val pc_new = ``<|bpc_label := BL_Address (Imm64 0xAECw); bpc_index := 0|>``; (* assert alignment of x8 *)

(*
val t = state;
val t1 = pc_old;
val t2 = pc_new;
*)
fun replace_subterm t t1 t2 =
  let
    val label_var_tm = ``(abcdef:bir_programcounter_t)``;
    val pat_tm = (snd o dest_eq o concl) (REWRITE_CONV [ASSUME ``^t1 = ^label_var_tm``] t);
  in
    subst [label_var_tm |-> t2] pat_tm
  end;
  
in

val state2 = replace_subterm state pc_old pc_new;

end;

open birsSyntax;

(* ================================================================================= *)
open birs_auxLib;
fun pc_lookup_fallback_fun pc_lookup_t =
  let
     val _ = print "falling back to evaluation to get current statement";
     val pc_lookup_thm = EVAL pc_lookup_t;
  in
    pc_lookup_thm
  end;
fun pc_lookup_fun (bprog_tm, pc_tm) =
  let
     val pc_lookup_t = mk_bir_get_current_statement (bprog_tm, pc_tm);
  in
 case (!cur_stmt_lookup_fun) pc_tm of
     NONE =>  pc_lookup_fallback_fun pc_lookup_t
   | SOME x => if (identical pc_lookup_t o fst o dest_eq o concl) x then x else pc_lookup_fallback_fun pc_lookup_t
  end;
(* ================================================================================= *)

open birs_stepLib;
open birs_execLib;

val bprog_tm = (fst o dest_eq o concl) bir_aespart_prog_def;

   val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
   val birs_simp_fun = birs_rule_SUBST_trysimp_fun birs_rule_SUBST_thm birs_simp_instancesLib.birs_simp_default_riscv;

local
  open bir_programSyntax;
  open optionSyntax;
in
  fun is_SOME_BStmtB_BStmt_Assign t = is_some t andalso (is_BStmtB o dest_some) t andalso (is_BStmt_Assign o dest_BStmtB o dest_some) t;
end

   fun birs_post_step_fun (t, (last_pc, last_stmt)) = 
    let
     val _ = print "starting postprocessing after step\n";
     val _ = print_term last_pc;
     val _ = print_term last_stmt;
     val _ = if is_SOME_BStmtB_BStmt_Assign last_stmt then print "is an assign\n" else print "is no assign\n";
     val t1 = (
     (fn t => (
	(*print_term ((last o pairSyntax.strip_pair o snd o dest_comb o concl) t);*)
	t)) o
     birs_simp_fun o
     birs_rule_tryprune_fun birs_rulesTheory.branch_prune1_spec_thm o
     birs_rule_tryprune_fun birs_rulesTheory.branch_prune2_spec_thm o
     birs_rule_tryjustassert_fun true) t;
    in
      t1
    end;

   val birs_rule_STEP_fun_spec =
     (birs_post_step_fun o
      birs_rule_STEP_fun birs_rule_STEP_thm);

(* ================================================================================= *)
val _ = print "assert and simplify large store sequence\n";
val timer = holba_miscLib.timer_start 0;
val state2_simpd_thm = birs_rule_STEP_fun_spec state2;
val _ = holba_miscLib.timer_stop (fn delta_s => print ("time to simplify large store sequence: " ^ delta_s ^ "\n")) timer;
val state2_simpd =
 let
  val (_, _, Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) state2_simpd_thm;
 in
  (hd o symb_sound_struct_Pi_to_birstatelist_fun) Pi_tm
 end;
val (_, state2_env, _, _) = dest_birs_state state2;
val (_, state2_simpd_env, _, _) = dest_birs_state state2_simpd;
val _ = if identical state2_simpd_env state2_env then print "unchanged\n" else print "changed\n";

val _ = print "taking step on simplified state\n";
val timer = holba_miscLib.timer_start 0;
val state3_thm = birs_rule_STEP_fun_spec state2_simpd;
val state3 =
 let
  val (_, _, Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) state3_thm;
 in
  (hd o symb_sound_struct_Pi_to_birstatelist_fun) Pi_tm
 end;
val (_, state3_env, _, _) = dest_birs_state state3;
val _ = holba_miscLib.timer_stop (fn delta_s => print ("time to step with simplifications and pruning: " ^ delta_s ^ "\n")) timer;

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(*

Profile.reset_all ()

Profile.print_profile_results (Profile.results ())
Profile.output_profile_results (iostream) (Profile.results ())

*)

(*
val smt_check_exp = ``BExp_Den (BVar "abc" (BType_Imm Bit1))``;

val howmanylist = List.tabulate (1000, fn _ => ());
val _ = List.foldr (fn (_,_) => bir_smtLib.bir_smt_check_sat false smt_check_exp) true howmanylist;


val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());
*)

(*
val teststring = holba_fileLib.read_from_file "/home/andreas/data/hol/HolBA_symbexec/examples/riscv/perftest/tempdir/smtquery_2024-08-08_11-38-51_253062_nil";


val z3bin = "/home/andreas/data/hol/HolBA_opt/z3-4.8.4/bin/z3";
fun openz3 z3bin = 
  (Unix.execute (z3bin, ["-in"])) : (TextIO.instream, TextIO.outstream) Unix.proc;

fun endmeexit p = Unix.fromStatus (Unix.reap p);

fun get_streams p = Unix.streamsOf p;

val p = openz3 z3bin;
val (s_in,s_out) = get_streams p;


val () = TextIO.output (s_out, teststring);
(* val s  = TextIO.inputLine s_in; *)
val s  = TextIO.input s_in;

val () = TextIO.output (s_out, "(reset)\n");


val _ = endmeexit p;
s;
*)