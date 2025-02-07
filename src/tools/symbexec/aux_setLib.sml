structure aux_setLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open bir_convLib;
  open holba_convLib;
  open holba_cacheLib;

  open bir_symbTheory;

  open birs_auxTheory;

  open HolBACoreSimps;

  open birsSyntax;
  open birs_utilsLib;

  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "aux_setLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)


(* ---------------------------------------------------------------------------------- *)
(*  birs state equality checker                                                       *)
(* ---------------------------------------------------------------------------------- *)

  fun birs_gen_env_check_eq env1 env2 =
    let
      val mappings1 = get_env_mappings env1;
      val mappings2 = get_env_mappings env2;
    in
      birs_utilsLib.list_eq_contents (fn (x,y) => pair_eq identical identical x y) mappings1 mappings2
    end;

  (* TODO: have to make provide a proof-producing version of this *)
  fun birs_env_EQ_CONV tm =
    let
      val (env1_tm, env2_tm) = dest_eq tm;
      (* need two symbolic environments with birs_gen_env *)
      val _ = birs_check_env_norm ("birs_env_EQ_CONV", ": 1") env1_tm;
      val _ = birs_check_env_norm ("birs_env_EQ_CONV", ": 2") env2_tm;
      val is_eq = birs_gen_env_check_eq env1_tm env2_tm;
      val _ = print (if is_eq then "symbolic environments are equal\n" else "symbolic environments are not equal\n");
      (* TODO: the false case might be wrong *)
      val _ = if is_eq then () else (
        (*print_term tm;*)
        print "the symbolic environments seem to be unequal, but they might be equal\n";
        raise ERR "birs_env_EQ_CONV" "the symbolic environments seem to be unequal, but they might be equal");
      val eq_thm = mk_oracle_thm "BIRS_ENV_EQ" ([], mk_eq (tm, if is_eq then T else F));
      val _ = print "oracle used: BIRS_ENV_EQ\n";
    in
      eq_thm
    end;
  val birs_env_EQ_CONV = Profile.profile "auxset_birs_env_EQ_CONV" birs_env_EQ_CONV;


  val birs_state_EQ_thm = prove(``
      !b21 f1 b11 b01 b22 f2 b12 b02.
       <|bsst_pc := b21; bsst_environ := f1; bsst_status := b11; bsst_pcond := b01|> =
       <|bsst_pc := b22; bsst_environ := f2; bsst_status := b12; bsst_pcond := b02|> <=>
       b11 = b12 /\ (b21 = b22 /\ (b01 = b02 /\ f1 = f2))
    ``,
      METIS_TAC [bir_symbTheory.birs_state_t_literal_11]
    ); (*status, pc, pcond, senv*)
  val birs_state_EQ_CONV =
    (REWR_CONV birs_state_EQ_thm) THENC
    CONJL_CONV
      (Profile.profile "auxset_birs_state_EQ_CONV_0status" bir_status_EQ_CONV (*status*))
      (CONJL_CONV
        (Profile.profile "auxset_birs_state_EQ_CONV_1pc" bir_pc_EQ_CONV (*pc*))
        (CONJL_CONV
          (Profile.profile "auxset_birs_state_EQ_CONV_2pcond" bir_exp_EQ_CONV (*pcond*))
          (Profile.profile "auxset_birs_state_EQ_CONV_3senv" birs_env_EQ_CONV (*senv*))));
  val birs_state_EQ_CONV = Profile.profile "auxset_birs_state_EQ_CONV" birs_state_EQ_CONV;


(* ---------------------------------------------------------------------------------- *)
(* set operation for composition, using the state equality checker above              *)
(* ---------------------------------------------------------------------------------- *)
  val birs_state_DELETE_CONV =
      pred_setLib.DELETE_CONV birs_state_EQ_CONV;

  val birs_state_INSERT_CONV =
      pred_setLib.INSERT_CONV birs_state_EQ_CONV;

  val birs_state_INSERT_DELETE_CONV =
      RAND_CONV birs_state_DELETE_CONV THENC
      TRY_CONV (birs_state_INSERT_CONV);

  val birs_state_DIFF_UNION_CONV =
      LAND_CONV (DIFF_CONV birs_state_EQ_CONV) THENC
      pred_setLib.UNION_CONV birs_state_EQ_CONV;

end (* local *)

end (* struct *)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR: set operation for composition *)
(* ---------------------------------------------------------------------------------- *)
(*
val tm = ``
  ({^st1_tm; ^st2_tm} DIFF
    {^st1_tm})
UNION
  {^st4_tm}
``;

val tm = ``
  {<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
          ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
          ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
          ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
          ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
          ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
          ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
          ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
          ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
          ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
          ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
          ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
          ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
          ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
          ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
          ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
          ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
          ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
          ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
          ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
          ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
          ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
          ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
          ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
          ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
          ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
          ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
          ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
          ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
          ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
          ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
          ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
          ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
          ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
          ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
          ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
          ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
          ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
          ("tmp_ModeHandler",
           BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
          ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
     bsst_status := BST_Running;
     bsst_pcond :=
       BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>} DIFF
{  <|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
          ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
          ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
          ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
          ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
          ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
          ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
          ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
          ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
          ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
          ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
          ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
          ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
          ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
          ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
          ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
          ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
          ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
          ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
          ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
          ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
          ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
          ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
          ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
          ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
          ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
          ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
          ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
          ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
          ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
          ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
          ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
          ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
          ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
          ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
          ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
          ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
          ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
          ("tmp_ModeHandler",
           BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
          ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
     bsst_status := BST_Running;
     bsst_pcond :=
       BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>} ∪
  {<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 2|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
          ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
          ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
          ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
          ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
          ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
          ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
          ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
          ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
          ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
          ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
          ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
          ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
          ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
          ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
          ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
          ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
          ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
          ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
          ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
          ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
          ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
          ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
          ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
          ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
          ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
          ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
          ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
          ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
          ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
          ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
          ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
          ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
          ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
          ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
          ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
          ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
          ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
          ("tmp_ModeHandler",
           BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
          ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
     bsst_status := BST_Running;
     bsst_pcond :=
       BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>}``;

birs_state_DIFF_UNION_CONV tm;
*)

(* ---------------------------------------------------------------------------------- *)
(*  TEST CASE FOR: state equality checker                                             *)
(* ---------------------------------------------------------------------------------- *)
(*
fun stx_tm addr_tm index_tm symbname_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm32 (^addr_tm)); bpc_index := (^index_tm)|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar (^symbname_tm) (BType_Imm Bit1)))];
     bsst_status := BST_Running;
     bsst_pcond :=
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>
``;
val st1_tm = stx_tm ``2824w:word32`` ``1:num`` ``"sy_PSR_Z"``;
val st2_tm = stx_tm ``2824w:word32`` ``2:num`` ``"sy_PSR_Z"``;
val st3_tm = stx_tm ``2825w:word32`` ``1:num`` ``"sy_PSR_A"``;
val st4_tm = stx_tm ``2824w:word32`` ``3:num`` ``"sy_PSR_Z"``;

val st_eq_1_tm = ``^st1_tm = ^st1_tm``;
val st_eq_2_tm = ``^st1_tm = ^st2_tm``;
val st_eq_3_tm = ``^st1_tm = ^st3_tm``;
val st_eq_4_tm = ``^st2_tm = ^st3_tm``;

val tm = st_eq_2_tm;
val tm = st_eq_3_tm;
val tm = st_eq_4_tm;

birs_state_EQ_CONV st_eq_1_tm
birs_state_EQ_CONV st_eq_2_tm
birs_state_EQ_CONV st_eq_3_tm
birs_state_EQ_CONV st_eq_4_tm
*)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR:                                                                     *)
(* faster set operations for bir variable sets (for computing freevarset, symbexec composition, merging, etc) *)
(* also for sets of symbolic BIR states                                               *)
(* ---------------------------------------------------------------------------------- *)
(*
EVAL tm

           val birs_exps_of_senv_CONV = (
    debug_conv2 THENC
    REPEATC (CHANGED_CONV (
      (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x) THENC
      (SIMP_CONV (std_ss) []) THENC
      (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (REWRITE_CONV [pred_setTheory.COMPONENT] THENC SIMP_CONV std_ss [pred_setTheory.IN_INSERT])))) THENC
      SIMP_CONV (std_ss) []
    ))
  );

           val birs_symb_symbols_CONV = (
    SIMP_CONV std_ss [birs_symb_symbols_thm] THENC
    SIMP_CONV (std_ss++birs_state_ss) [] THENC
    SIMP_CONV (std_ss) [birs_exps_of_senv_thm]
    (*(PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` birs_exps_of_senv_CONV)*)
  );
           val conv = birs_symb_symbols_CONV (*THENC EVAL*);
           val conv_ = computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC conv;
*)

(*
val tm = ``
{BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
    BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
    BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
    BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
    BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
    BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
    BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
    BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
    BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
    BVar "sy_SP_process" (BType_Imm Bit32);
    BVar "sy_ModeHandler" (BType_Imm Bit1);
    BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
    BVar "sy_tmp_COND" (BType_Imm Bit1);
    BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
    BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_R0" (BType_Imm Bit32);
    BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
    BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
    BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
    BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
    BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
    BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
    BVar "sy_tmp_LR" (BType_Imm Bit32);
    BVar "sy_tmp_SP_main" (BType_Imm Bit32);
    BVar "sy_tmp_SP_process" (BType_Imm Bit32);
    BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
    BVar "sy_tmp_countw" (BType_Imm Bit64)} ∩
   ({BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64);
     BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)} DIFF
    {BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)})
``;

val tm = ``
{BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);BVar "sy_countw" (BType_Imm Bit64);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1)} ∩
   ({BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);BVar "sy_countw" (BType_Imm Bit64);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1)} DIFF
    {
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)})
``;

val tm = (snd o dest_comb o fst o dest_comb o snd o dest_eq o concl o REWRITE_CONV [REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER]) tm;
val tm = (snd o dest_comb o snd o dest_eq o concl o REWRITE_CONV [Once (prove(``
!s t g.
g INTER (s DIFF t) =
s INTER (g DIFF t)
``,
(*REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER*)
METIS_TAC [pred_setTheory.INTER_COMM, pred_setTheory.DIFF_INTER]
))]) tm;

++pred_setSimps.PRED_SET_ss
val char_ss = rewrites (type_rws ``:char``);



val tm = ``
BVar "sy_countw" (BType_Imm Bit64) ∈
       {BVar "sy_MEM" (BType_Mem Bit32 Bit8);
        BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
        BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_Z" (BType_Imm Bit1);
        BVar "sy_R0" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
        BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
        BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
        BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
        BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
        BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
        BVar "sy_R12" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
        BVar "sy_SP_main" (BType_Imm Bit32);
        BVar "sy_SP_process" (BType_Imm Bit32);
        BVar "sy_ModeHandler" (BType_Imm Bit1);
        BVar "sy_countw" (BType_Imm Bit64);
        BVar "sy_tmp_PC" (BType_Imm Bit32);
        BVar "sy_tmp_COND" (BType_Imm Bit1);
        BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
        BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32);
        BVar "sy_tmp_R6" (BType_Imm Bit32);
        BVar "sy_tmp_R7" (BType_Imm Bit32);
        BVar "sy_tmp_R8" (BType_Imm Bit32);
        BVar "sy_tmp_R9" (BType_Imm Bit32);
        BVar "sy_tmp_R10" (BType_Imm Bit32);
        BVar "sy_tmp_R11" (BType_Imm Bit32);
        BVar "sy_tmp_R12" (BType_Imm Bit32);
        BVar "sy_tmp_LR" (BType_Imm Bit32);
        BVar "sy_tmp_SP_main" (BType_Imm Bit32);
        BVar "sy_tmp_SP_process" (BType_Imm Bit32);
        BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
        BVar "sy_tmp_countw" (BType_Imm Bit64)}
``;


*)
(*
val tm = ``
  EMPTY DIFF
     {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32)
     }
``;

val tm = ``
  {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32)
  } DIFF
     EMPTY
``;

val tm = ``
  {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32)
  } DIFF
     {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32)
     }
``;

val tm = ``
{
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32);
        BVar "sy_tmp_R8" (BType_Imm Bit32)
} INTER (^tm)
``; (* R4 and R5 *)
*)
