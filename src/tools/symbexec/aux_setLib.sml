structure aux_setLib =
struct

local

open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open bir_symbTheory;

open birs_auxTheory;

open HolBACoreSimps;



val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "aux_setLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname



in (* local *)

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

val birs_state_NEQ_pc_thm = prove(``
!bsys1 bsys2.
  (bsys1.bsst_pc <> bsys2.bsst_pc) ==>
  (bsys1 <> bsys2)
``,
  SIMP_TAC (std_ss++birs_state_ss) []
);
val birs_state_NEQ_pcond_thm = prove(``
!bsys1 bsys2.
  (bsys1.bsst_pcond <> bsys2.bsst_pcond) ==>
  (bsys1 <> bsys2)
``,
  SIMP_TAC (std_ss++birs_state_ss) []
);
val birs_state_NEQ_status_thm = prove(``
!bsys1 bsys2.
  (bsys1.bsst_status <> bsys2.bsst_status) ==>
  (bsys1 <> bsys2)
``,
  SIMP_TAC (std_ss++birs_state_ss) []
);

  fun try_prove_birs_state_try_justify_assumptions t =
    if (is_neg o concl) t orelse
       (not o is_imp o concl) t then
      t
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
        val assmpt_thm = (SIMP_CONV (std_ss++holBACore_ss++birs_state_ss) [] THENC EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "birs_simp_try_justify_assumptions" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "birs_simp_try_justify_assumptions" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        try_prove_birs_state_try_justify_assumptions
          (REWRITE_RULE [assmpt_thm] t)
      end;

fun try_prove_birs_state_NEQ bsys1_tm bsys2_tm =
  let
    val thms = [birs_state_NEQ_pc_thm, birs_state_NEQ_pcond_thm, birs_state_NEQ_status_thm];
    val t = hd thms;
    fun foldfun (t, r_o) =
      if isSome r_o then
        r_o
      else
        (*val t = (SPECL [bsys1_tm, bsys2_tm] t);*)
        SOME (try_prove_birs_state_try_justify_assumptions (SPECL [bsys1_tm, bsys2_tm] t))
        handle _ => NONE;
    val neq_t_o = List.foldl foldfun NONE thms;
  in
    if isSome neq_t_o then
      valOf neq_t_o
    else
      (print "\ncould not show inequality of the states, would need to check the environments\n";
       raise ERR "try_prove_birs_state_NEQ" "could not show inequality of the states, would need to check the environments")
  end;

fun birs_state_EQ_CONV tm =
  IFC
    (CHANGED_CONV (REWRITE_CONV []))
    (fn tm => (print "syntactically equal, done!\n"; REFL tm))
    (fn tm =>
      let
        val (bsys1_tm, bsys2_tm) = dest_eq tm;
        val neq_t = try_prove_birs_state_NEQ bsys1_tm bsys2_tm;
      in
        REWRITE_CONV [neq_t] tm
      end)
  tm;

(*
val tm = ``
  (IMAGE birs_symb_to_symbst {^st1_tm; ^st2_tm} DIFF
    {birs_symb_to_symbst ^st1_tm})
UNION
  IMAGE birs_symb_to_symbst {^st4_tm}
``;

val tm = ``
IMAGE birs_symb_to_symbst
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
{birs_symb_to_symbst
   <|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
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
IMAGE birs_symb_to_symbst
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
*)

val IMAGE_DIFF_SING_thm = prove(``
!f s x.
  (IMAGE f s) DIFF {f x} =
  (IMAGE f s) DIFF (IMAGE f {x})
``,
  SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY]
);


val IMAGE_DIFF_ASSOC_thm = prove(``
!f s1 s2.
  (!x y. f x = f y <=> x = y) ==>
  ((IMAGE f s1) DIFF (IMAGE f s2) =
   IMAGE f (s1 DIFF s2))
``,
  REPEAT STRIP_TAC >>
  SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, EXTENSION] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    METIS_TAC []
  )
);


val IMAGE_UNION_ASSOC_thm = prove(``
!f s1 s2.
  (!x y. f x = f y <=> x = y) ==>
  ((IMAGE f s1) UNION (IMAGE f s2) =
   IMAGE f (s1 UNION s2))
``,
  REPEAT STRIP_TAC >>
  SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, EXTENSION] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    METIS_TAC []
  )
);


    fun DIFF_UNION_CONV_cheat tm =
      let
        val pat_tm = ``(IMAGE (birs_symb_to_symbst) Pi_a) DIFF {birs_symb_to_symbst sys_b} UNION (IMAGE birs_symb_to_symbst Pi_b)``;
        val (tm_match, ty_match) = match_term pat_tm tm;

        val Pi_a  = pred_setSyntax.strip_set(subst tm_match (inst ty_match ``Pi_a:birs_state_t->bool``));
        val sys_b = subst tm_match (inst ty_match ``sys_b:birs_state_t``);
        val Pi_b  = pred_setSyntax.strip_set(subst tm_match (inst ty_match ``Pi_b:birs_state_t->bool``));

        fun eq_fun sys1 sys2 = identical sys1 sys2; (* TODO: birs_state_eq_fun*)
        fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
        val Pi_a_minus_b = List.filter (not o eq_fun sys_b) Pi_a;
        fun UNION_foldfun (sys,Pi) = if in_f Pi sys then Pi else (sys::Pi);
        val Pi_c = List.foldr UNION_foldfun Pi_a_minus_b Pi_b;
        val tm_l_set = if List.null Pi_c then pred_setSyntax.mk_empty (``:birs_state_t``) else pred_setSyntax.mk_set Pi_c;
(*
length Pi_a
length Pi_a_minus_b
length Pi_c
*)
      in
        prove(``^tm = IMAGE birs_symb_to_symbst ^tm_l_set``, cheat)
      end;

    val diffunioncheat_on = false;
    val birs_state_DIFF_UNION_CONV =
      if diffunioncheat_on then
        DIFF_UNION_CONV_cheat
      else
        fn tm =>
          (REWRITE_CONV [IMAGE_DIFF_SING_thm, MATCH_MP IMAGE_DIFF_ASSOC_thm bir_symbTheory.birs_symb_to_symbst_EQ_thm, GSYM DELETE_DEF] THENC
           RATOR_CONV (RAND_CONV (RAND_CONV (

fn tm =>
(
pred_setLib.DELETE_CONV birs_state_EQ_CONV tm
handle ex =>
  (print "\n\n\n";
   print_term tm;
   print "\n\n\n";
   raise ex
  )
)


))) THENC
           REWRITE_CONV [MATCH_MP IMAGE_UNION_ASSOC_thm bir_symbTheory.birs_symb_to_symbst_EQ_thm] THENC
           RAND_CONV (pred_setLib.UNION_CONV birs_state_EQ_CONV))

          tm;



(* ------------------------------------------------------------------------ *)
(* COPIED FROM TRANSFER-TEST (and modified) *)
(* ------------------------------------------------------------------------ *)

(*
val tm = ``
birs_symb_symbols
     <|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>;
       bsst_environ := (K NONE)⦇
             "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
             "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
             "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
             "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
             "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
             "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
             "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
             "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
             "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
             "SP_main" ↦
               SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
             "SP_process" ↦
               SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             "ModeHandler" ↦
               SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
             "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             "tmp_COND" ↦
               SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
             "tmp_MEM" ↦
               SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
             "tmp_PSR_C" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             "tmp_PSR_N" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
             "tmp_PSR_V" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
             "tmp_PSR_Z" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
             "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
             "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
             "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
             "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
             "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
             "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
             "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
             "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
             "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
             "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
             "tmp_R10" ↦
               SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
             "tmp_R11" ↦
               SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
             "tmp_R12" ↦
               SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
             "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
             "tmp_SP_main" ↦
               SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
             "tmp_SP_process" ↦
               SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             "tmp_ModeHandler" ↦
               SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
             "tmp_countw" ↦
               SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
           ⦈;
       bsst_status := BST_Running; bsst_pcond := BExp_BinExp BIExp_Plus (BExp_Den (BVar "hello" (BType_Imm Bit8))) (BExp_BinExp BIExp_Plus (BExp_Den (BVar "hello" (BType_Imm Bit8))) (BExp_Const (Imm1 1w)))|>
``;

val tm = ``
birs_exps_of_senv
  (K NONE)⦇
    "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
    "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
    "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
    "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
    "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
    "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
    "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
    "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
    "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
    "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
    "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
    "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
    "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
    "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
    "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
    "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
    "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
    "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
    "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
    "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
    "SP_process" ↦ SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
    "ModeHandler" ↦ SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
    "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
    "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
    "tmp_COND" ↦ SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
    "tmp_MEM" ↦ SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
    "tmp_PSR_C" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
    "tmp_PSR_N" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
    "tmp_PSR_V" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
    "tmp_PSR_Z" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
    "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
    "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
    "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
    "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
    "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
    "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
    "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
    "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
    "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
    "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
    "tmp_R10" ↦ SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
    "tmp_R11" ↦ SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
    "tmp_R12" ↦ SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
    "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
    "tmp_SP_main" ↦ SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
    "tmp_SP_process" ↦
      SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
    "tmp_ModeHandler" ↦
      SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
    "tmp_countw" ↦ SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
  ⦈
``;

val tm = ``
     birs_exps_of_senv_COMP ∅
       (K NONE)⦇
         "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
         "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
         "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
         "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
         "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
         "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
         "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
         "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
         "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
         "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
         "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
         "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
         "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
         "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
         "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
         "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
         "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
         "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
         "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
         "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
         "SP_process" ↦
           SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
         "ModeHandler" ↦
           SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
         "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
         "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
         "tmp_COND" ↦ SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
         "tmp_MEM" ↦
           SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
         "tmp_PSR_C" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
         "tmp_PSR_N" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
         "tmp_PSR_V" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
         "tmp_PSR_Z" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
         "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
         "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
         "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
         "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
         "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
         "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
         "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
         "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
         "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
         "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
         "tmp_R10" ↦ SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
         "tmp_R11" ↦ SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
         "tmp_R12" ↦ SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
         "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
         "tmp_SP_main" ↦
           SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
         "tmp_SP_process" ↦
           SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
         "tmp_ModeHandler" ↦
           SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         "tmp_countw" ↦
           SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
       ⦈
``;

val tm = ``
     birs_exps_of_senv_COMP ∅
       (K NONE)⦇
         "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
         "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
         "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
         "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
         "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)))
       ⦈
``;

val tm2 = ``
     birs_exps_of_senv_COMP ∅
       (K NONE)
``;

val tm = ``
birs_exps_of_senv_COMP {"PSR_Z"; "PSR_V"; "PSR_N"; "PSR_C"; "MEM"} (K NONE)
``;


val tm = ``
birs_exps_of_senv
  (K NONE)⦇
    "tmp_SP_process" ↦
      SOME
        (BExp_BinExp BIExp_Minus
           (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
           (BExp_Const (Imm32 8w)));
    "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
    "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
    "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
    "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
    "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
    "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
    "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
    "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
    "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
    "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
    "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
    "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
    "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
    "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
    "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
    "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
    "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
    "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
    "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
    "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
    "SP_process" ↦ SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
    "ModeHandler" ↦ SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
    "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
    "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
    "tmp_COND" ↦ SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
    "tmp_MEM" ↦ SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
    "tmp_PSR_C" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
    "tmp_PSR_N" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
    "tmp_PSR_V" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
    "tmp_PSR_Z" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
    "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
    "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
    "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
    "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
    "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
    "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
    "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
    "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
    "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
    "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
    "tmp_R10" ↦ SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
    "tmp_R11" ↦ SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
    "tmp_R12" ↦ SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
    "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
    "tmp_SP_main" ↦ SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
    "tmp_SP_process" ↦
      SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
    "tmp_ModeHandler" ↦
      SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
    "tmp_countw" ↦ SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
  ⦈
``;


val tm = ``
birs_exps_of_senv_COMP {"tmp_SP_process"}
       (K NONE)⦇
         "tmp_SP_process" ↦
           SOME
             (BExp_BinExp BIExp_Minus
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                (BExp_Const (Imm32 8w)));
         "tmp_ModeHandler" ↦
           SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         "tmp_countw" ↦
           SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
       ⦈
``;

*)

val debug_conv = (fn tm => (print_term tm; raise Fail "abcdE!!!"));
val debug_conv2 = (fn tm => (if true then print ".\n" else print_term tm; REFL tm));

  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;

(*
REPEATC
      (SIMP_CONV (std_ss) []) THENC
      (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (REWRITE_CONV [pred_setTheory.COMPONENT] THENC SIMP_CONV std_ss [pred_setTheory.IN_INSERT])))) THENC
      SIMP_CONV (std_ss) []
*)

(* ................................................ *)

fun string_in_set_CONV tm =
(
  REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY] THENC
  REPEATC (CHANGED_CONV ((fn xyz => REWRITE_CONV [Once pred_setTheory.IN_INSERT] xyz) THENC
     IFC
       (RATOR_CONV EVAL)
       (BETA_CONV THENC REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY])
       REFL))
) tm;

fun birs_exps_of_senv_COMP_ONCE_CONV tm =
(
  (QCHANGED_CONV (CHANGED_CONV (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x))) THENC
  IFC
    (RATOR_CONV (RATOR_CONV (RAND_CONV (string_in_set_CONV))))
    (REWRITE_CONV [])
    (REFL)
) tm;

(* TODO: add proper exceptions/exception messages if the unexpected happens... *)
fun birs_exps_of_senv_COMP_CONV_cheat tm =
  let
    val (s1, s2_l) = strip_comb tm;
    val _ = if ((fst o dest_const) s1) = "birs_exps_of_senv_COMP" then () else
            raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "constant not found";
    val _ = if length s2_l = 2 then () else
            raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "application not right";
    val initvarset = List.nth(s2_l, 0);
    val _ = if pred_setSyntax.is_empty initvarset then () else
            raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "must start with empty set";

    val tm_map = List.nth(s2_l, 1);

    fun eq_fun tm1 tm2 = tm1 = tm2;
    fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;

    val base_term = ``(K NONE):string -> bir_exp_t option``;
    fun collectfun excl acc tm_map =
      if identical tm_map base_term then acc else
      if not (combinSyntax.is_update_comb tm_map) then raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "should not happen" else
      let
        val ((mem_upd_k, mem_upd_v), tm_map_sub) = combinSyntax.dest_update_comb tm_map;
        val mem_upd_v_v = optionSyntax.dest_some mem_upd_v;
        val mem_upd_k_s = stringSyntax.fromHOLstring mem_upd_k;
        val k_s_is_excl = in_f excl mem_upd_k_s;
        val new_acc  = if k_s_is_excl then (acc)  else ([mem_upd_v_v]@acc);
        val new_excl = if k_s_is_excl then (excl) else ([mem_upd_k_s]@excl);
      in
        collectfun new_excl new_acc tm_map_sub
      end;

(*
    val s1_l = pred_setSyntax.strip_set s1;
    val s2_l = pred_setSyntax.strip_set s2;
List.foldr (fn (x, l) => if not (in_f s2_l x) then x::l else l) [] s1_l;
*)

    val l = collectfun [] [] tm_map;
    val tm_l_set = if List.null l then pred_setSyntax.mk_empty(``:bir_exp_t``) else pred_setSyntax.mk_set l;
  in
    mk_oracle_thm "FISHY_BIRS_BIR_SENV_VARSET" ([], mk_eq (tm, tm_l_set))
  end;

fun birs_exps_of_senv_COMP_CONV_norm tm =
(
(*(fn tm => (if false then print ".\n" else print_term tm; REFL tm)) THENC*)
(* (fn tm => (if true then print ".\n" else print_term tm; REFL tm)) THENC *)
(*
  if pred_setSyntax.is_empty tm then
    REFL
  else
*)
  IFC
    (birs_exps_of_senv_COMP_ONCE_CONV)
    (TRY_CONV (fn tm => (
      if pred_setSyntax.is_empty tm then
        REFL
      else if pred_setSyntax.is_insert tm then
        RAND_CONV birs_exps_of_senv_COMP_CONV_norm
      else
        birs_exps_of_senv_COMP_CONV_norm
    ) tm))
    (fn tm => (print_term tm; raise Fail "unexpected here"))
) tm;

val turn_speedcheat_on = false;
val birs_exps_of_senv_COMP_CONV =
  if turn_speedcheat_on then
    birs_exps_of_senv_COMP_CONV_cheat
  else
    birs_exps_of_senv_COMP_CONV_norm;


fun birs_exps_of_senv_CONV tm =
(
(*
(fn tm => (if false then print ".\n" else print_term tm; REFL tm)) THENC
*)
  REWRITE_CONV [birs_exps_of_senv_thm] THENC
  ((*TRY_CONV*) birs_exps_of_senv_COMP_CONV)
) tm;

fun is_birs_exps_of_senv tm = is_comb tm andalso
                              (is_const o fst o dest_comb) tm andalso
                              ((fn tm2 => tm2 = "birs_exps_of_senv") o fst o dest_const o fst o dest_comb) tm;
fun birs_symb_symbols_CONV tm =
(
  SIMP_CONV (std_ss++birs_state_ss) [birs_symb_symbols_thm] THENC
  debug_conv2 THENC
  GEN_match_conv is_birs_exps_of_senv birs_exps_of_senv_CONV THENC
  debug_conv2 THENC
  REWRITE_CONV [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, bir_typing_expTheory.bir_vars_of_exp_def] THENC

  debug_conv2 THENC
  RATOR_CONV (RAND_CONV (REWRITE_CONV [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY])) THENC

  REWRITE_CONV [Once pred_setTheory.UNION_COMM] THENC
  REWRITE_CONV [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]
) tm;

fun is_birs_symb_symbols tm = is_comb tm andalso
                              (is_const o fst o dest_comb) tm andalso
                              ((fn tm2 => tm2 = "birs_symb_symbols") o fst o dest_const o fst o dest_comb) tm;
fun birs_symb_symbols_MATCH_CONV tm =
  GEN_match_conv is_birs_symb_symbols birs_symb_symbols_CONV tm;

(* ................................................ *)

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

(* 65 * 30 * t_IN_VAR = 9-10s
t_IN_VAR = 0.005s *)
(* !!!!! try computeLib *)
val string_ss = rewrites (type_rws ``:string``);

val el_EQ_CONV = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [];
val el_EQ_CONV = RAND_CONV EVAL;

fun IN_INSERT_CONV el_EQ_CONV tm =
(
  REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY] THENC
  REPEATC (CHANGED_CONV (
     (fn xyz => REWRITE_CONV [Once pred_setTheory.IN_INSERT] xyz) THENC
     (*(fn tm => (if false then print ".\n" else print_term tm; print "aa\n\n"; REFL tm)) THENC*)
     IFC
       (RATOR_CONV el_EQ_CONV)
       (REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY])
       REFL))
) tm;

fun INTER_INSERT_ONCE_CONV el_EQ_CONV tm =
(
  (QCHANGED_CONV (CHANGED_CONV (fn x => REWRITE_CONV [Once pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY] x))) THENC
  IFC
    (RATOR_CONV (RATOR_CONV (RAND_CONV (
(*
fn tm => (print_term (concl (prove (mk_eq (tm, F), cheat))); prove (mk_eq (tm, F), cheat))
*)
(*fn tm => (prove (mk_eq (tm, F), cheat))*)
(*(fn tm => (if false then print ".\n" else print_term tm; print "aa\n\n"; REFL tm)) THENC*)
IN_INSERT_CONV el_EQ_CONV
))))
    (REWRITE_CONV [])
    (REFL)
) tm;

fun INTER_INSERT_CONV_norm el_EQ_CONV tm =
(
  if pred_setSyntax.is_empty tm then
    REFL
  else
  (fn tm => (if true then print ".\n" else (print_term tm; print "\n\n"); REFL tm)) THENC
  IFC
    (INTER_INSERT_ONCE_CONV el_EQ_CONV)
    (
(*
(fn tm => (if false then print ".\n" else print_term tm; print "bb\n\n"; REFL tm)) THENC
*)
(fn tm =>
      (
      (*(fn tm => (if false then print ".\n" else print_term tm; print "bb\n\n"; REFL tm)) THENC *)
      (if pred_setSyntax.is_empty tm then
       (REFL)
      else if pred_setSyntax.is_inter tm then
       (INTER_INSERT_CONV_norm el_EQ_CONV)
      else if pred_setSyntax.is_insert tm then
       (RAND_CONV (INTER_INSERT_CONV_norm el_EQ_CONV))
      else
       (REFL))) tm))
(* the following causes trouble as "normal exit" if there is nothing to be done at the first call *)
    (fn tm => (print_term tm; raise Fail "unexpected here"))
) tm;


(* TODO: fix this *)
fun bvar_eq_fun_cheat tm1 tm2 = identical tm1 tm2;

fun INTER_INSERT_CONV_cheat tm =
  let
    val (s1, s2) = pred_setSyntax.dest_inter tm
    val s1_l = pred_setSyntax.strip_set s1;
    val s2_l = pred_setSyntax.strip_set s2;
    val eq_fun = bvar_eq_fun_cheat;
    fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
    val l = List.foldr (fn (x, l) => if in_f s2_l x then x::l else l) [] s1_l;
    val tm_l_set = if List.null l then pred_setSyntax.mk_empty(pred_setSyntax.eltype  tm) else pred_setSyntax.mk_set l;
  in
    mk_oracle_thm "FISHY_BIRS_FREEVARSET" ([], mk_eq (tm, tm_l_set))
  end;

fun DIFF_INSERT_CONV_cheat tm =
  let
    val (s1, s2) = pred_setSyntax.dest_diff tm
    val s1_l = pred_setSyntax.strip_set s1;
    val s2_l = pred_setSyntax.strip_set s2;
    val eq_fun = bvar_eq_fun_cheat;
    fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
    val l = List.foldr (fn (x, l) => if not (in_f s2_l x) then x::l else l) [] s1_l;
    val tm_l_set = if List.null l then pred_setSyntax.mk_empty(pred_setSyntax.eltype  tm) else pred_setSyntax.mk_set l;
  in
    mk_oracle_thm "FISHY_BIRS_FREEVARSET" ([], mk_eq (tm, tm_l_set))
  end;


val INTER_INSERT_CONV =
  if turn_speedcheat_on then
    INTER_INSERT_CONV_cheat
  else
    INTER_INSERT_CONV_norm el_EQ_CONV;


val DIFF_INSERT_CONV =
  if turn_speedcheat_on then
    DIFF_INSERT_CONV_cheat
  else
    (*SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY, pred_setTheory.IN_DIFF, pred_setTheory.IN_INSERT]*)
    EVAL;







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


fun DIFF_CONV_Once el_EQ_CONV tm =
  (
    IFC
      (CHANGED_CONV (fn tm => REWRITE_CONV [Once INSERT_DIFF] tm))
      (RATOR_CONV (RATOR_CONV (RAND_CONV (pred_setLib.IN_CONV el_EQ_CONV))) THENC
       REWRITE_CONV [])
      (REFL)
  )
  tm;

fun DIFF_CONV el_EQ_CONV tm =
  if pred_setSyntax.is_empty tm then
    REFL tm
  else if pred_setSyntax.is_diff tm then
    if (pred_setSyntax.is_empty o fst o pred_setSyntax.dest_diff) tm then
       (print_term tm;
        REWRITE_CONV [EMPTY_DIFF] tm)
    else if (pred_setSyntax.is_insert o fst o pred_setSyntax.dest_diff) tm then
       (DIFF_CONV_Once el_EQ_CONV THENC
        DIFF_CONV el_EQ_CONV) tm
    else
      raise ERR "DIFF_CONV" "unexpected1"
  else if pred_setSyntax.is_insert tm then
    RAND_CONV
      (DIFF_CONV el_EQ_CONV)
      tm
  else
    (print_term tm;
     raise ERR "DIFF_CONV" "unexpected2");

(*
val el_EQ_CONV = EVAL;
DIFF_CONV el_EQ_CONV tm
*)

val simplerewrite_thm = prove(``
!s t g.
g INTER (s DIFF t) =
s INTER (g DIFF t)
``,
(*REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER*)
METIS_TAC [pred_setTheory.INTER_COMM, pred_setTheory.DIFF_INTER]
);


fun freevarset_CONV tm =
(
  REWRITE_CONV [Once (simplerewrite_thm)] THENC

  (RAND_CONV (
   DIFF_CONV EVAL
  )) THENC

  (* then INTER *)
  INTER_INSERT_CONV
) tm;


end (* local *)

end (* struct *)
