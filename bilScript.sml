(* ========================================================================= *)
(* FILE          : bilScript.sml                                             *)
(* DESCRIPTION   : A model of BAP Intermediate Language.                     *)
(*                 Based on Anthony Fox's binary words treatment.            *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;
open bil_imm_expTheory bil_mem_expTheory bil_envTheory;
open bil_expTheory;
open wordsLib;

val _ = new_theory "bil";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_label_t =
    Label string
  | Address bil_imm_t
`;

val _ = Datatype `bil_stmt_t =
  | Declare bil_var_t
  | Assign  bil_var_t bil_exp_t
  | Jmp     bil_label_t
  | CJmp    bil_exp_t bil_label_t bil_label_t
  | Halt    bil_exp_t
  | Assert  bil_exp_t
  | Assume  bil_exp_t
`;

val _ = Datatype `bil_block_t = <| label:bil_label_t ; statements:bil_stmt_t list |>`;
val _ = Datatype `bil_program_t = BilProgram (bil_block_t list)`;
val _ = Datatype `bil_programcounter_t = <| label:bil_label_t; index:num |>`;

val bil_pc_ss = rewrites (type_rws ``:bil_programcounter_t``);

val _ = Datatype `bil_termcode_t =
    Running
  | Halted bil_val_t
  | ReachedEnd
  | ReachedUnknownLabel bil_label_t
  | Failed
  | AssumptionViolated`

val _ = Datatype `bil_state_t = <|
  pc       : bil_programcounter_t;
  environ  : bil_var_environment_t;
  termcode : bil_termcode_t;
  debug    : string list;
  execs    : num
|>`;

val bil_state_ss = rewrites (type_rws ``:bil_state_t``);
val bil_termcode_ss = rewrites (type_rws ``:bil_termcode_t``);


(* ------------------------------------------------------------------------- *)
(* Programs                                                                  *)
(* ------------------------------------------------------------------------- *)

val bil_block_stmts_count_def = Define `bil_block_stmts_count bl = LENGTH bl.statements`;
val bil_program_stmts_count_def = Define`bil_program_stmts_count (BilProgram p) = SUM (MAP bil_block_stmts_count p)`;

val bil_labels_of_program_def = Define `bil_labels_of_program (BilProgram p) =
  MAP (\bl. bl.label) p`;

val bil_is_valid_labels_def = Define `bil_is_valid_labels p =
  ALL_DISTINCT (bil_labels_of_program p) /\ ~(MEM (Label "") (bil_labels_of_program p))`;

val bil_is_valid_program_def = Define `bil_is_valid_program p <=>
   (bil_is_valid_labels p /\ bil_program_stmts_count p > 0)`;


val bil_is_valid_labels_blocks_EQ_EL = store_thm ("bil_is_valid_labels_blocks_EQ_EL",
  ``!p n1 n2. (bil_is_valid_labels (BilProgram p) /\ n1 < LENGTH p /\ n2 < LENGTH p /\
                ((EL n1 p).label = (EL n2 p).label)) ==> (n1 = n2)``,

SIMP_TAC list_ss [bil_is_valid_labels_def, bil_labels_of_program_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.ISPEC `MAP (\bl. bl.label) (p:bil_block_t list)` listTheory.EL_ALL_DISTINCT_EL_EQ) >>
ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_IMP_THM] >>
Q.EXISTS_TAC `n1` >> Q.EXISTS_TAC `n2` >>
ASM_SIMP_TAC list_ss [listTheory.EL_MAP]);


val bil_is_valid_labels_blocks_EQ = store_thm ("bil_is_valid_labels_blocks_EQ",
  ``!p bl1 bl2. (bil_is_valid_labels (BilProgram p) /\ MEM bl1 p /\ MEM bl2 p /\
                (bl1.label = bl2.label)) ==> (bl1 = bl2)``,

METIS_TAC [listTheory.MEM_EL, bil_is_valid_labels_blocks_EQ_EL]);



val bil_get_program_block_info_by_label_def = Define `bil_get_program_block_info_by_label
  (BilProgram p) l = INDEX_FIND 0 (\(x:bil_block_t). x.label = l) p
`;

val bil_get_program_block_info_by_label_THM = store_thm ("bil_get_program_block_info_by_label_THM",
  ``(!p l. ((bil_get_program_block_info_by_label (BilProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.label <> l)))) /\

    (!p l i bl.
          (bil_get_program_block_info_by_label (BilProgram p) l = SOME (i, bl)) <=>
          ((((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.label = l) /\
             (!j'. j' < i ==> (EL j' p).label <> l))))``,

SIMP_TAC list_ss [bil_get_program_block_info_by_label_def, INDEX_FIND_EQ_NONE,
  listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0]);


val bil_get_program_block_info_by_label_valid_THM = store_thm ("bil_get_program_block_info_by_label_valid_THM",
  ``(!p l. ((bil_get_program_block_info_by_label (BilProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.label <> l)))) /\

    (!p l i bl. bil_is_valid_labels (BilProgram p) ==>
          ((bil_get_program_block_info_by_label (BilProgram p) l = SOME (i, bl)) <=>
           ((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.label = l)))``,

SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bil_get_program_block_info_by_label_def,
  INDEX_FIND_EQ_NONE, listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0] >>
REPEAT STRIP_TAC >>
`j' < LENGTH p` by DECIDE_TAC >>
`j' = i` by METIS_TAC[bil_is_valid_labels_blocks_EQ_EL] >>
FULL_SIMP_TAC arith_ss []);


val bil_get_program_block_info_by_label_valid_MEM = store_thm ("bil_get_program_block_info_by_label_valid_MEM",
  ``!p l. bil_is_valid_labels p /\ MEM l (bil_labels_of_program p) ==>
          (?i bl. bil_get_program_block_info_by_label p l = SOME (i, bl))``,

Cases >> rename1 `BilProgram p` >>
SIMP_TAC list_ss [bil_get_program_block_info_by_label_valid_THM,
  bil_labels_of_program_def, listTheory.MEM_MAP] >>
SIMP_TAC std_ss [listTheory.MEM_EL, GSYM RIGHT_EXISTS_AND_THM,
  GSYM LEFT_FORALL_IMP_THM] >>
METIS_TAC[]);



(* ------------------------------------------------------------------------- *)
(*  Program Counter                                                          *)
(* ------------------------------------------------------------------------- *)

val bil_is_valid_pc_def = Define `bil_is_valid_pc p pc =
   (?i bl. (bil_get_program_block_info_by_label p (pc.label) = SOME (i, bl)) /\
           (pc.index < LENGTH bl.statements))`;

val bil_is_end_pc_def = Define `bil_is_end_pc (BilProgram p) pc =
   (?i bl. (bil_get_program_block_info_by_label (BilProgram p) (pc.label) = SOME (i, bl)) /\
           ~(pc.index < LENGTH bl.statements) /\
      (!j. (i < j /\ j < LENGTH p) ==> (LENGTH ((EL j p).statements) = 0)))`;


val bil_is_valid_pc_not_end = store_thm ("bil_is_valid_pc_not_end",
  ``!p pc. bil_is_valid_pc p pc ==> ~(bil_is_end_pc p pc)``,
Cases >> rename1 `BilProgram p` >>
SIMP_TAC std_ss [bil_is_valid_pc_def, bil_is_end_pc_def,
  GSYM LEFT_FORALL_IMP_THM]);


val bil_is_valid_pc_of_valid_blocks = store_thm ("bil_is_valid_pc_of_valid_blocks",
  ``!p pc. bil_is_valid_labels (BilProgram p) ==>
           (bil_is_valid_pc (BilProgram p) pc <=> (?bl. MEM bl p /\ (pc.label = bl.label) /\
             (pc.index < LENGTH bl.statements)))``,
SIMP_TAC std_ss [bil_is_valid_pc_def, bil_get_program_block_info_by_label_valid_THM,
  listTheory.MEM_EL, GSYM LEFT_EXISTS_AND_THM] >>
METIS_TAC[]);


val bil_get_program_block_info_by_label_valid_pc = store_thm ("bil_get_program_block_info_by_label_valid_pc",
  ``!p pc. bil_is_valid_pc p pc ==> IS_SOME (bil_get_program_block_info_by_label p pc.label)``,

SIMP_TAC std_ss [bil_is_valid_pc_def, GSYM LEFT_FORALL_IMP_THM]);

val bil_get_current_statement_def = Define `bil_get_current_statement p pc =
  option_CASE (bil_get_program_block_info_by_label p pc.label) NONE
     (\ (_, bl). if (pc.index < LENGTH bl.statements) then SOME (EL (pc.index) bl.statements) else NONE) `;


val bil_get_current_statement_IS_SOME = store_thm ("bil_get_current_statement_IS_SOME",
  ``!p pc. IS_SOME (bil_get_current_statement p pc) <=> bil_is_valid_pc p pc``,

REPEAT GEN_TAC >>
Cases_on `bil_get_program_block_info_by_label p pc.label` >> (
  ASM_SIMP_TAC std_ss [bil_get_current_statement_def, bil_is_valid_pc_def]
) >>
SIMP_TAC (std_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) []);


val bil_pc_normalise_def = Define `
  (bil_pc_normalise (BilProgram p) pc = case bil_get_program_block_info_by_label (BilProgram p) (pc.label) of
        SOME (n, bl) => if (pc.index < LENGTH bl.statements)
          then SOME pc
          else (
            let p' = FILTER (\bl. LENGTH bl.statements > 0) (DROP (SUC n) p) in
            case p' of
              | [] => NONE
              | (bl'::_) => SOME <| label := bl'.label ; index := 0 |>
            )
      | _ => NONE
  )
`;


val bil_pc_next_def = Define `
  bil_pc_next p pc = bil_pc_normalise p (pc with index updated_by SUC)`


val bil_pc_normalise_EQ_SOME = store_thm ("bil_pc_normalise_EQ_SOME",
``!p pc i bl pc'. (bil_get_program_block_info_by_label (BilProgram p) (pc.label) = SOME (i, bl)) ==>
             ((bil_pc_normalise (BilProgram p) pc = SOME pc') <=>
                (if (pc.index < LENGTH bl.statements) then (pc' = pc) else
                (?j. (i < j /\ j < LENGTH p /\ (LENGTH ((EL j p).statements) <> 0) /\
                     (pc' = <| label := (EL j p).label; index := 0 |>) /\
                     (!j'. (i < j' /\ j' < j) ==> (LENGTH ((EL j' p).statements) = 0))))))``,

SIMP_TAC std_ss [bil_pc_normalise_def, pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >>
Cases_on `pc.index < LENGTH bl.statements` >- (
  ASM_SIMP_TAC arith_ss [] >> METIS_TAC[]
) >>
ASM_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `FILTER (\bl. LENGTH bl.statements > 0) (DROP (SUC i) p)` >| [
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  `MEM (EL j p) (DROP (SUC i) p)` by (
     SIMP_TAC (list_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, rich_listTheory.EL_DROP] >>
     Q.EXISTS_TAC `j - SUC i` >>
     ASM_SIMP_TAC arith_ss []
  ) >>
  `~(MEM (EL j p) (FILTER (\bl. LENGTH bl.statements > 0) (DROP (SUC i) p)))` by
    ASM_SIMP_TAC list_ss [] >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_FILTER] >>
  FULL_SIMP_TAC std_ss [],


  rename1 `FILTER _ _ = bl0::bls` >>
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  `?p1 p2. (LENGTH p1 = SUC i) /\ (p = p1 ++ p2)` by (
     Q.EXISTS_TAC `TAKE (SUC i) p` >>
     Q.EXISTS_TAC `DROP (SUC i) p` >>
     FULL_SIMP_TAC list_ss [bil_get_program_block_info_by_label_THM]
  ) >>
  FULL_SIMP_TAC list_ss [rich_listTheory.DROP_APPEND1, listTheory.DROP_LENGTH_TOO_LONG] >>
  Q.PAT_X_ASSUM `p = _ ++ _` (K ALL_TAC) >>
  Q.PAT_X_ASSUM `_ = SOME _` (K ALL_TAC) >>
  Induct_on `p2` >- ASM_SIMP_TAC list_ss [] >>
  CONV_TAC (RENAME_VARS_CONV ["bl1"]) >>
  REPEAT STRIP_TAC >>
  Cases_on `LENGTH (bl1.statements) > 0` >> FULL_SIMP_TAC list_ss [] >| [
    REPEAT (BasicProvers.VAR_EQ_TAC) >>
    EQ_TAC >> REPEAT STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >> ASM_SIMP_TAC list_ss [] >| [
      Q.EXISTS_TAC `SUC i` >>
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2],

      Cases_on `j = SUC i` >- ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2] >>
      Q.PAT_X_ASSUM `!j'. _` (MP_TAC o Q.SPEC `SUC i`) >>
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2]
    ],

    EQ_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >| [
      Q.EXISTS_TAC `SUC j` >>
      Q.PAT_X_ASSUM `LENGTH _ <> 0` MP_TAC >>
      Q.PAT_X_ASSUM `!j. _` MP_TAC >>
      `j - i = SUC (j - SUC i)` by DECIDE_TAC >>
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2] >>
      REPEAT STRIP_TAC >>
      Cases_on `j' = SUC i` >- ASM_SIMP_TAC list_ss [] >>
      Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `PRE j'`) >>
      `j' - SUC i = SUC (PRE j' - SUC i)` by DECIDE_TAC >>
      ASM_SIMP_TAC list_ss [],

      Q.EXISTS_TAC `PRE j` >>
      Q.PAT_X_ASSUM `LENGTH _ <> 0` MP_TAC >>
      Q.PAT_X_ASSUM `!j. _` MP_TAC >>

      Cases_on `j = SUC i` >- ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2] >>
      `j - SUC i = SUC (PRE j - SUC i)` by DECIDE_TAC >>
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2] >>
      REPEAT STRIP_TAC >>
      Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `SUC j'`) >>
      `j' - i = SUC (j' - SUC i)` by DECIDE_TAC >>
      ASM_SIMP_TAC list_ss []
    ]
  ]
]);


val bil_pc_normalise_EQ_NONE = store_thm ("bil_pc_normalise_EQ_NONE",
``!p pc i bl. (bil_get_program_block_info_by_label (BilProgram p) (pc.label) = SOME (i, bl)) ==>
             ((bil_pc_normalise (BilProgram p) pc = NONE) <=> (
                (LENGTH bl.statements <= pc.index) /\
                (!j. (i < j /\ j < LENGTH p) ==> (LENGTH ((EL j p).statements) = 0))))``,

SIMP_TAC std_ss [bil_pc_normalise_def, pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >>
Cases_on `pc.index < LENGTH bl.statements` >> (
  ASM_SIMP_TAC arith_ss []
) >>
Cases_on `FILTER (\bl. LENGTH bl.statements > 0) (DROP (SUC i) p)` >| [
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  REPEAT STRIP_TAC >>
  `MEM (EL j p) (DROP (SUC i) p)` by (
     SIMP_TAC (list_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, rich_listTheory.EL_DROP] >>
     Q.EXISTS_TAC `j - SUC i` >>
     ASM_SIMP_TAC arith_ss []
  ) >>
  `~(MEM (EL j p) (FILTER (\bl. LENGTH bl.statements > 0) (DROP (SUC i) p)))` by
    ASM_SIMP_TAC list_ss [] >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_FILTER] >>
  FULL_SIMP_TAC std_ss [],


  rename1 `FILTER _ _ = bl0::bls` >>
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  `MEM bl0 (FILTER (\bl. LENGTH bl.statements > 0) (DROP (SUC i) p))` by
    ASM_SIMP_TAC list_ss [] >>
  POP_ASSUM MP_TAC >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_FILTER] >>
  SIMP_TAC (list_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, rich_listTheory.EL_DROP] >>
  REPEAT STRIP_TAC >>
  rename1 `bl0 = EL (n + SUC i) p` >>
  Q.EXISTS_TAC `n + SUC i` >>
  FULL_SIMP_TAC list_ss []
]);


val bil_pc_normalise_EQ_NONE_is_end_pc = store_thm ("bil_pc_normalise_EQ_NONE_is_end_pc",
``!p pc. bil_is_valid_labels p /\ MEM (pc.label) (bil_labels_of_program p) ==>
         ((bil_pc_normalise p pc = NONE) <=> (
           bil_is_end_pc p pc))``,

REPEAT STRIP_TAC >>
`?i bl. bil_get_program_block_info_by_label p pc.label = SOME (i, bl)` by
  METIS_TAC[bil_get_program_block_info_by_label_valid_MEM] >>
Cases_on `p` >> rename1 `BilProgram p` >>
MP_TAC (Q.SPECL [`p`, `pc`, `i`, `bl`] bil_pc_normalise_EQ_NONE) >>
ASM_SIMP_TAC arith_ss [bil_is_end_pc_def, arithmeticTheory.NOT_LESS]);


val bil_pc_normalise_EQ_NONE_is_end_pc_IMP = store_thm ("bil_pc_normalise_EQ_NONE_is_end_pc_IMP",
``!p pc. (bil_is_valid_labels p /\ MEM (pc.label) (bil_labels_of_program p) /\
          (bil_pc_normalise p pc = NONE)) ==>
         bil_is_end_pc p pc``,
METIS_TAC[bil_pc_normalise_EQ_NONE_is_end_pc]);


val bil_pc_normalise_valid = store_thm ("bil_pc_normalise_valid",
``!p pc pc'. (bil_is_valid_labels p /\ (MEM pc.label (bil_labels_of_program p)) /\
              (bil_pc_normalise p pc = SOME pc')) ==>
             (bil_is_valid_pc p pc')``,

Cases >> rename1 `BilProgram p` >>
SIMP_TAC list_ss [bil_labels_of_program_def, bil_pc_normalise_EQ_SOME,
  listTheory.MEM_MAP, GSYM RIGHT_EXISTS_AND_THM] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [listTheory.MEM_EL] >>
rename1 `bl = EL i p` >>
`bil_get_program_block_info_by_label (BilProgram p) pc.label = SOME (i, bl)` by
  METIS_TAC[bil_get_program_block_info_by_label_valid_THM] >>

MP_TAC (Q.SPECL [`p`, `pc`, `i`, `bl`, `pc'`] bil_pc_normalise_EQ_SOME) >>
FULL_SIMP_TAC std_ss [bil_is_valid_pc_def] >>
Cases_on `pc.index < LENGTH (EL i p).statements` >| [
  ASM_SIMP_TAC std_ss [] >> METIS_TAC[],

  ASM_SIMP_TAC (std_ss++bil_pc_ss) [bil_get_program_block_info_by_label_valid_THM,
    GSYM LEFT_FORALL_IMP_THM] >>
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `j` >>
  ASM_SIMP_TAC arith_ss []
]);


val bil_pc_next_valid = store_thm ("bil_pc_next_valid",
``!p pc pc'. (bil_is_valid_labels p /\ bil_is_valid_pc p pc /\ (bil_pc_next p pc = SOME pc')) ==>
             (bil_is_valid_pc p pc')``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC bil_pc_normalise_valid >>
Q.EXISTS_TAC `pc with index updated_by SUC` >>
Cases_on `p` >>
FULL_SIMP_TAC (std_ss++bil_pc_ss) [bil_pc_next_def, bil_is_valid_pc_def, bil_labels_of_program_def,
  listTheory.MEM_MAP] >>
METIS_TAC[listTheory.MEM_EL, bil_get_program_block_info_by_label_valid_THM]);


val bil_pc_first_def = Define
  `bil_pc_first (BilProgram p) = let bl = HD (FILTER (\bl. LENGTH (bl.statements) > 0) p) in
    (<| label := bl.label; index := 0 |>):bil_programcounter_t`;

val bil_pc_last_def = Define
  `bil_pc_last (BilProgram p) = let bl = LAST (FILTER (\bl. LENGTH (bl.statements) > 0) p) in
    (<| label := bl.label; index := LENGTH bl.statements - 1 |>):bil_programcounter_t`;


val bil_program_stmts_count_FILTER_NEQ_NIL = store_thm ("bil_program_stmts_count_FILTER_NEQ_NIL",
  ``!p. (bil_program_stmts_count (BilProgram p) > 0) ==>
    (?bl0 bls. (FILTER (\bl. LENGTH bl.statements > 0) p = bl0 :: bls) /\
              EVERY (\bl. (LENGTH bl.statements > 0) /\ MEM bl p) (bl0::bls))``,

Induct_on `p` >> (
  FULL_SIMP_TAC list_ss [bil_program_stmts_count_def, bil_block_stmts_count_def]
) >>
CONV_TAC (RENAME_VARS_CONV ["bl"]) >> GEN_TAC >>
Cases_on `LENGTH bl.statements` >| [
  SIMP_TAC list_ss [] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM],

  SIMP_TAC list_ss [listTheory.EVERY_FILTER] >>
  ASM_SIMP_TAC list_ss [listTheory.EVERY_MEM]
]);


val bil_pc_first_valid = store_thm ("bil_pc_first_valid",
  ``!p. bil_is_valid_program p ==> bil_is_valid_pc p (bil_pc_first p)``,

Cases >> rename1 `BilProgram p` >>
SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_pc_of_valid_blocks, bil_is_valid_program_def,
  bil_pc_first_def, LET_DEF] >>
ASSUME_TAC (Q.SPEC `p` bil_program_stmts_count_FILTER_NEQ_NIL) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [] >>
rename1 `LENGTH bl0.statements > 0` >>
Q.EXISTS_TAC `bl0` >>
ASM_SIMP_TAC list_ss []);


val bil_pc_last_valid = store_thm ("bil_pc_last_valid",
  ``!p. bil_is_valid_program p ==> bil_is_valid_pc p (bil_pc_last p)``,

Cases >> rename1 `BilProgram p` >>
SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_pc_of_valid_blocks, bil_is_valid_program_def,
  bil_pc_last_def, LET_DEF] >>
ASSUME_TAC (Q.SPEC `p` bil_program_stmts_count_FILTER_NEQ_NIL) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [] >>
rename1 `FILTER _ p = bl0::bls` >>
Q.EXISTS_TAC `LAST (bl0::bls)` >>
`MEM (LAST (bl0::bls)) (bl0::bls)` by MATCH_ACCEPT_TAC rich_listTheory.MEM_LAST >>
FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM, arithmeticTheory.GREATER_DEF]);


val bil_is_valid_pc_label_OK = store_thm ("bil_is_valid_pc_label_OK",
  ``!p pc. bil_is_valid_pc p pc ==> MEM pc.label (bil_labels_of_program p)``,

Cases_on `p` >> rename1 `BilProgram p` >>
SIMP_TAC std_ss [bil_is_valid_pc_def, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bil_labels_of_program_def,
  bil_get_program_block_info_by_label_THM] >>
SIMP_TAC std_ss [listTheory.MEM_EL, GSYM RIGHT_EXISTS_AND_THM] >>
METIS_TAC[]);


val bil_pc_next_valid_EQ_NONE = store_thm ("bil_pc_next_valid_EQ_NONE",
``!p pc. (bil_is_valid_labels p /\ bil_is_valid_pc p pc) ==>
          ((bil_pc_next p pc = NONE) <=> (pc = bil_pc_last p))``,

REPEAT STRIP_TAC >>
`MEM (pc with index updated_by SUC).label (bil_labels_of_program p)` by (
  ASM_SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_pc_label_OK]
) >>
ASM_SIMP_TAC std_ss [bil_pc_next_def, bil_pc_normalise_EQ_NONE_is_end_pc] >>


Cases_on `p` >> rename1 `BilProgram p` >>
ASM_SIMP_TAC (std_ss++bil_pc_ss) [bil_pc_last_def, LET_THM, bil_is_end_pc_def] >>

`FILTER (\bl. LENGTH bl.statements > 0) p <> []` by (
  STRIP_TAC  >>
  FULL_SIMP_TAC std_ss [bil_is_valid_pc_def, bil_get_program_block_info_by_label_THM] >>
  `MEM (EL i p) (FILTER (\bl. LENGTH bl.statements > 0) p)` suffices_by ASM_SIMP_TAC list_ss [] >>
  SIMP_TAC list_ss [listTheory.MEM_FILTER, listTheory.MEM_EL] >>
  REPEAT STRIP_TAC >| [
    DECIDE_TAC,
    METIS_TAC[]
  ]
) >>

IMP_RES_TAC LAST_FILTER_EL >>
FULL_SIMP_TAC (list_ss++bil_pc_ss) [DB.fetch "-" "bil_programcounter_t_component_equality",
  bil_is_valid_pc_def] >>
REV_FULL_SIMP_TAC std_ss [bil_get_program_block_info_by_label_valid_THM] >>
EQ_TAC >> STRIP_TAC >| [
  `~(i < i')` by (
    STRIP_TAC >>
    `~(LENGTH bl.statements > 0)` by METIS_TAC[] >>
    DECIDE_TAC
  ) >>
  `~(i' < i)` by (
    STRIP_TAC >>
    `LENGTH (EL i p).statements = 0` by METIS_TAC[] >>
    DECIDE_TAC
  ) >>
  `i' = i` by DECIDE_TAC >>
  FULL_SIMP_TAC arith_ss [],

  `bl = EL i p` by METIS_TAC [bil_is_valid_labels_blocks_EQ, listTheory.MEM_EL] >>
  `i' = i` by METIS_TAC [bil_is_valid_labels_blocks_EQ_EL] >>
  FULL_SIMP_TAC arith_ss [] >>
  REPEAT STRIP_TAC >>
  `~(LENGTH (EL j p).statements > 0)` by METIS_TAC[] >>
  ASM_SIMP_TAC arith_ss []
]);



(* ------------------------------------------------------------------------- *)
(* Auxiliary stuff                                                           *)
(* ------------------------------------------------------------------------- *)

(* This definition is oriented to give an RX name to registers *)
val r2s_def = Define `r2s = \(w:bool[5]).STRCAT ("R") (w2s (10:num) HEX w)`;

val r2s_REWRS = store_thm ("r2s_REWRS", ``
  (r2s  0w = "R0" ) /\ (r2s  1w = "R1" ) /\ (r2s  2w = "R2" ) /\ (r2s  3w = "R3" ) /\
  (r2s  4w = "R4" ) /\ (r2s  5w = "R5" ) /\ (r2s  6w = "R6" ) /\ (r2s  7w = "R7" ) /\
  (r2s  8w = "R8" ) /\ (r2s  9w = "R9" ) /\ (r2s 10w = "R10") /\ (r2s 11w = "R11") /\
  (r2s 12w = "R12") /\ (r2s 13w = "R13") /\ (r2s 14w = "R14") /\ (r2s 15w = "R15") /\
  (r2s 16w = "R16") /\ (r2s 17w = "R17") /\ (r2s 18w = "R18") /\ (r2s 19w = "R19") /\
  (r2s 20w = "R20") /\ (r2s 21w = "R21") /\ (r2s 22w = "R22") /\ (r2s 23w = "R23") /\
  (r2s 24w = "R24") /\ (r2s 25w = "R25") /\ (r2s 26w = "R26") /\ (r2s 27w = "R27") /\
  (r2s 28w = "R28") /\ (r2s 29w = "R29") /\ (r2s 30w = "R30") /\ (r2s 31w = "R31")``,
EVAL_TAC);


(* Statement to string (useful for debugging purposes) *)
val bil_stmt_to_string_def = Define `bil_stmt_to_string stmt = case stmt of
  | Declare (Var s _) => CONCAT ["Declaration of "; s]
  | Assign (Var s _) _ => CONCAT ["Assignment of "; s]
  | Jmp _ => "Jump"
  | CJmp _ _ _ => "Conditional Jump"
  | Halt _ => "Halt"
  | Assert _ => "Assert"
  | Assume _ => "Assume"
  | _ => "-- unsupported statement"
`;


(* ------------------------------------------------------------------------- *)
(*  Program State                                                            *)
(* ------------------------------------------------------------------------- *)

val bil_state_add_execs_def = Define `bil_state_add_execs st n =
  st with execs updated_by ($+ n)`

val bil_state_is_terminated_def = Define `bil_state_is_terminated st =
  (st.termcode <> Running)`

val bil_state_is_failed_def = Define `bil_state_is_failed st =
  (st.termcode = Failed)`

val bil_state_set_failed_def = Define `bil_state_set_failed st msg =
  (st with termcode := Failed) with debug updated_by (\dbg. msg::dbg)`

val bil_state_set_failed_is_failed = store_thm ("bil_state_set_failed_is_failed",
  ``!st msg. bil_state_is_failed (bil_state_set_failed st msg)``,
SIMP_TAC (std_ss ++ bil_state_ss) [bil_state_set_failed_def, bil_state_is_failed_def]);

val bil_state_set_pc_def = Define `
  (bil_state_set_pc (st:bil_state_t) NONE = st with termcode := ReachedEnd) /\
  (bil_state_set_pc (st:bil_state_t) (SOME pc') = st with pc := pc')`


val bil_state_normalise_pc_def = Define `bil_state_normalise_pc p (st:bil_state_t) =
  case bil_pc_normalise p st.pc of
    | SOME pc' => (st with pc := pc')
    | NONE => (st with termcode := ReachedEnd)`;

val bil_state_incr_pc_def = Define `bil_state_incr_pc p (st:bil_state_t) =
  bil_state_normalise_pc p (st with pc := (st.pc with index updated_by SUC))`

val bil_state_set_pc_def = Define `bil_state_set_pc p (st:bil_state_t) pc' =
  bil_state_normalise_pc p (st with pc := pc')`;


val bil_is_valid_state_def = Define `bil_is_valid_state p st <=>
  ((is_valid_env st.environ) /\ (if st.termcode = ReachedEnd then bil_is_end_pc p st.pc else
      bil_is_valid_pc p st.pc))`;

val bil_state_init_def = Define `bil_state_init p = <|
    pc       := bil_pc_first p
  ; environ  := empty_env
  ; termcode := Running
  ; debug    := []
  ; execs    := 0
|>`;

val bil_state_init_valid = store_thm ("bil_state_init_valid",
  ``!p. bil_is_valid_program p ==> bil_is_valid_state p (bil_state_init p)``,

SIMP_TAC (std_ss++bil_state_ss++bil_termcode_ss) [bil_is_valid_state_def, bil_state_init_def,
  bil_pc_first_valid, is_valid_env_empty]);



(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

(* Execution of Jmp, CJmp, Halt, Assert, Assume doesn't change environment *)

val bil_declare_initial_value_def = Define `
  (bil_declare_initial_value NoType = NONE) /\
  (bil_declare_initial_value (ImmType _) = NONE) /\
  (bil_declare_initial_value (MemType at vt) = SOME (Mem at vt (K 0)))`;

val bil_exec_stmt_declare_def = Define `bil_exec_stmt_declare p v ty (st : bil_state_t) =
   let env = (
      let vo = bil_declare_initial_value ty in
      if bil_env_var_is_bound v st.environ then IrregularEnv else
      bil_env_update v vo ty st.environ) in
    if (is_env_regular env) then
       bil_state_incr_pc p (st with environ := env)
    else
       bil_state_set_failed st (CONCAT ["irregular environment after "; bil_stmt_to_string
          (Declare (Var v ty))])`;

val bil_exec_stmt_assign_def = Define `bil_exec_stmt_assign p v ex (st : bil_state_t) =
   let env = bil_env_write v (bil_eval_exp ex st.environ) st.environ in
    if (is_env_regular env) then
       bil_state_incr_pc p (st with environ := env)
    else
       bil_state_set_failed st (CONCAT ["irregular environment after "; bil_stmt_to_string
          (Assign v ex)])`;

val bil_exec_stmt_halt_def = Define `bil_exec_stmt_halt ex (st : bil_state_t) =
    (st with termcode := Halted (bil_eval_exp ex st.environ))`

val bil_exec_stmt_jmp_def = Define `bil_exec_stmt_jmp p l (st : bil_state_t) =
    if (MEM l (bil_labels_of_program p)) then
      bil_state_set_pc p st <| label := l; index := 0 |>
    else (st with termcode := (ReachedUnknownLabel l))`;

val bil_exec_stmt_cjmp_def = Define `bil_exec_stmt_cjmp p ex l1 l2 (st : bil_state_t) =
  case (bil_dest_bool_val (bil_eval_exp ex st.environ)) of
    | SOME T => bil_exec_stmt_jmp p l1 st
    | SOME F => bil_exec_stmt_jmp p l2 st
    | NONE => bil_state_set_failed st "condition of cjmp failed to evaluate"`;

val bil_exec_stmt_assert_def = Define `bil_exec_stmt_assert p ex (st : bil_state_t) =
  case (bil_dest_bool_val (bil_eval_exp ex st.environ)) of
    | SOME T => bil_state_incr_pc p st
    | SOME F => bil_state_set_failed st "assertion failed"
    | NONE => bil_state_set_failed st "condition of assert failed to evaluate"`

val bil_exec_stmt_assume_def = Define `bil_exec_stmt_assume p ex (st : bil_state_t) =
  case (bil_dest_bool_val (bil_eval_exp ex st.environ)) of
    | SOME T => bil_state_incr_pc p st
    | SOME F => (st with termcode := AssumptionViolated)
    | NONE => bil_state_set_failed st "condition of assume failed to evaluate"`;


val bil_exec_stmt_def = Define `
  (bil_exec_stmt p (Jmp l) st = bil_exec_stmt_jmp p l st) /\
  (bil_exec_stmt p (CJmp e l1 l2) st = bil_exec_stmt_cjmp p e l1 l2 st) /\
  (bil_exec_stmt p (Declare v) st = bil_exec_stmt_declare p (bil_var_name v) (bil_var_type v) st) /\
  (bil_exec_stmt p (Assert ex) st = bil_exec_stmt_assert p ex st) /\
  (bil_exec_stmt p (Assume ex) st = bil_exec_stmt_assume p ex st) /\
  (bil_exec_stmt p (Assign v ex) st = bil_exec_stmt_assign p v ex st) /\
  (bil_exec_stmt p (Halt ex) st = bil_exec_stmt_halt ex st)`;


val bil_exec_step_def = Define `bil_exec_step p state =
  if (bil_state_is_terminated state) then state else
  case (bil_get_current_statement p state.pc) of
    | NONE => bil_state_set_failed state "invalid program_counter"
    | SOME stm => (bil_exec_stmt p stm state) with execs updated_by SUC
`;

val bil_is_valid_state_exec_ignore = store_thm ("bil_is_valid_state_exec_ignore",
  ``!p st f. bil_is_valid_state p (st with execs updated_by f) =
             bil_is_valid_state p st``,
SIMP_TAC (std_ss++bil_state_ss) [bil_is_valid_state_def]);


val bil_exec_step_valid_THM = store_thm ("bil_exec_step_valid_THM",
 ``!p st. bil_is_valid_state p st ==>
          (if bil_state_is_terminated st then
             (bil_exec_step p st = st)
           else
             (bil_is_valid_pc p st.pc) /\
             (?stmt. (bil_get_current_statement p st.pc = SOME stmt) /\
                     (bil_exec_step p st = (bil_exec_stmt p stmt st with execs updated_by SUC))))``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bil_exec_step_def] >>
Cases_on `bil_state_is_terminated st` >> ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] >>
`st.termcode <> ReachedEnd` by (
  STRIP_TAC >> FULL_SIMP_TAC (std_ss++bil_termcode_ss) [bil_state_is_terminated_def]
) >>
`?stm. bil_get_current_statement p st.pc = SOME stm` by (
  `IS_SOME (bil_get_current_statement p st.pc)` suffices_by METIS_TAC[optionTheory.IS_SOME_EXISTS] >>
  FULL_SIMP_TAC std_ss [bil_get_current_statement_IS_SOME,
     bil_is_valid_state_def]
) >>
FULL_SIMP_TAC std_ss [bil_is_valid_state_def]);


val bil_is_valid_state_set_failed = store_thm ("bil_is_valid_state_set_failed",
  ``!p st msg. bil_is_valid_state p st /\ bil_is_valid_pc p st.pc ==>
               bil_is_valid_state p (bil_state_set_failed st msg)``,
SIMP_TAC (std_ss++bil_termcode_ss++bil_state_ss) [bil_is_valid_state_def, bil_state_set_failed_def]);


val bil_is_valid_state_incr_pc = store_thm ("bil_is_valid_state_incr_pc",
  ``!p st. bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc ==>
           bil_is_valid_state p (bil_state_incr_pc p st)``,
SIMP_TAC (std_ss++bil_state_ss++boolSimps.CONJ_ss) [bil_state_incr_pc_def, bil_is_valid_state_def,
  bil_state_normalise_pc_def, bil_is_valid_pc_not_end
] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on `bil_pc_normalise p (st.pc with index updated_by SUC)` >- (
  ASM_SIMP_TAC (std_ss++bil_state_ss) [] >>
  MATCH_MP_TAC bil_pc_normalise_EQ_NONE_is_end_pc_IMP >>
  FULL_SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_pc_label_OK,
    bil_is_valid_program_def]
) >>
rename1 `_ = SOME pc'` >>
ASM_SIMP_TAC (std_ss++bil_pc_ss++bil_state_ss) [] >>
MATCH_MP_TAC bil_pc_normalise_valid >>
Q.EXISTS_TAC `st.pc with index updated_by SUC` >>
FULL_SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_pc_label_OK,
   bil_is_valid_program_def]);



val bil_exec_step_valid_state_invar_declare = prove (
  ``!p st v. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
             bil_is_valid_state p (bil_exec_stmt p (Declare v) st)``,
Cases_on `v` >> rename1 `Var v ty` >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bil_exec_stmt_def, bil_exec_stmt_declare_def, LET_THM,
  bil_is_valid_state_set_failed, is_env_regular_def, bil_var_type_def, bil_var_name_def] >>
REPEAT STRIP_TAC >>
MATCH_MP_TAC bil_is_valid_state_incr_pc >>
ASM_SIMP_TAC (std_ss++bil_state_ss) [] >>
FULL_SIMP_TAC (std_ss++bil_state_ss) [bil_is_valid_state_def] >>
Q.PAT_X_ASSUM `is_env_regular _` MP_TAC >>
Cases_on `st.environ` >> SIMP_TAC std_ss [bil_env_update_def, is_env_regular_def] >>
COND_CASES_TAC >- SIMP_TAC std_ss [is_env_regular_def] >>
FULL_SIMP_TAC (std_ss) [is_env_regular_def, is_valid_env_def] >>
ConseqConv.CONSEQ_REWRITE_TAC ([finite_mapTheory.FEVERY_STRENGTHEN_THM], [], []) >>
Cases_on `bil_declare_initial_value ty` >> FULL_SIMP_TAC std_ss []);


val bil_exec_step_valid_state_invar_assign = prove (
  ``!p st v ex. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
                 bil_is_valid_state p (bil_exec_stmt p (Assign v ex) st)``,
Cases_on `v` >> rename1 `Var v ty` >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bil_exec_stmt_def, bil_exec_stmt_assign_def, LET_THM,
  bil_is_valid_state_set_failed, is_env_regular_def] >>
REPEAT STRIP_TAC >>
MATCH_MP_TAC bil_is_valid_state_incr_pc >>
ASM_SIMP_TAC (std_ss++bil_state_ss) [] >>
FULL_SIMP_TAC (std_ss++bil_state_ss) [bil_is_valid_state_def] >>
Q.PAT_X_ASSUM `is_env_regular _` MP_TAC >>
SIMP_TAC std_ss [bil_env_write_def] >>
COND_CASES_TAC >> SIMP_TAC std_ss [is_env_regular_def, bil_var_name_def, bil_var_type_def] >>
Cases_on `st.environ` >> SIMP_TAC std_ss [bil_env_update_def, is_env_regular_def] >>
COND_CASES_TAC >> SIMP_TAC std_ss [is_env_regular_def, is_valid_env_def] >>
ConseqConv.CONSEQ_REWRITE_TAC ([finite_mapTheory.FEVERY_STRENGTHEN_THM], [], []) >>
FULL_SIMP_TAC std_ss [is_valid_env_def]);


val bil_exec_step_valid_state_invar_jmp' = prove (
  ``!p st l. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
             bil_is_valid_state p (bil_exec_stmt_jmp p l st)``,
SIMP_TAC std_ss [bil_exec_stmt_jmp_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >| [
  ASM_SIMP_TAC (std_ss++bil_state_ss) [bil_is_valid_state_def, bil_state_set_pc_def,
    bil_state_normalise_pc_def] >>
  Cases_on `bil_pc_normalise p <|label := l; index := 0|>` >| [
    FULL_SIMP_TAC (std_ss++bil_state_ss) [bil_is_valid_state_def] >>
    MATCH_MP_TAC bil_pc_normalise_EQ_NONE_is_end_pc_IMP >>
    FULL_SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_program_def],

    rename1 `_ = SOME pc'` >>
    FULL_SIMP_TAC (std_ss++bil_pc_ss++bil_state_ss) [bil_is_valid_state_def,
      bil_is_valid_pc_not_end] >>
    MATCH_MP_TAC bil_pc_normalise_valid >>
    Q.EXISTS_TAC `<|label := l; index := 0|>` >>
    FULL_SIMP_TAC (std_ss++bil_pc_ss) [bil_is_valid_program_def]
  ],

  FULL_SIMP_TAC (std_ss++bil_state_ss++bil_termcode_ss) [bil_is_valid_state_def]
]);

val bil_exec_step_valid_state_invar_jmp = prove (
  ``!p st l. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
             bil_is_valid_state p (bil_exec_stmt p (Jmp l) st)``,
SIMP_TAC std_ss [bil_exec_stmt_def, bil_exec_step_valid_state_invar_jmp']);


val bil_exec_step_valid_state_invar_cjmp = prove (
  ``!p st ex l1 l2.
       (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
       bil_is_valid_state p (bil_exec_stmt p (CJmp ex l1 l2) st)``,
SIMP_TAC std_ss [bil_exec_stmt_def, bil_exec_stmt_cjmp_def] >>
REPEAT STRIP_TAC >>
Cases_on `bil_dest_bool_val (bil_eval_exp ex st.environ)` >- (
  ASM_SIMP_TAC std_ss [bil_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >> (
  ASM_SIMP_TAC std_ss [bil_exec_step_valid_state_invar_jmp']
));


val bil_exec_step_valid_state_invar_halt = prove (
  ``!p st ex. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
               bil_is_valid_state p (bil_exec_stmt p (Halt ex) st)``,

SIMP_TAC (std_ss++bil_state_ss++bil_termcode_ss) [bil_exec_stmt_def, bil_exec_stmt_halt_def,
  bil_is_valid_state_def]);


val bil_exec_step_valid_state_invar_assert = prove (
  ``!p st ex. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
               bil_is_valid_state p (bil_exec_stmt p (Assert ex) st)``,

SIMP_TAC (std_ss++bil_state_ss++bil_termcode_ss) [bil_exec_stmt_def, bil_exec_stmt_assert_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on `bil_dest_bool_val (bil_eval_exp ex st.environ)` >- (
  ASM_SIMP_TAC std_ss [bil_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >| [
  ASM_SIMP_TAC std_ss [bil_is_valid_state_incr_pc],
  ASM_SIMP_TAC std_ss [bil_is_valid_state_set_failed]
]);


val bil_exec_step_valid_state_invar_assume = prove (
  ``!p st ex. (bil_is_valid_program p /\ bil_is_valid_state p st /\ bil_is_valid_pc p st.pc) ==>
               bil_is_valid_state p (bil_exec_stmt p (Assume ex) st)``,

SIMP_TAC (std_ss++bil_state_ss++bil_termcode_ss) [bil_exec_stmt_def, bil_exec_stmt_assume_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on `bil_dest_bool_val (bil_eval_exp ex st.environ)` >- (
  ASM_SIMP_TAC std_ss [bil_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >| [
  ASM_SIMP_TAC std_ss [bil_is_valid_state_incr_pc],
  FULL_SIMP_TAC (std_ss++bil_state_ss++bil_termcode_ss) [bil_is_valid_state_def]
]);


val bil_exec_step_valid_state_invar = store_thm ("bil_exec_step_valid_state_invar",
``!p st. bil_is_valid_program p /\ bil_is_valid_state p st ==>
         bil_is_valid_state p (bil_exec_step p st)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bil_exec_step_valid_THM >>
Cases_on `bil_state_is_terminated st` >> FULL_SIMP_TAC std_ss [bil_is_valid_state_exec_ignore] >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bil_exec_step_valid_state_invar_declare,
    bil_exec_step_valid_state_invar_assign,
    bil_exec_step_valid_state_invar_cjmp,
    bil_exec_step_valid_state_invar_jmp,
    bil_exec_step_valid_state_invar_halt,
    bil_exec_step_valid_state_invar_assume,
    bil_exec_step_valid_state_invar_assert]
));

val bil_state_normalise_pc_execs = store_thm ("bil_state_normalise_pc_execs",
  ``!p st. (bil_state_normalise_pc p st).execs = st.execs``,
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bil_state_normalise_pc_def] >>
Cases_on `bil_pc_normalise p st.pc` >> (
  ASM_SIMP_TAC (std_ss++bil_state_ss) []
));


val bil_state_incr_pc_execs = store_thm ("bil_state_incr_pc_execs",
  ``!p st. (bil_state_incr_pc p st).execs = st.execs``,
SIMP_TAC (std_ss++bil_state_ss) [bil_state_incr_pc_def, bil_state_normalise_pc_execs]);


val bil_state_set_failed_execs = store_thm ("bil_state_set_failed_execs",
  ``!st msg. (bil_state_set_failed st msg).execs = st.execs``,
SIMP_TAC (std_ss++bil_state_ss) [bil_state_set_failed_def]);


val bil_state_set_pc_execs = store_thm ("bil_state_set_pc_execs",
  ``!st p pc'. (bil_state_set_pc p st pc').execs = st.execs``,
SIMP_TAC (std_ss++bil_state_ss) [bil_state_set_pc_def,
  bil_state_normalise_pc_execs]);

val bil_exec_step_execs = store_thm ("bil_exec_step_execs",
``!p st. bil_is_valid_state p st ==>
         (if bil_state_is_terminated st then
           (bil_exec_step p st = st)
         else ((bil_exec_step p st).execs = SUC (st.execs)))``,


REPEAT STRIP_TAC >>
IMP_RES_TAC bil_exec_step_valid_THM >>
Cases_on `bil_state_is_terminated st` >> FULL_SIMP_TAC (std_ss++bil_state_ss) [] >>
Cases_on `stmt` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++bil_state_ss) [bil_exec_stmt_def,
    bil_exec_stmt_declare_def, bil_exec_stmt_cjmp_def,
    bil_exec_stmt_assume_def, bil_exec_stmt_assign_def, bil_exec_stmt_jmp_def,
    LET_THM, bil_exec_stmt_halt_def, bil_exec_stmt_assert_def] >>
  REPEAT CASE_TAC >> (
    SIMP_TAC (std_ss++bil_state_ss) [bil_state_incr_pc_execs, bil_state_set_failed_execs,
      bil_state_set_pc_execs]
  )
));



(* Multiple execution of step *)
val bil_exec_steps_opt_def = Define `bil_exec_steps_opt p state b max_steps =
   OWHILE (\ (n, st). option_CASE max_steps T (\m. n < (m:num)) /\
                      ~(bil_state_is_terminated st)) (\ (n, st).
     (SUC n, bil_exec_step p st)) (b, state)`;

val bil_exec_step_n_def = Define `
  bil_exec_step_n p state n = THE (bil_exec_steps_opt p state 0 (SOME n))`;

val bil_exec_steps_def = Define `
  (bil_exec_steps p state = bil_exec_steps_opt p state 0 NONE)`


val bil_exec_steps_opt_NONE_REWRS = store_thm ("bil_exec_steps_opt_NONE_REWRS",
  ``bil_exec_steps_opt p state b NONE =
    (if bil_state_is_terminated state then SOME (b, state) else
       bil_exec_steps_opt p (bil_exec_step p state) (SUC b) NONE)``,

SIMP_TAC std_ss [Once whileTheory.OWHILE_THM, bil_exec_steps_opt_def] >>
METIS_TAC[]);


val bil_exec_steps_opt_SOME_REWRS = store_thm ("bil_exec_steps_opt_SOME_REWRS",
  ``bil_exec_steps_opt p state b (SOME m) =
    (if ((m <= b) \/ bil_state_is_terminated state) then SOME (b, state) else
       bil_exec_steps_opt p (bil_exec_step p state) (SUC b) (SOME m))``,

SIMP_TAC std_ss [Once whileTheory.OWHILE_THM, bil_exec_steps_opt_def] >>
COND_CASES_TAC >> FULL_SIMP_TAC arith_ss []);


val FUNPOW_bil_exec_steps_opt_REWR = store_thm ("FUNPOW_bil_exec_steps_opt_REWR",
  ``!n b st. (FUNPOW (\(n,st). (SUC n,bil_exec_step p st)) n (b,st)) =
      (b + n, FUNPOW (bil_exec_step p) n st)``,
Induct >> ASM_SIMP_TAC arith_ss [arithmeticTheory.FUNPOW]);


val bil_exec_steps_opt_EQ_NONE = store_thm ("bil_exec_steps_opt_EQ_NONE",
  ``(bil_exec_steps_opt p state b mo = NONE) <=>
    ((mo = NONE) /\ (!n. ~(bil_state_is_terminated (FUNPOW (bil_exec_step p) n state))))``,

SIMP_TAC (std_ss ++ boolSimps.EQUIV_EXTRACT_ss) [bil_exec_steps_opt_def, whileTheory.OWHILE_EQ_NONE,
  FUNPOW_bil_exec_steps_opt_REWR, FORALL_AND_THM] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
Cases_on `mo` >> SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `x` >> DECIDE_TAC);


val bil_exec_steps_EQ_NONE = store_thm ("bil_exec_steps_EQ_NONE",
  ``(bil_exec_steps p state = NONE) <=>
    (!n. ~(bil_state_is_terminated (FUNPOW (bil_exec_step p) n state)))``,

SIMP_TAC std_ss [bil_exec_steps_def, bil_exec_steps_opt_EQ_NONE]);


val bil_exec_steps_opt_EQ_SOME = store_thm ("bil_exec_steps_opt_EQ_SOME",
  ``(case mo of NONE => T | SOME m => (b <= m)) ==>
    ((bil_exec_steps_opt p state b mo = SOME (c, state')) <=>
    ((case mo of NONE => (bil_state_is_terminated state')
               | SOME m => ((c <= m) /\ ((c < m) ==> (bil_state_is_terminated state')))) /\
     (b <= c) /\
     (state' = FUNPOW (bil_exec_step p) (c - b) state) /\
     (!n. n < c-b ==> ~(bil_state_is_terminated (FUNPOW (bil_exec_step p) n state)))))``,

SIMP_TAC std_ss [whileTheory.OWHILE_def, bil_exec_steps_opt_def, FUNPOW_bil_exec_steps_opt_REWR] >>
STRIP_TAC >>
Q.ABBREV_TAC `P = \n. ~(case mo of NONE => T | SOME m => b + n < m) \/
  bil_state_is_terminated (FUNPOW (bil_exec_step p) n state)` >>
Tactical.REVERSE (Cases_on `?n. P n`) >- (
  UNABBREV_ALL_TAC >>
  FULL_SIMP_TAC std_ss [FORALL_AND_THM] >>
  Cases_on `mo` >| [
    SIMP_TAC std_ss [] >> METIS_TAC[],

    rename1 `SOME m` >>
    FULL_SIMP_TAC arith_ss [] >>
    Q.PAT_X_ASSUM `!n. b + n < m` (MP_TAC o Q.SPEC `m`) >>
    SIMP_TAC arith_ss []
  ]
) >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `$? (P:num->bool)` (fn thm => REWRITE_TAC [thm]) >- (
  UNABBREV_ALL_TAC >>
  Q.EXISTS_TAC `n` >> FULL_SIMP_TAC std_ss []
) >>
Tactical.REVERSE (Cases_on `b <= c`) >> ASM_SIMP_TAC arith_ss [] >>
Q.ABBREV_TAC `n' = c - b` >>
`c = b + n'` by (UNABBREV_ALL_TAC >> DECIDE_TAC) >>
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
STRIP_TAC >>
EQ_TAC >| [
  STRIP_TAC >>
  `!n. n < n' ==> ~(P n)` by METIS_TAC [whileTheory.LESS_LEAST] >>
  `P n'` by METIS_TAC[whileTheory.FULL_LEAST_INTRO] >>
  NTAC 2 (POP_ASSUM MP_TAC) >>
  Q.PAT_X_ASSUM `P n` (K ALL_TAC) >>
  Q.PAT_X_ASSUM `$LEAST P = _` (K ALL_TAC) >>
  Q.UNABBREV_TAC `P` >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `mo` >> SIMP_TAC arith_ss [DISJ_IMP_THM] >>
  Cases_on `b + n' <= x` >> ASM_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC arith_ss [] >>
  Cases_on `n'` >- FULL_SIMP_TAC arith_ss [] >>
  rename1 `~(b + SUC n'' <= _)` >>
  Q.EXISTS_TAC `n''` >>
  ASM_SIMP_TAC arith_ss [],


  STRIP_TAC >>
  MATCH_MP_TAC bitTheory.LEAST_THM >>
  Q.PAT_X_ASSUM `P n` (K ALL_TAC) >>
  Q.UNABBREV_TAC `P` >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `mo` >> FULL_SIMP_TAC arith_ss [] >>
  METIS_TAC[]
]);



val bil_exec_steps_EQ_SOME = store_thm ("bil_exec_steps_EQ_SOME",
  ``((bil_exec_steps p state = SOME (c, state')) <=>
    ((bil_state_is_terminated state') /\
     (state' = FUNPOW (bil_exec_step p) c state) /\
     (!n. n < c ==> ~(bil_state_is_terminated (FUNPOW (bil_exec_step p) n state)))))``,

SIMP_TAC std_ss [bil_exec_steps_def, bil_exec_steps_opt_EQ_SOME]);


val bil_exec_step_n_EQ_THM = store_thm ("bil_exec_step_n_EQ_THM",
  ``((bil_exec_step_n p state n = (c, state')) <=>
     ((c <= n) /\ ((c < n) ==> (bil_state_is_terminated state'))) /\
     (state' = FUNPOW (bil_exec_step p) c state) /\
     (!n'. n' < c ==> ~(bil_state_is_terminated (FUNPOW (bil_exec_step p) n' state))))``,

SIMP_TAC std_ss [bil_exec_step_n_def] >>
Cases_on `bil_exec_steps_opt p state 0 (SOME n)` >- (
  FULL_SIMP_TAC std_ss [bil_exec_steps_opt_EQ_NONE]
) >>
FULL_SIMP_TAC std_ss [] >>
rename1 `x = (c, state')` >>
Cases_on `x` >>
rename1 `(c0, state'') = (c, state')` >>
FULL_SIMP_TAC (std_ss) [bil_exec_steps_opt_EQ_SOME] >>
EQ_TAC >> STRIP_TAC >- (
  REPEAT (BasicProvers.VAR_EQ_TAC) >>
  ASM_SIMP_TAC std_ss []
) >>
ASM_SIMP_TAC (std_ss ++ boolSimps.CONJ_ss) [] >>
Cases_on `c < c0` >- (
  `c < n` by DECIDE_TAC >>
  METIS_TAC[]
) >>
Cases_on `c0 < c` >- (
  `c0 < n` by DECIDE_TAC >>
  METIS_TAC[]
) >>
DECIDE_TAC);


(* ------------------------------------------------------------------------- *)

val _ = export_theory();
