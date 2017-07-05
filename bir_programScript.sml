open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory;
open wordsLib;

val _ = new_theory "bir_program";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_label_t =
    BL_Label string
  | BL_Address bir_imm_t
`;

val _ = Datatype `bir_stmt_t =
  | BStmt_Declare bir_var_t
  | BStmt_Assign  bir_var_t bir_exp_t
  | BStmt_Jmp     bir_label_t
  | BStmt_CJmp    bir_exp_t bir_label_t bir_label_t
  | BStmt_Halt    bir_exp_t
  | BStmt_Assert  bir_exp_t
  | BStmt_Assume  bir_exp_t
`;

val _ = Datatype `bir_block_t = <| bb_label:bir_label_t ; bb_statements:bir_stmt_t list |>`;
val _ = Datatype `bir_program_t = BirProgram (bir_block_t list)`;
val _ = Datatype `bir_programcounter_t = <| bpc_label:bir_label_t; bpc_index:num |>`;

val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);

val _ = Datatype `bir_termcode_t =
    BTC_Running
  | BTC_Halted bir_val_t
  | BTC_ReachedEnd
  | BTC_ReachedUnknownLabel bir_label_t
  | BTC_Failed
  | BTC_AssumptionViolated`

val _ = Datatype `bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_termcode : bir_termcode_t;
  bst_debug    : string list;
  bst_execs    : num
|>`;

val bir_state_ss = rewrites (type_rws ``:bir_state_t``);
val bir_termcode_ss = rewrites (type_rws ``:bir_termcode_t``);


(* ------------------------------------------------------------------------- *)
(* Programs                                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_block_stmts_count_def = Define `bir_block_stmts_count bl = LENGTH bl.bb_statements`;
val bir_program_stmts_count_def = Define`bir_program_stmts_count (BirProgram p) = SUM (MAP bir_block_stmts_count p)`;

val bir_labels_of_program_def = Define `bir_labels_of_program (BirProgram p) =
  MAP (\bl. bl.bb_label) p`;

val bir_is_valid_labels_def = Define `bir_is_valid_labels p =
  ALL_DISTINCT (bir_labels_of_program p) /\ ~(MEM (BL_Label "") (bir_labels_of_program p))`;

val bir_is_valid_program_def = Define `bir_is_valid_program p <=>
   (bir_is_valid_labels p /\ bir_program_stmts_count p > 0)`;


val bir_is_valid_labels_blocks_EQ_EL = store_thm ("bir_is_valid_labels_blocks_EQ_EL",
  ``!p n1 n2. (bir_is_valid_labels (BirProgram p) /\ n1 < LENGTH p /\ n2 < LENGTH p /\
                ((EL n1 p).bb_label = (EL n2 p).bb_label)) ==> (n1 = n2)``,

SIMP_TAC list_ss [bir_is_valid_labels_def, bir_labels_of_program_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.ISPEC `MAP (\bl. bl.bb_label) (p:bir_block_t list)` listTheory.EL_ALL_DISTINCT_EL_EQ) >>
ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_IMP_THM] >>
Q.EXISTS_TAC `n1` >> Q.EXISTS_TAC `n2` >>
ASM_SIMP_TAC list_ss [listTheory.EL_MAP]);


val bir_is_valid_labels_blocks_EQ = store_thm ("bir_is_valid_labels_blocks_EQ",
  ``!p bl1 bl2. (bir_is_valid_labels (BirProgram p) /\ MEM bl1 p /\ MEM bl2 p /\
                (bl1.bb_label = bl2.bb_label)) ==> (bl1 = bl2)``,

METIS_TAC [listTheory.MEM_EL, bir_is_valid_labels_blocks_EQ_EL]);



val bir_get_program_block_info_by_label_def = Define `bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\(x:bir_block_t). x.bb_label = l) p
`;

val bir_get_program_block_info_by_label_THM = store_thm ("bir_get_program_block_info_by_label_THM",
  ``(!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.bb_label <> l)))) /\

    (!p l i bl.
          (bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
          ((((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.bb_label = l) /\
             (!j'. j' < i ==> (EL j' p).bb_label <> l))))``,

SIMP_TAC list_ss [bir_get_program_block_info_by_label_def, INDEX_FIND_EQ_NONE,
  listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0]);


val bir_get_program_block_info_by_label_valid_THM = store_thm ("bir_get_program_block_info_by_label_valid_THM",
  ``(!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.bb_label <> l)))) /\

    (!p l i bl. bir_is_valid_labels (BirProgram p) ==>
          ((bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
           ((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.bb_label = l)))``,

SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_get_program_block_info_by_label_def,
  INDEX_FIND_EQ_NONE, listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0] >>
REPEAT STRIP_TAC >>
`j' < LENGTH p` by DECIDE_TAC >>
`j' = i` by METIS_TAC[bir_is_valid_labels_blocks_EQ_EL] >>
FULL_SIMP_TAC arith_ss []);



val bir_get_program_block_info_by_label_MEM = store_thm ("bir_get_program_block_info_by_label_MEM",
  ``!p l. MEM l (bir_labels_of_program p) <=>
          (?i bl. bir_get_program_block_info_by_label p l = SOME (i, bl))``,

Cases_on `p` >> rename1 `BirProgram p` >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_labels_of_program_def, listTheory.MEM_MAP] >>
Cases_on `bir_get_program_block_info_by_label (BirProgram p) l` >| [
  FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM] >>
  METIS_TAC[],

  rename1 `_ = SOME ibl` >>
  Cases_on `ibl` >>
  FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM, listTheory.MEM_EL,
    GSYM RIGHT_EXISTS_AND_THM] >>
  METIS_TAC[]
]);



(* ------------------------------------------------------------------------- *)
(*  Program Counter                                                          *)
(* ------------------------------------------------------------------------- *)

val bir_is_valid_pc_def = Define `bir_is_valid_pc p pc =
   (?i bl. (bir_get_program_block_info_by_label p (pc.bpc_label) = SOME (i, bl)) /\
           (pc.bpc_index < LENGTH bl.bb_statements))`;

val bir_is_end_pc_def = Define `bir_is_end_pc (BirProgram p) pc =
   (?i bl. (bir_get_program_block_info_by_label (BirProgram p) (pc.bpc_label) = SOME (i, bl)) /\
           (pc.bpc_index = LENGTH bl.bb_statements) /\
      (!j. (i < j /\ j < LENGTH p) ==> (((EL j p).bb_statements) = [])))`;

val bir_is_allowed_pc_def = Define `bir_is_allowed_pc p pc =
   (?i bl. (bir_get_program_block_info_by_label p (pc.bpc_label) = SOME (i, bl)) /\
           (pc.bpc_index <= LENGTH bl.bb_statements))`;


val bir_is_valid_pc_not_end = store_thm ("bir_is_valid_pc_not_end",
  ``!p pc. bir_is_valid_pc p pc ==> ~(bir_is_end_pc p pc)``,
Cases >> rename1 `BirProgram p` >>
SIMP_TAC arith_ss [bir_is_valid_pc_def, bir_is_end_pc_def,
  GSYM LEFT_FORALL_IMP_THM]);


val bir_is_valid_pc_of_valid_blocks = store_thm ("bir_is_valid_pc_of_valid_blocks",
  ``!p pc. bir_is_valid_labels (BirProgram p) ==>
           (bir_is_valid_pc (BirProgram p) pc <=> (?bl. MEM bl p /\ (pc.bpc_label = bl.bb_label) /\
             (pc.bpc_index < LENGTH bl.bb_statements)))``,
SIMP_TAC std_ss [bir_is_valid_pc_def, bir_get_program_block_info_by_label_valid_THM,
  listTheory.MEM_EL, GSYM LEFT_EXISTS_AND_THM] >>
METIS_TAC[]);



val bir_get_program_block_info_by_label_valid_pc = store_thm ("bir_get_program_block_info_by_label_valid_pc",
  ``!p pc. bir_is_valid_pc p pc ==> IS_SOME (bir_get_program_block_info_by_label p pc.bpc_label)``,

SIMP_TAC std_ss [bir_is_valid_pc_def, GSYM LEFT_FORALL_IMP_THM]);

val bir_get_current_statement_def = Define `bir_get_current_statement p pc =
  option_CASE (bir_get_program_block_info_by_label p pc.bpc_label) NONE
     (\ (_, bl). if (pc.bpc_index < LENGTH bl.bb_statements) then SOME (EL (pc.bpc_index) bl.bb_statements) else NONE) `;


val bir_get_current_statement_IS_SOME = store_thm ("bir_get_current_statement_IS_SOME",
  ``!p pc. IS_SOME (bir_get_current_statement p pc) <=> bir_is_valid_pc p pc``,

REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def, bir_is_valid_pc_def]
) >>
SIMP_TAC (std_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) []);


val bir_pc_normalise_def = Define `
  (bir_pc_normalise (BirProgram p) pc = case bir_get_program_block_info_by_label (BirProgram p) (pc.bpc_label) of
        SOME (n, bl) => if (pc.bpc_index < LENGTH bl.bb_statements)
          then SOME pc
          else (
            let p' = FILTER (\bl. bl.bb_statements <> []) (DROP (SUC n) p) in
            case p' of
              | [] => NONE
              | (bl'::_) => SOME <| bpc_label := bl'.bb_label ; bpc_index := 0 |>
            )
      | _ => NONE
  )
`;


val bir_pc_next_def = Define `
  bir_pc_next p pc = bir_pc_normalise p (pc with bpc_index updated_by SUC)`;


val bir_pc_normalise_EQ_SOME = store_thm ("bir_pc_normalise_EQ_SOME",
``!p pc i bl pc'. (bir_get_program_block_info_by_label (BirProgram p) (pc.bpc_label) = SOME (i, bl)) ==>
             ((bir_pc_normalise (BirProgram p) pc = SOME pc') <=>
                (if (pc.bpc_index < LENGTH bl.bb_statements) then (pc' = pc) else
                (?j. (i < j /\ j < LENGTH p /\ ((EL j p).bb_statements <> []) /\
                     (pc' = <| bpc_label := (EL j p).bb_label; bpc_index := 0 |>) /\
                     (!j'. (i < j' /\ j' < j) ==> (((EL j' p).bb_statements) = []))))))``,

SIMP_TAC std_ss [bir_pc_normalise_def, pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >>
Cases_on `pc.bpc_index < LENGTH bl.bb_statements` >- (
  ASM_SIMP_TAC arith_ss [] >> METIS_TAC[]
) >>
ASM_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `FILTER (\bl. bl.bb_statements <> []) (DROP (SUC i) p)` >| [
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  `MEM (EL j p) (DROP (SUC i) p)` by (
     SIMP_TAC (list_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, rich_listTheory.EL_DROP] >>
     Q.EXISTS_TAC `j - SUC i` >>
     ASM_SIMP_TAC arith_ss []
  ) >>
  `~(MEM (EL j p) (FILTER (\bl. bl.bb_statements <> []) (DROP (SUC i) p)))` by
    ASM_SIMP_TAC list_ss [] >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_FILTER] >>
  FULL_SIMP_TAC std_ss [],


  rename1 `FILTER _ _ = bl0::bls` >>
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  `?p1 p2. (LENGTH p1 = SUC i) /\ (p = p1 ++ p2)` by (
     Q.EXISTS_TAC `TAKE (SUC i) p` >>
     Q.EXISTS_TAC `DROP (SUC i) p` >>
     FULL_SIMP_TAC list_ss [bir_get_program_block_info_by_label_THM]
  ) >>
  FULL_SIMP_TAC list_ss [rich_listTheory.DROP_APPEND1, listTheory.DROP_LENGTH_TOO_LONG] >>
  Q.PAT_X_ASSUM `p = _ ++ _` (K ALL_TAC) >>
  Q.PAT_X_ASSUM `_ = SOME _` (K ALL_TAC) >>
  Induct_on `p2` >- ASM_SIMP_TAC list_ss [] >>
  CONV_TAC (RENAME_VARS_CONV ["bl1"]) >>
  REPEAT STRIP_TAC >>
  Cases_on `(bl1.bb_statements) <> []` >> FULL_SIMP_TAC list_ss [] >| [
    REPEAT (BasicProvers.VAR_EQ_TAC) >>
    EQ_TAC >> REPEAT STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >> ASM_SIMP_TAC list_ss [] >| [
      Q.EXISTS_TAC `SUC i` >>
      ASM_SIMP_TAC (list_ss++QI_ss) [rich_listTheory.EL_APPEND2],

      Cases_on `j = SUC i` >- ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2] >>
      Q.PAT_X_ASSUM `!j'. _` (MP_TAC o Q.SPEC `SUC i`) >>
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2]
    ],

    EQ_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >| [
      Q.EXISTS_TAC `SUC j` >>
      Q.PAT_X_ASSUM `_ <> []` MP_TAC >>
      Q.PAT_X_ASSUM `!j. _` MP_TAC >>
      `j - i = SUC (j - SUC i)` by DECIDE_TAC >>
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2] >>
      REPEAT STRIP_TAC >>
      Cases_on `j' = SUC i` >- ASM_SIMP_TAC list_ss [] >>
      Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `PRE j'`) >>
      `j' - SUC i = SUC (PRE j' - SUC i)` by DECIDE_TAC >>
      ASM_SIMP_TAC list_ss [],

      Q.EXISTS_TAC `PRE j` >>
      Q.PAT_X_ASSUM `_ <> []` MP_TAC >>
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


val bir_pc_normalise_EQ_NONE = store_thm ("bir_pc_normalise_EQ_NONE",
``!p pc i bl. (bir_get_program_block_info_by_label (BirProgram p) (pc.bpc_label) = SOME (i, bl)) ==>
             ((bir_pc_normalise (BirProgram p) pc = NONE) <=> (
                (LENGTH bl.bb_statements <= pc.bpc_index) /\
                (!j. (i < j /\ j < LENGTH p) ==> (((EL j p).bb_statements) = []))))``,

SIMP_TAC std_ss [bir_pc_normalise_def, pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >>
Cases_on `pc.bpc_index < LENGTH bl.bb_statements` >> (
  ASM_SIMP_TAC arith_ss []
) >>
Cases_on `FILTER (\bl. bl.bb_statements <> []) (DROP (SUC i) p)` >| [
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  REPEAT STRIP_TAC >>
  `MEM (EL j p) (DROP (SUC i) p)` by (
     SIMP_TAC (list_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, rich_listTheory.EL_DROP] >>
     Q.EXISTS_TAC `j - SUC i` >>
     ASM_SIMP_TAC arith_ss []
  ) >>
  `~(MEM (EL j p) (FILTER (\bl. bl.bb_statements <> []) (DROP (SUC i) p)))` by
    ASM_SIMP_TAC list_ss [] >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_FILTER] >>
  FULL_SIMP_TAC std_ss [],


  rename1 `FILTER _ _ = bl0::bls` >>
  ASM_SIMP_TAC list_ss [LET_DEF] >>
  `MEM bl0 (FILTER (\bl. bl.bb_statements <> []) (DROP (SUC i) p))` by
    ASM_SIMP_TAC list_ss [] >>
  POP_ASSUM MP_TAC >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_FILTER] >>
  SIMP_TAC (list_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, rich_listTheory.EL_DROP] >>
  REPEAT STRIP_TAC >>
  rename1 `bl0 = EL (n + SUC i) p` >>
  Q.EXISTS_TAC `n + SUC i` >>
  FULL_SIMP_TAC list_ss []
]);


val bir_pc_normalise_EQ_NONE_not_is_valid = store_thm ("bir_pc_normalise_EQ_NONE_not_is_valid",
``!p pc. (bir_pc_normalise p pc = NONE) ==> (
         ~(bir_is_valid_pc p pc))``,

Cases_on `p` >> rename1 `BirProgram p` >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_valid_pc_def, bir_pc_normalise_def] >>
FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm]);


val bir_pc_normalise_EQ_NONE_is_end_pc = store_thm ("bir_pc_normalise_EQ_NONE_is_end_pc",
``!p pc. bir_is_allowed_pc p pc ==>
         ((bir_pc_normalise p pc = NONE) <=> (
           bir_is_end_pc p pc))``,

Cases_on `p` >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_allowed_pc_def, GSYM LEFT_FORALL_IMP_THM] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `pc`] bir_pc_normalise_EQ_NONE) >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_end_pc_def]);



val bir_is_allowed_pc_inc_valid = store_thm ("bir_is_allowed_pc_inc_valid",
``!p pc. bir_is_valid_pc p pc ==> bir_is_allowed_pc p (pc with bpc_index updated_by SUC)``,

SIMP_TAC (arith_ss++bir_pc_ss) [bir_is_valid_pc_def, bir_is_allowed_pc_def, GSYM LEFT_FORALL_IMP_THM]);

val bir_is_allowed_pc_jmp = store_thm ("bir_is_allowed_pc_jmp",
``!l p. MEM l (bir_labels_of_program p) ==>
        bir_is_allowed_pc p <| bpc_label := l; bpc_index := 0 |>``,

SIMP_TAC (std_ss++bir_pc_ss) [bir_is_allowed_pc_def, GSYM bir_get_program_block_info_by_label_MEM]);


val bir_pc_normalise_valid = store_thm ("bir_pc_normalise_valid",
``!p pc pc'. (bir_is_valid_labels p /\ (MEM pc.bpc_label (bir_labels_of_program p)) /\
              (bir_pc_normalise p pc = SOME pc')) ==>
             (bir_is_valid_pc p pc')``,

Cases >> rename1 `BirProgram p` >>
SIMP_TAC list_ss [bir_labels_of_program_def, bir_pc_normalise_EQ_SOME,
  listTheory.MEM_MAP, GSYM RIGHT_EXISTS_AND_THM] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [listTheory.MEM_EL] >>
rename1 `bl = EL i p` >>
`bir_get_program_block_info_by_label (BirProgram p) pc.bpc_label = SOME (i, bl)` by
  METIS_TAC[bir_get_program_block_info_by_label_valid_THM] >>

MP_TAC (Q.SPECL [`p`, `pc`, `i`, `bl`, `pc'`] bir_pc_normalise_EQ_SOME) >>
FULL_SIMP_TAC std_ss [bir_is_valid_pc_def] >>
Cases_on `pc.bpc_index < LENGTH (EL i p).bb_statements` >| [
  ASM_SIMP_TAC std_ss [] >> METIS_TAC[],

  ASM_SIMP_TAC (std_ss++bir_pc_ss) [bir_get_program_block_info_by_label_valid_THM,
    GSYM LEFT_FORALL_IMP_THM] >>
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `j` >>
  ASM_SIMP_TAC arith_ss [] >>
  Cases_on `(EL j p).bb_statements` >> FULL_SIMP_TAC list_ss []
]);


val bir_pc_next_valid = store_thm ("bir_pc_next_valid",
``!p pc pc'. (bir_is_valid_labels p /\ bir_is_valid_pc p pc /\ (bir_pc_next p pc = SOME pc')) ==>
             (bir_is_valid_pc p pc')``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_pc_normalise_valid >>
Q.EXISTS_TAC `pc with bpc_index updated_by SUC` >>
Cases_on `p` >>
FULL_SIMP_TAC (std_ss++bir_pc_ss) [bir_pc_next_def, bir_is_valid_pc_def, bir_labels_of_program_def,
  listTheory.MEM_MAP] >>
METIS_TAC[listTheory.MEM_EL, bir_get_program_block_info_by_label_valid_THM]);


val bir_pc_first_def = Define
  `bir_pc_first (BirProgram p) = let bl = HD (FILTER (\bl. (bl.bb_statements) <> []) p) in
    (<| bpc_label := bl.bb_label; bpc_index := 0 |>):bir_programcounter_t`;

val bir_pc_last_def = Define
  `bir_pc_last (BirProgram p) = let bl = LAST (FILTER (\bl. (bl.bb_statements) <> []) p) in
    (<| bpc_label := bl.bb_label; bpc_index := LENGTH bl.bb_statements - 1 |>):bir_programcounter_t`;


val bir_program_stmts_count_FILTER_NEQ_NIL = store_thm ("bir_program_stmts_count_FILTER_NEQ_NIL",
  ``!p. (bir_program_stmts_count (BirProgram p) > 0) ==>
    (?bl0 bls. (FILTER (\bl. bl.bb_statements <> []) p = bl0 :: bls) /\
              EVERY (\bl. (bl.bb_statements <> []) /\ MEM bl p) (bl0::bls))``,

Induct_on `p` >> (
  FULL_SIMP_TAC list_ss [bir_program_stmts_count_def, bir_block_stmts_count_def]
) >>
CONV_TAC (RENAME_VARS_CONV ["bl"]) >> GEN_TAC >>
Cases_on `bl.bb_statements` >| [
  SIMP_TAC list_ss [] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM],

  SIMP_TAC list_ss [listTheory.EVERY_FILTER] >>
  ASM_SIMP_TAC list_ss [listTheory.EVERY_MEM]
]);


val bir_pc_first_valid = store_thm ("bir_pc_first_valid",
  ``!p. bir_is_valid_program p ==> bir_is_valid_pc p (bir_pc_first p)``,

Cases >> rename1 `BirProgram p` >>
SIMP_TAC (std_ss++bir_pc_ss) [bir_is_valid_pc_of_valid_blocks, bir_is_valid_program_def,
  bir_pc_first_def, LET_DEF] >>
ASSUME_TAC (Q.SPEC `p` bir_program_stmts_count_FILTER_NEQ_NIL) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [] >>
rename1 `bl0.bb_statements <> []` >>
Q.EXISTS_TAC `bl0` >>
Cases_on `bl0.bb_statements` >> FULL_SIMP_TAC list_ss []);


val bir_pc_last_valid = store_thm ("bir_pc_last_valid",
  ``!p. bir_is_valid_program p ==> bir_is_valid_pc p (bir_pc_last p)``,

Cases >> rename1 `BirProgram p` >>
SIMP_TAC (std_ss++bir_pc_ss) [bir_is_valid_pc_of_valid_blocks, bir_is_valid_program_def,
  bir_pc_last_def, LET_DEF] >>
ASSUME_TAC (Q.SPEC `p` bir_program_stmts_count_FILTER_NEQ_NIL) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [] >>
rename1 `FILTER _ p = bl0::bls` >>
Q.EXISTS_TAC `LAST (bl0::bls)` >>
`MEM (LAST (bl0::bls)) (bl0::bls)` by MATCH_ACCEPT_TAC rich_listTheory.MEM_LAST >>
ASM_SIMP_TAC arith_ss [rich_listTheory.LENGTH_NOT_NULL, listTheory.NULL_EQ] >>
FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM]);



val bir_is_valid_pc_label_OK = store_thm ("bir_is_valid_pc_label_OK",
  ``!p pc. bir_is_valid_pc p pc ==> MEM pc.bpc_label (bir_labels_of_program p)``,

Cases_on `p` >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_valid_pc_def, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bir_labels_of_program_def,
  bir_get_program_block_info_by_label_THM] >>
SIMP_TAC std_ss [listTheory.MEM_EL, GSYM RIGHT_EXISTS_AND_THM] >>
METIS_TAC[]);


val bir_pc_next_valid_EQ_NONE = store_thm ("bir_pc_next_valid_EQ_NONE",
``!p pc. (bir_is_valid_labels p /\ bir_is_valid_pc p pc) ==>
          ((bir_pc_next p pc = NONE) <=> (pc = bir_pc_last p))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_pc_next_def,
  bir_pc_normalise_EQ_NONE_is_end_pc, bir_is_allowed_pc_inc_valid] >>

Cases_on `p` >> rename1 `BirProgram p` >>
ASM_SIMP_TAC (std_ss++bir_pc_ss) [bir_pc_last_def, LET_THM, bir_is_end_pc_def] >>

`FILTER (\bl. bl.bb_statements <> []) p <> []` by (
  STRIP_TAC  >>
  FULL_SIMP_TAC std_ss [bir_is_valid_pc_def, bir_get_program_block_info_by_label_THM] >>
  `MEM (EL i p) (FILTER (\bl. bl.bb_statements <> []) p)` suffices_by ASM_SIMP_TAC list_ss [] >>
  SIMP_TAC list_ss [listTheory.MEM_FILTER, listTheory.MEM_EL] >>
  REPEAT STRIP_TAC >| [
    Cases_on `(EL i p).bb_statements` >> FULL_SIMP_TAC list_ss [],
    METIS_TAC[]
  ]
) >>

IMP_RES_TAC LAST_FILTER_EL >>
FULL_SIMP_TAC (list_ss++bir_pc_ss) [DB.fetch "-" "bir_programcounter_t_component_equality",
  bir_is_valid_pc_def] >>
REV_FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_valid_THM] >>
EQ_TAC >> STRIP_TAC >| [
  `~(i < i')` by (
    STRIP_TAC >>
    `bl.bb_statements = []` by METIS_TAC[] >>
    FULL_SIMP_TAC list_ss []
  ) >>
  `~(i' < i)` by (
    STRIP_TAC >>
    `(EL i p).bb_statements = []` by METIS_TAC[] >>
    FULL_SIMP_TAC list_ss []
  ) >>
  `i' = i` by DECIDE_TAC >>
  FULL_SIMP_TAC arith_ss [],

  `bl = EL i p` by METIS_TAC [bir_is_valid_labels_blocks_EQ, listTheory.MEM_EL] >>
  `i' = i` by METIS_TAC [bir_is_valid_labels_blocks_EQ_EL] >>
  FULL_SIMP_TAC arith_ss [] >>
  REPEAT STRIP_TAC >>
  `~(LENGTH (EL j p).bb_statements > 0)` by METIS_TAC[] >>
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
val bir_stmt_to_string_def = Define `bir_stmt_to_string stmt = case stmt of
  | BStmt_Declare (BVar s _) => CONCAT ["Declaration of "; s]
  | BStmt_Assign (BVar s _) _ => CONCAT ["Assignment of "; s]
  | BStmt_Jmp _ => "Jump"
  | BStmt_CJmp _ _ _ => "Conditional Jump"
  | BStmt_Halt _ => "Halt"
  | BStmt_Assert _ => "Assert"
  | BStmt_Assume _ => "Assume"
  | _ => "-- unsupported statement"
`;


(* ------------------------------------------------------------------------- *)
(*  Program State                                                            *)
(* ------------------------------------------------------------------------- *)

val bir_state_add_execs_def = Define `bir_state_add_execs st n =
  st with bst_execs updated_by ($+ n)`;

val bir_state_is_terminated_def = Define `bir_state_is_terminated st =
  (st.bst_termcode <> BTC_Running)`;

val bir_state_is_terminated_IMP = store_thm ("bir_state_is_terminated_IMP",
  ``(!st. (st.bst_termcode = BTC_Running) ==> ~(bir_state_is_terminated st)) /\
    (!st. (st.bst_termcode <> BTC_Running) ==> (bir_state_is_terminated st))``,
  SIMP_TAC std_ss [bir_state_is_terminated_def]);

val bir_state_is_failed_def = Define `bir_state_is_failed st =
  (st.bst_termcode = BTC_Failed)`;

val bir_state_set_failed_def = Define `bir_state_set_failed st msg =
  (st with bst_termcode := BTC_Failed) with bst_debug updated_by (\dbg. msg::dbg)`;

val bir_state_set_failed_is_failed = store_thm ("bir_state_set_failed_is_failed",
  ``!st msg. bir_state_is_failed (bir_state_set_failed st msg)``,
SIMP_TAC (std_ss ++ bir_state_ss) [bir_state_set_failed_def, bir_state_is_failed_def]);

val bir_state_normalise_pc_def = Define `bir_state_normalise_pc p (st:bir_state_t) =
  case bir_pc_normalise p st.bst_pc of
    | SOME pc' => (st with bst_pc := pc')
    | NONE => (st with bst_termcode := BTC_ReachedEnd)`;

val bir_state_incr_pc_def = Define `bir_state_incr_pc p (st:bir_state_t) =
  bir_state_normalise_pc p (st with bst_pc := (st.bst_pc with bpc_index updated_by SUC))`

val bir_state_set_pc_def = Define `bir_state_set_pc p (st:bir_state_t) pc' =
  bir_state_normalise_pc p (st with bst_pc := pc')`;

val bir_state_init_def = Define `bir_state_init p = <|
    bst_pc       := bir_pc_first p
  ; bst_environ  := bir_empty_env
  ; bst_termcode := BTC_Running
  ; bst_debug    := []
  ; bst_execs    := 0
|>`;


(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

(* Execution of Jmp, CJmp, Halt, Assert, Assume doesn't change environment *)

val bir_declare_initial_value_def = Define `
  (bir_declare_initial_value (BType_Imm _) = NONE) /\
  (bir_declare_initial_value (BType_Mem at vt) = SOME (BVal_Mem at vt (K 0)))`;

val bir_exec_stmt_declare_def = Define `bir_exec_stmt_declare p v ty (st : bir_state_t) =
   let env = (
      let vo = bir_declare_initial_value ty in
      if bir_env_varname_is_bound st.bst_environ v then BEnv_Irregular else
      bir_env_update v vo ty st.bst_environ) in
    if (bir_is_regular_env env) then
       bir_state_incr_pc p (st with bst_environ := env)
    else
       bir_state_set_failed st (CONCAT ["irregular environment after "; bir_stmt_to_string
          (BStmt_Declare (BVar v ty))])`;

val bir_exec_stmt_assign_def = Define `bir_exec_stmt_assign p v ex (st : bir_state_t) =
   let env = bir_env_write v (bir_eval_exp ex st.bst_environ) st.bst_environ in
    if (bir_is_regular_env env) then
       bir_state_incr_pc p (st with bst_environ := env)
    else
       bir_state_set_failed st (CONCAT ["irregular environment after "; bir_stmt_to_string
          (BStmt_Assign v ex)])`;

val bir_exec_stmt_halt_def = Define `bir_exec_stmt_halt ex (st : bir_state_t) =
    (st with bst_termcode := BTC_Halted (bir_eval_exp ex st.bst_environ))`;

val bir_exec_stmt_jmp_def = Define `bir_exec_stmt_jmp p l (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      bir_state_set_pc p st <| bpc_label := l; bpc_index := 0 |>
    else (st with bst_termcode := (BTC_ReachedUnknownLabel l))`;

val bir_exec_stmt_cjmp_def = Define `bir_exec_stmt_cjmp p ex l1 l2 (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ex st.bst_environ)) of
    | SOME T => bir_exec_stmt_jmp p l1 st
    | SOME F => bir_exec_stmt_jmp p l2 st
    | NONE => bir_state_set_failed st "condition of cjmp failed to evaluate"`;

val bir_exec_stmt_assert_def = Define `bir_exec_stmt_assert p ex (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ex st.bst_environ)) of
    | SOME T => bir_state_incr_pc p st
    | SOME F => bir_state_set_failed st "assertion failed"
    | NONE => bir_state_set_failed st "condition of assert failed to evaluate"`

val bir_exec_stmt_assume_def = Define `bir_exec_stmt_assume p ex (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ex st.bst_environ)) of
    | SOME T => bir_state_incr_pc p st
    | SOME F => (st with bst_termcode := BTC_AssumptionViolated)
    | NONE => bir_state_set_failed st "condition of assume failed to evaluate"`;


val bir_exec_stmt_def = Define `
  (bir_exec_stmt p (BStmt_Jmp l) st = bir_exec_stmt_jmp p l st) /\
  (bir_exec_stmt p (BStmt_CJmp e l1 l2) st = bir_exec_stmt_cjmp p e l1 l2 st) /\
  (bir_exec_stmt p (BStmt_Declare v) st = bir_exec_stmt_declare p (bir_var_name v) (bir_var_type v) st) /\
  (bir_exec_stmt p (BStmt_Assert ex) st = bir_exec_stmt_assert p ex st) /\
  (bir_exec_stmt p (BStmt_Assume ex) st = bir_exec_stmt_assume p ex st) /\
  (bir_exec_stmt p (BStmt_Assign v ex) st = bir_exec_stmt_assign p v ex st) /\
  (bir_exec_stmt p (BStmt_Halt ex) st = bir_exec_stmt_halt ex st)`;


val bir_exec_step_def = Define `bir_exec_step p state =
  if (bir_state_is_terminated state) then state else
  case (bir_get_current_statement p state.bst_pc) of
    | NONE => bir_state_set_failed state "invalid program_counter"
    | SOME stm => (bir_exec_stmt p stm state) with bst_execs updated_by SUC
`;


(* ------------------------------------------------------------------------- *)
(*  Semantics preserve validity of states                                    *)
(* ------------------------------------------------------------------------- *)

val bir_is_valid_state_def = Define `bir_is_valid_state p st <=>
  ((bir_is_well_typed_env st.bst_environ) /\ (if st.bst_termcode = BTC_ReachedEnd then bir_is_end_pc p st.bst_pc else
      bir_is_valid_pc p st.bst_pc))`;

val bir_state_init_valid = store_thm ("bir_state_init_valid",
  ``!p. bir_is_valid_program p ==> bir_is_valid_state p (bir_state_init p)``,

SIMP_TAC (std_ss++bir_state_ss++bir_termcode_ss) [bir_is_valid_state_def, bir_state_init_def,
  bir_pc_first_valid, bir_is_well_typed_env_empty]);


val bir_is_valid_state_exec_ignore = store_thm ("bir_is_valid_state_exec_ignore",
  ``!p st f. bir_is_valid_state p (st with bst_execs updated_by f) =
             bir_is_valid_state p st``,
SIMP_TAC (std_ss++bir_state_ss) [bir_is_valid_state_def]);


val bir_exec_step_valid_THM = store_thm ("bir_exec_step_valid_THM",
 ``!p st. bir_is_valid_state p st ==>
          (if bir_state_is_terminated st then
             (bir_exec_step p st = st)
           else
             (bir_is_valid_pc p st.bst_pc) /\
             (?stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) /\
                     (bir_exec_step p st = (bir_exec_stmt p stmt st with bst_execs updated_by SUC))))``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_step_def] >>
Cases_on `bir_state_is_terminated st` >> ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] >>
`st.bst_termcode <> BTC_ReachedEnd` by (
  STRIP_TAC >> FULL_SIMP_TAC (std_ss++bir_termcode_ss) [bir_state_is_terminated_def]
) >>
`?stm. bir_get_current_statement p st.bst_pc = SOME stm` by (
  `IS_SOME (bir_get_current_statement p st.bst_pc)` suffices_by METIS_TAC[optionTheory.IS_SOME_EXISTS] >>
  FULL_SIMP_TAC std_ss [bir_get_current_statement_IS_SOME,
     bir_is_valid_state_def]
) >>
FULL_SIMP_TAC std_ss [bir_is_valid_state_def]);


val bir_is_valid_state_set_failed = store_thm ("bir_is_valid_state_set_failed",
  ``!p st msg. bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc ==>
               bir_is_valid_state p (bir_state_set_failed st msg)``,
SIMP_TAC (std_ss++bir_termcode_ss++bir_state_ss) [bir_is_valid_state_def, bir_state_set_failed_def]);


val bir_is_valid_state_incr_pc = store_thm ("bir_is_valid_state_incr_pc",
  ``!p st. bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc ==>
           bir_is_valid_state p (bir_state_incr_pc p st)``,
SIMP_TAC (std_ss++bir_state_ss++boolSimps.CONJ_ss) [bir_state_incr_pc_def, bir_is_valid_state_def,
  bir_state_normalise_pc_def, bir_is_valid_pc_not_end
] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on `bir_pc_normalise p (st.bst_pc with bpc_index updated_by SUC)` >- (
  ASM_SIMP_TAC (std_ss++bir_state_ss) [GSYM bir_pc_normalise_EQ_NONE_is_end_pc,
    bir_is_allowed_pc_inc_valid]
) >>
rename1 `_ = SOME pc'` >>
ASM_SIMP_TAC (std_ss++bir_pc_ss++bir_state_ss) [] >>
MATCH_MP_TAC bir_pc_normalise_valid >>
Q.EXISTS_TAC `st.bst_pc with bpc_index updated_by SUC` >>
FULL_SIMP_TAC (std_ss++bir_pc_ss) [bir_is_valid_pc_label_OK,
   bir_is_valid_program_def]);



val bir_exec_step_valid_state_invar_declare = prove (
  ``!p st v. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
             bir_is_valid_state p (bir_exec_stmt p (BStmt_Declare v) st)``,
Cases_on `v` >> rename1 `BVar v ty` >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_stmt_def, bir_exec_stmt_declare_def, LET_THM,
  bir_is_valid_state_set_failed, bir_is_regular_env_def, bir_var_type_def, bir_var_name_def] >>
REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_is_valid_state_incr_pc >>
ASM_SIMP_TAC (std_ss++bir_state_ss) [] >>
FULL_SIMP_TAC (std_ss++bir_state_ss) [bir_is_valid_state_def] >>
Q.PAT_X_ASSUM `bir_is_regular_env _` MP_TAC >>
Cases_on `st.bst_environ` >> SIMP_TAC std_ss [bir_env_update_def, bir_is_regular_env_def] >>
COND_CASES_TAC >- SIMP_TAC std_ss [bir_is_regular_env_def] >>
FULL_SIMP_TAC (std_ss) [bir_is_regular_env_def, bir_is_well_typed_env_def] >>
ConseqConv.CONSEQ_REWRITE_TAC ([finite_mapTheory.FEVERY_STRENGTHEN_THM], [], []) >>
Cases_on `bir_declare_initial_value ty` >> FULL_SIMP_TAC std_ss []);


val bir_exec_step_valid_state_invar_assign = prove (
  ``!p st v ex. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
                 bir_is_valid_state p (bir_exec_stmt p (BStmt_Assign v ex) st)``,
Cases_on `v` >> rename1 `BVar v ty` >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_stmt_def, bir_exec_stmt_assign_def, LET_THM,
  bir_is_valid_state_set_failed, bir_is_regular_env_def] >>
REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_is_valid_state_incr_pc >>
ASM_SIMP_TAC (std_ss++bir_state_ss) [] >>
FULL_SIMP_TAC (std_ss++bir_state_ss) [bir_is_valid_state_def] >>
Q.PAT_X_ASSUM `bir_is_regular_env _` MP_TAC >>
SIMP_TAC std_ss [bir_env_write_def] >>
COND_CASES_TAC >> SIMP_TAC std_ss [bir_is_regular_env_def, bir_var_name_def, bir_var_type_def] >>
Cases_on `st.bst_environ` >> SIMP_TAC std_ss [bir_env_update_def, bir_is_regular_env_def] >>
COND_CASES_TAC >> SIMP_TAC std_ss [bir_is_regular_env_def, bir_is_well_typed_env_def] >>
ConseqConv.CONSEQ_REWRITE_TAC ([finite_mapTheory.FEVERY_STRENGTHEN_THM], [], []) >>
FULL_SIMP_TAC std_ss [bir_is_well_typed_env_def]);


val bir_exec_step_valid_state_invar_jmp' = prove (
  ``!p st l. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
             bir_is_valid_state p (bir_exec_stmt_jmp p l st)``,
SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >| [
  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_is_valid_state_def, bir_state_set_pc_def,
    bir_state_normalise_pc_def] >>
  Cases_on `bir_pc_normalise p <|bpc_label := l; bpc_index := 0|>` >| [
    FULL_SIMP_TAC (std_ss++bir_state_ss) [bir_is_valid_state_def] >>
    ASM_SIMP_TAC std_ss [GSYM bir_pc_normalise_EQ_NONE_is_end_pc,
      bir_is_allowed_pc_jmp],

    rename1 `_ = SOME pc'` >>
    FULL_SIMP_TAC (std_ss++bir_pc_ss++bir_state_ss) [bir_is_valid_state_def,
      bir_is_valid_pc_not_end] >>
    MATCH_MP_TAC bir_pc_normalise_valid >>
    Q.EXISTS_TAC `<| bpc_label := l; bpc_index := 0|>` >>
    FULL_SIMP_TAC (std_ss++bir_pc_ss) [bir_is_valid_program_def]
  ],

  FULL_SIMP_TAC (std_ss++bir_state_ss++bir_termcode_ss) [bir_is_valid_state_def]
]);

val bir_exec_step_valid_state_invar_jmp = prove (
  ``!p st l. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
             bir_is_valid_state p (bir_exec_stmt p (BStmt_Jmp l) st)``,
SIMP_TAC std_ss [bir_exec_stmt_def, bir_exec_step_valid_state_invar_jmp']);


val bir_exec_step_valid_state_invar_cjmp = prove (
  ``!p st ex l1 l2.
       (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
       bir_is_valid_state p (bir_exec_stmt p (BStmt_CJmp ex l1 l2) st)``,
SIMP_TAC std_ss [bir_exec_stmt_def, bir_exec_stmt_cjmp_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_dest_bool_val (bir_eval_exp ex st.bst_environ)` >- (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >> (
  ASM_SIMP_TAC std_ss [bir_exec_step_valid_state_invar_jmp']
));


val bir_exec_step_valid_state_invar_halt = prove (
  ``!p st ex. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
               bir_is_valid_state p (bir_exec_stmt p (BStmt_Halt ex) st)``,

SIMP_TAC (std_ss++bir_state_ss++bir_termcode_ss) [bir_exec_stmt_def, bir_exec_stmt_halt_def,
  bir_is_valid_state_def]);


val bir_exec_step_valid_state_invar_assert = prove (
  ``!p st ex. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
               bir_is_valid_state p (bir_exec_stmt p (BStmt_Assert ex) st)``,

SIMP_TAC (std_ss++bir_state_ss++bir_termcode_ss) [bir_exec_stmt_def, bir_exec_stmt_assert_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on `bir_dest_bool_val (bir_eval_exp ex st.bst_environ)` >- (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >| [
  ASM_SIMP_TAC std_ss [bir_is_valid_state_incr_pc],
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
]);


val bir_exec_step_valid_state_invar_assume = prove (
  ``!p st ex. (bir_is_valid_program p /\ bir_is_valid_state p st /\ bir_is_valid_pc p st.bst_pc) ==>
               bir_is_valid_state p (bir_exec_stmt p (BStmt_Assume ex) st)``,

SIMP_TAC (std_ss++bir_state_ss++bir_termcode_ss) [bir_exec_stmt_def, bir_exec_stmt_assume_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on `bir_dest_bool_val (bir_eval_exp ex st.bst_environ)` >- (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >| [
  ASM_SIMP_TAC std_ss [bir_is_valid_state_incr_pc],
  FULL_SIMP_TAC (std_ss++bir_state_ss++bir_termcode_ss) [bir_is_valid_state_def]
]);


val bir_exec_step_valid_state_invar = store_thm ("bir_exec_step_valid_state_invar",
``!p st. bir_is_valid_program p /\ bir_is_valid_state p st ==>
         bir_is_valid_state p (bir_exec_step p st)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_step_valid_THM >>
Cases_on `bir_state_is_terminated st` >> FULL_SIMP_TAC std_ss [bir_is_valid_state_exec_ignore] >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_step_valid_state_invar_declare,
    bir_exec_step_valid_state_invar_assign,
    bir_exec_step_valid_state_invar_cjmp,
    bir_exec_step_valid_state_invar_jmp,
    bir_exec_step_valid_state_invar_halt,
    bir_exec_step_valid_state_invar_assume,
    bir_exec_step_valid_state_invar_assert]
));



val bir_exec_step_FUNPOW_valid_state_invar = store_thm ("bir_exec_step_FUNPOW_valid_state_invar",
``!p st n. bir_is_valid_program p /\ bir_is_valid_state p st ==>
           bir_is_valid_state p (FUNPOW (bir_exec_step p) n st)``,

Induct_on `n` >> (
  ASM_SIMP_TAC std_ss [arithmeticTheory.FUNPOW, bir_exec_step_valid_state_invar]
));




(* ------------------------------------------------------------------------- *)
(*  The execs field is just a counter                                        *)
(* ------------------------------------------------------------------------- *)

val bir_state_normalise_pc_execs = store_thm ("bir_state_normalise_pc_execs",
  ``!p st. (bir_state_normalise_pc p st).bst_execs = st.bst_execs``,
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_state_normalise_pc_def] >>
Cases_on `bir_pc_normalise p st.bst_pc` >> (
  ASM_SIMP_TAC (std_ss++bir_state_ss) []
));


val bir_state_incr_pc_execs = store_thm ("bir_state_incr_pc_execs",
  ``!p st. (bir_state_incr_pc p st).bst_execs = st.bst_execs``,
SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_def, bir_state_normalise_pc_execs]);


val bir_state_set_failed_execs = store_thm ("bir_state_set_failed_execs",
  ``!st msg. (bir_state_set_failed st msg).bst_execs = st.bst_execs``,
SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def]);


val bir_state_set_pc_execs = store_thm ("bir_state_set_pc_execs",
  ``!st p pc'. (bir_state_set_pc p st pc').bst_execs = st.bst_execs``,
SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_pc_def,
  bir_state_normalise_pc_execs]);


val bir_exec_step_execs = store_thm ("bir_exec_step_execs",
``!p st. bir_is_valid_state p st ==>
         (if bir_state_is_terminated st then
           (bir_exec_step p st = st)
         else ((bir_exec_step p st).bst_execs = SUC (st.bst_execs)))``,


REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_step_valid_THM >>
Cases_on `bir_state_is_terminated st` >> FULL_SIMP_TAC (std_ss++bir_state_ss) [] >>
Cases_on `stmt` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++bir_state_ss) [bir_exec_stmt_def,
    bir_exec_stmt_declare_def, bir_exec_stmt_cjmp_def,
    bir_exec_stmt_assume_def, bir_exec_stmt_assign_def, bir_exec_stmt_jmp_def,
    LET_THM, bir_exec_stmt_halt_def, bir_exec_stmt_assert_def] >>
  REPEAT CASE_TAC >> (
    SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_execs, bir_state_set_failed_execs,
      bir_state_set_pc_execs]
  )
));


val bir_state_EQ_EXCEPT_EXECS_def = Define `
  bir_state_EQ_EXCEPT_EXECS st st' <=>
  ((st' with bst_execs := 0) = (st with bst_execs := 0))`;

val bir_state_EQ_EXCEPT_EXECS_ALT_DEF = save_thm ("bir_state_EQ_EXCEPT_EXECS_ALT_DEF",
SIMP_RULE (std_ss++bir_state_ss) [DB.fetch "-" "bir_state_t_component_equality"]
  bir_state_EQ_EXCEPT_EXECS_def);

val bir_state_EQ_EXCEPT_EXECS_ALT_DEF = save_thm ("bir_state_EQ_EXCEPT_EXECS_ALT_DEF",
SIMP_RULE (std_ss++bir_state_ss) [DB.fetch "-" "bir_state_t_component_equality"]
  bir_state_EQ_EXCEPT_EXECS_def);


val bir_state_EQ_EXCEPT_EXECS_IMP = save_thm ("bir_state_EQ_EXCEPT_EXECS_IMP",
GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL bir_state_EQ_EXCEPT_EXECS_ALT_DEF))));


val bir_state_normalise_pc_CHANGE_EXECS = store_thm ("bir_state_normalise_pc_CHANGE_EXECS",
``!p st1 st2. bir_state_EQ_EXCEPT_EXECS st1 st2 ==>
              bir_state_EQ_EXCEPT_EXECS (bir_state_normalise_pc p st1) (bir_state_normalise_pc p st2)``,

SIMP_TAC std_ss [bir_state_normalise_pc_def, bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
REPEAT GEN_TAC >> STRIP_TAC >>
CASE_TAC >> ASM_SIMP_TAC (std_ss++bir_state_ss) []);


val bir_state_incr_pc_CHANGE_EXECS = store_thm ("bir_state_incr_pc_CHANGE_EXECS",
``!p st1 st2. bir_state_EQ_EXCEPT_EXECS st1 st2 ==>
              bir_state_EQ_EXCEPT_EXECS (bir_state_incr_pc p st1) (bir_state_incr_pc p st2)``,

SIMP_TAC std_ss [bir_state_incr_pc_def, bir_state_normalise_pc_def, bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
REPEAT GEN_TAC >> STRIP_TAC >>
CASE_TAC >> CASE_TAC >> FULL_SIMP_TAC (std_ss++bir_state_ss) []);


val bir_state_set_pc_CHANGE_EXECS = store_thm ("bir_state_set_pc_CHANGE_EXECS",
``!p st1 st2 l. bir_state_EQ_EXCEPT_EXECS st1 st2 ==>
                bir_state_EQ_EXCEPT_EXECS (bir_state_set_pc p st1 l) (bir_state_set_pc p st2 l)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_state_set_pc_def] >>
MATCH_MP_TAC bir_state_normalise_pc_CHANGE_EXECS >>
FULL_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]);


val bir_exec_stmt_CHANGE_EXECS = store_thm ("bir_exec_stmt_CHANGE_EXECS",
``!p st1 st2. bir_state_EQ_EXCEPT_EXECS st1 st2 ==>
              (!stmt. bir_state_EQ_EXCEPT_EXECS (bir_exec_stmt p stmt st1) (bir_exec_stmt p stmt st2))``,

Cases_on `p` >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [Once bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Cases >> ASM_SIMP_TAC std_ss [bir_exec_stmt_def] >| [
  ASM_SIMP_TAC std_ss [bir_exec_stmt_declare_def, LET_DEF] >>
  Q.HO_MATCH_ABBREV_TAC `bir_state_EQ_EXCEPT_EXECS (if (bir_is_regular_env env) then _ else _) _` >>
  CASE_TAC >- (
    MATCH_MP_TAC bir_state_incr_pc_CHANGE_EXECS >>
    ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
  ) >>
  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def, bir_state_EQ_EXCEPT_EXECS_ALT_DEF],


  ASM_SIMP_TAC std_ss [bir_exec_stmt_assign_def, LET_DEF] >>
  Q.HO_MATCH_ABBREV_TAC `bir_state_EQ_EXCEPT_EXECS (if (bir_is_regular_env env) then _ else _) _` >>
  CASE_TAC >- (
    MATCH_MP_TAC bir_state_incr_pc_CHANGE_EXECS >>
    ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
  ) >>
  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def, bir_state_EQ_EXCEPT_EXECS_ALT_DEF],


  ASM_SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>
  CASE_TAC >- (
    MATCH_MP_TAC bir_state_set_pc_CHANGE_EXECS >>
    ASM_SIMP_TAC std_ss [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
  ) >>
  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF],


  ASM_SIMP_TAC std_ss [bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_def] >>
  REPEAT CASE_TAC >> TRY (
    ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def,
      bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
    NO_TAC
  ) >> (
    MATCH_MP_TAC bir_state_set_pc_CHANGE_EXECS >>
    ASM_SIMP_TAC std_ss [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
  ),


  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_halt_def,
    bir_state_EQ_EXCEPT_EXECS_ALT_DEF],

  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_assert_def] >>
  REPEAT CASE_TAC >> TRY (
    ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def,
      bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
    NO_TAC
  ) >>
  MATCH_MP_TAC bir_state_incr_pc_CHANGE_EXECS >>
  ASM_SIMP_TAC std_ss [bir_state_EQ_EXCEPT_EXECS_ALT_DEF],


  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_assume_def] >>
  REPEAT CASE_TAC >> TRY (
    ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def,
      bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
    NO_TAC
  ) >>
  MATCH_MP_TAC bir_state_incr_pc_CHANGE_EXECS >>
  ASM_SIMP_TAC std_ss [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
]);



val bir_exec_step_CHANGE_EXECS = store_thm ("bir_exec_step_CHANGE_EXECS",
``!p st1 st2. bir_state_EQ_EXCEPT_EXECS st1 st2 ==>
              bir_state_EQ_EXCEPT_EXECS (bir_exec_step p st1) (bir_exec_step p st2)``,

SIMP_TAC std_ss [bir_exec_step_def, Once bir_state_EQ_EXCEPT_EXECS_ALT_DEF] >>
REPEAT STRIP_TAC >>
`bir_state_is_terminated st1 = bir_state_is_terminated st2` by
  ASM_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
Cases_on `bir_state_is_terminated st2` >- (
  ASM_SIMP_TAC std_ss [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
) >>
Cases_on `bir_get_current_statement p st1.bst_pc` >- (
  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF,
    bir_state_set_failed_def]
) >>
rename1 `_ = SOME stmt` >>
`bir_state_EQ_EXCEPT_EXECS
   (bir_exec_stmt p stmt st1) (bir_exec_stmt p stmt st2)` suffices_by (
  ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]
) >>
MATCH_MP_TAC bir_exec_stmt_CHANGE_EXECS >>
ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_EQ_EXCEPT_EXECS_ALT_DEF]);




(* ------------------------------------------------------------------------- *)
(*  Executing multiple steps                                                 *)
(* ------------------------------------------------------------------------- *)

val bir_exec_steps_opt_def = Define `bir_exec_steps_opt p state b max_steps =
   OWHILE (\ (n, st). option_CASE max_steps T (\m. n < (m:num)) /\
                      ~(bir_state_is_terminated st)) (\ (n, st).
     (SUC n, bir_exec_step p st)) (b, state)`;

val bir_exec_step_n_def = Define `
  bir_exec_step_n p state n = THE (bir_exec_steps_opt p state 0 (SOME n))`;

val bir_exec_steps_def = Define `
  (bir_exec_steps p state = bir_exec_steps_opt p state 0 NONE)`


val bir_exec_steps_opt_NONE_REWRS = store_thm ("bir_exec_steps_opt_NONE_REWRS",
  ``bir_exec_steps_opt p state b NONE =
    (if bir_state_is_terminated state then SOME (b, state) else
       bir_exec_steps_opt p (bir_exec_step p state) (SUC b) NONE)``,

SIMP_TAC std_ss [Once whileTheory.OWHILE_THM, bir_exec_steps_opt_def] >>
METIS_TAC[]);


val bir_exec_steps_opt_SOME_REWRS = store_thm ("bir_exec_steps_opt_SOME_REWRS",
  ``bir_exec_steps_opt p state b (SOME m) =
    (if ((m <= b) \/ bir_state_is_terminated state) then SOME (b, state) else
       bir_exec_steps_opt p (bir_exec_step p state) (SUC b) (SOME m))``,

SIMP_TAC std_ss [Once whileTheory.OWHILE_THM, bir_exec_steps_opt_def] >>
COND_CASES_TAC >> FULL_SIMP_TAC arith_ss []);


val FUNPOW_bir_exec_steps_opt_REWR = store_thm ("FUNPOW_bir_exec_steps_opt_REWR",
  ``!n b st. (FUNPOW (\(n,st). (SUC n,bir_exec_step p st)) n (b,st)) =
      (b + n, FUNPOW (bir_exec_step p) n st)``,
Induct >> ASM_SIMP_TAC arith_ss [arithmeticTheory.FUNPOW]);


val bir_exec_steps_opt_EQ_NONE = store_thm ("bir_exec_steps_opt_EQ_NONE",
  ``(bir_exec_steps_opt p state b mo = NONE) <=>
    ((mo = NONE) /\ (!n. ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state))))``,

SIMP_TAC (std_ss ++ boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_opt_def, whileTheory.OWHILE_EQ_NONE,
  FUNPOW_bir_exec_steps_opt_REWR, FORALL_AND_THM] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
Cases_on `mo` >> SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `x` >> DECIDE_TAC);


val bir_exec_steps_EQ_NONE = store_thm ("bir_exec_steps_EQ_NONE",
  ``(bir_exec_steps p state = NONE) <=>
    (!n. ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_EQ_NONE]);


val bir_exec_steps_opt_EQ_SOME = store_thm ("bir_exec_steps_opt_EQ_SOME",
  ``(case mo of NONE => T | SOME m => (b <= m)) ==>
    ((bir_exec_steps_opt p state b mo = SOME (c, state')) <=>
    ((case mo of NONE => (bir_state_is_terminated state')
               | SOME m => ((c <= m) /\ ((c < m) ==> (bir_state_is_terminated state')))) /\
     (b <= c) /\
     (state' = FUNPOW (bir_exec_step p) (c - b) state) /\
     (!n. n < c-b ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)))))``,

SIMP_TAC std_ss [whileTheory.OWHILE_def, bir_exec_steps_opt_def, FUNPOW_bir_exec_steps_opt_REWR] >>
STRIP_TAC >>
Q.ABBREV_TAC `P = \n. ~(case mo of NONE => T | SOME m => b + n < m) \/
  bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)` >>
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



val bir_exec_steps_EQ_SOME = store_thm ("bir_exec_steps_EQ_SOME",
  ``((bir_exec_steps p state = SOME (c, state')) <=>
    ((bir_state_is_terminated state') /\
     (state' = FUNPOW (bir_exec_step p) c state) /\
     (!n. n < c ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)))))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_EQ_SOME]);


val bir_exec_step_n_EQ_THM = store_thm ("bir_exec_step_n_EQ_THM",
  ``((bir_exec_step_n p state n = (c, state')) <=>
     ((c <= n) /\ ((c < n) ==> (bir_state_is_terminated state'))) /\
     (state' = FUNPOW (bir_exec_step p) c state) /\
     (!n'. n' < c ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n' state))))``,

SIMP_TAC std_ss [bir_exec_step_n_def] >>
Cases_on `bir_exec_steps_opt p state 0 (SOME n)` >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_opt_EQ_NONE]
) >>
FULL_SIMP_TAC std_ss [] >>
rename1 `x = (c, state')` >>
Cases_on `x` >>
rename1 `(c0, state'') = (c, state')` >>
FULL_SIMP_TAC (std_ss) [bir_exec_steps_opt_EQ_SOME] >>
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


val bir_exec_step_FUNPOW_EXECS_ADD = store_thm ("bir_exec_step_FUNPOW_EXECS_ADD",
``!p state n.
    bir_is_valid_state p state ==> bir_is_valid_program p ==>
    (!i. i < n ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) i state))) ==>
    ((FUNPOW (bir_exec_step p) n state).bst_execs = state.bst_execs + n)``,

GEN_TAC >> GEN_TAC >>
Induct_on `n` >- (
  SIMP_TAC std_ss [arithmeticTheory.FUNPOW]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC arith_ss [arithmeticTheory.FUNPOW_SUC] >>
Q.ABBREV_TAC `state' =  (FUNPOW (bir_exec_step p) n state)` >>
MP_TAC (Q.SPECL [`p`, `state'`] bir_exec_step_execs) >>
`bir_is_valid_state p state'` by METIS_TAC[bir_exec_step_FUNPOW_valid_state_invar] >>
Q.PAT_X_ASSUM `!i. _` (MP_TAC o Q.SPEC `n`) >>
ASM_SIMP_TAC arith_ss []);



val bir_exec_steps_opt_EXECS_ADD = store_thm ("bir_exec_steps_opt_EXECS_ADD",
``!p state state' b mo c.
    bir_is_valid_state p state ==> bir_is_valid_program p ==>
    (case mo of NONE => T | SOME m => b <= m) ==>
    (bir_exec_steps_opt p state b mo = SOME (c, state')) ==>
    (state'.bst_execs = state.bst_execs + (c - b))``,

SIMP_TAC std_ss [bir_exec_steps_opt_EQ_SOME] >>
REPEAT STRIP_TAC >>
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_exec_step_FUNPOW_EXECS_ADD) >>
ASM_SIMP_TAC std_ss []);



val bir_exec_step_n_EXECS_ADD = store_thm ("bir_exec_step_n_EXECS_ADD",
``!p state state' n c.
    bir_is_valid_state p state ==> bir_is_valid_program p ==>
    (bir_exec_step_n p state n = (c, state')) ==>
    (state'.bst_execs = state.bst_execs + c)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM] >>
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_exec_step_FUNPOW_EXECS_ADD) >>
ASM_SIMP_TAC std_ss []);



val bir_exec_steps_EXECS_ADD = store_thm ("bir_exec_steps_EXECS_ADD",
``!p state state' c.
    bir_is_valid_state p state ==> bir_is_valid_program p ==>
    (bir_exec_steps p state = SOME (c, state')) ==>
    (state'.bst_execs = state.bst_execs + c)``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `state`, `state'`, `0`, `NONE`] bir_exec_steps_opt_EXECS_ADD) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_def]);




(* ------------------------------------------------------------------------- *)
(*  Environment Order                                                        *)
(* ------------------------------------------------------------------------- *)


val bir_state_set_failed_SAME_ENV = store_thm ("bir_state_set_failed_SAME_ENV",
  ``!st msg. (bir_state_set_failed st msg).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_failed_def]);


val bir_state_normalise_pc_SAME_ENV = store_thm ("bir_state_normalise_pc_SAME_ENV",
  ``!p st. (bir_state_normalise_pc p st).bst_environ = st.bst_environ``,
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_state_normalise_pc_def] >>
CASE_TAC >> SIMP_TAC (std_ss++bir_state_ss) []);


val bir_state_incr_pc_SAME_ENV = store_thm ("bir_state_incr_pc_SAME_ENV",
  ``!p st. (bir_state_incr_pc p st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_def, bir_state_normalise_pc_SAME_ENV]);

val bir_state_set_pc_SAME_ENV = store_thm ("bir_state_set_pc_SAME_ENV",
  ``!p st l. (bir_state_set_pc p st l).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_pc_def, bir_state_normalise_pc_SAME_ENV]);


val bir_exec_stmt_jmp_SAME_ENV = store_thm("bir_exec_stmt_jmp_SAME_ENV",
  ``!p st l. (bir_exec_stmt_jmp p l st).bst_environ = st.bst_environ``,
SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC (std_ss++bir_state_ss) [bir_state_set_pc_SAME_ENV]);



val bir_exec_stmt_cjmp_SAME_ENV = store_thm("bir_exec_stmt_cjmp_SAME_ENV",
  ``!p e st l1 l2. (bir_exec_stmt_cjmp p e l1 l2 st).bst_environ = st.bst_environ``,
SIMP_TAC std_ss [bir_exec_stmt_cjmp_def] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_jmp_SAME_ENV,
   bir_state_set_failed_SAME_ENV]
);


val bir_exec_stmt_halt_SAME_ENV = store_thm("bir_exec_stmt_halt_SAME_ENV",
  ``!e st. (bir_exec_stmt_halt e st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_halt_def]);


val bir_exec_stmt_assert_SAME_ENV = store_thm("bir_exec_stmt_assert_SAME_ENV",
  ``!p e st. (bir_exec_stmt_assert p e st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_assert_def] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_SAME_ENV,
   bir_state_set_failed_SAME_ENV]
);


val bir_exec_stmt_assume_SAME_ENV = store_thm("bir_exec_stmt_assume_SAME_ENV",
  ``!p e st. (bir_exec_stmt_assume p e st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_assume_def] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_SAME_ENV,
   bir_state_set_failed_SAME_ENV]
);


val bir_exec_stmt_declare_ENV = store_thm("bir_exec_stmt_declare_ENV",
  ``!p vn vty st. (bir_exec_stmt_declare p vn vty st).bst_environ =
      if (bir_env_varname_is_bound st.bst_environ vn) then st.bst_environ else
      (bir_env_update vn (bir_declare_initial_value vty) vty
            st.bst_environ)``,

SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_declare_def, LET_DEF] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_SAME_ENV,
     bir_state_set_failed_SAME_ENV, bir_is_regular_env_def]
) >>
Cases_on `st.bst_environ` >> FULL_SIMP_TAC std_ss [bir_env_update_def] >>
Cases_on `vty` >> FULL_SIMP_TAC std_ss [bir_declare_initial_value_def,
  bir_is_regular_env_def, type_of_bir_val_def]);


val bir_exec_stmt_assign_ENV = store_thm("bir_exec_stmt_assign_ENV",
  ``!p v e st.
      (bir_exec_stmt_assign p v e st).bst_environ =
      (if bir_is_regular_env (bir_env_write v (bir_eval_exp e st.bst_environ) st.bst_environ) then
         (bir_env_write v (bir_eval_exp e st.bst_environ) st.bst_environ)
       else st.bst_environ)``,

SIMP_TAC (std_ss++bir_state_ss) [bir_exec_stmt_assign_def, LET_DEF] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> (
   ASM_SIMP_TAC (std_ss++bir_state_ss) [bir_state_incr_pc_SAME_ENV,
     bir_state_set_failed_SAME_ENV]
));


val bir_exec_stmt_ENV_ORDER = store_thm ("bir_exec_stmt_ENV_ORDER",
``!p st stmt. bir_env_order st.bst_environ (bir_exec_stmt p stmt st).bst_environ``,

Cases_on `stmt` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_stmt_def, bir_exec_stmt_jmp_SAME_ENV,
    bir_exec_stmt_cjmp_SAME_ENV, bir_exec_stmt_halt_SAME_ENV,
    bir_exec_stmt_assert_SAME_ENV, bir_exec_stmt_assume_SAME_ENV,
    bir_env_order_REFL, bir_exec_stmt_assign_ENV,  bir_exec_stmt_declare_ENV]
) >- (
  REPEAT STRIP_TAC >>
  rename1 `bir_var_name v` >>
  Cases_on `bir_env_varname_is_bound st.bst_environ (bir_var_name v)` >> ASM_REWRITE_TAC[] >>
  MATCH_MP_TAC bir_env_order_update >>
  ASM_REWRITE_TAC[] >>
  Cases_on `bir_var_type v` >> (
    ASM_SIMP_TAC std_ss [bir_declare_initial_value_def, type_of_bir_val_def]
  )
) >- (
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC bir_env_order_write >>
  ASM_REWRITE_TAC[]
));


val bir_exec_step_ENV_ORDER = store_thm ("bir_exec_step_ENV_ORDER",
``!p st. bir_env_order st.bst_environ (bir_exec_step p st).bst_environ``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_exec_step_def] >>
REPEAT CASE_TAC >> (
  SIMP_TAC (std_ss++bir_state_ss) [bir_env_order_REFL, bir_state_set_failed_SAME_ENV,
    bir_exec_stmt_ENV_ORDER]
));



val bir_exec_step_FUNPOW_ENV_ORDER = store_thm ("bir_exec_step_FUNPOW_ENV_ORDER",
``!p n st. bir_env_order st.bst_environ (FUNPOW (bir_exec_step p) n st).bst_environ``,

GEN_TAC >>
Induct >> (
  SIMP_TAC std_ss [arithmeticTheory.FUNPOW, bir_env_order_REFL]
) >>
GEN_TAC >>
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_env_order_TRANS) >>
Q.EXISTS_TAC `(bir_exec_step p st).bst_environ` >>
ASM_SIMP_TAC std_ss [bir_exec_step_ENV_ORDER]);



val bir_exec_steps_ENV_ORDER = store_thm ("bir_exec_steps_ENV_ORDER",
``!p c st st'. (bir_exec_steps p st = SOME (c, st')) ==>
  bir_env_order st.bst_environ st'.bst_environ``,

SIMP_TAC std_ss [bir_exec_steps_EQ_SOME, bir_exec_step_FUNPOW_ENV_ORDER]);


val bir_exec_step_n_ENV_ORDER = store_thm ("bir_exec_step_n_ENV_ORDER",
``!p c n st st'. (bir_exec_step_n p st n = (c, st')) ==>
  bir_env_order st.bst_environ st'.bst_environ``,

SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, bir_exec_step_FUNPOW_ENV_ORDER]);


val _ = export_theory();
