open HolKernel Parse boolLib bossLib;
open bir_programTheory;
open bslSyntax;

val _ = new_theory "bir_obs_model";

val map_obs_prog_def = Define `
map_obs_prog f (BirProgram xs) = BirProgram (MAP f xs)
`;

val observe_label_def = Define `
observe_label (BL_Address addr) =
BStmt_Observe (BExp_Const (Imm1 1w)) [BExp_Const addr]
              HD
`;

val add_block_pc_obs_def = Define`
add_block_pc_obs block =
block with bb_statements :=
observe_label (block.bb_label) :: block.bb_statements
`;

val add_obs_pc_def = Define`
add_obs_pc p = map_obs_prog add_block_pc_obs p
`;

val select_loads_def = Define`
select_loads exp =
case exp of
    BExp_Cast c e t => select_loads e
  | BExp_UnaryExp ue e => select_loads e
  | BExp_BinExp be e1 e2 => select_loads e1 ++ select_loads e2
  | BExp_BinPred bp e1 e2 => select_loads e1 ++ select_loads e2
  | BExp_MemEq e1 e2 => select_loads e1 ++ select_loads e2
  | BExp_IfThenElse e1 e2 e3 => select_loads e1 ++ select_loads e2 ++ select_loads e3
  | BExp_Load e1 e2 a b => BExp_Load e1 e2 a b :: (select_loads e1 ++ select_loads e2)
  | BExp_Store e1 e2 a e3 => select_loads e1 ++ select_loads e2 ++ select_loads e3
  | _ => []
`;

val observe_load_def = Define`
observe_load (BExp_Load _ e _ _) =
         BStmt_Observe (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_And
                                     (BExp_Const (Imm64 0x1FC0w))
                                     e])
                       HD
`;

val constrain_load_def = Define`
constrain_load (BExp_Load _ e _ _) =
  BStmt_Assert
       (BExp_BinExp BIExp_And
                    (BExp_BinPred
                         BIExp_LessOrEqual
                         (BExp_Const (Imm64 0x80030000w))
                         e)
                    (BExp_BinPred
                         BIExp_LessOrEqual
                         e
                         (BExp_Const (Imm64 0x80042FF8w))))
`;

val add_obs_stmts_def = Define `
(add_obs_stmts [] = []) /\
(add_obs_stmts (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_loads e of
          [] => x :: add_obs_stmts xs
        | lds => (APPEND (MAP constrain_load lds)
                      (x :: (APPEND (MAP observe_load lds) (add_obs_stmts xs)))))
   | _ => x :: add_obs_stmts xs)
`;


val observe_load_tag_def = Define`
observe_load_tag (BExp_Load _ e _ _) =
         BStmt_Observe (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_And
                                     (BExp_Const (Imm64 0xFFFFE000w))
                                     e])
                       HD
`;


val add_obs_stmts_tag_def = Define `
(add_obs_stmts_tag [] = []) /\
(add_obs_stmts_tag (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_loads e of
          [] => x :: add_obs_stmts_tag xs
        | lds => (APPEND (MAP constrain_load lds)
                         (x :: (APPEND (MAP observe_load_tag lds) (add_obs_stmts_tag xs)))))
   | _ => x :: add_obs_stmts_tag xs)
`;



val add_block_cache_line_def = Define`
add_block_cache_line block =
         block with bb_statements := add_obs_stmts block.bb_statements
`;

val add_obs_cache_line_armv8_def = Define`
add_obs_cache_line_armv8 p = map_obs_prog add_block_cache_line p
`;

val add_block_cache_line_tag_def = Define`
add_block_cache_line_tag block =
        block with bb_statements := add_obs_stmts_tag block.bb_statements
`;

val add_obs_cache_line_tag_armv8_def = Define`
add_obs_cache_line_tag_armv8 p = map_obs_prog add_block_cache_line p
`;


val _ = export_theory();
