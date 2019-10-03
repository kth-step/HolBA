open HolKernel Parse boolLib bossLib;
open bir_programTheory;
open bslSyntax;
open wordsSyntax;
open bir_embexp_driverLib;

val _ = new_theory "bir_obs_model";

val (mem_base, mem_offset) = bir_embexp_params_memory;
val (mem_min, mem_max) =
    (mk_wordi (bir_embexp_params_cacheable mem_base, 64),
     mk_wordi (bir_embexp_params_cacheable (Arbnum.- (Arbnum.+ (mem_base, mem_offset), Arbnum.fromInt 128)), 64));

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

val select_mem_def = Define`
select_mem exp =
case exp of
    BExp_Cast c e t => select_mem e
  | BExp_UnaryExp ue e => select_mem e
  | BExp_BinExp be e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_BinPred bp e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_MemEq e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_IfThenElse e1 e2 e3 => select_mem e1 ++ select_mem e2 ++ select_mem e3
  | BExp_Load e1 e2 a b => e2 :: (select_mem e1 ++ select_mem e2)
  | BExp_Store e1 e2 a e3 => e2 :: (select_mem e1 ++ select_mem e2 ++ select_mem e3)
  | _ => []
`;

val constrain_mem_def = Define`
constrain_mem e =
  BStmt_Assert
       (BExp_BinExp BIExp_And
                    (BExp_BinPred
                         BIExp_LessOrEqual
                         (BExp_Const (Imm64 ^(mem_min)))
                         e)
                    (BExp_BinPred
                         BIExp_LessThan
                         e
                         (BExp_Const (Imm64 ^(mem_max)))))
`;


(* observe tag & set index *)
val observe_mem_def = Define`
observe_mem e =
         BStmt_Observe (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w))])
                       HD
`;

val add_obs_stmts_def = Define `
(add_obs_stmts [] = []) /\
(add_obs_stmts (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_mem e of
          [] => x :: add_obs_stmts xs
        | lds => (APPEND (MAP constrain_mem lds)
                      (x :: (APPEND (MAP observe_mem lds) (add_obs_stmts xs)))))
   | _ => x :: add_obs_stmts xs)
`;

val add_block_cache_line_def = Define`
add_block_cache_line block =
         block with bb_statements := add_obs_stmts block.bb_statements
`;

val add_obs_cache_line_armv8_def = Define`
add_obs_cache_line_armv8 p = map_obs_prog add_block_cache_line p
`;


(* observe tag only *)
val observe_mem_tag_def = Define`
observe_mem_tag e =
         BStmt_Observe (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 13w))])
                       HD
`;

val add_obs_stmts_tag_def = Define `
(add_obs_stmts_tag [] = []) /\
(add_obs_stmts_tag (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_mem e of
          [] => x :: add_obs_stmts_tag xs
        | lds => (APPEND (MAP constrain_mem lds)
                         (x :: (APPEND (MAP observe_mem_tag lds) (add_obs_stmts_tag xs)))))
   | _ => x :: add_obs_stmts_tag xs)
`;

val add_block_cache_line_tag_def = Define`
add_block_cache_line_tag block =
        block with bb_statements := add_obs_stmts_tag block.bb_statements
`;

val add_obs_cache_line_tag_armv8_def = Define`
add_obs_cache_line_tag_armv8 p = map_obs_prog add_block_cache_line p
`;


(* observe tag & set index, if set index is in lower half *)
val observe_mem_subset_def = Define`
observe_mem_subset e =
         BStmt_Observe (BExp_BinPred BIExp_Equal
                                     (BExp_BinExp BIExp_And
                                                  (BExp_Const (Imm1 0x1000w))
                                                  e)
                                     (BExp_Const (Imm1 0w)))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w))])
                       HD
`;

val add_obs_stmts_subset_def = Define `
(add_obs_stmts_subset [] = []) /\
(add_obs_stmts_subset (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_mem e of
          [] => x :: add_obs_stmts_subset xs
        | lds => (APPEND (MAP constrain_mem lds)
                      (x :: (APPEND (MAP observe_mem_subset lds) (add_obs_stmts_subset xs)))))
   | _ => x :: add_obs_stmts_subset xs)
`;

val add_block_cache_line_subset_def = Define`
add_block_cache_line_subset block =
         block with bb_statements := add_obs_stmts_subset block.bb_statements
`;

val add_obs_cache_line_subset_armv8_def = Define`
add_obs_cache_line_subset_armv8 p = map_obs_prog add_block_cache_line_subset p
`;


val _ = export_theory();
