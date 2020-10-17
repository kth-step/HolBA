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

val select_mem_def = Define`
select_mem exp =
(case exp of
    BExp_Cast c e t => select_mem e
  | BExp_UnaryExp ue e => select_mem e
  | BExp_BinExp be e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_BinPred bp e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_MemEq e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_IfThenElse e1 e2 e3 => select_mem e1 ++ select_mem e2 ++ select_mem e3
  | BExp_Load e1 e2 a b =>   e2 :: (select_mem e1 ++ select_mem e2) 
  | BExp_Store e1 e2 a e3 => e2 :: (select_mem e1 ++ select_mem e2 ++ select_mem e3)
  | _ => [])

`;

val constrain_mem_def = Define`
constrain_mem e =
    BStmt_Assert
     (BExp_BinExp BIExp_And
       (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 ^(mem_min))) (e))
       (BExp_BinPred BIExp_LessThan (e) (BExp_Const (Imm64 ^(mem_max)))))
`;

val add_obs_1_stmts_def = Define `
(add_obs_1_stmts obs_fun [] = []) /\
(add_obs_1_stmts obs_fun (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_mem e of
          [] => x :: add_obs_1_stmts obs_fun xs
        | lds => (APPEND (MAP constrain_mem lds)
                      (APPEND (APPEND (MAP obs_fun lds) (add_obs_1_stmts obs_fun xs)) [x])))
   | _ => x :: add_obs_1_stmts obs_fun xs)
`;

val add_obs_1_block_def = Define`
    add_obs_1_block obs_fun block =
      block with bb_statements := add_obs_1_stmts obs_fun block.bb_statements
`;


(* observe pc *)
(* ============================================================================== *)
val observe_label_def = Define `
    observe_label (BL_Address addr) =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       [BExp_Const addr]
                       HD
`;

val add_obs_pc_block_def = Define`
    add_obs_pc_block block =
      block with bb_statements :=
        observe_label (block.bb_label) :: block.bb_statements
`;

val add_obs_pc_def = Define`
    add_obs_pc p = map_obs_prog add_obs_pc_block p
`;


(* observe whole memory address and pc *)
(* ============================================================================== *)
val observe_mem_addr_def = Define`
    observe_mem_addr e = 
      BStmt_Observe 0
                    (BExp_Const (Imm1 1w))
                    [e]
                    HD
`;

(* TODO: better use add_obs_pc_block and don't append in the end for no reason
         but, it seems that at the moment use of add_obs_pc_block always leads to
              unsatisfiable... what's that??? *)
val append_obs_pc_block_def = Define`
    append_obs_pc_block block =
      block with bb_statements :=
        APPEND (block.bb_statements) [observe_label (block.bb_label)]
`;

val add_obs_mem_addr_pc_armv8_def = Define`
    add_obs_mem_addr_pc_armv8 p = 
      map_obs_prog (add_obs_pc_block o (add_obs_1_block observe_mem_addr)) p
`;


(* generic helper for augmentation of transient execution
   (prepend observation to specific block) *)
(* ============================================================================== *)
val prepend_obs_in_bir_block_def = Define`
    prepend_obs_in_bir_block id_obs block = 
      let (lbl, obs) = id_obs in
        if lbl = block.bb_label
        then block with bb_statements := APPEND obs block.bb_statements
        else block
`;

val prepend_obs_in_bir_prog_block_def = Define`
    prepend_obs_in_bir_prog_block id_obs p =
      map_obs_prog (prepend_obs_in_bir_block id_obs) p
`;


(* observe tag & set index *)
(* ============================================================================== *)
val observe_mem_tag_index_def = Define`
    observe_mem_tag_index e =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w))])
                       HD
`;

val add_obs_cache_line_tag_index_armv8_def = Define`
    add_obs_cache_line_tag_index_armv8 p = map_obs_prog (add_obs_1_block observe_mem_tag_index) p
`;


(* observe tag only *)
(* ============================================================================== *)
val observe_mem_tag_def = Define`
    observe_mem_tag e =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 13w))])
                       HD
`;

val add_obs_cache_line_tag_armv8_def = Define`
    add_obs_cache_line_tag_armv8 p = map_obs_prog (add_obs_1_block observe_mem_tag) p
`;


(* observe index only *)
(* ============================================================================== *)
val observe_mem_index_def = Define`
    observe_mem_index e =
         BStmt_Observe
           0
           (BExp_Const (Imm1 1w))
           ([BExp_BinExp BIExp_And
                    (BExp_Const (Imm64 0x7Fw))
                    (BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w)))])
           HD
`;

val add_obs_cache_line_index_armv8_def = Define`
add_obs_cache_line_index_armv8 p = map_obs_prog (add_obs_1_block observe_mem_index) p
`;


(* observe tag & set index, if set index is in upper half, misses page boundary by 3 sets *)
(* ============================================================================== *)
val observe_mem_subset_def = Define`
    observe_mem_subset e =
         BStmt_Observe
           0
           (BExp_BinPred BIExp_LessThan
               (BExp_Const (Imm64 60w))
               (BExp_BinExp BIExp_Mod
                     (BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w)))
                     (BExp_Const (Imm64 128w))))
                            (* (BExp_BinExp BIExp_And *)
                            (*              (BExp_Const (Imm64 0x1000w))) *)
                            (*          (BExp_Const (Imm64 0w))) *)
           ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w))])
           HD
`;

val add_obs_cache_line_subset_armv8_def = Define`
    add_obs_cache_line_subset_armv8 p = map_obs_prog (add_obs_1_block observe_mem_subset) p
`;


(* observe tag & set index, if set index is in upper half, on page boundary *)
(* ============================================================================== *)
val observe_mem_subset_page_def = Define`
    observe_mem_subset_page e =
         BStmt_Observe
           0
           (BExp_BinPred BIExp_LessThan
                (BExp_Const (Imm64 63w))
                (BExp_BinExp BIExp_Mod
                   (BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w)))
                   (BExp_Const (Imm64 128w))))
                            (* (BExp_BinExp BIExp_And *)
                            (*              (BExp_Const (Imm64 0x1000w))) *)
                            (*          (BExp_Const (Imm64 0w))) *)
           ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w))])
           HD
`;

val add_obs_cache_line_subset_page_armv8_def = Define`
add_obs_cache_line_subset_page_armv8 p = map_obs_prog (add_obs_1_block observe_mem_subset_page) p
`;


(* Subset with extra observation *)
(* ============================================================================== *)
val observe_mem_line_def = Define`
    observe_mem_line e =
         BStmt_Observe
              0
              ^btrue
              ([BExp_BinExp BIExp_RightShift (
                  BExp_BinExp BIExp_And e (
                    BExp_BinExp BIExp_LeftShift
                         (BExp_Const (Imm64 0x7Fw))
                         (BExp_Const (Imm64 6w))))
                (BExp_Const (Imm64 6w))])
              HD
`;

val add_obs_stmts_subset_def = Define `
    add_obs_stmts_subset = add_obs_1_stmts observe_mem_subset`;

val add_obs_stmts_subset_and_line_def = Define `
(add_obs_stmts_subset_and_line [] = []) /\
(add_obs_stmts_subset_and_line (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_mem e of
          [] => x :: add_obs_stmts_subset xs
        | lds => (APPEND (MAP constrain_mem lds)
                         (x :: (APPEND (MAP observe_mem_subset lds)
                                       (APPEND (MAP observe_mem_line lds)
                                               (add_obs_stmts_subset xs))))))
   | _ => x :: add_obs_stmts_subset xs)
`;

val add_block_cache_line_subset_and_line_def = Define`
add_block_cache_line_subset_and_line block =
   block with bb_statements := add_obs_stmts_subset_and_line block.bb_statements
`;

val add_obs_cache_line_subset_and_line_armv8_def = Define`
add_obs_cache_line_subset_and_line_armv8 p = map_obs_prog add_block_cache_line_subset_and_line p
                                                                                                 `;


val _ = export_theory();
