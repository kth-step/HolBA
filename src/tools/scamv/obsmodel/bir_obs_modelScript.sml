open HolKernel Parse boolLib bossLib;
open bir_programTheory;
open bslSyntax;
open wordsSyntax;

val _ = new_theory "bir_obs_model";

val _ = Datatype `load_store_pc_t =
   LSPC_Load bir_val_t
 | LSPC_Store bir_val_t
 | LSPC_PC bir_val_t`;

val gen_LSPC_Load_def = Define `
  gen_LSPC_Load [x] = LSPC_Load x
`;

val gen_LSPC_Store_def = Define `
  gen_LSPC_Store [x] = LSPC_Store x
`;

val gen_LSPC_PC_def = Define `
  gen_LSPC_PC [x] = LSPC_PC x
`;

val map_obs_prog_def = Define `
map_obs_prog f (BirProgram xs) = BirProgram (MAP f xs)
`;


val _ = Datatype `select_mem_t =
   select_mem_LD bir_exp_t
 | select_mem_ST bir_exp_t`;
 
val select_mem_def = Define`
select_mem exp =
(case exp of
    BExp_Cast c e t => select_mem e
  | BExp_UnaryExp ue e => select_mem e
  | BExp_BinExp be e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_BinPred bp e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_MemEq e1 e2 => select_mem e1 ++ select_mem e2
  | BExp_IfThenElse e1 e2 e3 => select_mem e1 ++ select_mem e2 ++ select_mem e3
  | BExp_Load e1 e2 a b =>   (select_mem_LD e2) :: (select_mem e1 ++ select_mem e2) 
  | BExp_Store e1 e2 a e3 => (select_mem_ST e2) :: (select_mem e1 ++ select_mem e2 ++ select_mem e3)
  | _ => [])
`;

val select_mem_flatten_def = Define`
select_mem_flatten x = case x of select_mem_LD e => e | select_mem_ST e => e
`;

(* ======================= *)
(* Stack pointer alignment *)
(* ======================= *)

open bir_exp_recursionTheory;

val check_sp_def = Define`
check_sp exp =
((BVar "SP_EL0" (BType_Imm Bit64)) IN (bir_varset_of_exp exp))
`;

val sp_align_constrain_def = Define`
sp_align_constrain =
    BStmt_Assert
     (BExp_BinPred BIExp_Equal
       (BExp_BinExp BIExp_And
         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
         (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)))
`;

val add_obs_constr_sp_stmts_def = Define `
(add_obs_constr_sp_stmts [] = []) /\
(add_obs_constr_sp_stmts (x :: xs) =
 case x of
     BStmt_Assign v e =>
       (case check_sp e of
          F => x :: add_obs_constr_sp_stmts xs
        | T => sp_align_constrain :: x :: add_obs_constr_sp_stmts xs)
 | _ => x :: add_obs_constr_sp_stmts xs)
`;

val add_obs_constr_sp_block_def = Define`
    add_obs_constr_sp_block block =
      block with bb_statements := add_obs_constr_sp_stmts block.bb_statements
`;

(* ======================= *)
(* ======================= *)

val constrain_mem_def = Define`
constrain_mem (mem_min, mem_max) e =
    BStmt_Assert
     (BExp_BinExp BIExp_And
       (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 mem_min)) (e))
       (BExp_BinPred BIExp_LessThan (e) (BExp_Const (Imm64 mem_max))))
`;

val add_obs_constr_mem_stmts_ls_def = Define `
(add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st [] = []) /\
(add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case select_mem e of
          [] => x :: add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st xs
        | lds => (APPEND (MAP (constrain_mem mem_bounds) (MAP select_mem_flatten lds))
                      (* TODO: (Andreas:) Can it be that there is a bug here with the order, first xs, and then x? *)
                      (APPEND (APPEND (MAP (\x. case x of select_mem_LD e => obs_fun_ld e | select_mem_ST e => obs_fun_st e) lds) (add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st xs)) [x])))
   | _ => x :: add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st xs)
`;

val add_obs_constr_mem_stmts_def = Define `
    add_obs_constr_mem_stmts mem_bounds obs_fun = add_obs_constr_mem_stmts_ls mem_bounds obs_fun obs_fun
`;

val add_obs_constr_mem_block_def = Define`
    add_obs_constr_mem_block mem_bounds obs_fun block =
      block with bb_statements := add_obs_constr_mem_stmts mem_bounds obs_fun block.bb_statements
`;

val add_obs_constr_mem_block_ls_def = Define`
    add_obs_constr_mem_block_ls mem_bounds obs_fun_ld obs_fun_st block =
      block with bb_statements := add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st block.bb_statements
`;


val map_end_prog_def = Define‘
   map_end_prog f [] = []
/\ map_end_prog f [b] = [b]
/\ map_end_prog f (b::next_b::bs) =
   (b with <| bb_last_statement updated_by (f (next_b.bb_label)) |>):: map_end_prog f (next_b::bs)
’;

val jmp_to_cjmp_def = Define‘
    (jmp_to_cjmp next_lbl (BStmt_Jmp target) =
     if target <> (BLE_Label next_lbl)
     then BStmt_CJmp (BExp_Const (Imm1 1w)) target (BLE_Label next_lbl)
     else BStmt_Jmp target)
 /\ jmp_to_cjmp next_lbl stmt = stmt
’;

val jmp_to_cjmp_prog_def = Define‘
   jmp_to_cjmp_prog (BirProgram xs) = BirProgram (map_end_prog jmp_to_cjmp xs)
’;

(* observe pc *)
(* ============================================================================== *)
val observe_label_def = Define `
    observe_label (BL_Address addr) =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       [BExp_Const addr]
                       HD
`;
val observe_label_pc_def = Define `
    observe_label_pc (BL_Address addr) =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       [BExp_Const addr]
                       gen_LSPC_PC
`;

val add_obs_pc_block_def = Define`
    add_obs_pc_block block =
      block with bb_statements :=
        observe_label (block.bb_label) :: block.bb_statements
`;

val add_obs_pc_block_pc_def = Define`
    add_obs_pc_block_pc block =
      block with bb_statements :=
        observe_label_pc (block.bb_label) :: block.bb_statements
`;

val add_obs_pc_def = Define`
    add_obs_pc p = map_obs_prog add_obs_pc_block p
`;

(* observe whole memory address *)
(* ============================================================================== *)
val observe_mem_addr_def = Define`
    observe_mem_addr e = 
      BStmt_Observe 0
                    (BExp_Const (Imm1 1w))
                    [e]
                    HD
`;
val observe_gen_def = Define`
    observe_gen gen_fun e = 
      BStmt_Observe 0
                    (BExp_Const (Imm1 1w))
                    [e]
                    gen_fun
`;

val add_obs_mem_addr_armv8_def = Define`
    add_obs_mem_addr_armv8 mem_bounds p = 
map_obs_prog (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_addr)) p
`;


(* observe whole memory address and pc *)
(* ============================================================================== *)
val add_obs_mem_addr_pc_armv8_def = Define`
    add_obs_mem_addr_pc_armv8 mem_bounds p = 
      map_obs_prog (add_obs_pc_block o (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_addr))) p
`;


(* observe whole memory address and pc (lspc type construction annototation) *)
(* ============================================================================== *)
val add_obs_mem_addr_pc_lspc_armv8_def = Define`
    add_obs_mem_addr_pc_lspc_armv8 mem_bounds p = 
      map_obs_prog (add_obs_pc_block_pc o (add_obs_constr_sp_block o (add_obs_constr_mem_block_ls mem_bounds (observe_gen gen_LSPC_Load) (observe_gen gen_LSPC_Store)))) p
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
    add_obs_cache_line_tag_index_armv8 mem_bounds p = map_obs_prog (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_tag_index)) p
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
    add_obs_cache_line_tag_armv8 mem_bounds p = map_obs_prog (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_tag)) p
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
add_obs_cache_line_index_armv8 mem_bounds p = map_obs_prog (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_index)) p
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
    add_obs_cache_line_subset_armv8 mem_bounds p = map_obs_prog (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_subset)) p
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
add_obs_cache_line_subset_page_armv8 mem_bounds p = map_obs_prog (add_obs_constr_sp_block o (add_obs_constr_mem_block mem_bounds observe_mem_subset_page)) p
`;


(* Subset with extra observation: (Andreas: extra obs seems to be only added if first stmt is an Assign) *)
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
    add_obs_stmts_subset mem_bounds = add_obs_constr_mem_stmts mem_bounds observe_mem_subset`;

val add_obs_stmts_subset_and_line_def = Define `
(add_obs_constr_mem_stmts_subset_and_line mem_bounds [] = []) /\
(add_obs_constr_mem_stmts_subset_and_line mem_bounds (x :: xs) =
 case x of
     BStmt_Assign v e =>
     (case MAP select_mem_flatten (select_mem e) of
          [] => x :: add_obs_stmts_subset mem_bounds xs
        | lds => (APPEND (MAP (constrain_mem mem_bounds) lds)
                         (x :: (APPEND (MAP observe_mem_subset lds)
                                       (APPEND (MAP observe_mem_line lds)
                                               (add_obs_stmts_subset mem_bounds xs))))))
   | _ => x :: add_obs_stmts_subset mem_bounds xs)
`;

val add_block_cache_line_subset_and_line_def = Define`
add_block_cache_line_subset_and_line mem_bounds block =
   block with bb_statements := add_obs_constr_mem_stmts_subset_and_line mem_bounds block.bb_statements
`;

val add_obs_cache_line_subset_and_line_armv8_def = Define`
add_obs_cache_line_subset_and_line_armv8 mem_bounds p = map_obs_prog (add_block_cache_line_subset_and_line mem_bounds) p
`;


(* helper definitions for speculative branch augmentation (cache_speculation) *)
(* ============================================================================== *)
val constrain_spec_obs_vars_def = Define`
    constrain_spec_obs_vars (e1, e2) =
    BStmt_Assign  (e1) (e2) :bir_val_t bir_stmt_basic_t
    `;

val append_list_def = Define`
    append_list (lbl, (l1:  bir_val_t bir_stmt_basic_t list)) l2 =
    let combLst = APPEND l2 l1 in (lbl, combLst)
    `;


val _ = export_theory();
