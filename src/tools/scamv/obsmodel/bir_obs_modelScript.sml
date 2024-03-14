open HolKernel Parse boolLib bossLib;
open bir_programTheory;
open bslSyntax;
open wordsSyntax;

val _ = new_theory "bir_obs_model";

Datatype:
  load_store_pc_t =
   LSPC_Load bir_val_t
 | LSPC_Store bir_val_t
 | LSPC_PC bir_val_t
End

Definition gen_LSPC_Load_def:
  gen_LSPC_Load [x] = LSPC_Load x
End

Definition gen_LSPC_Store_def:
  gen_LSPC_Store [x] = LSPC_Store x
End

Definition gen_LSPC_PC_def:
  gen_LSPC_PC [x] = LSPC_PC x
End

Definition map_obs_prog_def:
  map_obs_prog f (BirProgram xs) = BirProgram (MAP f xs)
End


Datatype:
  select_mem_t =
   select_mem_LD bir_exp_t
 | select_mem_ST bir_exp_t
End
 
Definition select_mem_def:
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
End

Definition select_mem_flatten_def:
  select_mem_flatten x = case x of select_mem_LD e => e | select_mem_ST e => e
End


Definition constrain_mem_def:
  constrain_mem (mem_min, mem_max) e =
    BStmt_Assert
     (BExp_BinExp BIExp_And
       (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 mem_min)) (e))
       (BExp_BinPred BIExp_LessThan (e) (BExp_Const (Imm64 mem_max))))
End

Definition add_obs_constr_mem_stmts_ls_def:
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
End

Definition add_obs_constr_mem_stmts_def:
  add_obs_constr_mem_stmts mem_bounds obs_fun = add_obs_constr_mem_stmts_ls mem_bounds obs_fun obs_fun
End

Definition add_obs_constr_mem_block_def:
  add_obs_constr_mem_block mem_bounds obs_fun block =
      block with bb_statements := add_obs_constr_mem_stmts mem_bounds obs_fun block.bb_statements
End

Definition add_obs_constr_mem_block_ls_def:
  add_obs_constr_mem_block_ls mem_bounds obs_fun_ld obs_fun_st block =
      block with bb_statements := add_obs_constr_mem_stmts_ls mem_bounds obs_fun_ld obs_fun_st block.bb_statements
End


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
Definition observe_label_def:
  observe_label (BL_Address addr) =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       [BExp_Const addr]
                       HD
End
Definition observe_label_pc_def:
  observe_label_pc (BL_Address addr) =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       [BExp_Const addr]
                       gen_LSPC_PC
End

Definition add_obs_pc_block_def:
  add_obs_pc_block block =
      block with bb_statements :=
        observe_label (block.bb_label) :: block.bb_statements
End

Definition add_obs_pc_block_pc_def:
  add_obs_pc_block_pc block =
      block with bb_statements :=
        observe_label_pc (block.bb_label) :: block.bb_statements
End

Definition add_obs_pc_def:
  add_obs_pc p = map_obs_prog add_obs_pc_block p
End

(* observe whole memory address *)
(* ============================================================================== *)
Definition observe_mem_addr_def:
  observe_mem_addr e = 
      BStmt_Observe 0
                    (BExp_Const (Imm1 1w))
                    [e]
                    HD
End
Definition observe_gen_def:
  observe_gen gen_fun e = 
      BStmt_Observe 0
                    (BExp_Const (Imm1 1w))
                    [e]
                    gen_fun
End

Definition add_obs_mem_addr_armv8_def:
  add_obs_mem_addr_armv8 mem_bounds p = 
      map_obs_prog (add_obs_constr_mem_block mem_bounds observe_mem_addr) p
End


(* observe whole memory address and pc *)
(* ============================================================================== *)
Definition add_obs_mem_addr_pc_armv8_def:
  add_obs_mem_addr_pc_armv8 mem_bounds p = 
      map_obs_prog (add_obs_pc_block o (add_obs_constr_mem_block mem_bounds observe_mem_addr)) p
End


(* observe whole memory address and pc (lspc type construction annototation) *)
(* ============================================================================== *)
Definition add_obs_mem_addr_pc_lspc_armv8_def:
  add_obs_mem_addr_pc_lspc_armv8 mem_bounds p = 
      map_obs_prog (add_obs_pc_block_pc o (add_obs_constr_mem_block_ls mem_bounds (observe_gen gen_LSPC_Load) (observe_gen gen_LSPC_Store))) p
End


(* generic helper for augmentation of transient execution
   (prepend observation to specific block) *)
(* ============================================================================== *)
Definition prepend_obs_in_bir_block_def:
  prepend_obs_in_bir_block id_obs block = 
      let (lbl, obs) = id_obs in
        if lbl = block.bb_label
        then block with bb_statements := APPEND obs block.bb_statements
        else block
End

Definition prepend_obs_in_bir_prog_block_def:
  prepend_obs_in_bir_prog_block id_obs p =
      map_obs_prog (prepend_obs_in_bir_block id_obs) p
End


(* observe tag & set index *)
(* ============================================================================== *)
Definition observe_mem_tag_index_def:
  observe_mem_tag_index e =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w))])
                       HD
End

Definition add_obs_cache_line_tag_index_armv8_def:
  add_obs_cache_line_tag_index_armv8 mem_bounds p = map_obs_prog (add_obs_constr_mem_block mem_bounds observe_mem_tag_index) p
End


(* observe tag only *)
(* ============================================================================== *)
Definition observe_mem_tag_def:
  observe_mem_tag e =
         BStmt_Observe 0
                       (BExp_Const (Imm1 1w))
                       ([BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 13w))])
                       HD
End

Definition add_obs_cache_line_tag_armv8_def:
  add_obs_cache_line_tag_armv8 mem_bounds p = map_obs_prog (add_obs_constr_mem_block mem_bounds observe_mem_tag) p
End


(* observe index only *)
(* ============================================================================== *)
Definition observe_mem_index_def:
  observe_mem_index e =
         BStmt_Observe
           0
           (BExp_Const (Imm1 1w))
           ([BExp_BinExp BIExp_And
                    (BExp_Const (Imm64 0x7Fw))
                    (BExp_BinExp BIExp_RightShift e (BExp_Const (Imm64 6w)))])
           HD
End

Definition add_obs_cache_line_index_armv8_def:
  add_obs_cache_line_index_armv8 mem_bounds p = map_obs_prog (add_obs_constr_mem_block mem_bounds observe_mem_index) p
End


(* observe tag & set index, if set index is in upper half, misses page boundary by 3 sets *)
(* ============================================================================== *)
Definition observe_mem_subset_def:
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
End

Definition add_obs_cache_line_subset_armv8_def:
  add_obs_cache_line_subset_armv8 mem_bounds p = map_obs_prog (add_obs_constr_mem_block mem_bounds observe_mem_subset) p
End


(* observe tag & set index, if set index is in upper half, on page boundary *)
(* ============================================================================== *)
Definition observe_mem_subset_page_def:
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
End

Definition add_obs_cache_line_subset_page_armv8_def:
  add_obs_cache_line_subset_page_armv8 mem_bounds p = map_obs_prog (add_obs_constr_mem_block mem_bounds observe_mem_subset_page) p
End


(* Subset with extra observation: (Andreas: extra obs seems to be only added if first stmt is an Assign) *)
(* ============================================================================== *)
Definition observe_mem_line_def:
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
End

Definition add_obs_stmts_subset_def:
  add_obs_stmts_subset mem_bounds = add_obs_constr_mem_stmts mem_bounds observe_mem_subset
End

Definition add_obs_stmts_subset_and_line_def:
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
End

Definition add_block_cache_line_subset_and_line_def:
  add_block_cache_line_subset_and_line mem_bounds block =
   block with bb_statements := add_obs_constr_mem_stmts_subset_and_line mem_bounds block.bb_statements
End

Definition add_obs_cache_line_subset_and_line_armv8_def:
  add_obs_cache_line_subset_and_line_armv8 mem_bounds p = map_obs_prog (add_block_cache_line_subset_and_line mem_bounds) p
End


(* helper definitions for speculative branch augmentation (cache_speculation) *)
(* ============================================================================== *)
Definition constrain_spec_obs_vars_def:
  constrain_spec_obs_vars (e1, e2) =
    BStmt_Assign  (e1) (e2) :bir_val_t bir_stmt_basic_t
End

Definition append_list_def:
  append_list (lbl, (l1:  bir_val_t bir_stmt_basic_t list)) l2 =
    let combLst = APPEND l2 l1 in (lbl, combLst)
End


val _ = export_theory();
