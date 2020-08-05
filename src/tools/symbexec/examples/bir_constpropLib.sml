structure bir_constpropLib =
struct
local

val bir_exp_is_const_def = Define `
  (bir_exp_is_const (BExp_Const n) = T) /\
  (bir_exp_is_const _              = F)
`;

val bir_exp_is_mem_const_def = Define `
  (bir_exp_is_mem_const (BExp_MemConst aty vty mmap) = T) /\
  (bir_exp_is_mem_const _              = F)
`;

val bir_val_to_const_def = Define `
  (bir_val_to_const (BVal_Imm n) = (BExp_Const n)) /\
  (bir_val_to_const (BVal_Mem aty vty mmap) = (BExp_MemConst aty vty mmap))
`;

val bir_exp_eval_consts_def = Define `
  bir_exp_eval_consts e = bir_val_to_const(THE (bir_eval_exp e (BEnv (K NONE))))
`;


val bir_exp_const_prop_def = Define `
  (bir_exp_const_prop (BExp_Const n) = (BExp_Const n)) /\

  (bir_exp_const_prop (BExp_MemConst aty vty mmap) = (BExp_MemConst aty vty mmap)) /\

  (bir_exp_const_prop (BExp_Den v) = (BExp_Den v)) /\

  (bir_exp_const_prop (BExp_Cast ct e ty) = (
     let e_cp = (bir_exp_const_prop e); in
     if (bir_exp_is_const e_cp) then
       bir_exp_eval_consts (BExp_Cast ct e_cp ty)
     else
       (BExp_Cast ct e_cp ty)
  )) /\

  (bir_exp_const_prop (BExp_UnaryExp et e) = (
     let e_cp = (bir_exp_const_prop e); in
     if (bir_exp_is_const e_cp) then
       bir_exp_eval_consts (BExp_UnaryExp et e_cp)
     else
       (BExp_UnaryExp et e_cp)
  )) /\

  (bir_exp_const_prop (BExp_BinExp et e1 e2) = (
     let e1_cp = (bir_exp_const_prop e1);
         e2_cp = (bir_exp_const_prop e2); in
     if (EVERY bir_exp_is_const [e1_cp; e2_cp]) then
       bir_exp_eval_consts (BExp_BinExp et e1_cp e2_cp)
     else
       (BExp_BinExp et e1_cp e2_cp)
  )) /\

  (bir_exp_const_prop (BExp_BinPred pt e1 e2) = (
     let e1_cp = (bir_exp_const_prop e1);
         e2_cp = (bir_exp_const_prop e2); in
     if (EVERY bir_exp_is_const [e1_cp; e2_cp]) then
       bir_exp_eval_consts (BExp_BinPred pt e1_cp e2_cp)
     else
       (BExp_BinPred pt e1_cp e2_cp)
  )) /\

  (bir_exp_const_prop (BExp_MemEq e1 e2) = (
     let e1_cp = (bir_exp_const_prop e1);
         e2_cp = (bir_exp_const_prop e2); in
     if (EVERY bir_exp_is_const [e1_cp; e2_cp]) then
       bir_exp_eval_consts (BExp_MemEq e1_cp e2_cp)
     else
       (BExp_MemEq e1_cp e2_cp)
  )) /\

  (bir_exp_const_prop (BExp_IfThenElse c et ef) = (
     let c_cp  = (bir_exp_const_prop c);
         et_cp = (bir_exp_const_prop et);
         ef_cp = (bir_exp_const_prop ef); in
     if (EVERY bir_exp_is_const [c_cp; et_cp; ef_cp]) then
       bir_exp_eval_consts (BExp_IfThenElse c_cp et_cp ef_cp)
     else
       (BExp_IfThenElse c_cp et_cp ef_cp)
  )) /\

  (bir_exp_const_prop (BExp_Load mem_e a_e en ty) = (
     let mem_e_cp = (bir_exp_const_prop mem_e);
         a_e_cp   = (bir_exp_const_prop a_e); in
     if (EVERY bir_exp_is_const [mem_e_cp; a_e_cp]) then
       bir_exp_eval_consts (BExp_Load mem_e_cp a_e_cp en ty)
     else
       (BExp_Load mem_e_cp a_e_cp en ty)
  )) /\

  (bir_exp_const_prop (BExp_Store mem_e a_e en v_e) = (
     let mem_e_cp = (bir_exp_const_prop mem_e);
         a_e_cp   = (bir_exp_const_prop a_e);
         v_e_cp   = (bir_exp_const_prop v_e); in
     if (EVERY bir_exp_is_const [mem_e_cp; a_e_cp; v_e_cp]) then
       bir_exp_eval_consts (BExp_Store mem_e_cp a_e_cp en v_e_cp)
     else
       (BExp_Store mem_e_cp a_e_cp en v_e_cp)
  ))
`;

fun mk_bir_exp_const_prop t = ``bir_exp_const_prop ^t``;

(*
val t1 = ``
(BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 3w)))
``
val t2 = ``
(BExp_BinExp BIExp_Plus
             (BExp_Const (Imm64 19w))
             (BExp_Const (Imm64 3w)))
``
val t = ``
(BExp_BinExp BIExp_Plus
             ^t1
             ^t2)
``

(EVAL o mk_bir_exp_const_prop) t
*)

  open bir_exp_substitutionsSyntax;

in (* local *)


  fun eval_constprop t = (snd o dest_eq o concl o computeLib.RESTR_EVAL_CONV [``BType_Bool``] o mk_bir_exp_const_prop) t;

  val subst_exp = (eval_constprop o mk_bir_exp_subst1);

end (* local *)
end (* struct *)
