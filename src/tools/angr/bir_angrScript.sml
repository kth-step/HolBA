open HolKernel Parse boolLib bossLib;

val _ = new_theory "bir_angr";

  val _ = if type_of “BirMask” = Type‘:bir_exp_t -> num -> num -> bir_exp_t’
          then ()
          else new_constant ("BirMask",Type‘:bir_exp_t -> num -> num -> bir_exp_t’);
  val _ = if type_of “BirAppendMask” = Type‘:(bir_exp_t # num # num) list -> bir_exp_t’
          then ()
          else new_constant ("BirAppendMask",Type‘:(bir_exp_t # num # num) list -> bir_exp_t’);
  
  val BirMask_type_of = store_thm ("BirMask_type_of",
 ``!e u l. type_of_bir_exp (BirMask e u l) =
    type_of_bir_exp e``,
                    cheat);
 val BirAppendMask_type_of = store_thm ("BirAppendMask_type_of",
 ``!es. type_of_bir_exp (BirAppendMask es) =
 if LENGTH es > 0
 then case bir_immtype_of_size (FOLDR $+ (0:num) (MAP (\ (_,u,l). u-l+1) es)) of
          NONE => NONE
         | SOME ty => SOME (BType_Imm ty)
 else NONE``,
        cheat);

val _ = export_theory();
