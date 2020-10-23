signature bir_lifting_machinesLib_instances =
sig
   (* This library provides instances for various architectures of
      the machine record defined in bir_lifting_machinesLib. *)

   (* The record for arm8 *)
   val arm8_bmr_rec : bir_lifting_machinesLib.bmr_rec;

   (* Records for m0, parameters are endianness and whether to use
      process and main SP. The 4 possible instances are also precomputed. *)
   val m0_bmr_rec : bool -> bool -> bir_lifting_machinesLib.bmr_rec;

   val m0_bmr_rec_LittleEnd_Main    : bir_lifting_machinesLib.bmr_rec;
   val m0_bmr_rec_BigEnd_Main       : bir_lifting_machinesLib.bmr_rec;
   val m0_bmr_rec_LittleEnd_Process : bir_lifting_machinesLib.bmr_rec;
   val m0_bmr_rec_BigEnd_Process    : bir_lifting_machinesLib.bmr_rec;

   (* repeated for the modified m0 version: m0_mod *)
   val m0_mod_bmr_rec : bool -> bool -> bir_lifting_machinesLib.bmr_rec;

   val m0_mod_bmr_rec_LittleEnd_Main    : bir_lifting_machinesLib.bmr_rec;
   val m0_mod_bmr_rec_BigEnd_Main       : bir_lifting_machinesLib.bmr_rec;
   val m0_mod_bmr_rec_LittleEnd_Process : bir_lifting_machinesLib.bmr_rec;
   val m0_mod_bmr_rec_BigEnd_Process    : bir_lifting_machinesLib.bmr_rec;

   (* The machine record for RISC-V *)
   val riscv_bmr_rec                    : bir_lifting_machinesLib.bmr_rec;

end
