signature bir_exp_liftingSyntax =
sig
  include Abbrev

  val mk_bir_lift_val_t : hol_type * hol_type -> hol_type
  val dest_bir_lift_val_t : hol_type -> hol_type * hol_type
  val is_bir_lift_val_t : hol_type -> bool

  val bir_is_lifted_exp_tm : term
  val dest_bir_is_lifted_exp : term -> term * term * term
  val is_bir_is_lifted_exp : term -> bool
  val mk_bir_is_lifted_exp : term * term * term -> term

  val BLV_Imm_tm : term
  val dest_BLV_Imm : term -> term
  val is_BLV_Imm : term -> bool
  val mk_BLV_Imm : term -> term

  val BLV_Mem_tm : term
  val dest_BLV_Mem : term -> term
  val is_BLV_Mem : term -> bool
  val mk_BLV_Mem : term -> term

  val gen_mk_BLV : term -> term

end
