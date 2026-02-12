signature bir_cv_basicLib =
sig
  include Abbrev;

  (* Output a theorem : bir_val = from_cv_val cv_val *)
  val bir_val_conv : conv;
  (* Output a theorem : bir_val_opt = from_cv_val_option cv_val *)
  val bir_val_option_conv : conv;
  (* Output a theorem : fmap = alist_to_fmap l *)
  val fmap_to_alist_conv : conv;
(* Convert any BExp_xxx to a theorem : bir_exp = from_cv_exp *)
  val bir_exp_conv : conv;



end
