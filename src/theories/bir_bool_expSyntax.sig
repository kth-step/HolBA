signature bir_bool_expSyntax =
sig
    include Abbrev

    val bir_val_true_tm     : term
    val is_bir_val_true     : term -> bool
    val bir_val_false_tm    : term
    val is_bir_val_false    : term -> bool

    val bir_exp_true_tm     : term
    val is_bir_exp_true     : term -> bool
    val bir_exp_false_tm    : term
    val is_bir_exp_false    : term -> bool

    val bir_exp_or_tm       : term
    val mk_bir_exp_or       : term * term -> term
    val dest_bir_exp_or     : term -> term * term
    val is_bir_exp_or       : term -> bool
    val bir_exp_and_tm      : term
    val mk_bir_exp_and      : term * term -> term
    val dest_bir_exp_and    : term -> term * term
    val is_bir_exp_and      : term -> bool
    val bir_exp_not_tm      : term
    val mk_bir_exp_not      : term -> term
    val dest_bir_exp_not    : term -> term
    val is_bir_exp_not      : term -> bool
    val bir_exp_imp_tm      : term
    val mk_bir_exp_imp      : term * term -> term
    val dest_bir_exp_imp    : term -> term * term
    val is_bir_exp_imp      : term -> bool

end
