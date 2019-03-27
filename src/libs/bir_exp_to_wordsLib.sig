signature bir_exp_to_wordsLib =
sig

    include Abbrev

    val w2bool: term -> term
    val bool2w: term -> term
    val bir2w: term -> term
    val bir2bool: term -> term

end
