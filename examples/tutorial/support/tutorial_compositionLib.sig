signature tutorial_compositionLib =
sig
   include Abbrev
   
   val get_contract_prog: thm -> term;
   val get_contract_l: thm -> term;
   val get_contract_ls: thm -> term;
   val get_contract_pre: thm -> term;
   val get_contract_post: thm -> term;

   
   val vars_ss: simpset;

   val use_impl_rule: thm->thm->thm;

end
