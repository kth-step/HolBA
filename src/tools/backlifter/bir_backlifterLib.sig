signature bir_backlifterLib =
sig

  include Abbrev;

  val get_arm8_contract_sing : thm -> term -> term -> term ->
    thm -> thm list -> thm -> thm -> thm list -> thm -> thm -> thm;

  val get_riscv_contract_sing : thm -> term -> term -> term ->
    thm -> thm list -> thm -> thm -> thm list -> thm -> thm -> thm;

end
