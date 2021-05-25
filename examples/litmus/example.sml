open litmusInterfaceLib

val litmus = lift_herd_litmus "S.litmus"

val _ = save_litmus ("S.json", litmus)
