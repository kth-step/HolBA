# select mem_mode
# 0 - main flash, 1 - system flash, 3 - sram
set {unsigned int}0x40010000 = 0


# write sp and pc
set $sp = {unsigned int}0x0
set $pc = {unsigned int}0x00000004

