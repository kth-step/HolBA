
# select isr table flash
set {unsigned int}0x40048000 = 2

# write sp and pc
set $sp = {unsigned int}0x0
set $pc = {unsigned int}0x4
#set $pc = (unsigned int)ResetISR

#p/x $sp

