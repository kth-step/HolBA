
# fail if gcc variable is still undefined
ifndef HOLBA_GCC_RISCV64_CROSS
  $(info !!! ERROR)
  $(info !!! - HOLBA_GCC_RISCV64_CROSS undefined)
  $(info !!! - please install RISC-V gcc using the install scripts)
  $(info !!! - and re-run configure.sh)
  $(info )
  $(error see the message above)
endif
$(info !!! Using HOLBA_GCC_RISCV64_CROSS=$(HOLBA_GCC_RISCV64_CROSS))


