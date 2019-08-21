
# fail if gcc variable is still undefined
ifndef HOLBA_GCC_ARM8_CROSS
  $(info !!! ERROR)
  $(info !!! - HOLBA_GCC_ARM8_CROSS undefined)
  $(info !!! - please install arm8 gcc using the install scripts)
  $(info !!! - and re-run configure.sh)
  $(info )
  $(error see the message above)
endif
$(info !!! Using HOLBA_GCC_ARM8_CROSS=$(HOLBA_GCC_ARM8_CROSS))


