
# reedundant, HOLBA_HOL_DIR would always be defined here
ifdef HOLBA_HOL_DIR
  HOLBA_HOLMAKE=$(HOLBA_HOL_DIR)/bin/Holmake
else
  $(info !!! WARNING)
  $(info !!! - HOLBA_HOL_DIR undefined)
endif


# check whether HOLBA_HOLMAKE is usable
ifeq ("$(shell which $(HOLBA_HOLMAKE))","")
  $(info !!! WARNING)
  ifndef HOLBA_HOLMAKE
    $(info !!! - HOLBA_HOLMAKE undefined)
  else
    $(info !!! - "$(HOLBA_HOLMAKE)" does not exist)
  endif
  $(info ---------------------------------)
  $(info -\|/- Holmake not available -\|/-)
  $(info ---------------------------------)
  HOLBA_HOLMAKE=
else
  $(info !!! Using HOLBA_HOLMAKE=$(HOLBA_HOLMAKE))
endif

$(info )

