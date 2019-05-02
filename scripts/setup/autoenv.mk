ifndef HOLBA_HOLMAKE

  $(info !!! HOLBA_HOLMAKE not defined, trying HOLBA_OPT_DIR)
  ifdef HOLBA_OPT_DIR

    HOLBA_HOLMAKE = $(HOLBA_OPT_DIR)/hol_k12_holba/bin/Holmake

  else

    $(info !!! HOLBA_OPT_DIR not defined, trying PATH)
    HOLBA_HOLMAKE = Holmake

  endif

endif

HOLBA_HOLMAKE_AVAILABLE =
ifeq ("$(shell which $(HOLBA_HOLMAKE))","")
  $(info !!! HOLBA_HOLMAKE undefined, HOLBA_OPT_DIR undefined, Holmake not in PATH)
  $(info ---------------------------------)
  $(info -\|/- Holmake not available -\|/-)
  $(info ---------------------------------)
else
  $(info !!! Using HOLBA_HOLMAKE=$(HOLBA_HOLMAKE))
  HOLBA_HOLMAKE_AVAILABLE = 1
endif

$(info )


