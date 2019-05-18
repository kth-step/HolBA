# check if HOLBA_HOLMAKE is defined, priority
ifndef HOLBA_HOLMAKE

  $(info !!! HOLBA_HOLMAKE not defined, trying HOLBA_OPT_DIR)
  # then check HOLBA_OPT_DIR
  ifdef HOLBA_OPT_DIR

    HOLBA_HOLMAKE = $(HOLBA_OPT_DIR)/hol_k12_holba/bin/Holmake

  else

    $(info !!! HOLBA_OPT_DIR not defined, trying HOLBA/opt)
    # then check if the defined HOLBA_DIR
    # (or alternatively the local HolBA) contains opt

    ifndef HOLBA_DIR
      HOLBA_DIR = $(CURDIR)
    endif

    ifneq ("$(wildcard $(HOLBA_DIR)/opt/.*)", "")

      HOLBA_HOLMAKE=$(CURDIR)/opt/hol_k12_holba/bin/Holmake

    else

      $(info !!! HOLBA/opt does not exist, trying PATH)
      # then we can only check the path
      HOLBA_HOLMAKE = Holmake

    endif

  endif

endif

# check whether HOLBA_HOLMAKE is usable
HOLBA_HOLMAKE_AVAILABLE =
ifeq ("$(shell which $(HOLBA_HOLMAKE))","")
  $(info !!! WARNING)
  $(info !!! - HOLBA_HOLMAKE undefined,)
  $(info !!! - nothing in HOLBA_OPT_DIR,)
  $(info !!! - nothing in HOLBA/opt, and)
  $(info !!! - Holmake not in PATH)
  $(info ---------------------------------)
  $(info -\|/- Holmake not available -\|/-)
  $(info ---------------------------------)
else
  $(info !!! Using HOLBA_HOLMAKE=$(HOLBA_HOLMAKE))
  HOLBA_HOLMAKE_AVAILABLE = 1
endif

$(info )


