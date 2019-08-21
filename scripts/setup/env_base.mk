# we need to have a HOLBA_DIR, provide it like a parameter
ifndef HOLBA_DIR
  $(info !!! ERROR)
  $(info !!! - HOLBA_DIR undefined, cannot find config.env.sh)
  $(info )
  $(error see the message above)
endif


# include HOLBA_CONFIG_ENV if it can be found
HOLBA_CONFIG_ENV = $(HOLBA_DIR)/config.env.sh
ifeq ("$(wildcard $(HOLBA_CONFIG_ENV))", "")
  $(info !!! WARNING)
  $(info !!! - "$(HOLBA_CONFIG_ENV)" does not exist)
  $(info !!! - please run "./configure.sh")
else
  $(info !!! including "$(HOLBA_CONFIG_ENV)")
  include $(HOLBA_CONFIG_ENV)
endif

$(info )


