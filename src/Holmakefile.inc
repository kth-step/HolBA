
# general configs
# ----------------------------------
all: $(TARGETS) $(if $(NEWHOLHEAP),$(NEWHOLHEAP),) \
                $(if $(SELFTEST_DEP),selftest.exe,)

INCLUDES = $(DEPENDENCIES) $(if $(HOLHEAP),$(shell dirname $(HOLHEAP)),)

EXTRA_CLEANS = $(if $(NEWHOLHEAP),$(NEWHOLHEAP) $(NEWHOLHEAP).o,) \
               $(if $(SELFTEST_DEP),selftest.exe,)

OPTIONS = QUIT_ON_FAILURE

default: all

.PHONY: all default


# holheap part
# ----------------------------------
ifdef POLY

$(NEWHOLHEAP): $(TARGETS) $(HOLHEAP)
	$(protect $(HOLDIR)/bin/buildheap) $(if $(HOLHEAP),-b $(HOLHEAP),) -o $@ $(HEAPINC)

endif


# selftest part
# ----------------------------------
ifdef SELFTEST_DEP

selftest.exe: selftest.uo $(SELFTEST_DEP)
	$(HOLMOSMLC) -o $@ $<

endif

