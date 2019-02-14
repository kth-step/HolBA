
# holheap part
# ----------------------------------
ifdef POLY

$(NEWHOLHEAP): $(TARGETS)
	$(protect $(HOLDIR)/bin/buildheap) $(if $(HOLHEAP),-b $(HOLHEAP),) -o $(NEWHOLHEAP) $(HEAPINC)

endif


# selftest-part
# ----------------------------------
ifdef SELFTEST_DEP

selftest.exe: selftest.uo
	$(HOLMOSMLC) -o $@ $<


endif


# remainder
# ----------------------------------
all: $(TARGETS) $(if $(NEWHOLHEAP),$(NEWHOLHEAP),) \
                $(if $(HAS_SELFTEST),selftest.exe,)

EXTRA_CLEANS = $(if $(NEWHOLHEAP),$(NEWHOLHEAP) $(NEWHOLHEAP).o,) \
               $(if $(HAS_SELFTEST),selftest.exe,)

OPTIONS = QUIT_ON_FAILURE

default: all

.PHONY: all default



