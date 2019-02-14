
# general configs
# ----------------------------------
all: $(TARGETS) $(if $(NEWHOLHEAP),$(NEWHOLHEAP),) \
                $(if $(SELFTEST_DEP),selftest.exe,)

EXTRA_CLEANS = $(if $(NEWHOLHEAP),$(NEWHOLHEAP) $(NEWHOLHEAP).o,) \
               $(if $(SELFTEST_DEP),selftest.exe,)

OPTIONS = QUIT_ON_FAILURE

default: all

.PHONY: all default


# holheap part
# ----------------------------------
ifdef POLY

$(NEWHOLHEAP): $(TARGETS)
	$(protect $(HOLDIR)/bin/buildheap) $(if $(HOLHEAP),-b $(HOLHEAP),) -o $(NEWHOLHEAP) $(HEAPINC)

endif


# selftest part
# ----------------------------------
ifdef SELFTEST_DEP

selftest.exe: selftest.uo $(SELFTEST_DEP)
	$(HOLMOSMLC) -o $@ $<

endif

