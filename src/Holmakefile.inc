
# automatic Holmake targets (all theories and non-"Script.sml" .sml files)
# automatic heap inclusion by name pattern
# ----------------------------------
SMLFILES       = $(subst *.sml,,  $(patsubst %Script.sml,%Theory.sml,$(wildcard *.sml)))
TARGETS        = $(patsubst %.sml,%.uo,$(SMLFILES))

HEAPINC        = $(subst *Theory,,$(patsubst %Script.sml,%Theory    ,$(wildcard *Script.sml))) \
                 $(subst *Syntax,,$(patsubst       %.sml,%          ,$(wildcard *Syntax.sml))) \
                 $(subst *Simps,, $(patsubst       %.sml,%          ,$(wildcard *Simps.sml ))) \
                 $(subst *Lib,,   $(patsubst       %.sml,%          ,$(wildcard *Lib.sml   ))) \
                 $(HEAPINC_EXTRA)


# general configs
# ----------------------------------
all: $(TARGETS) $(if $(NEWHOLHEAP),$(NEWHOLHEAP),)

INCLUDES       = $(DEPENDENCIES) $(if $(HOLHEAP),$(shell dirname $(HOLHEAP)),)

EXTRA_CLEANS   = $(if $(NEWHOLHEAP),$(NEWHOLHEAP) $(NEWHOLHEAP).o,) $(wildcard *.exe)

OPTIONS        = QUIT_ON_FAILURE

default: all

.PHONY: all default


# holheap part
# ----------------------------------
ifdef POLY

$(NEWHOLHEAP): $(TARGETS) $(HOLHEAP)
	$(protect $(HOLDIR)/bin/buildheap) $(if $(HOLHEAP),-b $(HOLHEAP),) -o $@ $(HEAPINC)

endif


