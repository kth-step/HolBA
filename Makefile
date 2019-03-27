-include Makefile.local
ifndef HOLMAKE # we need a specific HOL version - see README.md
  HOLMAKE = Holmake
endif

SRCDIR     = $(CURDIR)/src

EXAMPLES_BASE = $(SRCDIR)/libs/examples               \
                $(SRCDIR)/tools/cfg/examples          \
                $(SRCDIR)/tools/exec/examples         \
                $(SRCDIR)/tools/lifter/examples       \
                $(SRCDIR)/tools/wp/examples

EXAMPLES_ALL = $(EXAMPLES_BASE)                       \
               $(SRCDIR)/examples

BENCHMARKS = $(SRCDIR)/tools/lifter/benchmark         \
             $(SRCDIR)/tools/wp/benchmark

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,src/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)

.DEFAULT_GOAL := all
all:
	@echo "Please use sub-rules to build HolBA:\n\
     - core: builds only src/core, src/theories and src/libs\n\
     - main: builds HolBA, but without the examples or documentation\n\
     - examples-base: builds HolBA and the examples for each tool\n\
     - examples-all: builds HolBA and all the examples (base + src/examples/)\n\
     - benchmarks: builds HolBA and all the benchmarks\n\
     - gendoc: generate the documentation\n\
     - cleanslate: removes all files that are .gignore-d under src/"

%Holmakefile: %Holmakefile.gen src/Holmakefile.inc
	@./gen_Holmakefiles.py $<

Holmakefiles: $(HOLMAKEFILES)

main: Holmakefiles
	cd $(SRCDIR) && $(HOLMAKE)

core: $(HOLMAKEFILES)
	cd $(SRCDIR)/libs && $(HOLMAKE)

examples-base: main $(EXAMPLES_BASE)

examples-all: main $(EXAMPLES_ALL)

$(EXAMPLES_ALL):
	cd $@ && $(HOLMAKE)

benchmarks: main $(BENCHMARKS)

$(BENCHMARKS):
	cd $@ && $(HOLMAKE)

gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -fdX src

.PHONY: Holmakefiles
.PHONY: main gendoc cleanslate
.PHONY: examples-base examples-all $(EXAMPLES_BASE) $(EXAMPLES_ALL)
.PHONY: benchmarks $(BENCHMARKS)
