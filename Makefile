-include Makefile.local
ifndef HOLMAKE # we need a specific HOL version - see README.md
  HOLMAKE = Holmake
endif

SRCDIR     = $(CURDIR)/src

EXAMPLES   = $(SRCDIR)/tools/lifter/examples \
             $(SRCDIR)/tools/cfg/examples    \
             $(SRCDIR)/tools/exec/examples   \
             $(SRCDIR)/tools/wp/examples

BENCHMARKS = $(SRCDIR)/tools/lifter/benchmark \
             $(SRCDIR)/tools/wp/benchmark

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,src/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)

all:
	@echo "Please use sub-rules to build HolBA (main, examples, benchmarks, gendoc,...)."

main: $(HOLMAKEFILES)
	cd $(SRCDIR) && $(HOLMAKE)

%Holmakefile: %Holmakefile.gen
	@./gen_Holmakefiles.py $<

examples: main $(EXAMPLES)

$(EXAMPLES):
	cd $@ && $(HOLMAKE)

benchmarks: main $(BENCHMARKS)

$(BENCHMARKS):
	cd $@ && $(HOLMAKE)

gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -f -d -x src

.PHONY: main gendoc cleanslate
.PHONY: examples $(EXAMPLES)
.PHONY: benchmarks $(BENCHMARKS)
