-include Makefile.local
ifndef HOLBA_HOLMAKE # we need a specific HOL version - see README.md
  $(info -------- HOLBA_HOLMAKE not defined --------)
  ifndef HOLBA_OPT_DIR
    $(info -------- HOLBA_OPT_DIR not defined --------)
    HOLBA_HOLMAKE = Holmake
    ifeq ("$(shell which $(HOLBA_HOLMAKE))","")
      $(error HOLBA_HOLMAKE undefined, HOLBA_OPT_DIR undefined, Holmake not in PATH)
    endif
  else
    include scripts/setup/env.mk
  endif
endif
$(info "---- HOLBA_HOLMAKE=$(HOLBA_HOLMAKE) ----")


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

SML_RUNS         = $(foreach sml,$(call rwildcard,src/,*.sml),$(sml)_run)

TEST_SMLS        = $(call rwildcard,src/,selftest.sml) $(call rwildcard,src/,test-*.sml)
TEST_EXES        = $(TEST_SMLS:.sml=.exe)
TEST_SML_RUNS    = $(TEST_SMLS:.sml=.sml_run)
TEST_DIRS        = $(sort $(foreach sml,$(TEST_SMLS),$(dir $(sml))))

.DEFAULT_GOAL := all
all: show-rules
	@echo "Please use sub-rules to build HolBA."

show-rules:
	@echo "Available rules:\n\
     - Holmakefiles: generates \`Holmakefile\`s from \`Holmakefile.gen\` files.\n\
     - setup: creates a subdirectory opt and installs all dependencies there\n\
     - core: builds only src/core, src/theories and src/libs\n\
     - main: builds HolBA, but without the examples or documentation\n\
     - tests: builds HolBA and runs all the tests\n\
     - examples-base: builds HolBA and the examples for each tool\n\
     - examples-all: builds HolBA and all the examples (base + src/examples/)\n\
     - benchmarks: builds HolBA and all the benchmarks\n\
     - gendoc: generate the documentation\n\
     - cleanslate: removes all files that are .gignore-d under src/"

%Holmakefile: %Holmakefile.gen src/Holmakefile.inc
	@./scripts/gen_Holmakefiles.py $<

Holmakefiles: $(HOLMAKEFILES)

core: Holmakefiles
	cd $(SRCDIR)/libs && $(HOLBA_HOLMAKE)

main: Holmakefiles
	cd $(SRCDIR) && $(HOLBA_HOLMAKE)

tests: $(TEST_DIRS) $(TEST_EXES)
	@./scripts/run-tests.sh

$(TEST_DIRS):
	cd $@ && $(HOLBA_HOLMAKE)

_run_tests: $(TEST_SML_RUNS)

%.exe: %.sml
	@/usr/bin/env HOLBA_HOLMAKE="$(HOLBA_HOLMAKE)" ./scripts/mk-exe.sh $(@:.exe=.sml)

$(SML_RUNS): main
	@/usr/bin/env HOLBA_HOLMAKE="$(HOLBA_HOLMAKE)" ./scripts/run-test.sh $(@:.sml_run=.sml)

examples-base: main $(EXAMPLES_BASE)

examples-all: main $(EXAMPLES_ALL)

$(EXAMPLES_ALL):
	cd $@ && $(HOLBA_HOLMAKE)

benchmarks: main $(BENCHMARKS)

$(BENCHMARKS):
	cd $@ && $(HOLBA_HOLMAKE)

gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -fdX src

.PHONY: Holmakefiles
.PHONY: core main gendoc cleanslate
.PHONY: $(SML_RUNS)
.PHONY: tests _run_tests $(TEST_DIRS)
.PHONY: examples-base examples-all $(EXAMPLES_BASE) $(EXAMPLES_ALL)
.PHONY: benchmarks $(BENCHMARKS)

