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

##########################################################

HOLBA_DIR     = $(CURDIR)
SRCDIR        = src
EXAMPLESDIR   = examples

EXAMPLES_BASE = $(SRCDIR)/shared/examples             \
                $(SRCDIR)/tools/cfg/examples          \
                $(SRCDIR)/tools/exec/examples         \
                $(SRCDIR)/tools/lifter/examples       \
                $(SRCDIR)/tools/wp/examples

EXAMPLES_ALL  = $(EXAMPLES_BASE)                      \
                $(EXAMPLESDIR)

BENCHMARKS    = $(SRCDIR)/tools/lifter/benchmark      \
                $(SRCDIR)/tools/wp/benchmark

##########################################################

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,$(SRCDIR)/,Holmakefile.gen) \
                   $(call rwildcard,$(EXAMPLESDIR)/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)
HOLMAKEFILE_DIRS = $(patsubst %/,%,$(sort $(foreach file,$(HOLMAKEFILE_GENS),$(dir $(file)))))

SML_RUNS         = $(foreach sml,$(call rwildcard,$(SRCDIR)/,*.sml),$(sml)_run)
SML_RUNQS        = $(foreach sml,$(call rwildcard,$(SRCDIR)/,*.sml),$(sml)_runq)

TEST_SMLS        = $(call rwildcard,$(SRCDIR)/,selftest.sml) $(call rwildcard,$(SRCDIR)/,test-*.sml)
TEST_EXES        = $(TEST_SMLS:.sml=.exe)
TEST_SML_RUNQS   = $(TEST_SMLS:.sml=.sml_runq)
TEST_DIRS        = $(patsubst %/,%,$(sort $(foreach sml,$(TEST_SMLS),$(dir $(sml)))))

##########################################################

.DEFAULT_GOAL := all
all: show-rules
	@echo "Please use sub-rules to build HolBA."

show-rules:
	@echo "Available rules:\n\
     - Holmakefiles: generates \`Holmakefile\`s from \`Holmakefile.gen\` files.\n\
     - theory: builds only src/theory\n\
     - main: builds HolBA, but without the examples or documentation\n\
     - tests: builds HolBA and runs all the tests\n\
     - examples-base: builds HolBA and the examples for each tool\n\
     - examples-all: builds HolBA and all the examples (base + HOLBA/examples/)\n\
     - benchmarks: builds HolBA and all the benchmarks\n\
     - gendoc: generate the documentation\n\
     - cleanslate: removes all files that are .gignore-d under src/"

##########################################################

%Holmakefile: %Holmakefile.gen $(SRCDIR)/Holmakefile.inc
	@./scripts/gen_Holmakefiles.py $<

Holmakefiles: $(HOLMAKEFILES)


$(HOLMAKEFILE_DIRS): Holmakefiles
	cd $@ && $(HOLBA_HOLMAKE)


%.exe: %.sml
	@/usr/bin/env HOLBA_HOLMAKE="$(HOLBA_HOLMAKE)" ./scripts/mk-exe.sh $(@:.exe=.sml)

# this is a target for all sml files to run as scripts,
# it properly prepares first
$(SML_RUNS):
	@make $(@:.sml_run=.exe)
	@make $(patsubst %/,%,$(dir $@))
	@./scripts/run-test.sh $(@:.sml_run=.exe)

# this target is for quick running (no preparation,
# for tests where preparation is done before)
%.sml_runq:
	@./scripts/run-test.sh $(@:.sml_runq=.exe)

##########################################################

theory: $(SRCDIR)/theory
main: $(SRCDIR)

examples-base: main $(EXAMPLES_BASE)
examples-all: main $(EXAMPLES_ALL)
benchmarks: main $(BENCHMARKS)


tests: $(TEST_EXES) $(TEST_DIRS)
	@./scripts/run-tests.sh

# this target can be made with multiple jobs, the others cannot!
_run_tests: $(TEST_SML_RUNQS)


gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -fdX src

##########################################################

.PHONY: Holmakefiles
.PHONY: $(HOLMAKEFILE_DIRS)

.PHONY: $(SML_RUNS)
# note: SML_RUNQS cannot be defined phony,
# because it uses suffix rules apparently
#.PHONY: $(SML_RUNQS) 

.PHONY: core main gendoc cleanslate

.PHONY: tests _run_tests
.PHONY: examples-base examples-all
.PHONY: benchmarks

