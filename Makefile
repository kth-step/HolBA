HOLBA_DIR = .
include $(HOLBA_DIR)/scripts/setup/env_base.mk
include $(HOLBA_DIR)/scripts/setup/env_check_hol4.mk



# set make's shell to bash
SHELL := /bin/bash

##########################################################

SRCDIR        = src
EXSDIR        = examples

EXAMPLES_BASE = $(SRCDIR)/shared/examples             \
                $(SRCDIR)/tools/cfg/examples          \
                $(SRCDIR)/tools/exec/examples         \
                $(SRCDIR)/tools/lifter/examples       \
                $(SRCDIR)/tools/wp/examples

EXAMPLES_ALL  = $(EXAMPLES_BASE)                      \
                $(EXSDIR)

BENCHMARKS    = $(SRCDIR)/tools/lifter/benchmark      \
                $(SRCDIR)/tools/wp/benchmark

##########################################################

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,$(SRCDIR)/,Holmakefile.gen) \
                   $(call rwildcard,$(EXSDIR)/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)


ifdef HOLBA_HOLMAKE
HOLMAKEFILE_DIRS = $(patsubst %/,%,$(sort $(foreach file,$(HOLMAKEFILE_GENS),$(dir $(file)))))

SML_RUNS         = $(foreach sml,$(call rwildcard,$(SRCDIR)/,*.sml),$(sml)_run) \
                   $(foreach sml,$(call rwildcard,$(EXSDIR)/,*.sml),$(sml)_run)

TEST_SMLS        = $(call rwildcard,$(SRCDIR)/,selftest.sml) $(call rwildcard,$(SRCDIR)/,selftest_*.sml) $(call rwildcard,$(SRCDIR)/,test-*.sml) \
                   $(call rwildcard,$(EXSDIR)/,selftest.sml) $(call rwildcard,$(EXSDIR)/,selftest_*.sml) $(call rwildcard,$(EXSDIR)/,test-*.sml)
TEST_EXES        = $(TEST_SMLS:.sml=.exe)
TEST_SML_RUNQS   = $(TEST_SMLS:.sml=.sml_runq)
TEST_DIRS        = $(patsubst %/,%,$(sort $(foreach sml,$(TEST_SMLS),$(dir $(sml)))))
endif

##########################################################

.DEFAULT_GOAL := all
all: show-rules
	@echo 'Please use sub-rules to build HolBA.'

show-rules:
	@echo 'Available rules:'
	@echo '     - Holmakefiles: generates `Holmakefile`s from `Holmakefile.gen` files.'
ifdef HOLBA_HOLMAKE
	@echo '     - theory: builds only src/theory/'
	@echo '     - main: builds HolBA, but without the examples or documentation'
	@echo '     - tests: builds HolBA and runs all the tests'
	@echo '     - examples-base: builds HolBA and the examples for each tool'
	@echo '     - examples-all: builds HolBA and all the examples (base + HolBA/examples/)'
	@echo '     - benchmarks: builds HolBA and all the benchmarks'
endif
	@echo '     - gendoc: generate the documentation'
	@echo '     - cleanslate: removes all files that are .gitignore-d under src/ and examples/'

##########################################################

%Holmakefile: %Holmakefile.gen $(SRCDIR)/Holmakefile.inc
	@./scripts/gen_Holmakefiles.py $<

Holmakefiles: $(HOLMAKEFILES)


$(HOLMAKEFILE_DIRS): Holmakefiles
	source ./scripts/setup/env_derive.sh && cd $@ && $(HOLBA_HOLMAKE) $(HOLBA_HOLMAKE_OPTS)


%.exe: %.sml Holmakefiles
	@/usr/bin/env HOLBA_HOLMAKE="$(HOLBA_HOLMAKE)" ./scripts/mk-exe.sh $(@:.exe=.sml)

# this is a target for all sml files to run as scripts,
# it properly prepares first
# it also tries to find the undefined environment variables
$(SML_RUNS):
	@make $(patsubst %/,%,$(dir $@))
	@make $(@:.sml_run=.exe)
	@source ./scripts/setup/env_derive.sh && ./scripts/run-test.sh $(@:.sml_run=.exe)

# this target is for quick running, mainly for the run-tests.sh
# (no environment preparation, it assumes that all
#  TEST_DIRS are "made" and env.sh has been sourced)
%.sml_runq:
	@./scripts/run-test.sh $(@:.sml_runq=.exe)

##########################################################

ifdef HOLBA_HOLMAKE
theory:        $(SRCDIR)/theory
main:          $(SRCDIR)

examples-base: main $(EXAMPLES_BASE)
examples-all:  main $(EXAMPLES_ALL)
benchmarks:    main $(BENCHMARKS)
riscv:         main src/tools/symbexec/examples/riscv


tests: $(TEST_EXES) $(TEST_DIRS)
	@source ./scripts/setup/env_derive.sh && ./scripts/run-tests.sh

# this target can be made with multiple jobs, the others cannot!
_run_tests: $(TEST_SML_RUNQS)
endif


gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -fdX src
	git clean -fdX examples

##########################################################

.PHONY: Holmakefiles

ifdef HOLBA_HOLMAKE
.PHONY: $(HOLMAKEFILE_DIRS)
.PHONY: $(SML_RUNS)

.PHONY: theory main
.PHONY: tests _run_tests
.PHONY: examples-base examples-all
.PHONY: benchmarks
endif

.PHONY: gendoc cleanslate
