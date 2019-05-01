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

EXAMPLES_BASE = $(SRCDIR)/libs/examples               \
                $(SRCDIR)/tools/cfg/examples          \
                $(SRCDIR)/tools/exec/examples         \
                $(SRCDIR)/tools/lifter/examples       \
                $(SRCDIR)/tools/wp/examples

EXAMPLES_ALL  = $(EXAMPLES_BASE)                      \
                $(SRCDIR)/examples

BENCHMARKS    = $(SRCDIR)/tools/lifter/benchmark      \
                $(SRCDIR)/tools/wp/benchmark

##########################################################

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,$(SRCDIR)/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)
HOLMAKEFILE_DIRS = $(patsubst %/,%,$(sort $(foreach file,$(HOLMAKEFILE_GENS),$(dir $(file)))))

SML_RUNS         = $(foreach sml,$(call rwildcard,$(SRCDIR)/,*.sml),$(sml)_run)

TEST_SMLS        = $(call rwildcard,$(SRCDIR)/,selftest.sml) $(call rwildcard,$(SRCDIR)/,test-*.sml)
TEST_EXES        = $(TEST_SMLS:.sml=.exe)
TEST_SML_RUNS    = $(TEST_SMLS:.sml=.sml_run)
TEST_DIRS        = $(patsubst %/,%,$(sort $(foreach sml,$(TEST_SMLS),$(dir $(sml)))))

##########################################################

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

##########################################################

%Holmakefile: %Holmakefile.gen $(SRCDIR)/Holmakefile.inc
	@./scripts/gen_Holmakefiles.py $<

Holmakefiles: $(HOLMAKEFILES)


$(HOLMAKEFILE_DIRS): Holmakefiles
	cd $@ && $(HOLBA_HOLMAKE)


%.exe: %.sml
	@/usr/bin/env HOLBA_HOLMAKE="$(HOLBA_HOLMAKE)" ./scripts/mk-exe.sh $(@:.exe=.sml)

# workaround: this only works for tests currently
# these dependencies enable multiple jobs
#   (because of this and static nature of Makefile dependencies,
#    this target has to be depndent on all test-directories for
#    Holmake to run before)
%.sml_run: main $(TEST_DIRS) %.exe
	@./scripts/run-test.sh $(@:.sml_run=.exe)


##########################################################

core: $(SRCDIR)/libs
main: $(SRCDIR)

examples-base: main $(EXAMPLES_BASE)
examples-all: main $(EXAMPLES_ALL)
benchmarks: main $(BENCHMARKS)


tests: $(TEST_EXES)
	@./scripts/run-tests.sh

# this target can be made with multiple jobs
_run_tests: $(TEST_SML_RUNS)


gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -fdX src

##########################################################

.PHONY: Holmakefiles
.PHONY: $(HOLMAKEFILE_DIRS)

# workaround: cannot be defined phony currently
#.PHONY: $(SML_RUNS)

.PHONY: core main gendoc cleanslate

.PHONY: tests _run_tests
.PHONY: examples-base examples-all
.PHONY: benchmarks

