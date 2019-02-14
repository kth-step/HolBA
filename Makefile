-include Makefile.local
ifndef PYTHON # python 2.7.13 works
  PYTHON  = python
endif
ifndef HOLMAKE # we need a specific HOL version - see README.md
  HOLMAKE = Holmake
endif

SRCDIR     = $(CURDIR)/src

EXAMPLES   = $(SRCDIR)/tools/lifter/examples \
             $(SRCDIR)/tools/cfg/examples
BENCHMARKS = $(SRCDIR)/tools/lifter/benchmark

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,src/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)

main: $(HOLMAKEFILES)
	echo "\n\nExecute \"$(HOLMAKE)\" in \"$(SRCDIR)\".\n"
	cd $(SRCDIR) && $(HOLMAKE)

examples: main
	for dir in $(EXAMPLES); \
	do \
		echo "\n\nExecute \"$(HOLMAKE)\" in \"$$dir\".\n"; \
		cd $$dir && $(HOLMAKE); \
	done

benchmarks: main
	for dir in $(BENCHMARKS); \
	do \
		echo "\n\nExecute \"$(HOLMAKE)\" in \"$$dir\".\n"; \
		cd $$dir && $(HOLMAKE); \
	done

%Holmakefile: %Holmakefile.gen
	$(PYTHON) gen_Holmakefiles.py $<

cleanslate:
	git clean -f -d -x src

