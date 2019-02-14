-include Makefile.local
ifndef PYTHON # python 2.7.13 works
  PYTHON  = python
endif
ifndef HOLMAKE
  HOLMAKE = Holmake
endif

SRCDIR  = src

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,src/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)

main: $(HOLMAKEFILES)
	echo "\n\nExecute \"$(HOLMAKE)\" in \"$(SRCDIR)\".\n"
	cd $(SRCDIR) && $(HOLMAKE)

%Holmakefile: %Holmakefile.gen
	$(PYTHON) gen_Holmakefiles.py $<

cleanslate:
	git clean -f -d -x .

