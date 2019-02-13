PYTHON  = python
HOLMAKE = /opt/hol_snapshot3/bin/Holmake

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,src/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)

main: Holmakefiles
	echo "\n\nExecute \"Holmake\" in \"src\"."
	cd src && $(HOLMAKE)

Holmakefiles: $(HOLMAKEFILES)

%Holmakefile: %Holmakefile.gen
	$(PYTHON) gen_Holmakefiles.py $<

cleanslate:
	git clean -f -d -x .

