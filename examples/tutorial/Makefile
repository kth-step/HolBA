
MAKEFILE_DIRS=1-code 3-exec
HOLMAKEFILE_DIRS=2-lift 4-bir-to-arm 5-wp 6-smt 7-composition

##########################################################

.DEFAULT_GOAL := all
all:2-lift
#all:7-composition

##########################################################

$(MAKEFILE_DIRS):
	make --directory=$@

$(HOLMAKEFILE_DIRS):
	make --directory=../.. examples/tutorial/$@

##########################################################

cleantutorial:
	git clean -fdX .

reverttutorial:
	git clean -fd .
	git checkout HEAD -- .

##########################################################

.PHONY: $(MAKEFILE_DIRS) $(HOLMAKEFILE_DIRS)
.PHONY: cleantutorial reverttutorial


