# For compilation and disassembling
HOLBA_DIR = ../..
include $(HOLBA_DIR)/scripts/setup/env_check_gcc_arm8.mk
CROSS =$(HOLBA_GCC_ARM8_CROSS)
CFLAGS_BAREMETAL = -Iinc -ggdb3 -std=gnu99 -Wall -fno-builtin # -O1

.DEFAULT_GOAL := all
all: build evalc evalbir

build:
	# Count lines for proof-producing procedures and verified function
	wc -l resolveFullyLib.sml
	wc -l resolveFullyScript.sml resolveScript.sml resolutionScript.sml simulationScript.sml simulationFailScript.sml contractTransferScript.sml
	wc -l cProgEvaluation.sml
	wc -l generationLib.sml evaluation.sml
	wc -l examplesScript.sml
	# Compile, link and disassemble C evaluation program
	${CROSS}gcc -DBAREMETAL= ${CFLAGS_BAREMETAL} -c -o composition.o -fno-stack-protector composition.c
	${CROSS}ld -o composition.ld composition.o
	${CROSS}objdump -d composition.ld > composition.da

evalc:
	# Run C program evaluation
	make --directory=../.. examples/ijr/cProgEvaluation.sml_run

evalbir:
	# Run synthetic evaluation
	make --directory=../.. examples/ijr/evaluation.sml_run
	# Plot
	python3 plot.py
