# For compilation and disassembling
HOLBA_DIR = ../..
include $(HOLBA_DIR)/scripts/setup/env_check_gcc_arm8.mk
CROSS =$(HOLBA_GCC_ARM8_CROSS)
CFLAGS_BAREMETAL = -Iinc -ggdb3 -std=gnu99 -Wall -fno-builtin # -O1

.DEFAULT_GOAL := all
all:
	# Count
	wc -l resolveFullyLib.sml
	wc -l resolveFullyScript.sml resolveScript.sml resolutionScript.sml simulationScript.sml simulationFailScript.sml contractTransferScript.sml
	# Run
	make --directory=../.. examples/ijr/evaluation.sml_run
	# Plot
	python3 plot.py
	# Compile and disassemble c evaluation program
	${CROSS}gcc -DBAREMETAL= ${CFLAGS_BAREMETAL} -c -o composition.o -fno-stack-protector composition.c
	${CROSS}objdump -d composition.o > composition.da