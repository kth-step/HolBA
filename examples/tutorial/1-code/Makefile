##########################################################
# cross compiler
##########################################################

HOLBA_DIR = ../../..
include $(HOLBA_DIR)/scripts/setup/autoenv_gcc.mk

ifndef HOLBA_GDB
  HOLBA_GDB             = $(HOLBA_GCC_ARM8_CROSS)gdb
endif

CROSS   =$(HOLBA_GCC_ARM8_CROSS)
GDB     =$(HOLBA_GDB)

$(shell mkdir -p bin)


##########################################################
# settings
##########################################################

ELF	  = bin/examples.elf
ELF_TEST = bin/test.elf
CFLAGS	= -ggdb3 -std=gnu99 -Wall -fno-builtin # -O1
#LDFLAGS = --gc-sections -nostartfiles -nostdlib

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))

##########################################################
# source definition
##########################################################

SOURCES_C     = $(call rwildcard, src/, *.c)
SOURCES_S     = $(call rwildcard, src/, *.S)
SOURCES       = $(SOURCES_C) $(SOURCES_S)

OBJECTS       = $(SOURCES_C:.c=.o) $(SOURCES_S:.S=.o)

OBJECT_DAS    = $(OBJECTS:.o=.da)

##########################################################
# compilation and linking
##########################################################

.DEFAULT_GOAL := all
all: $(OBJECT_DAS) $(ELF).da

##########################################################

%.o: %.S
	${CROSS}as -o $@ $<

%.o: %.c
	${CROSS}gcc -DBAREMETAL= ${CFLAGS} -c -o $@ -fno-stack-protector $<

##########################################################

$(ELF): ${OBJECTS}
	${CROSS}ld -o $@ $^

#$(ELF): $(SOURCES)
#	${CROSS}gcc -DBAREMETAL= ${CFLAGS} $(SOURCES) -o $@

##########################################################

TOUCH_SCRIPT_FILE=touch "../2-lift/examplesBinaryScript.sml"

$(ELF).da: $(ELF)
	${TOUCH_SCRIPT_FILE}
	${CROSS}objdump -d $< > $@
%.da: %.o
	${TOUCH_SCRIPT_FILE}
	${CROSS}objdump -d $< > $@

##########################################################

$(ELF_TEST): $(SOURCES_C)
	gcc $^ -o $@

test: $(ELF_TEST)
	./$(ELF_TEST)

##########################################################

clean:
	rm -f $(OBJECTS) $(OBJECT_DAS) $(ELF) $(ELF).da $(ELF_TEST)

##########################################################

.PHONY: test


