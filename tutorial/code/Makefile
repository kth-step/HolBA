# cross compiler
# ---------------------------------
-include Makefile.local
ifndef CROSS
  CROSS	= aarch64-linux-gnu-
endif
ifndef GDB
  GDB   = gdb-multiarch
endif


# settings
# ---------------------------------
NAME	= example-program.elf
CFLAGS	= -ggdb3 -std=gnu99 -Wall -fno-builtin -Iinc
LDFLAGS = --gc-sections -nostartfiles -nostdlib


rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))



# source definition
# ---------------------------------
SOURCES_C   = $(wildcard src/*.c) \
              $(wildcard src/*/*.c)

SOURCES_ASM = $(wildcard src/*.asm) \
              $(wildcard src/*/*.asm)

INCLUDE_FILES = $(call rwildcard, inc/, *.h)


OBJECTS     = $(SOURCES_C:.c=.o) $(SOURCES_ASM:.asm=.o)




# compilation and linking
# ---------------------------------
all: $(KERNEL)

%.o: %.asm ${INCLUDE_FILES}
	${CROSS}as -o $@ $<

%.o: %.c ${INCLUDE_FILES}
	${CROSS}gcc ${CFLAGS} -c -o $@ -fno-stack-protector $<

$(NAME): ${OBJECTS} entry/entry.o
	${CROSS}ld $(LDFLAGS) -o $@ -T linkerscript.ld $^

test.elf:
	gcc examples.c -o test.elf

clean:
	rm -f $(KERNEL) $(NAME) ${OBJECTS} entry/entry.o


