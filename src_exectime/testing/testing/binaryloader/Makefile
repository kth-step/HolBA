# toolchain
PROGPLAT_ARCH = arm8
include ../../Makefile.toolchain


# common definitions
# ---------------------------------
OUTDIR  = output
NAME	= ${OUTDIR}/program.elf

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))


# file definitions
# ---------------------------------
SOURCES_C     = $(call rwildcard, src/, *.c)
SOURCES_S     = $(call rwildcard, src/, *.S)
INCLUDE_FILES = $(call rwildcard, inc/, *.h)

OBJECTS       = $(SOURCES_C:.c=.o) $(SOURCES_S:.S=.o)

LINKERFILE    = rpi3.ld


# compiler flags
# ---------------------------------
LDFLAGS_PRE  = -Bstatic -nostartfiles -nostdlib

CFLAGS_EXTRA  = -ggdb3

INCFLAGS     = -Iinc
SFLAGS       = ${SFLAGS_EXTRA} ${INCFLAGS}
CFLAGS	     = -std=gnu99 -Wall -fno-builtin -fno-stack-protector ${INCFLAGS} ${CFLAGS_EXTRA}



# compilation and linking
# ---------------------------------
all: $(NAME)

%.o: %.S ${INCLUDE_FILES}
	${CROSS}cpp ${INCFLAGS} $< | ${CROSS}as ${SFLAGS} -o $@ -

%.o: %.c ${INCLUDE_FILES}
	${CROSS}gcc ${CFLAGS} -c -o $@ $<

$(NAME): ${OBJECTS} ${INCLUDE_FILES}
	mkdir -p ${OUTDIR}
	${CROSS}ld $(LDFLAGS_PRE) -o $@ -T $(LINKERFILE) ${OBJECTS} $(LDFLAGS_POST)
	${CROSS}objdump -t -h -D $@ > "$@_da"

clean:
	rm -rf ${OUTDIR}
	rm -f $(call rwildcard, , *.o)


.PHONY: all clean


