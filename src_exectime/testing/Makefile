CONFIGFILE = Makefile.config

# config
include ${CONFIGFILE}

# local settings
-include Makefile.local

# toolchain
include Makefile.toolchain


# common definitions
# ---------------------------------
OUTDIR  = output
NAME	= ${OUTDIR}/program.elf

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))


# file definitions
# ---------------------------------
ifeq ("$(PROGPLAT_BOARD)", "lpc11c24")
  CODE_DIRS_EXTRA = libs/CMSIS_CORE_LPC11xx
endif

CODE_DIRS     = all arch/$(PROGPLAT_ARCH) board/$(PROGPLAT_BOARD) ${CODE_DIRS_EXTRA}

SOURCES_C     = $(foreach d,$(CODE_DIRS),$(call rwildcard, $d/src/, *.c))
SOURCES_S     = $(foreach d,$(CODE_DIRS),$(call rwildcard, $d/src/, *.S))
INCLUDE_FILES = $(foreach d,$(CODE_DIRS),$(call rwildcard, $d/inc/, *.h)) all/inc/config_input.h

OBJECTS       = $(SOURCES_C:.c=.o) $(SOURCES_S:.S=.o)

BOARDCONFIG   = $(PROGPLAT_BOARD)
LINKERFILE    = board/$(PROGPLAT_BOARD)/$(BOARDCONFIG).ld


# compiler flags
# ---------------------------------
#OPTIMIZED_MODE = 1
ifeq ("$(OPTIMIZED_MODE)", "")
  OPTIMIZATION_FLAG = -O0
else
  OPTIMIZATION_FLAG = -O3
endif

LDFLAGS_PRE  = -Bstatic -nostartfiles -nostdlib

ifeq ("$(PROGPLAT_ARCH)", "arm8")
  CFLAGS_EXTRA  = -ggdb3
else ifeq ("$(PROGPLAT_BOARD)", "rpi2")
  CFLAGS_EXTRA  = -ggdb3 -mcpu=cortex-a7 -mfloat-abi=soft -mfpu=neon-vfpv4 -mlittle-endian -ffreestanding -fno-builtin
else ifeq ("$(PROGPLAT_ARCH)", "m0")
  SFLAGS_EXTRA  = -mcpu=cortex-m0 -mthumb
  CFLAGS_EXTRA  = -g3 -specs=nosys.specs -DUSE_OLD_STYLE_DATA_BSS_INIT -ffunction-sections -fdata-sections -mcpu=cortex-m0 -mthumb -fno-common -D__USE_CMSIS=CMSIS_CORE_LPC11xx
  LDFLAGS_POST  = -L$(ARMSYS) -L$(ARMLIB) -lgcc
else ifeq ("$(PROGPLAT_ARCH)", "rv32imac")
  SFLAGS_EXTRA  = -march=rv32imac -mabi=ilp32 -mno-relax
  CFLAGS_EXTRA  = -g3 -ffreestanding -march=rv32imac -mabi=ilp32 -mno-relax
  LDFLAGS_PRE  += -melf32lriscv
  LDFLAGS_POST  = -L$(RVSYS) -L$(RVLIB) -lgcc
endif

INCFLAGS     = $(foreach d,$(CODE_DIRS),-I$d/inc)
SFLAGS       = ${SFLAGS_EXTRA} ${INCFLAGS}
CFLAGS	     = -std=gnu99 -Wall -fno-builtin -fno-stack-protector ${INCFLAGS} ${OPTIMIZATION_FLAG} ${CFLAGS_EXTRA}

BENCHMARK_MODE = 1
ifeq ("$(BENCHMARK_MODE)", "")
  DEFINES_EXTRA  = 
else
  DEFINES_EXTRA  = -D__BENCHMARK_MODE
endif


# compilation and linking
# ---------------------------------
all: $(NAME)

all/inc/config_input.h: ${CONFIGFILE}
	./scripts/gen_config_input.py

%.o: %.S ${INCLUDE_FILES}
	${CROSS}cpp ${INCFLAGS} ${DEFINES_EXTRA} $< | ${CROSS}as ${SFLAGS} -o $@ -

%.o: %.c ${INCLUDE_FILES}
	${CROSS}gcc ${CFLAGS} ${DEFINES_EXTRA} -c -o $@ $<

$(NAME): ${OBJECTS} ${INCLUDE_FILES} $(LINKERFILE) Makefile
	mkdir -p ${OUTDIR}
	${CROSS}ld $(LDFLAGS_PRE) -o $@ -T $(LINKERFILE) ${OBJECTS} $(LDFLAGS_POST)
	${CROSS}objdump -t -h $@ > "$@.table"
	${CROSS}objdump -d    $@ > "$@.da"
	${CROSS}objdump -D    $@ > "$@.da.all"
	${CROSS}objdump -j.text -j.data -j.bss -d $@ > "$@.da.plus"
	${CROSS}objdump -j.text -j.data -j.bss -s $@ > "$@.mem"
#	${CROSS}objdump -j.reloadtext -t -h $@ > "$@.reloadtext.table"
#	${CROSS}objdump -j.reloadtext -d $@ > "$@.reloadtext.da"
#	${CROSS}objcopy --gap-fill=0xff -j.reloadtext -O binary $@ "$@.reloadtext"
#	${CROSS}objcopy -O ihex $@ "$@.ihex"

clean:
	rm -rf ${OUTDIR}
	rm -f $(call rwildcard, , *.o) all/inc/config_input.h


.PHONY: all clean


# running and debugging
include Makefile.run

