
# CC=
CC=/home/andreas/Downloads/lifter/binary_blobs_for_analysis/compilers/arm/gcc-arm-none-eabi-7-2018-q2-update/bin/arm-none-eabi

CFLAGS=-Wall -Winline -mthumb -mcpu=cortex-m0 -O0 -g

main:
	${CC}-gcc ${CFLAGS} -o a.out toy.c --specs=nosys.specs
	${CC}-objdump -d a.out > m0-toy.da
