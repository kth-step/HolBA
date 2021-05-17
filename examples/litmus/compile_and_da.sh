#!/bin/bash

source ../../config.env.sh
AS=${HOLBA_GCC_RISCV64_CROSS}as
OBJDUMP=${HOLBA_GCC_RISCV64_CROSS}objdump

TMP_S=$(mktemp /tmp/XXXXXX.s)
TMP_BIN=${TMP_S}.bin
TMP_DA=${TMP_S}.da
cat - > $TMP_S && \
	$AS $TMP_S -o $TMP_BIN && \
	$OBJDUMP -d $TMP_BIN > $TMP_DA && \
	printf $TMP_DA
