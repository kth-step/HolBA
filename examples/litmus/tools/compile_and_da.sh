#!/bin/bash
DIR=$(dirname "${BASH_SOURCE[0]}")
source $DIR/../../../config.env.sh

CROSS=${HOLBA_GCC_RISCV64_CROSS}
AS=${CROSS}as
OBJDUMP=${CROSS}objdump

AS_FLAGS=-march=rv64ima

TMP_S=$(mktemp /tmp/XXXXXX.s)
TMP_BIN=${TMP_S}.bin
TMP_DA=${TMP_S}.da

cat - > $TMP_S && \
	$AS $AS_FLAGS $TMP_S -o $TMP_BIN && \
	$OBJDUMP -d $TMP_BIN > $TMP_DA && \
	printf $TMP_DA
