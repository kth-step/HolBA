#!/bin/bash
set -e

# get setup directory path
SCAMVEX_DIR=$(dirname "${BASH_SOURCE[0]}")
HOLBA_DIR=$(readlink -f "${SCAMVEX_DIR}/../../../..")

FORWARD_ARGS=${@:1}

"${HOLBA_DIR}/src/shared/holba_entry.sh" driver-test $FORWARD_ARGS

