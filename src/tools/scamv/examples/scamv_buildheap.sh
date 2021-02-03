#!/bin/bash
set -e

# get setup directory path
SCAMVEX_DIR=$(dirname "${BASH_SOURCE[0]}")
HOLBA_DIR=$(readlink -f "${SCAMVEX_DIR}/../../../..")

if [[ "$1" == "QUICK" ]]; then
  QUICK_RUN=YES
  FORWARD_ARGS=${@:2}
else
  QUICK_RUN=NO
  FORWARD_ARGS=${@:1}
fi

if [[ "${QUICK_RUN}" == "NO" ]]; then
  make -C "${HOLBA_DIR}" "src/tools/scamv/examples"
fi

# source the overall environment script
set --
source "${HOLBA_DIR}/env.sh"
set -e

SCRIPT_NAME=driver-entry
HEAPNAME=../HolBATools_ScamV-heap
BUILDHEAP=${HOLBA_HOL_DIR}/bin/buildheap

"${BUILDHEAP}" --gcthreads=1 --holstate="${HEAPNAME}" driver-test.sml "${SCRIPT_NAME}" --extra="${FORWARD_ARGS}"

exit 0
