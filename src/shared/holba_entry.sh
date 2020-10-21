#!/bin/bash
set -e

# get setup directory path
SHARED_DIR=$(dirname "${BASH_SOURCE[0]}")
HOLBA_DIR=$(readlink -f "${SHARED_DIR}/../..")

if [[ "$1" == "QUICK" ]]; then
  # we need at least 2 arguments
  if [[ "$#" -lt 2 ]]; then
    echo "ERROR: need the script name"
    exit 1
  fi

  QUICK_RUN=YES
  SCRIPT_NAME=${2}
  FORWARD_ARGS=${@:2}
else
  # we need at least 1 argument
  if [[ "$#" -lt 1 ]]; then
    echo "ERROR: need the script name"
    exit 1
  fi

  QUICK_RUN=NO
  SCRIPT_NAME=${1}
  FORWARD_ARGS=${@:1}
fi

if [[ "${QUICK_RUN}" == "NO" ]]; then
  make -C "${HOLBA_DIR}" "src"
fi

# source the overall environment script
set --
source "${HOLBA_DIR}/env.sh"

HEAPNAME=../HolBA-heap
BUILDHEAP=${HOLBA_HOL_DIR}/bin/buildheap

"${BUILDHEAP}" --gcthreads=1 --holstate="${HEAPNAME}" "${SCRIPT_NAME}" --extra="${FORWARD_ARGS}"

exit 0

