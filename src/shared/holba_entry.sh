#!/bin/bash
set -e

# get setup directory path
SHARED_DIR=$(dirname "${BASH_SOURCE[0]}")
HOLBA_DIR=$(readlink -f "${SHARED_DIR}/../..")

CURRENT_DIR=$(pwd)

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
  MAKETARGET=$(python3 -c "import os.path; print(os.path.relpath('${CURRENT_DIR}', '${HOLBA_DIR}'))")
  make -C "${HOLBA_DIR}" main
  make -C "${HOLBA_DIR}" "${MAKETARGET}"
fi

# source the overall environment script
set --
source "${HOLBA_DIR}/env.sh"

# TODO: would need to find heap that corresponds to current dir, quickfix: make main a few
#       lines up and require that the current dir heap is subsumed in the one defined here
HEAPNAME=${HOLBA_DIR}/src/HolBA-heap
BUILDHEAP=${HOLBA_HOL_DIR}/bin/buildheap

echo
#"${BUILDHEAP}" --gcthreads=1 --holstate="${HEAPNAME}" "${SCRIPT_NAME}" --extra="${FORWARD_ARGS}"
echo "Building executable now."
"${BUILDHEAP}" --holstate="${HEAPNAME}" "${SCRIPT_NAME}" -o main_holba.exe --exe main_holba --extra="${FORWARD_ARGS}"
echo "Done building executable."
./main_holba.exe --extra="${FORWARD_ARGS}"

exit 0

