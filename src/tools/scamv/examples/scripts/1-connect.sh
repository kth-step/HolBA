#!/usr/bin/env bash

set -e

EMBEXP_BOARD_PARAM=$1

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# check inputs
if [[ -z "${EMBEXP_BOARD_PARAM}" ]]; then
  echo "ERROR: please provide board type as parameter (e.g. rpi3)"
  exit 1
fi

# find environment
source "${HOLBA_DIR}/env.sh"
echo "============================"

EMBEXP_INSTANCE_IDX_PARAM=
if [[ ! -z "${EMBEXP_INSTANCE_IDX}" ]]; then
  EMBEXP_INSTANCE_IDX_PARAM="-idx ${EMBEXP_INSTANCE_IDX}"
fi
${HOLBA_EMBEXP_DIR}/EmbExp-Box/interface/remote.py ${EMBEXP_BOARD_PARAM} ${EMBEXP_INSTANCE_IDX_PARAM}


