#!/usr/bin/env bash

set -e

EXPGENRUN_PREFIX_PARAM=$1
EXPGENRUN_ID_PARAM=$2

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# find the environment
source "${HOLBA_DIR}/env.sh"
echo "============================"

# find experiment generation run parameters
EXPGENRUN_FILE=${SCAMV_EXAMPLES_DIR}/expgenruns/${EXPGENRUN_ID_PARAM}.txt
if [[ ! -f "${EXPGENRUN_FILE}" ]]; then
  echo "experiment generation description file not found: ${EXPGENRUN_FILE}"
  exit 1
fi
export SCAMV_EXPGENRUN_PARAMS=$(head -n 1 "${EXPGENRUN_FILE}")
echo "Using scamv parameters: ${SCAMV_EXPGENRUN_PARAMS}"

# check that logs directory exists, and assume that it is in the right state
if [[ -z "${HOLBA_EMBEXP_LOGS}" ]]; then
  echo "logs repository not defined"
  exit 1
fi
if [[ ! -d "${HOLBA_EMBEXP_LOGS}" ]]; then
  echo "logs repository not found: ${HOLBA_EMBEXP_LOGS}"
  exit 1
fi

# TODO: push "${EXPGENRUN_PREFIX_PARAM}_${EXPGENRUN_ID_PARAM}" into the description for holbarun

# start experiment generation process
cd "${SCAMV_EXAMPLES_DIR}"
./scamv.sh ${SCAMV_EXPGENRUN_PARAMS}


