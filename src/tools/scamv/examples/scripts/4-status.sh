#!/usr/bin/env bash

set -e

ID=$1
OPTIONS=$2

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# find the environment
source "${HOLBA_DIR}/env.sh"
echo "============================"

# in the logs directory, call the status script
cd "${HOLBA_EMBEXP_LOGS}"
./scripts/status.py -ri ${ID} ${OPTIONS}

