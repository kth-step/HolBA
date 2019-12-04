#!/usr/bin/env bash

set -e

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# find the environment
source "${HOLBA_DIR}/env.sh"
echo "============================"

# update HOLBA
cd "${HOLBA_DIR}"
git pull
make main

# update EmbExp-Box
cd "${HOLBA_EMBEXP_DIR}/EmbExp-Box"
git pull


