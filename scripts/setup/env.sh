#!/usr/bin/env bash

# exit immediately if an error happens
set -e

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

export HOLBA_DIR=${SETUP_DIR}/../..
export HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")

# if opt_dir is not set, default to a local one in the HolBA directory itself
if [ -z "${HOLBA_OPT_DIR}" ]; then
  export HOLBA_OPT_DIR="${HOLBA_DIR}/opt"
fi

# make Holmake available
HOL4_DIR=${HOLBA_OPT_DIR}/hol_k12_holba
export HOLBA_HOLMAKE=${HOL4_DIR}/bin/Holmake


