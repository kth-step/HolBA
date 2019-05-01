#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

if [ -z "${HOLBA_DIR}" ]; then
  export HOLBA_DIR=${SETUP_DIR}/../..
  export HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")
fi

# if opt_dir is not set, 
#   depending on whether there is a parameter given to env.sh,
#     use the parameter or
#     default to a local one in the HolBA directory itself
if [ -z "${HOLBA_OPT_DIR}" ]; then
  if [ "$#" -ne 1 ]; then
    export HOLBA_OPT_DIR="${HOLBA_DIR}/opt"
    echo "defaulting to directory opt in HolBA"
  else
    export HOLBA_OPT_DIR=${OPT_DIR_PARAM}
  fi
fi
export HOLBA_OPT_DIR=$(readlink -f "${HOLBA_OPT_DIR}")

# make Holmake available
if [ -z "${HOLBA_HOLMAKE}" ]; then
  HOL4_DIR=${HOLBA_OPT_DIR}/hol_k12_holba
  export HOLBA_HOLMAKE=${HOL4_DIR}/bin/Holmake
fi


