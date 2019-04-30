#!/usr/bin/env bash

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the opt_dir
if [ -z "${HOLBA_OPT_DIR}" ]; then
  if [ "$#" -ne 1 ]; then
    export HOLBA_OPT_DIR="${SETUP_DIR}/../../opt"
    echo "defaulting to directory opt in HolBA"
  else
    export HOLBA_OPT_DIR=${OPT_DIR_PARAM}
  fi
fi
export HOLBA_OPT_DIR=$(readlink -f "${HOLBA_OPT_DIR}")

echo "-----------------------------------------------"
echo "-- using HOLBA_OPT_DIR=${HOLBA_OPT_DIR}"
echo "-----------------------------------------------"

# install poly
"${SETUP_DIR}/install_poly.sh"

# install hol4
"${SETUP_DIR}/install_hol4.sh"

# place Makefile.local to set Holmake
. "${SETUP_DIR}/env.sh"
echo "HOLBA_HOLMAKE=${HOLBA_HOLMAKE}" > Makefile.local

