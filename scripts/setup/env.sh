#!/usr/bin/env bash

# exit immediately if an error happens
#   note: this has to be undone in the end of this script!
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

if [ -z "${HOLBA_DIR}" ]; then
  export HOLBA_DIR=${SETUP_DIR}/../..
  export HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")
fi


#####################################################
# core parameters
#####################################################


####### HOLBA_OPT_DIR

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


####### HOLBA_HOLMAKE

# make Holmake available
if [ -z "${HOLBA_HOLMAKE}" ]; then
  HOL4_DIR=${HOLBA_OPT_DIR}/hol_k12_holba
  export HOLBA_HOLMAKE=${HOL4_DIR}/bin/Holmake
fi



#####################################################
# additional parameters:
#   - either already defined or search in opt_dir
#####################################################


####### HOLBA_Z3_DIR

if [ -z "${HOLBA_Z3_DIR}" ]; then
  Z3_DIR=${HOLBA_OPT_DIR}/z3-4.8.4.d6df51951f4c
  if [ -d "${Z3_DIR}/bin/python" ]; then
    export HOLBA_Z3_DIR=${Z3_DIR}

    export PYTHONPATH=${HOLBA_Z3_DIR}/bin/python
    export LD_LIBRARY_PATH=${HOLBA_Z3_DIR}/bin:$LD_LIBRARY_PATH

    export HOL4_Z3_EXECUTABLE=${HOLBA_Z3_DIR}/bin/z3
    export HOL4_Z3_WRAPPED_EXECUTABLE=${HOLBA_DIR}/src/shared/z3_wrapper.py
  fi
fi


####### HOLBA_EMBEXP_DIR

if [ -z "${HOLBA_EMBEXP_DIR}" ]; then
  EMBEXP_DIR=${HOLBA_OPT_DIR}/embexp
  if [ -d "${EMBEXP_DIR}/EmbExp-ProgPlatform" ]; then
    export HOLBA_EMBEXP_DIR=${EMBEXP_DIR}
  fi
fi



####### HOLBA_GCC_ARM8_CROSS

if [ -z "${HOLBA_GCC_ARM8_CROSS}" ]; then
  CROSS="${HOLBA_OPT_DIR}/gcc-arm8-8.2-2018.08-aarch64-elf/bin/aarch64-elf-"
  if [ -f "${CROSS}gcc" ]; then
    export HOLBA_GCC_ARM8_CROSS=${CROSS}
  fi
fi



####### HOLBA_SCAMV_LOGS

if [ -z "${HOLBA_SCAMV_LOGS}" ]; then
  LOGS_DIR=${HOLBA_DIR}/logs
  if [ -d "${LOGS_DIR}" ]; then
    mkdir "${LOGS_DIR}"
  fi
  export HOLBA_SCAMV_LOGS=${LOGS_DIR}
fi


# enable sourcing of this script without weird behavior
set +e


