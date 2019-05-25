#!/usr/bin/env bash

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]:-${(%):-%x}}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")


#####################################################
# check if autoenv.sh ran before
#####################################################

# script needs to run sourced
if [[ "$0" == "$BASH_SOURCE" ]]; then
  echo "ERROR: script is not sourced"
  exit 1
fi

if [[ ! -z "${HOLBA_SKIP_AUTOENV}" ]]; then
  echo "INFO: skipping autoenv.sh"
  return 0
fi


#####################################################
# find HolBA dir for this script
#####################################################

if [[ -z "${HOLBA_DIR}" ]]; then
  HOLBA_DIR=${SETUP_DIR}/../..
  HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")
fi

function is_holba {
  # Apparently not a good practice (https://stackoverflow.com/a/43840545)
  # but this enables to easily "echo then return $FALSE"
  local FALSE="1"

  [[ -d "$1/scripts/setup" ]] \
      || { echo "bad scripts dir" > /dev/stderr; return $FALSE; }

  [[ -f "$1/scripts/setup/autoenv.sh" ]] \
      || { echo "no autoenv.sh" > /dev/stderr; return $FALSE; }

  [[ "$(grep -c 'HOLBA' "$1/scripts/setup/autoenv.sh")" -ge 1 ]] \
      || { echo "bad autoenv.sh" > /dev/stderr; return $FALSE; }

  [[ -f "$1/README.md" ]] \
      || { echo "no README.md" > /dev/stderr; return $FALSE; }

  [[ "$(head -n1 "$1/README.md" 2> /dev/null | grep -c '# HolBA')" -eq 1 ]] \
      || { echo "bad README.md" > /dev/stderr; return $FALSE; }

  true
}

if ! is_holba "${HOLBA_DIR}"; then
  echo "ERROR: HOLBA_DIR not found or incorrect (tried: '${HOLBA_DIR}')"
  return 2
fi

echo "NOTICE: HOLBA_DIR is never exported"
echo
echo "Using HOLBA_DIR=${HOLBA_DIR}"
echo


function print_export_msg() {
  RED='\033[0;31m'
  NC='\033[0m'
  printf "${RED}%%%%%%%%%%%% Exporting $1 %%%%%%%%%%%%${NC}\n"
}

#####################################################
# core parameters
#####################################################


####### HOLBA_OPT_DIR

# the parameter to this script has precedence
if [[ ! -z "${OPT_DIR_PARAM}" ]]; then
  print_export_msg "Exporting HOLBA_OPT_DIR (parameter)"
  export HOLBA_OPT_DIR=$(readlink -f "${OPT_DIR_PARAM}")
else
  # if there is no parameter, and no environment variable
  if [[ -z "${HOLBA_OPT_DIR}" ]]; then
    # take opt in HOLBA_DIR
    print_export_msg "Exporting HOLBA_OPT_DIR (default in HolBA)"
    export HOLBA_OPT_DIR="${HOLBA_DIR}/opt"
  fi
fi
echo "Using HOLBA_OPT_DIR=${HOLBA_OPT_DIR}"
echo


####### HOLBA_HOL_BIN_DIR
## SECONDARY: HOLBA_HOLMAKE, PATH

# first define HOLBA_HOL_BIN_DIR if undefined (default)
if [[ -z "${HOLBA_HOL_BIN_DIR}" ]]; then
  print_export_msg "Exporting HOLBA_HOL_BIN_DIR"
  export HOLBA_HOL_BIN_DIR=${HOLBA_OPT_DIR}/hol_k12_holba/bin
  echo "Using HOLBA_HOL_BIN_DIR=${HOLBA_HOL_BIN_DIR}"
fi

# fail if HOLBA_HOL_BIN_DIR doesn't exist
if [[ ! -d "${HOLBA_HOL_BIN_DIR}" ]]; then
  echo "WARNING: hol/bin directory does not exist ('${HOLBA_HOL_BIN_DIR}')"
  #return 3
fi

if [[ -d "${HOLBA_HOL_BIN_DIR}" ]]; then
  # make "hol/bin" available in PATH
  print_export_msg "Exporting PATH"
  # do it conditional if needed (also in install_mk_env.sh): [[ ":$PATH:" != *":${HOLBA_HOL_BIN_DIR}:"* ]] && export ...
  export PATH="${HOLBA_HOL_BIN_DIR}:${PATH}"
  echo "Using PATH=${PATH}"

  # make Holmake available
  print_export_msg "Exporting HOLBA_HOLMAKE"
  export HOLBA_HOLMAKE="${HOLBA_HOL_BIN_DIR}/Holmake"
  echo "Using HOLBA_HOLMAKE=${HOLBA_HOLMAKE}"
fi
echo


#####################################################
# additional parameters:
#   - either already defined or search in opt_dir
#####################################################


####### HOLBA_Z3_DIR
## SECONDARY: PYTHONPATH, LD_LIBRARY_PATH,
##            HOL4_Z3_EXECUTABLE, HOL4_Z3_WRAPPED_EXECUTABLE

if [[ -z "${HOLBA_Z3_DIR}" ]]; then
  Z3_DIR=${HOLBA_OPT_DIR}/z3-4.8.4.d6df51951f4c
  if [[ -d "${Z3_DIR}/bin/python" ]]; then
    print_export_msg "Exporting HOLBA_Z3_DIR"
    export HOLBA_Z3_DIR=${Z3_DIR}
  else
    # try the folder name for the version compiled from source
    Z3_DIR=${HOLBA_OPT_DIR}/z3_4.8.4
    if [[ -d "${Z3_DIR}/bin/python" ]]; then
      print_export_msg "Exporting HOLBA_Z3_DIR"
      export HOLBA_Z3_DIR=${Z3_DIR}
    fi
  fi
fi
echo "Using HOLBA_Z3_DIR=${HOLBA_Z3_DIR}"

# if HOLBA_Z3_DIR has been found, export secondary variables
if [[ ! -z "${HOLBA_Z3_DIR}" ]]; then
    print_export_msg "Exporting HOLBA_Z3_DIR's secondaries"
    export PYTHONPATH=${HOLBA_Z3_DIR}/bin/python
    export LD_LIBRARY_PATH=${HOLBA_Z3_DIR}/bin:$LD_LIBRARY_PATH

    export HOL4_Z3_EXECUTABLE=${HOLBA_Z3_DIR}/bin/z3
    export HOL4_Z3_WRAPPED_EXECUTABLE=${HOLBA_DIR}/src/shared/z3_wrapper.py

    echo "Using PYTHONPATH=${PYTHONPATH}"
    echo "Using LD_LIBRARY_PATH=${LD_LIBRARY_PATH}"
    echo "Using HOL4_Z3_EXECUTABLE=${HOL4_Z3_EXECUTABLE}"
    echo "Using HOL4_Z3_WRAPPED_EXECUTABLE=${HOL4_Z3_WRAPPED_EXECUTABLE}"
fi
echo

####### HOLBA_EMBEXP_DIR

if [[ -z "${HOLBA_EMBEXP_DIR}" ]]; then
  EMBEXP_DIR=${HOLBA_OPT_DIR}/embexp
  if [[ -d "${EMBEXP_DIR}/EmbExp-ProgPlatform" ]]; then
    print_export_msg "Exporting HOLBA_EMBEXP_DIR"
    export HOLBA_EMBEXP_DIR=${EMBEXP_DIR}
  fi
fi
echo "Using HOLBA_EMBEXP_DIR=${HOLBA_EMBEXP_DIR}"
echo



####### HOLBA_GCC_ARM8_CROSS

if [[ -z "${HOLBA_GCC_ARM8_CROSS}" ]]; then
  CROSS="${HOLBA_OPT_DIR}/gcc-arm8-8.2-2018.08-aarch64-elf/bin/aarch64-elf-"
  if [[ -f "${CROSS}gcc" ]]; then
    print_export_msg "HOLBA_GCC_ARM8_CROSS"
    export HOLBA_GCC_ARM8_CROSS=${CROSS}
  fi
fi
echo "Using HOLBA_GCC_ARM8_CROSS=${HOLBA_GCC_ARM8_CROSS}"
echo



####### HOLBA_SCAMV_LOGS

if [[ -z "${HOLBA_SCAMV_LOGS}" ]]; then
  LOGS_DIR=${HOLBA_DIR}/logs
  print_export_msg "Exporting HOLBA_SCAMV_LOGS"
  export HOLBA_SCAMV_LOGS=${LOGS_DIR}
fi
echo "Using HOLBA_SCAMV_LOGS=${HOLBA_SCAMV_LOGS}"
echo


print_export_msg "Exporting HOLBA_SKIP_AUTOENV"
export HOLBA_SKIP_AUTOENV=1

