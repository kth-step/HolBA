#!/usr/bin/env bash

OPT_DIR_PARAM=$1

# get current holba directory path
HOLBA_DIR=$(dirname "${BASH_SOURCE[0]:-${(%):-%x}}")/../..
HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")


#####################################################
# check that this script is sourced
#####################################################

# script needs to run sourced
if [[ "$0" == "$BASH_SOURCE" ]]; then
  echo "ERROR HOLBA: script is not sourced"
  exit 1
fi


#####################################################
# check HolBA dir for this script
#####################################################

function is_holba {
  # Apparently not a good practice (https://stackoverflow.com/a/43840545)
  # but this enables to easily "echo then return $FALSE"
  local FALSE="1"

  [[ -d "$1/scripts/setup" ]] \
      || { echo "bad scripts dir" > /dev/stderr; return $FALSE; }

  [[ -f "$1/scripts/setup/env_derive.sh" ]] \
      || { echo "no env_derive.sh" > /dev/stderr; return $FALSE; }

  [[ "$(grep -c 'HOLBA' "$1/scripts/setup/env_derive.sh")" -ge 1 ]] \
      || { echo "bad env_derive.sh" > /dev/stderr; return $FALSE; }

  [[ -f "$1/README.md" ]] \
      || { echo "no README.md" > /dev/stderr; return $FALSE; }

  [[ "$(head -n1 "$1/README.md" 2> /dev/null | grep -c '# HolBA')" -eq 1 ]] \
      || { echo "bad README.md" > /dev/stderr; return $FALSE; }

  true
}

if ! is_holba "${HOLBA_DIR}"; then
  echo "ERROR HOLBA: HOLBA_DIR not found or incorrect (tried: '${HOLBA_DIR}')"
  return 2
fi

echo "Using HOLBA_DIR=${HOLBA_DIR}"
echo


function print_export_msg() {
  RED='\033[0;31m'
  NC='\033[0m'
  printf "${RED}%%%%%%%%%%%% Exporting $1 %%%%%%%%%%%%${NC}\n"
}


#####################################################
# core parameter HOLBA_OPT_DIR
#####################################################

# the parameter to this script has precedence
if [[ ! -z "${OPT_DIR_PARAM}" ]]; then
  if [[ ! -d "${OPT_DIR_PARAM}" ]]; then
    echo "ERROR HOLBA: not a directory: ${OPT_DIR_PARAM}"
    return 2
  fi
  print_export_msg "HOLBA_OPT_DIR (parameter)"
  export HOLBA_OPT_DIR=$(readlink -f "${OPT_DIR_PARAM}")
else
  # if there is no parameter, and no environment variable
  if [[ -z "${HOLBA_OPT_DIR}" ]]; then
    # take opt in HOLBA_DIR
    print_export_msg "HOLBA_OPT_DIR (default in HolBA)"
    export HOLBA_OPT_DIR="${HOLBA_DIR}/opt"
  fi
  mkdir -p ${HOLBA_OPT_DIR}
fi
echo "Using HOLBA_OPT_DIR=${HOLBA_OPT_DIR}"
echo


#####################################################
# base parameters:
#   - either already defined or search in opt_dir
#####################################################


####### HOLBA_HOL_DIR

# first define HOLBA_HOL_DIR if undefined (default)
if [[ ( -z "${HOLBA_HOL_DIR}" ) || ( ! -z "${OPT_DIR_PARAM}" ) ]]; then
  print_export_msg "HOLBA_HOL_DIR"
  export HOLBA_HOL_DIR="${HOLBA_OPT_DIR}/hol_t1"
fi

HOLBA_HOL_BIN_DIR="${HOLBA_HOL_DIR}/bin"
# warn if directory HOLBA_HOL_BIN_DIR doesn't exist
if [[ ( ! -d "${HOLBA_HOL_DIR}" ) || ( ! -d "${HOLBA_HOL_BIN_DIR}" ) ]]; then
  echo "WARNING HOLBA: hol/bin directory does not exist ('${HOLBA_HOL_BIN_DIR}')"
  # note: don't fail because this script is used before install script run
fi
if [[ ( ! -d "${HOLBA_HOL_DIR}" ) ]]; then
  print_export_msg "HOLBA_HOL_DIR"
  export HOLBA_HOL_DIR=
fi
echo "Using HOLBA_HOL_DIR=${HOLBA_HOL_DIR}"
echo


####### HOLBA_Z3_DIR

if [[ ( -z "${HOLBA_Z3_DIR}" ) || ( ! -z "${OPT_DIR_PARAM}" ) ]]; then
  Z3_DIR="${HOLBA_OPT_DIR}/z3-4.13.4"
  if [[ -d "${Z3_DIR}/bin/python" ]]; then
    print_export_msg "HOLBA_Z3_DIR"
    export HOLBA_Z3_DIR="${Z3_DIR}"
  else
    # try the folder name for the version compiled from source
    Z3_DIR="${HOLBA_OPT_DIR}/z3_4.13.4"
    if [[ -d "${Z3_DIR}/bin/python" ]]; then
      print_export_msg "HOLBA_Z3_DIR"
      export HOLBA_Z3_DIR=${Z3_DIR}
    fi
  fi
fi
if [[ ( ! -d "${HOLBA_Z3_DIR}" ) ]]; then
  print_export_msg "HOLBA_Z3_DIR"
  export HOLBA_Z3_DIR=
fi
echo "Using HOLBA_Z3_DIR=${HOLBA_Z3_DIR}"
echo



####### HOLBA_GCC_ARM8_CROSS

if [[ ( -z "${HOLBA_GCC_ARM8_CROSS}" ) || ( ! -z "${OPT_DIR_PARAM}" ) ]]; then
  CROSS="${HOLBA_OPT_DIR}/gcc-arm8-8.2-2018.08-aarch64-elf/bin/aarch64-elf-"
  if [[ -f "${CROSS}gcc" ]]; then
    print_export_msg "HOLBA_GCC_ARM8_CROSS"
    export HOLBA_GCC_ARM8_CROSS=${CROSS}
  fi
fi
if [[ ( ! -f "${HOLBA_GCC_ARM8_CROSS}gcc" ) ]]; then
  print_export_msg "HOLBA_GCC_ARM8_CROSS"
  export HOLBA_GCC_ARM8_CROSS=
fi
echo "Using HOLBA_GCC_ARM8_CROSS=${HOLBA_GCC_ARM8_CROSS}"
echo



####### HOLBA_GCC_ARM_CROSS

if [[ ( -z "${HOLBA_GCC_ARM_CROSS}" ) || ( ! -z "${OPT_DIR_PARAM}" ) ]]; then
  CROSS="${HOLBA_OPT_DIR}/gcc-arm-none-eabi-7-2018-q2u/bin/arm-none-eabi-"
  if [[ -f "${CROSS}gcc" ]]; then
    print_export_msg "HOLBA_GCC_ARM_CROSS"
    export HOLBA_GCC_ARM_CROSS=${CROSS}
  fi
fi
if [[ ( ! -f "${HOLBA_GCC_ARM_CROSS}gcc" ) ]]; then
  print_export_msg "HOLBA_GCC_ARM_CROSS"
  export HOLBA_GCC_ARM_CROSS=
fi
echo "Using HOLBA_GCC_ARM_CROSS=${HOLBA_GCC_ARM_CROSS}"
echo



####### HOLBA_GCC_RISCV64_CROSS

if [[ ( -z "${HOLBA_GCC_RISCV64_CROSS}" ) || ( ! -z "${OPT_DIR_PARAM}" ) ]]; then
  CROSS="${HOLBA_OPT_DIR}/gcc-riscv64-unknown-elf-8.3.0-2019.08.0/bin/riscv64-unknown-elf-"
  if [[ -f "${CROSS}gcc" ]]; then
    print_export_msg "HOLBA_GCC_RISCV64_CROSS"
    export HOLBA_GCC_RISCV64_CROSS=${CROSS}
  fi
fi
if [[ ( ! -f "${HOLBA_GCC_RISCV64_CROSS}gcc" ) ]]; then
  print_export_msg "HOLBA_GCC_RISCV64_CROSS"
  export HOLBA_GCC_RISCV64_CROSS=
fi
echo "Using HOLBA_GCC_RISCV64_CROSS=${HOLBA_GCC_RISCV64_CROSS}"
echo



