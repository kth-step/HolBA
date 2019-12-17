#!/usr/bin/env bash



# get current holba directory path
HOLBA_DIR=$(dirname "${BASH_SOURCE[0]:-${(%):-%x}}")/../..
HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")


#####################################################
# check that this script is sourced
#####################################################

# script needs to run sourced
if [[ "$0" == "$BASH_SOURCE" ]]; then
  echo "ERROR: script is not sourced"
  exit 1
fi



function print_export_msg() {
  RED='\033[0;31m'
  NC='\033[0m'
  printf "${RED}%%%%%%%%%%%% Exporting $1 %%%%%%%%%%%%${NC}\n"
}

#####################################################
# derive parameters is base parameters have been defined
#####################################################

####### HOLBA_HOL_DIR
## derived: PATH
if [[ ! -z "${HOLBA_HOL_DIR}" ]] && [[ -d "${HOLBA_HOL_DIR}" ]]; then
  HOLBA_HOL_BIN_DIR="${HOLBA_HOL_DIR}/bin"
  # fail if directory HOLBA_HOL_BIN_DIR doesn't exist
  if [[ ! -d "${HOLBA_HOL_BIN_DIR}" ]]; then
    echo "WARNING: hol/bin directory does not exist ('${HOLBA_HOL_BIN_DIR}')"
    return 3
  fi

  if [[ -d "${HOLBA_HOL_BIN_DIR}" ]]; then
    HOLMAKE_BIN_DIR=$(dirname "$(which Holmake)")
    if [[ "${HOLBA_HOL_BIN_DIR}" == "${HOLMAKE_BIN_DIR}" ]]; then
      print_export_msg "not, because ${HOLBA_HOL_BIN_DIR} already is in the PATH"
    else
      # make "hol/bin" available in PATH
      print_export_msg "PATH"
      export PATH="${HOLBA_HOL_BIN_DIR}:${PATH}"
      echo "Using PATH=${PATH}"
    fi
  fi
fi



####### HOLBA_Z3_DIR
## derived: PYTHONPATH, LD_LIBRARY_PATH, PATH,
##          HOL4_Z3_EXECUTABLE, HOL4_Z3_WRAPPED_EXECUTABLE
# if HOLBA_Z3_DIR has been found, export derived variables
if [[ ! -z "${HOLBA_Z3_DIR}" ]]; then
    print_export_msg "HOLBA_Z3_DIR's derived variables"
    export PYTHONPATH="${HOLBA_Z3_DIR}/bin/python"
    export LD_LIBRARY_PATH="${HOLBA_Z3_DIR}/bin:$LD_LIBRARY_PATH"
    export PATH="${HOLBA_Z3_DIR}/bin:${PATH}"

    export HOL4_Z3_EXECUTABLE="${HOLBA_Z3_DIR}/bin/z3"
    export HOL4_Z3_WRAPPED_EXECUTABLE="${HOLBA_DIR}/src/shared/z3_wrapper.py"

    echo "Using PYTHONPATH=${PYTHONPATH}"
    echo "Using LD_LIBRARY_PATH=${LD_LIBRARY_PATH}"
    echo "Using HOL4_Z3_EXECUTABLE=${HOL4_Z3_EXECUTABLE}"
    echo "Using HOL4_Z3_WRAPPED_EXECUTABLE=${HOL4_Z3_WRAPPED_EXECUTABLE}"
fi



####### HOLBA_USE_OWN_PYTHON3
if [[ ! -z "${HOLBA_USE_OWN_PYTHON3}" ]]; then
  PYTHON3_DIR=${HOLBA_OPT_DIR}/python_3.7.4
  if [[ -d "${PYTHON3_DIR}" ]]; then
    export PATH=${PYTHON3_DIR}/bin:${PATH}
    echo "Using PATH=${PATH}"
    export LD_LIBRARY_PATH=${PYTHON3_DIR}/lib:${LD_LIBRARY_PATH}
    echo "Using LD_LIBRARY_PATH=${LD_LIBRARY_PATH}"
  fi
fi


