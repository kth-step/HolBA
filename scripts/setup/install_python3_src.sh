#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
set --
source "${SETUP_DIR}/env_config_gen.sh" "${OPT_DIR_PARAM}"

##################################################################


# download package
PYTHON3_VERSION="3.7.4"
PYTHON3_URL="https://www.python.org/ftp/python/${PYTHON3_VERSION}/Python-${PYTHON3_VERSION}.tar.xz"

PYTHON3_DIR=${HOLBA_OPT_DIR}/python_${PYTHON3_VERSION}
PYTHON3_DIR_SRC=${HOLBA_OPT_DIR}/python_${PYTHON3_VERSION}_src

PYTHON3_BIN=python3.7
PYTHON3_LIN=python3






##################################################################


# if the output directory exists, we already have a python3 in the cache
if [[ -d "${PYTHON3_DIR}" ]]; then
  echo "python3 is already available in the cache, exiting."
  exit 0
else
  echo "python3 is not in the cache, downloading it now."
fi

# prepare directories
mkdir "${PYTHON3_DIR_SRC}"
mkdir "${PYTHON3_DIR}"

# download python3
wget -qO- ${PYTHON3_URL} | \
  tar -xJ -C "${PYTHON3_DIR_SRC}" --strip-components 1

# compile python3
cd "${PYTHON3_DIR_SRC}"
./configure --prefix=${PYTHON3_DIR}
make -j 8

# install python3 to prefix dir
make altinstall

cd "${PYTHON3_DIR}/bin"
ln -s ${PYTHON3_BIN} ${PYTHON3_LIN}

# remove source directory
cd "${HOLBA_OPT_DIR}"
rm -rf "${PYTHON3_DIR_SRC}"

