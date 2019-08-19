#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
set --
source "${SETUP_DIR}/autoenv.sh" "${OPT_DIR_PARAM}"

##################################################################


# download package
Z3_BASE="https://github.com/Z3Prover/z3"
Z3_VERSION="4.8.4"
Z3_URL=${Z3_BASE}/archive/z3-${Z3_VERSION}.tar.gz

Z3_DIR=${HOLBA_OPT_DIR}/z3_${Z3_VERSION}
Z3_DIR_SRC=${HOLBA_OPT_DIR}/z3_${Z3_VERSION}_src








##################################################################


# if the output directory exists, we already have a z3 in the cache
if [[ -d "${Z3_DIR}" ]]; then
  echo "z3 is already available in the cache, exiting."
  exit 0
else
  echo "z3 is not in the cache, downloading it now."
fi

# prepare directories
mkdir "${Z3_DIR_SRC}"
mkdir "${Z3_DIR}"

# download z3
wget -qO- ${Z3_URL} | \
  tar xvz -C "${Z3_DIR_SRC}" --strip-components 1

# compile z3
cd "${Z3_DIR_SRC}"
python3 scripts/mk_make.py --prefix=${Z3_DIR} --python --pypkgdir=${Z3_DIR}/bin/python
cd build
make

# install z3 to prefix dir
make install

# remove source directory
cd "${HOLBA_OPT_DIR}"
rm -rf "${Z3_DIR_SRC}"

