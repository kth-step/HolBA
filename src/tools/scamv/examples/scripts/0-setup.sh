#!/usr/bin/env bash

set -e

EMBEXP_IDX_PARAM=$1
OPT_DIR_PARAM=$2
# EMBEXP_BOX_DIR=$3

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# define environment
export HOLBA_LOGS_DIR=
export HOLBA_EMBEXP_LOGS=
if [[ ! -z "${OPT_DIR_PARAM}" ]]; then
  if [[ -d "${OPT_DIR_PARAM}/.." ]]; then
    mkdir -p "${OPT_DIR_PARAM}"
  fi
  export HOLBA_OPT_DIR=${OPT_DIR_PARAM}
fi


# the actual setup takes place in the current HOLBA_DIR root
cd "${HOLBA_DIR}"
./scripts/setup/install_base.sh

./scripts/setup/install_z3.sh
./scripts/setup/install_gcc_arm8.sh

./scripts/setup/install_embexp_opt.sh
./scripts/setup/install_embexp_logs.sh

# create config.env.sh
./configure.sh

# add embexp configuration to config.env.sh
if [[ ! -z "${EMBEXP_IDX_PARAM}" ]]; then
  export EMBEXP_INSTANCE_IDX=${EMBEXP_IDX_PARAM}
  echo "export EMBEXP_INSTANCE_IDX=${EMBEXP_INSTANCE_IDX}" >> config.env.sh
fi
echo "export EMBEXP_BOX_USERNAME=${USER}" >> config.env.sh
echo "" >> config.env.sh

# compile HolBA
make main

