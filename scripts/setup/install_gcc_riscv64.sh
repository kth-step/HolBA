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
GCC_URL="https://static.dev.sifive.com/dev-tools/riscv64-unknown-elf-gcc-8.3.0-2020.04.1-x86_64-linux-ubuntu14.tar.gz"

GCC_DIR=${HOLBA_OPT_DIR}/gcc-riscv64-unknown-elf-8.3.0-2020.04.1








##################################################################


# if the output directory exists, we already have a gcc in the cache
if [[ -d "${GCC_DIR}" ]]; then
  echo "gcc_riscv64 is already available in the cache, exiting."
  exit 0
else
  echo "gcc_riscv64 is not in the cache, downloading it now."
fi

# download gcc
mkdir "${GCC_DIR}"
wget -qO- ${GCC_URL} | tar -xz -C "${GCC_DIR}" --strip-components 1


