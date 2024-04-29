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

# use a default polyml version if it is not specified in the environment
POLY_VERSION="v5.9.1"
if [[ ! -z "${HOLBA_POLYML_VERSION}" ]]; then
  POLY_VERSION=${HOLBA_POLYML_VERSION}
fi

# make polyml binaries and libraries available
POLY_DIR=${HOLBA_OPT_DIR}/polyml_${POLY_VERSION}
export PATH=${POLY_DIR}/bin:$PATH
export LD_LIBRARY_PATH=${POLY_DIR}/lib:$LD_LIBRARY_PATH

# use a default hol4 version if it is not specified in the environment
HOL4_VERSION="trindemossen-1"
if [[ ! -z "${HOLBA_HOL4_VERSION}" ]]; then
  HOL4_VERSION=${HOLBA_HOL4_VERSION}
fi

# HOL4 source and branch
GIT_URL=https://github.com/HOL-Theorem-Prover/HOL.git
GIT_IS_TAG=1

HOL4_DIR=${HOLBA_OPT_DIR}/hol_t1


##################################################################


# if HOL does exist, check if it is up-to-date and remove it in case it is not
if [[ -d "${HOL4_DIR}" ]]; then
  if [[ ! -z "${GIT_IS_TAG}" ]]; then
    echo "the cached HOL4 version is based on a tag, keeping it"
  else
    cd "${HOL4_DIR}"
    git fetch origin

    # does the remote branch exist locally?
    if [[ ! `git branch --all --list origin/${HOL4_VERSION}` ]]; then
      echo "the cached HOL4 version seems to be on another branch, deleting it now"
      # delete the stale HOL4 build
      cd "${HOLBA_OPT_DIR}"
      rm -rf "${HOL4_DIR}"
    else
      # is there a difference between the current and the remote branch?
      GIT_DIFF=$(git diff)
      GIT_DIFF_REMOTE=$(git diff HEAD remotes/origin/${HOL4_VERSION})
      if [[ "${GIT_DIFF}${GIT_DIFF_REMOTE}" ]]; then
        echo "the cached HOL4 version has differences, deleting it now"
        # delete the stale HOL4 build
        cd "${HOLBA_OPT_DIR}"
        rm -rf "${HOL4_DIR}"
      else
        echo "the cached HOL4 version is correct, keeping it"
      fi
    fi
  fi
fi
cd "${HOLBA_OPT_DIR}"


# if HOL does not exist already, clone and build it
if [[ ! -d "${HOL4_DIR}" ]]; then
  # clone the specified HOL4 branch only
  git clone -b ${HOL4_VERSION} --single-branch ${GIT_URL} "${HOL4_DIR}"
  cd "${HOL4_DIR}"

  # patch HOL4-kananaskis-14 to fix C++ issues
  if [ "${HOL4_VERSION}" = "kananaskis-14" ]; then
    sed -i 's/CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing.*/& -std=c++14/g' src/HolSat/sat_solvers/minisat/Makefile
    sed -i 's/g++ -O3 Proof.o File.o zc2hs.cpp -o zc2hs.*/& -std=c++14/g' src/HolSat/sat_solvers/zc2hs/Makefile
  fi

  # compile HOL4
  poly < tools/smart-configure.sml
  bin/build --nograph
fi
cd "${HOLBA_OPT_DIR}"



# extra builds (e.g. some l3 models)
declare -a hol4_extrabuild=(
  "examples/l3-machine-code/common"
  "examples/l3-machine-code/arm8/model"
  "examples/l3-machine-code/arm8/step"
  "examples/l3-machine-code/arm8/prog"
  "examples/l3-machine-code/m0/model"
  "examples/l3-machine-code/m0/step"
  "examples/l3-machine-code/riscv/model"
  "examples/l3-machine-code/riscv/step"
)

for dir in "${hol4_extrabuild[@]}"
do
  echo "Holmaking: ${dir}"
  cd "${HOL4_DIR}/${dir}"
  ${HOL4_DIR}/bin/Holmake
done

