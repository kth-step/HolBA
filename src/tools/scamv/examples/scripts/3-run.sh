#!/usr/bin/env bash

set -e

ARCH_EXPTYPE_PARAM=$1

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# check inputs
if [[ -z "${ARCH_EXPTYPE_PARAM}" ]]; then
  echo "ERROR: please provide experiment architecture and type as parameter (e.g. arm8/exps2)"
  exit 1
fi

# find the environment
source "${HOLBA_DIR}/env.sh"
echo "============================"

# create EmbExp-ProgPlatform working directory
export EMBEXP_PROGPLATFORM=${SCAMV_EXAMPLES_DIR}/tempdir/EmbExp-ProgPlatform
mkdir -p "${EMBEXP_PROGPLATFORM}"
rm -rf "${EMBEXP_PROGPLATFORM}"
git clone https://github.com/kth-step/EmbExp-ProgPlatform.git "${EMBEXP_PROGPLATFORM}"
cd "${EMBEXP_PROGPLATFORM}"
git checkout scamv

# in the logs directory ...
cd "${HOLBA_EMBEXP_LOGS}"
# find the exp classes,
EXPSDIR=${HOLBA_EMBEXP_LOGS}/${ARCH_EXPTYPE_PARAM}
for dir in "${EXPSDIR}"/*/
do
  dir=${dir%*/}
  dir=${dir##*/}

  # and start the experiments
  ./scripts/run_batch.py --exp_class "${ARCH_EXPTYPE_PARAM}/${dir}"
done


