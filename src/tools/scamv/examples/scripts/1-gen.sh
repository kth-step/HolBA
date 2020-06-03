#!/usr/bin/env bash

set -e

EXPGENRUN_PREFIX_PARAM=$1
EXPGENRUN_ID_PARAM=$2

# get scamv examples and holba directory path
SCAMV_EXAMPLES_DIR=$(dirname "${BASH_SOURCE[0]}")
SCAMV_EXAMPLES_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/..")
HOLBA_DIR=$(readlink -f "${SCAMV_EXAMPLES_DIR}/../../../..")

# find the environment
source "${HOLBA_DIR}/env.sh"
echo "============================"

# find experiment generation run parameters
EXPGENRUN_FILE=${SCAMV_EXAMPLES_DIR}/expgenruns/${EXPGENRUN_ID_PARAM}.txt
if [[ ! -f "${EXPGENRUN_FILE}" ]]; then
  echo "experiment generation description file not found: ${EXPGENRUN_FILE}"
  exit 1
fi
export SCAMV_EXPGENRUN_PARAMS=$(head -n 1 "${EXPGENRUN_FILE}")
echo "Using scamv parameters: ${SCAMV_EXPGENRUN_PARAMS}"

# try to prepare logs directory accordingly
cd "${HOLBA_EMBEXP_LOGS}"
if [[ ! -z "$(git status --porcelain)" ]]; then
  echo "logs repository is not clean, cannot go ahead"
  exit 1
fi

# see if git push is desired
echo "Do you want to push the current branch of EmbExp-Logs?"
select yn in "Yes" "No"; do
  case $yn in
    Yes ) git push; break;;
    No ) break;;
  esac
done

# clean everything
git checkout master
git clean -fd
git clean -fdX
git clean -fdx
# create branch based on latest master
git pull --all
git checkout -b "${EXPGENRUN_PREFIX_PARAM}_${EXPGENRUN_ID_PARAM}"


# start experiment generation process
cd "${SCAMV_EXAMPLES_DIR}"
./scamv.sh ${SCAMV_EXPGENRUN_PARAMS}


