#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OUTPUT_FILE_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
set --
source "${SETUP_DIR}/autoenv.sh"

##################################################################

# set output file param if it is unset
OUTPUT_FILE=${OUTPUT_FILE_PARAM}
if [ -z "${OUTPUT_FILE}" ]; then
  OUTPUT_FILE=${HOLBA_OPT_DIR}/env.sh
fi
echo "Output file: ${OUTPUT_FILE}"
echo


# variables to export if defined
declare -a vararr=(
  "HOLBA_OPT_DIR"
  "HOLBA_HOLMAKE"

  "HOLBA_Z3_DIR"
  "HOLBA_EMBEXP_DIR"
  "HOLBA_GCC_ARM8_CROSS"
  "HOLBA_SCAMV_LOGS"
)

# collect output in variable
PAD_LEN=30
OUTPUT="#!/usr/bin/env bash\n"
for var in "${vararr[@]}"
do
  var_val=$(printenv ${var} | cat)
  if [ ! -z "${var_val}" ]; then
    printf -v var_pad %${PAD_LEN}.${PAD_LEN}s "${var}"
    OUTPUT="${OUTPUT}\nexport ${var_pad}=${var_val}"
    echo "Exporting ${var}"
  fi
done
OUTPUT="${OUTPUT}\n"
echo

# generate env export script for all variables
echo -e "${OUTPUT}" > "${OUTPUT_FILE}"
echo "File generated."


