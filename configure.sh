#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
HOLBA_DIR=$(dirname "${BASH_SOURCE[0]}")
HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")

# find the core and base environment variables (if undefined)
set --
source "${HOLBA_DIR}/scripts/setup/env_config_gen.sh" "${OPT_DIR_PARAM}"

##################################################################

# output file
OUTPUT_FILE="${HOLBA_DIR}/config.env.sh"
echo "Output file: ${OUTPUT_FILE}"
echo


# variables to export
declare -a vararr=(
  "HOLBA_OPT_DIR"

  "HOLBA_HOL_DIR"
  "HOLBA_Z3_DIR"
  "HOLBA_EMBEXP_DIR"
  "HOLBA_GCC_ARM8_CROSS"
  "HOLBA_SCAMV_LOGS"
)

# collect output in variable
PAD_LEN=30
#OUTPUT="#!/usr/bin/env bash"
#OUTPUT="${OUTPUT}\n"
OUTPUT="${OUTPUT}\n# please don't change the format of this file."
OUTPUT="${OUTPUT}\n# it is used for both bash and make!"
OUTPUT="${OUTPUT}\n"
for var in "${vararr[@]}"
do
  var_val=$(printenv ${var} | cat)
  printf -v var_pad "%${PAD_LEN}.${PAD_LEN}s" "${var}"
  OUTPUT="${OUTPUT}\nexport ${var_pad}=${var_val}"
  echo "Exporting ${var}"
done
OUTPUT="${OUTPUT}\n"
echo

# generate env export script for all variables
echo -e "${OUTPUT}" > "${OUTPUT_FILE}"
echo "File generated: ${OUTPUT_FILE}"


