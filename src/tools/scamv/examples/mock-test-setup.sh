#!/bin/bash

if [ -z "${HOLBA_DIR}" ]
then
  export HOLBA_DIR=../../../../
fi

if [ -z "${HOLBA_Z3_DIR}" ]
then
  export HOLBA_Z3_DIR=${HOLBA_OPT_DIR}/z3-4.8.4.d6df51951f4c/
fi

if [ -z "${HOLBA_EMBEXP_DIR}" ]
then
  export HOLBA_EMBEXP_DIR=${HOLBA_OPT_DIR}/embexp/
fi

if [ -z "${HOLBA_SCAMV_LOGS}" ]
then
  export HOLBA_SCAMV_LOGS=${HOLBA_DIR}/logs
fi



# test setup
#PYTHONPATH=${HOLBA_Z3_DIR}/bin/python LD_LIBRARY_PATH=${HOLBA_Z3_DIR}/bin python3

export PYTHONPATH=${HOLBA_Z3_DIR}/bin/python
export LD_LIBRARY_PATH=${HOLBA_Z3_DIR}/bin:$LD_LIBRARY_PATH
export HOL4_Z3_EXECUTABLE=${HOLBA_Z3_DIR}/bin/z3

export HOL4_Z3_WRAPPED_EXECUTABLE=${HOLBA_DIR}/src/shared/z3_wrapper.py



#export HOLBA_GCC_ARM8_CROSS="${HOLBA_OPT_DIR}/gcc-arm8-8.2-2018.08-aarch64-elf/bin/aarch64-elf-"
export HOLBA_GCC_ARM8_CROSS=aarch64-linux-gnu-


