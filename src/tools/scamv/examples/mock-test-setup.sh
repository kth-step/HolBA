#!/bin/bash

if [ -z "${SCAMV_BASEDIR}" ]
then
  export SCAMV_BASEDIR=../../../../../
fi

if [ -z "${Z3_BASEDIR}" ]
then
  export Z3_BASEDIR=${SCAMV_BASEDIR}/z3-4.8.4.d6df51951f4c/
fi


# test setup
#PYTHONPATH=${Z3_BASEDIR}/bin/python LD_LIBRARY_PATH=${Z3_BASEDIR}/bin python3

export PYTHONPATH=${Z3_BASEDIR}/bin/python
export LD_LIBRARY_PATH=${Z3_BASEDIR}/bin:$LD_LIBRARY_PATH
export HOL4_Z3_EXECUTABLE=${Z3_BASEDIR}/bin/z3

export HOL4_Z3_WRAPPED_EXECUTABLE=${SCAMV_BASEDIR}/HolBA/src/libs/z3_wrapper.py


