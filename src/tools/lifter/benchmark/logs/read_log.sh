#!/bin/bash

FILENAME=binaries-test.exe.log_$1

#echo ${FILENAME}

cat ${FILENAME} | grep -v " @ " | grep -v " failed" | grep -v "^$"

