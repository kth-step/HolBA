#!/bin/bash

FILENAME=binaries-test.exe.log_$1

#echo ${FILENAME}

cat ${FILENAME} | grep -v "Saved " | grep -v "<<HO" | grep -v "=====" | grep -v "(length: " | grep -v "heory \""


