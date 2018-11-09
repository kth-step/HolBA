#!/bin/bash

cat binaries-test.exe.log | grep -v "Saved " | grep -v "<<HO" | grep -v "=====" | grep -v "(length: " | grep -v "heory \""

