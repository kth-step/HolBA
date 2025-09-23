#!/usr/bin/env python3

import subprocess

makeswitches = ["--silent", "--ignore-errors", "--no-print-directory"]

retval = subprocess.call(["scripts/check_ready.sh"])
if retval == 0:
	subprocess.call(["make"] + makeswitches + ["runlog"])
else:
	subprocess.call(["scripts/connect_and_run.py"])

