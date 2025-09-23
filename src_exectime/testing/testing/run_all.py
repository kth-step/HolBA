#!/usr/bin/env python3

import sys
import os
test_cases_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "testcases"))

import argparse
import logging
import time
import subprocess

# parse arguments
parser = argparse.ArgumentParser()
parser.add_argument("testcaseprefix", help="prefix of testcases to run")

parser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true")
args = parser.parse_args()

# set log level
if args.verbose:
	logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
else:
	logging.basicConfig(stream=sys.stderr, level=logging.WARNING)

testcaseprefix = args.testcaseprefix


# find all testcases to run
# =====================================================
testcases = []
for name in os.listdir(test_cases_dir):
	fullname = os.path.join(test_cases_dir, name)
	if os.path.isdir(fullname):
		if name.startswith(testcaseprefix):
			testcases.append(name)
	else:
		raise Exception("there shouldn't be any files in the test cases directory")
testcases.sort()


# run each testcase
# - write result per testcase
# - fail altogether if at least one was not successful
# =====================================================
all_successful = True
for testcase in testcases:
	print(f"Running '{testcase}'")
	cmdl = [os.path.join(os.path.dirname(__file__), "run_testcase.py"), testcase]
	res = subprocess.call(cmdl, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
	# need cooldown between experiments, failing experiments cause some form of congestion if reusing the same board connection
	# TODO: fix this issue in the experiment running makefile or similar
	time.sleep(2)
	success = res == 0
	print(f"\t- {'success' if success else 'fail'}")
	all_successful &= success

if all_successful:
	print("All test cases ran successfully.")
else:
	print("Some test cases FAILED!!!")
	exit(-1)
