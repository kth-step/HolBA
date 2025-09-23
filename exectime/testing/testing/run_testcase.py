#!/usr/bin/env python3

import sys
import os
test_cases_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "testcases"))
embexp_progplatform_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

import argparse
import logging
import json
import shutil
import subprocess

# parse arguments
parser = argparse.ArgumentParser()
parser.add_argument("testcase", help="id of testcase")

# pre-cleanup of progplatform
parser.add_argument("-fc", "--force_cleanup", help="force input file cleanup before running", action="store_true")
# post-cleanup of progplatform
parser.add_argument("-npc", "--no_post_clean",     help="do not cleanup after running", action="store_true")

parser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true")
args = parser.parse_args()

# set log level
if args.verbose:
	logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
else:
	logging.basicConfig(stream=sys.stderr, level=logging.WARNING)

do_pre_clean  = args.force_cleanup
no_post_clean = args.no_post_clean
testcasedir = os.path.join(test_cases_dir, args.testcase)
if not os.path.isdir(testcasedir):
	raise Exception(f"testcase directory does not exist: {testcasedir}")

# define what are input files and where they belong
inputfilemap = {
	"asm.h":             "all/inc/experiment/asm.h",
	"asm_setup_1.h":     "all/inc/experiment/asm_setup_1.h",
	"asm_setup_2.h":     "all/inc/experiment/asm_setup_2.h",
	"asm_setup_train.h": "all/inc/experiment/asm_setup_train.h",
	"binpatch.h":        "all/inc/experiment/binpatch.h",
	"Makefile.config":   "Makefile.config",
	"program.elf":       "program.elf"
}


# copied from embexp-logs
# =====================================================
def call_cmd(cmdl, error_msg, show_output = True, show_error = True):
	output_file = None
	if not show_output:
		output_file = subprocess.DEVNULL
	error_file = None
	if not show_error:
		error_file = subprocess.DEVNULL
	res = subprocess.call(cmdl, stdout=output_file, stderr=error_file)
	if res != 0:
		raise Exception(f"command {cmdl} not successful: {res} : {error_msg}")

def _call_make_cmd(makecmdl, error_msg):
	show_outputs = args.verbose
	call_cmd(["make", "-C", embexp_progplatform_dir] + makecmdl, error_msg, show_outputs, show_outputs)

def run_experiment(conn_mode = None):
	error_msg = "experiment didn't run successful"
	maketarget = "targetdoesnotexist"
	if conn_mode == "try" or conn_mode == None:
		maketarget = "runlog_try"
	elif conn_mode == "run":
		maketarget = "runlog"
	elif conn_mode == "reset":
		maketarget = "runlog_reset"
	else:
		raise Exception(f"invalid conn_mode: {conn_mode}")
	_call_make_cmd(["clean"], "error cleaning, somehow")
	_call_make_cmd([maketarget], error_msg)
	# read and return the uart output (binary)
	with open(os.path.join(embexp_progplatform_dir, "temp/uart.log"), "r") as f:
			uartlogdata = f.read()
	_call_make_cmd(["clean"], "error cleaning, somehow")
	return uartlogdata


# preparation
# =====================================================

# validate that all possible input files don't exist yet in repo
for name in inputfilemap:
	dst_file = os.path.join(embexp_progplatform_dir, inputfilemap[name])
	if os.path.isfile(dst_file):
		if do_pre_clean:
			os.remove(dst_file)
		else:
			raise Exception(f"destination file already exists: {dst_file}")

# find files in testcase dir
outputfile = "result_expected.json"
outputfile_found = False
inputfiles = []
for name in os.listdir(testcasedir):
	src_file = os.path.join(testcasedir, name)
	if os.path.isfile(src_file):
		if name in inputfilemap:
			dst_file = os.path.join(embexp_progplatform_dir, inputfilemap[name])
			# double check
			if os.path.isfile(dst_file):
				raise Exception(f"destination file already exists: {dst_file}")
			inputfiles.append((src_file, dst_file))
		else:
			assert(name == outputfile)
			outputfile = src_file
			outputfile_found = True
	else:
		raise Exception("there should not be anything but files in test case directories")
	#print(name)

if not outputfile_found:
	raise Exception("file with expected output not found")

# parse outputfile contents
with open(outputfile, 'r') as f:
	expected_structure = json.load(f)


# start
# =====================================================
# copy input files and run the test process, need to cleanup properly in the end
createdfiles = []
try:
	for (src_file, dst_file) in inputfiles:
		#print((src_file, dst_file))
		createdfiles.append(dst_file)
		shutil.copyfile(src_file, dst_file)

	result = run_experiment()
finally:
	for filename in createdfiles:
		if os.path.isfile(filename):
			if no_post_clean:
				logging.warning(f"keeping file: {filename}")
			else:
				os.remove(filename)
		else:
			logging.warning(f"cleanup issue. file does not exist: {filename}")

# if output is undefined, write raw output string as json and fail
if expected_structure == None:
	print(json.dumps(result))
	exit(-1)

if expected_structure["result_type"] == "raw_ok":
	expected = expected_structure["result"]
	if expected != result:
		print("unexpected result:")
		print("=" * 40)
		print(result)
		print("expecting result:")
		print("=" * 40)
		print(expected)
		exit(-2)
else:
	print(expected_structure)
	raise Exception("unknown result_type")


