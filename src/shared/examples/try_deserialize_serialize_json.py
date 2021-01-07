#!/usr/bin/env python3

import argparse
import logging

import sys
import json

# parse arguments
parser = argparse.ArgumentParser()

parser.add_argument("operation", help="operation to execute", choices=["test", "test2"])

parser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true")

args = parser.parse_args()

# set log level
if args.verbose:
	logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
else:
	logging.basicConfig(stream=sys.stderr, level=logging.WARNING)

operation = args.operation

# parse operation arguments from stdin
logging.info(f"parsing json arguments.")
json_arguments = json.load(sys.stdin)

# serialize them again
print(json.dumps(json_arguments))

