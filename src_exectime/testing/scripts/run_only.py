#!/usr/bin/env python3

import sys
import os
import subprocess

rdycheck__exec = ["scripts/check_ready.sh"]
postuart__exec = ["nc", "localhost", os.environ["EMBEXP_UART_PORT"]]
postdebug_exec = ["scripts/run_gdb.py"] + sys.argv[1:]

tempuartlog = "./temp/uart.log"

retval = subprocess.call(rdycheck__exec)

if retval != 0:
	raise Exception("connection has not been established yet, run \"make connect\" first")

print( "---------------------------")
print(f"uart log > {tempuartlog}")
print( "---------------------------")

subprocess.call(["mkdir", "-p", os.path.dirname(tempuartlog)])
subprocess.call(["rm", "-f", tempuartlog])

with open(tempuartlog, "w") as uartlog:
	uartproc = subprocess.Popen(postuart__exec, stdin=subprocess.PIPE, stdout=uartlog, stderr=None)
	try:
		print("starting uart logging")
		subprocess.call(postdebug_exec)
		print("finishing uart logging")
	finally:
		print()
		print("terminating uart logging process")
		uartproc.terminate()

