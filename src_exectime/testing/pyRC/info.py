#!/usr/bin/env python3


import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), "lib"))

import balrobcomm
import balrob

try:
	with balrobcomm.BalrobComm() as bc:
		while True:
			balrob.handle_message(bc, balrob.package_handler)
except KeyboardInterrupt:
	pass

print("terminating.")

