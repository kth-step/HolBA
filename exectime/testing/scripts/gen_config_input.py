#!/usr/bin/env python3

output_text = ""
with open("Makefile.config", "r") as f:
	for line in f:
		if line.strip() == "":
			continue
		parts = line.split("=")
		assert len(parts) == 2
		k = parts[0].strip()
		v = parts[1].strip()
		if k == "PROGPLAT_LOAD_ELF":
			continue
		if k.startswith("__") and k.endswith("__"):
			output_text += f"#define {k} {v}\n"
		else:
			output_text += f"#define __{k.upper()}__{v.upper()}\n"

with open("all/inc/config_input.h", "w") as f:
	f.write(output_text)

