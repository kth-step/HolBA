#!/bin/bash

# https://static.docs.arm.com/100898/0100/the_a64_Instruction_set_100898_0100.pdf
# https://www.element14.com/community/servlet/JiveServlet/previewBody/41836-102-1-229511/ARM.Reference_Manual.pdf
# http://infocenter.arm.com/help/topic/com.arm.doc.dui0801d/dom1359731161338.html


#CROSS="${HOLBA_OPT_DIR}/gcc-arm8-8.2-2018.08-aarch64-elf/bin/aarch64-elf-"
CROSS=aarch64-linux-gnu-



${CROSS}gcc -c asm.s
${CROSS}objdump -d asm.o > asm.da

