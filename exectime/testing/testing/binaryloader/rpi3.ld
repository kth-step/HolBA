/*
 * Derived from code:
 * (C) Copyright 2013 David Feng <fenghua@phytium.com.cn>
 * (C) Copyright 2002 Gary Jennejohn, DENX Software Engineering, <garyj@denx.de>
 *
 * SPDX-License-Identifier:	GPL-2.0
 */

OUTPUT_FORMAT("elf64-littleaarch64", "elf64-littleaarch64", "elf64-littleaarch64")
OUTPUT_ARCH(aarch64)
ENTRY(_start)
SECTIONS
{
	__experiment_code_loc   = 0x200000;
	__experiment_memory_loc = 0x100000;
	__experiment_memory_len =  0x40000;/* 32 * 1024 * 8 */


	. = __experiment_code_loc;

	. = ALIGN(8);
	.text __experiment_code_loc :
	{
		src/entry.o (.text*)
	}

	. = __experiment_memory_loc;
	. = ALIGN(8);
	.rodata : { *(SORT_BY_ALIGNMENT(SORT_BY_NAME(.rodata*))) }

	. = ALIGN(8);
	.data : {
		*(.data*);
		*(.sdata*);
	}

	. = ALIGN(8);

	.rel_dyn_start :
	{
		*(.__rel_dyn_start)
	}

	.rela.dyn : {
		*(.rela*)
	}

	.rel_dyn_end :
	{
		*(.__rel_dyn_end)
	}

	_end = .;

	. = ALIGN(8);

	.bss_start : {
		KEEP(*(.__bss_start));
	}

	.bss : {
		*(.bss*);
		*(.sbss*);
		 . = ALIGN(8);
	}

	.bss_end : {
		KEEP(*(.__bss_end));
	}

	__experiment_memory_top = .;

	CHECK_EXP_MEM_SPACE = 1 / (__experiment_memory_top <= (__experiment_memory_loc + __experiment_memory_len));
	/*ASSERT(((__experiment_memory_loc + __experiment_memory_len) <= __experiment_memory_top), "error: not enough room in the experiment memory");*/


	/DISCARD/ : { *(.dynsym) }
	/DISCARD/ : { *(.dynstr*) }
	/DISCARD/ : { *(.dynamic*) }
	/DISCARD/ : { *(.plt*) }
	/DISCARD/ : { *(.interp*) }
	/DISCARD/ : { *(.gnu*) }
}
