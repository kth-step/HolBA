/*
 * Derived from code:
 * (C) Copyright 2013 David Feng <fenghua@phytium.com.cn>
 * (C) Copyright 2002 Gary Jennejohn, DENX Software Engineering, <garyj@denx.de>
 *
 * SPDX-License-Identifier:	GPL-2.0
 */

OUTPUT_FORMAT("elf32-littlearm", "elf32-littlearm", "elf32-littlearm")
OUTPUT_ARCH(arm)
ENTRY(_start)
SECTIONS
{
	__boot_loc              =   0x1000;

	__experiment_code_loc   =   0x2000;
	__experiment_memory_loc = 0x100000;
	__experiment_memory_len =  0x40000;/* 32 * 1024 * 8 */


	. = __boot_loc;

	. = ALIGN(8);
	.text __boot_loc :
	{
		board/rpi2/src/entry.o (.text*)

		__experiment_code_loc_rel = __experiment_code_loc - __boot_loc;
		. = __experiment_code_loc_rel;
		KEEP(*(.experiment_code)) /* keep variable even if not referenced */

		*(.text*);
		*(.rodata*);
	}

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

	.experiment_memory __experiment_memory_loc :
	{
		_experiment_memory = . ;
		. += __experiment_memory_len ;/* 32 * 1024 * 8 */
	}

	/DISCARD/ : { *(.dynsym) }
	/DISCARD/ : { *(.dynstr*) }
	/DISCARD/ : { *(.dynamic*) }
	/DISCARD/ : { *(.plt*) }
	/DISCARD/ : { *(.interp*) }
	/DISCARD/ : { *(.gnu*) }
}
