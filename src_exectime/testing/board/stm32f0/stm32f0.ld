SECTIONS
{
	.text 0x08000000: {
		*(isrv_sys); /* Interrupt Service Routine Vector - System */
		*(isrv_irq); /* Interrupt Service Routine Vector - Peripherals IRQs */
		. = 0x000000C0;
		KEEP(*(.experiment_code));
		EXCLUDE_FILE (*/libgcc.a */pid.o */otherbenchs.o */morebenchs_asm.o */morebenchs.o) *(.text*);
    . = 0x000004000;
    *libgcc.a:*(*); /* .text* .text.* */
    . = 0x000006000;
    */pid.o (.text*)
    . = 0x000007000;
    */otherbenchs.o (.text*)
    . = 0x000008000;
    */morebenchs_asm.o (.text*)
    . = 0x000009000;
    */morebenchs.o (.text*)
	}

	. = ALIGN(16);
	.etext = .;

	.rodata : {
		*(.rodata)
	}

	. = ALIGN(16);
	_erom = .;

	.data 0x20000000: AT (_erom) {
		_sdata_flash = LOADADDR(.data);
		_sdata = .;
		*(.data*);
	  _edata = .;
	}

	.bss : {
		. = ALIGN(16);
		_sbss = .;
		*(.bss*);
		. = ALIGN(16);
	  _ebss = .;
	}
}
