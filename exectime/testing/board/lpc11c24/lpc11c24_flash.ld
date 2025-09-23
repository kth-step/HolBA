MEMORY
{
    flash (rx)  : org = 0x00000000, len = 32k
    ram   (xrw) : org = 0x10000000, len = 8k
}
  
SECTIONS
{
	. = ORIGIN(flash);
        .text : 
        {
                FILL(0xff)
                KEEP (*(.isr_vector));
                KEEP (*(.after_vectors));
		KEEP(*(.experiment_code));
                *(.text*);
                *(.rodata*);
                . = ALIGN(4);
        } >flash
        
	. = ORIGIN(ram);
        .data : ALIGN(4)
        {
                *(.data*);
                *(.sdata*);
                . = ALIGN(8);
        } >ram AT>flash

        PROVIDE(_etext = LOADADDR(.data));
        PROVIDE(_data = ADDR(.data));
        PROVIDE(_edata = ADDR(.data) + SIZEOF(.data));

        .bss : ALIGN(4)
        {
                *(.bss*);
                *(.sbss*);
                . = ALIGN(8);
        } > ram

        PROVIDE(_bss = ADDR(.bss));
        PROVIDE(_ebss = ADDR(.bss) + SIZEOF(.bss));
        PROVIDE(__bss_start__ = ADDR(.bss));
        PROVIDE(__bss_end__ = ADDR(.bss) + SIZEOF(.bss));

	_vStackTop = 0x10000000 + 0x2000 -16;
}
