
MEMORY
{
    ram   (xrw) : org = 0x80000000, len = 16k
}
  
SECTIONS
{
    . = ORIGIN(ram);

    .text : 
    {
        board/arty_a7_100t__fe310/src/entry.o (.text*)
        KEEP (*(.experiment_code));
        *(.text*);
        *(.rodata*);
    } >ram

    .data : ALIGN(4)
    {
        *(.data*);
        *(.sdata*);
        . = ALIGN(8);
    } >ram AT>ram

    PROVIDE(_data_lma = LOADADDR(.data)); 
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

    __stack_pointer$ = 0x80000000 + 0x4000;
}

