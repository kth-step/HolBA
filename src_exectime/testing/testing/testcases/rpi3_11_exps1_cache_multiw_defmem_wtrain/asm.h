
	// always load first, seems to be needed
	ldr x22, [x12]

	// load the default memory value somewhere
	ldrb w10, [x0, #5]

	// skip the second load if we have the magic default memory value
	cmp x10, x20
	b.eq magic_skip_label

	// for experimenting with blocking the speculative load (seem to need two in this case)
	//add x27,x27,x27
	//add x27,x27,x27

	// speculative access
	ldr x21, [x11]

magic_skip_label:
	// done

