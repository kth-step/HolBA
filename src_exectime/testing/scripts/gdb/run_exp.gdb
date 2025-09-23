
# setup final breakpoint and exit procedure
b experiment_complete_marker
commands
delete
detach
quit
end

# jump to an entry point that resets the stack also
#j _embexp_entry
continue

# in case of interruption:
set confirm off
delete
detach
quit

