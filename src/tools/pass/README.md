This is a non-proof producing tool for passification of BIR programs into passified SSA form.

For example, if you have the file `aesfragment.bir` in the subdirectory `examples`, you would do the following:

```
val bir_prog_tm = bir_prog_rff "examples/aesfragment.bir"
val bir_prog_pass_tm = passify_prog_ssa bir_prog_tm
```

and then save the result in its own file:

```
val _ = bir_prog_wtf "examples/aesfragmentpassified.bir" bir_prog_pass_tm
```
