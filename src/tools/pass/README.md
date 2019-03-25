This is a non-proof producing tool for passification of BIR programs into passified SSA form.

For example, if you have the file `aesfragment.bir` in the subdirectory `examples`, you would do the following to obtain it in passified form:

```
val bir_prog_tm = bir_prog_rff "examples/aesfragment.bir"
val bir_prog_pass_tm = bir_prog_pass_ssa bir_prog_tm
```

and then perhaps save the result in its own file:

```
val _ = bir_prog_wtf "examples/aesfragmentpassified.bir" bir_prog_pass_tm
```
