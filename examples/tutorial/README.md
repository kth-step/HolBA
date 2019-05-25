# The HolBA tutorial with `add_reg`

## Overview

A diagram of the tutorial flow with theorem connections/relations goes here.

A diagram of the binary control flow goes here.

## Build system

You may use the following commands:

* `make` to build all tutorials
* `make {DIRNAME}` to build the directory `{DIRNAME}`, e.g. `make 3-exec`
* `make cleantutorial` to remove all temporary files
* `make reverttutorial` to remove and revert all files (warning: all development in the tutorial will be lost!)


## Working interactively

1. Prepare your terminal with `source {HOLBA_DIR}/scripts/setup/autoenv.sh`
2. In the directory with a code file of interest, run either
  * `rlwrap hol`, or
  * `emacs` (your `~/.emacs` file has to be prepared for the hol-mode, see `{HOLBA_DIR}/scripts/setup/config.emacs`)


## HolBA-tutorial VM

Using the prepared VM, you don't need to worry about `autoenv.sh` and emacs configurations. The environment is prepared so that you can run `make`, `Holmake`, `rlwrap hol` and `emacs` from a terminal in the HolBA directories as needed. The most relevant HolBA directories are `~/tutorial/HolBA_tutorial/examples/tutorial` and `~/tutorial/HolBA_scamv/src/tools/scamv`.

