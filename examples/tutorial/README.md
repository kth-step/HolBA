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

### Some useful keyboard shortcuts for Emacs
It is usually nice to split the Emacs frame into two windows side-by-side: one where you look at some file you are editing, and one where you have the HOL4 REPL. Do this using

<kbd>Ctrl</kbd>+<kbd>x</kbd>, <kbd>3</kbd> (to split the frame)

<kbd>Ctrl</kbd>+<kbd>x</kbd>, <kbd>o</kbd> (to switch window inside the frame)

<kbd>Alt</kbd>+<kbd>h</kbd>, <kbd>h</kbd> (to start the HOL4 REPL)

Now switch back to the window with your code. Mark some code, then press

<kbd>Alt</kbd>+<kbd>h</kbd>, <kbd>Ctrl</kbd>+<kbd>r</kbd> (to suppress output - indispensable when opening theories)

<kbd>Alt</kbd>+<kbd>h</kbd>, <kbd>Alt</kbd>+<kbd>r</kbd> (to not suppress output - when you want to see what values you assigned)

to send it to the HOL4 REPL.

A lot people are unused to Emacs keyboard bindings for copying and pasting. To bind these to the regular CUA shortcuts, press

<kbd>Alt</kbd>+<kbd>x</kbd>

then write `cua-mode` and press <kbd>Enter</kbd>.

## HolBA-tutorial VM

Using the prepared VM, you don't need to worry about `autoenv.sh` and emacs configurations. The environment is prepared so that you can run `make`, `Holmake`, `rlwrap hol` and `emacs` from a terminal in the HolBA directories as needed. The most relevant HolBA directories are `~/tutorial/HolBA_tutorial/examples/tutorial` and `~/tutorial/HolBA_scamv/src/tools/scamv`.

