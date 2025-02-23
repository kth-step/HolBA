# The HolBA tutorial

## Overview

The tutorial features verification of three examples:

* `add_reg`, a program that incrementally adds one register to another. This demonstrates the full HolBA workflow: from transpilation of an ARMv8 binary to BIR, to transfer of the BIR contract to ARMv8.
* `mutrec`, a program using mutually recursive functions to compute the parity of an integer.
* `freuse`, a program calling a function twice.

The different directories contain the different stages of verification (with `3-exec` and `8-symbexec` added in as bonus experiments). `7-composition` contains the theorems stating the final contracts.

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

Using the prepared VM, you don't need to worry about `autoenv.sh` and emacs configurations. The environment is prepared so that you can run `make`, `Holmake`, `rlwrap hol` and `emacs` from a terminal in the HolBA directories as needed. The most relevant HolBA directory is `~/tutorial/HolBA_tutorial/examples/tutorial`.

