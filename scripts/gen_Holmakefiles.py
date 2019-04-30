#!/usr/bin/env python2

""" Holmakefile generator.

This script generates `Holmakefile` files from `Holmakefile.gen` files, in
order to add support for inclusion.

Syntax:
    Lines beginning with `include ` will be replaced by the content of all
    files whose paths follow on the line, in the order they appear on the line.

    For example,

        include ../Holmakefile /some/other/file

    will be replaced by the content of `../Holmakefile` first, then the content
    of `/some/other/file`.
"""

from __future__ import print_function
import sys
import os

out_filename = "Holmakefile"
gen_filename = out_filename + ".gen"

src_root = "./src"


def gen_holmakefile_in(dir_path):
    """ Generates a `Holmakefile` from the `Holmakefile.gen` file present in
        dir_path.
    """

    out_path = os.path.join(dir_path, out_filename)
    gen_path = os.path.join(dir_path, gen_filename)

    assert os.path.isfile(gen_path), \
        "Cannot generate '{}': missing '{}'.".format(out_path, gen_path)

    print("Generating: {}".format(out_path))

    result = ""
    with open(gen_path) as gen_file:
        for line in gen_file:
            if line.startswith("include "):
                files_to_include = map(str.strip, line.split(" ")[1:])
                for inc_path in files_to_include:
                    inc_path = os.path.join(dir_path, inc_path)
                    assert os.path.isfile(inc_path), \
                        "Cannot include '{}': invalid path.".format(inc_path)
                    with open(inc_path) as inc_file:
                        result += "".join(inc_file.readlines())
            else:
                result += line

        with open(out_path, 'w') as f:
            f.write(result)


def main():
    argc = len(sys.argv)
    if len(sys.argv) == 1:  # Working in `src_root/`
        print("Recursively working in: {}".format(src_root))

        dir_paths = []
        for path, subdirs, files in os.walk(src_root):
            for f in files:
                if f == gen_filename:
                    dir_paths.append(path)

        for dir_path in dir_paths:
            gen_holmakefile_in(dir_path)

    elif argc == 2:  # Working in the given directory
        path = sys.argv[1]
        dir_path = os.path.dirname(os.path.abspath(path))

        # print("Working in: {}".format(dir_path))
        gen_holmakefile_in(dir_path)

    else:
        print("Invalid invocation.\nUsage: {} [directory]".format(
            sys.argv[0]), file=sys.stderr)


main()
