#!/usr/bin/env python3

import string
import sys
from z3 import *

def model_compress_string():
    major,minor,build,rev = z3.get_version()
    result = ""
    if major >= 4 and ((not (major == 4)) or minor >= 8) and ((not (major == 4 and minor == 8)) or build >= 7):
        result = "model.compact"
    else:
        result = "model_compress"
    return result

# turn z3 model compression/compacting off
z3.set_param(model_compress_string(), False)

""" Z3 wrapper for HOL4.

Usage: script.py
       script.py input-file

This script uses Z3's Python module. To use a Z3 at a custom location, you can
set the following environment variables:
 - PYTHONPATH=/path/to/z3/build/python:$PYTHONPATH
 - LD_LIBRARY_PATH=/path/to/z3/build:$LD_LIBRARY_PATH

This script uses Z3 to get the verdict on the given instance. It then prints
the result on stdout. The first line will contains "sat", "unsat" or "unknown"
depending on Z3's verdict.

If the verdict is SAT, then the model will follow:
 - two lines per variable in the model
 - variable name on the first line
 - corresponding HOL4 term on the following line
 - both are printed without quotation marks (neither " nor ``)

If the script fails, check stderr for details.
"""

# example input that can be used for debugging, should return a proper model if used as input
def debug_input(solver):
    # TODO: build test cases from input files

    # used for debugging: input1 and input2 are SAT
    filename = "examples/z3_wrapper_test/z3_wrapper_input2"

    with open(filename) as f:
        input_str = f.read()

    solver.from_string(input_str)

# convert a z3 model expression recursively to a hol term string
def z3_ast_to_HolTerm(exp):
    assert(is_ast(exp))

    if is_expr(exp):
        # Function declaration
        if is_func_decl(exp):
            return ("func_decl({} {})".format(
                exp.name(),
                " ".join(z3_ast_to_HolTerm(p) for p in exp.params())))

        # Predicates
        if is_and(exp):
            return "(%s)" % " /\\ ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_or(exp):
            return "(%s)" % " \\/ ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_implies(exp):
            return "(%s)" % " ==> ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_not(exp):
            return "(~(%s))" % z3_ast_to_HolTerm(exp.arg(0))
        if is_eq(exp):
            return "(%s)" % " = ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_le(exp):
            return "(%s)" % " <= ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_lt(exp):
            return "(%s)" % " < ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_ge(exp):
            return "(%s)" % " >= ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_gt(exp):
            return "(%s)" % " > ".join(z3_ast_to_HolTerm(p) for p in exp.children())

        # Binary expressions
        if is_add(exp):
            return "(%s)" % " + ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_mul(exp):
            return "(%s)" % " * ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_sub(exp):
            return "(%s)" % " - ".join(z3_ast_to_HolTerm(p) for p in exp.children())
        if is_div(exp):
            raise NotImplementedError("is_div")
        if is_idiv(exp):
            raise NotImplementedError("is_idiv")
        if is_mod(exp):
            raise NotImplementedError("is_mod")

        # Literals
        if is_true(exp):
            return "(T: bool)"
        if is_false(exp):
            return "(F: bool)"
        if is_bv_value(exp):
            # TODO: can we avoid string reparsing? (this reparse pattern occurs in several other places in this script)
            return "(0x{:X}w: {} word)".format(int(str(exp)), exp.size())
        if is_int_value(exp):
            return "({}: int)".format(exp)
        if is_rational_value(exp):
            raise NotImplementedError("is_rational_value")
        if is_algebraic_value(exp):
            raise NotImplementedError("is_algebraic_value")
        if is_string_value(exp):
            return "\"{}\"".format(exp)

        # Arrays
        if is_array(exp):
            # "select (children[0-1])"
            if is_select(exp):
                args = [z3_ast_to_HolTerm(p) for p in exp.children()]
                assert(len(args) == 2)
                return "(FAPPLY ({}) ({}))".format(args[0], args[1])

            # "store (children[0-2])"
            if is_store(exp):
                args = [z3_ast_to_HolTerm(p) for p in exp.children()]
                assert(len(args) == 3)
                return args[0] + " |+ " + "({}, {})".format(args[1], args[2])

            # "K (domain, children[0])"
            if is_const_array(exp):
                if exp.num_args() != 1 and len(exp.children()) != 1:
                    raise NotImplementedError("Not handled: special constant array: {}".format(exp))
                child = exp.children()[0]

                sz_arg = exp.domain().size()
                sz_vlu = child.size()
                return "(FUN_FMAP (K ({})) (UNIV) : {} word |-> {} word)".format(z3_ast_to_HolTerm(child), sz_arg, sz_vlu)

    raise NotImplementedError("Not handled: {} as {}".format(type(exp), exp))

# convert z3 "function interpretation" to finite_map
def z3_funcint_to_HolTerm(funcint):
    assert(isinstance(funcint, z3.FuncInterp))
    # convert memory in the model returned by  z3 to  HOL4 terms using words library.
    # Before this conversion the function completes(be invking mk_memory_complete) the range of
    #   memory assignments in the model using the value of the "else" statement.
    # For exmaple [0 -> 23, 1-> 48, 4 -> 67, 6 -> 65, else -> 1] would be [0 -> 23, 1-> 48, 2 -> 1, 3 -> 1, 4 -> 67, 5 -> 1, 6 -> 65, 7 -> 1].
    # This is important to not export wrong values.

    # Deconstruct z3 model and convert it to a list
    model_as_list = funcint.as_list()
    else_value = funcint.else_value()
    # find out the default value of the z3 function interpretation
    default_value = int(str(model_as_list.pop()))
    assert(else_value == default_value)

    # Function interpretation: Used for memory
    # Example the input [3 -> 0, 5 -> 0, 7 -> 0, 2 -> 0, 0 -> 20, 4 -> 0, 1 -> 0, 6 -> 0, else -> 0]
    # Will be turned into (['3 0', '5 0', '7 0', '2 0', '0 20', '4 0', '1 0', '6 0'], 64, 8)
    # Note that arg.size and vlu.size are in bits (I think)
    def funcinterp_collect(exp):
        res = []
        sz_arg = None
        sz_vlu = None
        for idx in range(0, exp.num_entries()):
            arg = (exp.entry(idx)).arg_value(0)
            vlu = (exp.entry(idx)).value()

            if sz_arg == None:
                sz_arg = arg.size()
                sz_vlu = vlu.size()
            else:
                assert(sz_arg == arg.size())
                assert(sz_vlu == vlu.size())

            res.append((int(str(arg)), int(str(vlu))))
        assert(sz_arg != None)
        assert(sz_vlu != None)
        return (res, sz_arg, sz_vlu)

    # Convert the pairs of (address, value) into dictionary {address: value}
    (mem_to_intList, arg_size, vlu_size) = (funcinterp_collect(funcint))
    #mem_to_dict = dict(mem_to_intList)

    # construct the hol term from the memory map
    res = []
    for (addr,val) in mem_to_intList:
        res.append("(0x{:X}w, 0x{:X}w)".format(addr, val))
    else_value_word_str = "(0x{:X}w: {} word)".format(int(str(default_value)), vlu_size)
    return ("(FUN_FMAP (K ({})) (UNIV) : {} word |-> {} word) |+ ".format(else_value_word_str, arg_size, vlu_size) + " |+ ".join(tm for tm in res ))


def z3_assign_to_HolTerm(assign):
        (stripped_name, mvalue) = assign

        # process the assignment
        if is_ast(mvalue):
            term = z3_ast_to_HolTerm(mvalue)
        elif isinstance(mvalue, z3.FuncInterp):
            term = z3_funcint_to_HolTerm(mvalue)
        else:
            raise Exception("unknown assignment type. can only handle some of z3 AST expressions and function interpretations")

        # append the result as pair again
        return (stripped_name, term)

# function to convert z3 variable names to hol names
def strip_z3_name(x):
    return len(x.split('_', maxsplit=1)) > 1 and x.split('_', maxsplit=1)[1] or x.split('_', maxsplit=1)[0]

# create list of string pairs from model: (varname, holterm)
def model_to_list(model):
    # map to pair (model variables (stripped hol name), variables value) and filter auxiliary assignments
    assigns_pre = filter (lambda x: not ("!" in x[0]), map(lambda x: (strip_z3_name(str(x.name())), model[x]), model))

    # partition, sort individually, put together again
    assign_ast = []
    assign_oth = []
    for x in assigns_pre:
        (assign_ast if is_ast(x[1]) else assign_oth).append(x)
    assigns = sorted(assign_ast) + sorted(assign_oth)

    # finally, map to hol terms
    sml_list = list(map(z3_assign_to_HolTerm, assigns))

    # check for duplicate names
    names = set()
    for (name,_) in sml_list:
        if name in names:
            raise AssertionError("Duplicated stripped name: {}".format(name))
        names.add(name)

    # return the collected hol assignments
    return sml_list

# script entry point
def main():
    use_files = len(sys.argv) > 1
    s = Solver()

    do_debug = False
    if do_debug:
        debug_input(s)
    elif use_files:
        s.from_file(sys.argv[1])
    else:
        stdin = "\n".join(sys.stdin.readlines())
        s.from_string(stdin)

    r = s.check()
    if r == unsat:
        print("unsat")
        exit(0)
    elif r == unknown:
        print("unknown")
        print("failed to prove", file=sys.stderr)
        print(s.model(), file=sys.stderr)
        exit(0)
    else:
        print("sat")
        #print(s.model(), file=sys.stderr)

    model = s.model()
    hol_list = model_to_list(model)

    for (varname, term) in hol_list:
        print(varname)
        print(term)
        #print("on stdout: {}".format(line), file=sys.stderr)


if __name__ == '__main__':
    main()
