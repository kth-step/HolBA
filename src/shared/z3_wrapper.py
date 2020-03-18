#!/usr/bin/env python3

import string
import sys
from z3 import *
import re


z3.set_param('model_compress', False)

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


def debug_input(solver):
    """ Used for debugging. This is SAT. """
    solver.from_string("""
        (declare-const mem0 (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const addr1 (_ BitVec 32))
        (declare-const addr2 (_ BitVec 32))

        (assert (= mem
            (store
                (store mem0
                (bvadd addr1 (_ bv0 32)) ((_ extract 7 0) (_ bv42 32)))
                (bvadd addr1 (_ bv1 32)) ((_ extract 15 8) (_ bv42 32)))
            ))

        (assert
            (and
                (= (select mem (bvadd addr2 (_ bv0 32))) ((_ extract 7 0) (_ bv42 32)))
                (= (select mem (bvadd addr2 (_ bv1 32))) ((_ extract 15 8) (_ bv42 32)))
            ))

        (assert (=
            mem0
            ((as const (Array (_ BitVec 32) (_ BitVec 8))) (_ bv0 8))))

        (assert (= addr1 addr2))

        (check-sat)
        (get-model)
    """)


def z3_to_HolTerm(exp):
    # assert(is_ast(exp))
    if is_expr(exp):
        # Function declaration
        if is_func_decl(exp):
            return ("func_decl({} {})".format(
                exp.name(),
                " ".join(z3_to_HolTerm(p) for p in exp.params())))

        # Predicates
        if is_and(exp):
            return "(%s)" % " /\\ ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_or(exp):
            return "(%s)" % " \\/ ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_implies(exp):
            return "(%s)" % " ==> ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_not(exp):
            return "(~(%s))" % z3_to_HolTerm(exp.arg(0))
        if is_eq(exp):
            return "(%s)" % " = ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_le(exp):
            return "(%s)" % " <= ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_lt(exp):
            return "(%s)" % " < ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_ge(exp):
            return "(%s)" % " >= ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_gt(exp):
            return "(%s)" % " > ".join(z3_to_HolTerm(p) for p in exp.children())

        # Binary expressions
        if is_add(exp):
            return "(%s)" % " + ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_mul(exp):
            return "(%s)" % " * ".join(z3_to_HolTerm(p) for p in exp.children())
        if is_sub(exp):
            return "(%s)" % " - ".join(z3_to_HolTerm(p) for p in exp.children())
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
            return "({}w: {} word)".format(exp, exp.size())
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
            if is_select(exp):
                return "(select %s)" % " ".join(z3_to_HolTerm(p) for p in exp.children())
            if is_store(exp):
                return "(store %s)" % " ".join(z3_to_HolTerm(p) for p in exp.children())
            if is_const_array(exp):
                if exp.num_args() != 1 and len(exp.children()) != 1:
                    raise NotImplementedError("Not handled: special constant array: {}".format(exp))
                #params = " ".join(string.ascii_lowercase[:exp.num_args()])
                expr = ", ".join(z3_to_HolTerm(p) for p in exp.children())
                return "(FUN_MAP2 (K ({})) (UNIV))".format(expr)
    res = []
    for idx in range(0,exp.num_entries()):
        arg = (exp.entry(idx)).arg_value(0)
        vlu = (exp.entry(idx)).value()
        res.append( "(({}w: {} word),({}w: {} word))".format(arg, arg.size(),vlu, vlu.size()))
    return ("(FEMPTY : word64 |-> word8) |+" + "|+".join(t for t in res ))
              
    raise NotImplementedError("Not handled: {} as {}".format(type(exp), exp))


def model_to_list(model):
    sml_list = []
    names = set()
    string_check= re.compile('!')
    for x in model:
        name = str(x.name())
        if(string_check.search(name) != None):
            continue   
        term = z3_to_HolTerm(model[x])
        stripped_name = name.split('_', maxsplit=1)[1]
        if stripped_name in names:
            raise AssertionError("Duplicated stripped name: {}".format(stripped_name))
        names.add(stripped_name)

        sml_list.append(stripped_name)
        sml_list.append(term)

    return sml_list


def main():
    use_files = len(sys.argv) > 1
    
    s = Solver()
    # debug_input(s)
    if use_files:
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
        print(s.model(), file=sys.stderr)

    model = s.model()
    hol_list = model_to_list(model)

    for line in hol_list:
        print(line)
        #print("on stdout: {}".format(line), file=sys.stderr)


if __name__ == '__main__':
    main()
