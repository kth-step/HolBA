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

class z3_memory (object):
    def __init__(self, model):
        self.model    = model
        self.memory   = {}
        # This is equivalent to 0xFFFFFFF8 and it is used to find out the base address of a (8 bytes) memory address
        self.adr_mask = 4294967288 
        self.arg_size = 0

    # Update dictionary d2 with values in d1    
    def update(self, d1, d2):
        for k in d1.keys():
            d2[k] = d1[k]
        return d2
    
    def mk_memory_complete(self):
        # Deconstruct z3 model and convert it to a list
        model_as_list = self.model.as_list()
        # find out the value for the else statement for the memory in the z3 model
        else_value = model_as_list.pop()
        # This part relies on the result constructed by the "Function interpretation" in the z3_to_HolTerm function
        (mem_to_string, self.arg_size, self.vlu_size) = (z3_to_HolTerm(self.model))

        # Convert the result returned by z3_to_HolTerm into pairs of (address, value) where address and value are integers
        mem_to_intList = map (lambda x : tuple(int(el) for el in x.split(' ')), mem_to_string)
        # Convert the pairs of (address, value) into dictionary {address: value}
        mem_to_dict = dict(mem_to_intList)
        # Make complete the ranges of addresses in the returned model
        base_addresses = set(map(lambda x : (x & self.adr_mask), mem_to_dict.keys()))
    
        mem_full = {}
        for adr in base_addresses:
            for i in range(0,8):
                mem_full[adr + i] = else_value
        # update main dictionary
        self.memory = self.update(mem_to_dict, mem_full)

    '''
    The function is meant to convert memory in the model returned by  z3 to  HOL4 terms using words library.
    Before this conversion the function compelets(be invking mk_memory_complete) the range of memory assignments in the model using the value of the "else" statement.
    For exmaple [0 -> 23, 1-> 48, 4 -> 67, 6 -> 65, else -> 1] would be [0 -> 23, 1-> 48, 2 -> 1, 3 -> 1, 4 -> 67, 5 -> 1, 6 -> 65, 7 -> 1].
    This is important to not export wrong values.
    '''
    def mem_to_word(self):
        res = []
        self.mk_memory_complete()
        for k in self.memory.keys():
            res.append( "(({}w: {} word),({}w: {} word))".format(k, self.arg_size, self.memory[k], self.vlu_size))
        return ("(FEMPTY : word64 |-> word8) |+" + "|+".join(tm for tm in res ))


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
                # return "(FUN_MAP2 (K ({})) (UNIV))".format(expr)
                return "(FEMPTY : word64 |-> word8) |+" + "((BitVec: 64 word),({}: 8 word))".format(expr)

    # Function interpretation: Used for memory
    # Example the input [3 -> 0, 5 -> 0, 7 -> 0, 2 -> 0, 0 -> 20, 4 -> 0, 1 -> 0, 6 -> 0, else -> 0]
    # Will be turned into (['3 0', '5 0', '7 0', '2 0', '0 20', '4 0', '1 0', '6 0'], 64, 8)
    # Note that arg.size and vlu.size are in bits (I think)
    if isinstance(exp, z3.FuncInterp):
        res = []
        for idx in range(0, exp.num_entries()):
            arg = (exp.entry(idx)).arg_value(0)
            vlu = (exp.entry(idx)).value()
            res.append("{} {}".format(arg, vlu))
        return (res, arg.size(),vlu.size())

    raise NotImplementedError("Not handled: {} as {}".format(type(exp), exp))

# Python code t get difference of two lists 
# Using set() 
def Diff(li1, li2): 
    return (list(set(li1) - set(li2)))

# Dirty hack to fix the problem of memory stores when mem <> mem' 
def model_to_list(model):
    mem_list = []
    sml_list = []
    names = set()
    # search filters
    mem_check   = re.compile('MEM')
    array_check = re.compile('!')
    strip_name = lambda x: len(x.split('_', maxsplit=1)) > 1 and x.split('_', maxsplit=1)[1] or x.split('_', maxsplit=1)[0]
    def model_to_word (mdl):
        try:
            for (name, mvalue) in mdl:
                term = z3_to_HolTerm(mvalue)
            
                stripped_name = strip_name(name)
                if stripped_name in names:
                    raise AssertionError("Duplicated stripped name: {}".format(stripped_name))
                names.add(stripped_name)
                sml_list.append(stripped_name)
                sml_list.append(term)
            return sml_list
        except Exception as e:
            sys.exit(str(e))  # Print the message to stderr and exit with status 1

    
    # processing the model
    # Deconstruct the z3 model and create a list of pairs (model variables, variables value)
    model_2_list = sorted(list(map(lambda x: (str(x.name()), model[x]), model)))
    # filtering k!x maps
    kmap = list( filter (lambda x: array_check.search(str(x.name)), model) )

    # Get memory mappings from the model
    funcInterps = sorted([pair for pair in model_2_list if isinstance(pair[1], z3.FuncInterp)])
    funcInterps_mem = sorted([pair for pair in funcInterps if mem_check.search(pair[0])])
    # Find model register assignments
    model_regs = Diff(model_2_list, funcInterps)
    # Convert register and memory assignments to HOL4 words 
    sml_list = model_to_word(model_regs)    

    if len(kmap) > 0:
        list(map(lambda x : (sml_list.append(strip_name(x[0])), sml_list.append(z3_memory(x[1]).mem_to_word())), funcInterps_mem))     
    else:
        sml_list = model_to_word(model_2_list)

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
