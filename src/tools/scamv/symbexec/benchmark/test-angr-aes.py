#!/usr/bin/env python3

import angr
import timeit

replacements = {}

def fix_exit(state):
    if state.inspect.exit_jumpkind == 'Ijk_NoDecode':
        state.inspect.exit_jumpkind = 'Ijk_Exit'

def mem_read_after(state):
    print("\nMEM READ AFTER")
    print("IP", state.ip)
    print(state.inspect.mem_read_address)
    print(state.inspect.mem_read_expr)

    if state.inspect.mem_read_expr.symbolic and state.inspect.mem_read_expr.uninitialized:
        mem_addr = state.inspect.mem_read_address
        mem_ast_set = set()

        if state.inspect.mem_read_expr.op == "BVS" and state.inspect.mem_read_expr.args[0].startswith("mem_"):
            mem_ast_set.add(state.inspect.mem_read_expr)
        else:
            iterator_ast = state.inspect.mem_read_expr.children_asts()
            while True:
                try:
                    subast = iterator_ast.__next__()
                except StopIteration:
                    break
                else:
                    if subast.op == "BVS" and subast.args[0].startswith("mem_"):
                        mem_ast_set.add(subast)

        for mem_ast in mem_ast_set:
            if not mem_ast.cache_key in replacements:
                mem_var = claripy.BVS(f"MEM[{mem_addr}]", mem_ast.length)
                replacements[mem_ast.cache_key] = mem_var
                mem_expr_constraint = mem_var == mem_ast
                state.add_constraints(mem_expr_constraint)

        #print("\n", replacements, "\n")
        state.inspect.mem_read_expr = state.inspect.mem_read_expr.replace_dict(replacements)

    print(state.inspect.mem_read_expr)
    print()

def mem_write_after(state):
    print("\nMEM WRITE AFTER")
    print("IP", state.ip)
    print(state.inspect.mem_write_address)
    print(state.inspect.mem_write_expr)

def address_concretization_after(state):
    print("_"*100)
    print("\nADDRESS CONCRETIZATION AFTER")
    print("IP", state.ip)
    print(state.inspect.address_concretization_expr)
    print(state.inspect.address_concretization_strategy)
    print(state.inspect.address_concretization_result)
    #print(state.solver.constraints)
    print("UNSAT")
    print(state.solver.unsat_core())





######################### START #########################

proj = angr.Project("/home/tiziano/scamv/HolBA/src/tools/angr/python/aes.out", load_options={'auto_load_libs' : False}) #main_opts={'base_addr': 0} 
#lbl = proj.loader.find_symbol('lbl_0x00400570')
#print(lbl)


state = proj.factory.entry_state(addr=0x406460) #addr=0x400570

state.options.add(angr.options.LAZY_SOLVES)
state.options.add(angr.options.CONSERVATIVE_READ_STRATEGY)
state.options.add(angr.options.CONSERVATIVE_WRITE_STRATEGY)
state.options.add(angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY)
state.options.add(angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS)
state.options.add(angr.options.CONSTRAINT_TRACKING_IN_SOLVER)

'''
import claripy
state.regs.x0 = claripy.BVS("R0", 64)
state.regs.x1 = claripy.BVS("R1", 64)
state.regs.x2 = claripy.BVS("R2", 64)
state.regs.x3 = claripy.BVS("R3", 64)
state.regs.x4 = claripy.BVS("R4", 64)
state.regs.x5 = claripy.BVS("R5", 64)
state.regs.x6 = claripy.BVS("R6", 64)
state.regs.x7 = claripy.BVS("R7", 64)
state.regs.x8 = claripy.BVS("R8", 64)
state.regs.x9 = claripy.BVS("R9", 64)
state.regs.x10 = claripy.BVS("R10", 64)
state.regs.x11 = claripy.BVS("R11", 64)
state.regs.x12 = claripy.BVS("R12", 64)
state.regs.x13 = claripy.BVS("R13", 64)
'''

#state.inspect.b('irsb')
state.inspect.b('exit', when=angr.BP_BEFORE, action=fix_exit)
#state.inspect.b('mem_read', when=angr.BP_AFTER, action=mem_read_after)
#state.inspect.b('mem_write', when=angr.BP_AFTER, action=mem_write_after)
#state.inspect.b('address_concretization', when=angr.BP_AFTER, action=address_concretization_after)


simgr = proj.factory.simulation_manager(state)

cfg = proj.analyses.CFGFast(normalize=True)
simgr.use_technique(angr.exploration_techniques.LoopSeer(cfg=cfg, functions=None, bound=1))
loop_finder = proj.analyses.LoopFinder()
print(loop_finder.loops)


simgr.explore(avoid=[0x406864, 0x406894, 0x40689c])
#time = timeit.Timer(simgr.explore).timeit(number=1)
#print("\n\nTIME: {}".format(time))







######################### RESULT #########################
print("\n\n")
print(f"RESULT: {simgr}")
print("-"*80)
print("ERRORED STATES:", simgr.errored)

simgr_states = [(name, ls) for name, ls in simgr._stashes.items() if len(ls) != 0 and name != 'errored']
for name, final_states in simgr_states:
    print("-"*80)
    print(len(final_states), name)
    for state in final_states:
        print("="*80)
        print("STATE:", state)
        # is a listing of the basic block addresses executed by the state.
        list_addrs = state.history.bbl_addrs.hardcopy
        # converts addresses from decimal to hex
        list_addrs = list(map(lambda value: hex(value), list_addrs))
        print("\t- Path:", ''.join("\n\t\t{0}".format(addr) for addr in list_addrs))
        print("\t- Guards:", ''.join("\n\t\t{0}".format(str(g)) for g in state.history.jump_guards.hardcopy))
        print("\t- State Constraints:", ''.join("\n\t\t\t{0}".format(str(sc)) for sc in state.solver.constraints))
        print("="*80)
        '''print("Number of blocks:", len(list_addrs))
        for addr in list_addrs:
            irsb = proj.factory.block(addr=int(addr, 16))
            print("Number of instructions:", irsb.instructions)
            irsb.pp()'''

