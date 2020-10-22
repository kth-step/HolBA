#!/usr/bin/python2


import os
import sys



src_path = os.path.realpath("../../src")


# change to directory src
#os.chdir(src_path)

print "/*"

print src_path
print


#TODO Add more stuff here...
modules = ["aux",
           "shared",
           "shared/HolSmt",
           "theory/abstract_hoare_logic",
           "theory/bir",
           "theory/bir-support",
           "theory/models/l3mod",
           "theory/tools/comp",
           "theory/tools/lifter",
           "theory/tools/wp",
           "tools/cfg",
           "tools/lifter"]


def read_dep_file(filename):
	with open(filename) as f:
		content = f.readlines()

	content = [x.strip() for x in content]
	return content




def find_deps(module_name):
	print module_name
        print "------------------------"

	path = os.path.join(src_path, module_name)
	if not os.path.isdir(path):
		return ([],[])

	all_files = [f for f in map(lambda x: os.path.join(path, x),os.listdir(path)) if os.path.isfile(f)]
	dep_files = filter(lambda x: x.endswith(".uo") or x.endswith(".ui"), all_files)

	def remove_path(path, x):
		return x.replace(path+"/", "").replace(path, "")

	def remove_extensions_distinct(exts, l):
		return list(set(map(lambda x: reduce(lambda y,ext: y.replace(ext, ""), exts, x), l)))

	def group_by_module(l):
		temp = map(lambda x: os.path.split(x), l)

		result = map(lambda m: (m,map(lambda (_,x): x, filter(lambda (x, _): m == x, temp))), modules)
		result = filter(lambda (_,x): x != [], result)

		#DEBUG
		#for m in modules:
		#	print m
		#for t in temp:
		#	print t
		assert all(any(m_ == m for m in modules) for (m_,_) in temp)

		return result



	# module dependencies
	deps_l = map(read_dep_file, dep_files)
	deps = list(set([item for sublist in deps_l for item in sublist]))

	assert all((d.startswith(src_path) or d.startswith("$(HOLDIR)") or d.startswith(os.environ['HOLBA_HOL_DIR']) for d in deps))
	deps = map(lambda x: remove_path(src_path, x), filter(lambda x: x.startswith(src_path), deps))

	deps = map(lambda x: os.path.split(x)[0], deps)
	deps = filter(lambda x: x != module_name, deps)
	deps = list(set(deps))
	#print deps

	# lib and Theory dependencies
	dep_files_groups = remove_extensions_distinct([".uo", ".ui"], dep_files)
	dep_files_grouping = map(lambda x: (remove_path(path, x), filter(lambda x: os.path.isfile(x), [x+".uo",x+".ui"])), dep_files_groups)

	dep_lib = map(lambda (x,l): (x,map(read_dep_file, l)), dep_files_grouping)
	dep_lib = map(lambda (x,l): (x,list(set([item for sublist in l for item in sublist]))), dep_lib)
	dep_lib = map(lambda (x,l): (x,map(lambda x: remove_path(src_path, x), filter(lambda x: x.startswith(src_path), l))), dep_lib)
	dep_lib = map(lambda (x,l): (x,remove_extensions_distinct([".sml", ".sig"], l)), dep_lib)
        dep_lib = map(lambda (x,l): (x,filter(lambda y: y != os.path.join(module_name,x), l)), dep_lib)
	dep_lib = map(lambda (x,l): (x,group_by_module(l)), dep_lib)
	#print dep_lib

	print
	return (deps,dep_lib)



# find all dependencies
module_dependencies = map(lambda x: (x, find_deps(x)), modules)

(module_deps,lib_deps) = ([],[])
for (m,(d,d_l)) in module_dependencies:
	#print m
	#print "--------------"
	module_deps.append((m,d))
	lib_deps.append((m,d_l))

print module_deps

print "*/"
print
print





format_simple = """digraph L {
  node [shape=record fontname=Arial];

%s
%s
}
"""

def node_simple(i,str):
	return ("  n_%d [label=\"%s\"];" % (i, str))

def edge_simple(i,j):
	return ("  n_%d -> n_%d;" % (i,j))

def find_unique_idx(m):
	x = -1
	for i in range(len(module_deps)):
		m_ = module_deps[i][0]
		if x == -1:
			if m_ == m:
				x = i
		else:
			assert m_ != m
	return x

nodes = "\n".join(map(lambda (m,_): node_simple(find_unique_idx(m),m), module_deps))
#print nodes

edges = "\n".join(map(lambda (m,ds): "\n".join(map(lambda d: edge_simple(find_unique_idx(m),find_unique_idx(d)), ds)), module_deps))
#print edges


print_simple = False
if print_simple:
	print (format_simple % (nodes,edges))
	print
	print




#print lib_deps[0]

format_subgraph = """  subgraph cluster__%s {
    label = "%s";
    color = blue;

    node [style=filled];

%s
  }
"""

format_nested = """digraph G {

//  node [shape=record fontname=Arial];

%s

%s
}
"""

def escape_dot_name(x):
	return x.replace("/", "__").replace("-","_")

def node_nested(m,l):
	return ("    n__%s__%s [label=\"%s\"];" % (m, l, l))

def edge_nested(m1,l1,m2,l2):
	if m1 != m2 or l1.endswith("Syntax") or l1.endswith("selftest") or l1.endswith("Lib") or l1.endswith("Simps"):
		return ""
	m1_esc = escape_dot_name(m1)
	m2_esc = escape_dot_name(m2)
        return ("  n__%s__%s -> n__%s__%s;" % (m1_esc,l1,m2_esc,l2))

def cluster_nested(m,ls):
	m_esc = escape_dot_name(m)
	nodes = "\n".join(map(lambda l: node_nested(m_esc,l), ls))
	return (format_subgraph % (m_esc, m, nodes))


clusters = "\n".join(map(lambda (m,lds): cluster_nested(m,map(lambda (l,_): l, lds)), lib_deps))
#print nodes

edges = "\n".join(map(lambda (m1,lds): "\n".join(map(lambda (l1,mlds): "\n".join(map(lambda (m2,lds2): "\n".join(map(lambda l2: edge_nested(m1,l1,m2,l2), lds2)), mlds)), lds)), lib_deps))
#print edges

print (format_nested % (clusters,edges))
print
print



'''
digraph G {

	subgraph cluster_0 {
		style=filled;
		color=lightgrey;
		node [style=filled,color=white];
		a0 -> a1 -> a2 -> a3;
		label = "process #1";
	}

	subgraph cluster_1 {
		node [style=filled];
		b0 -> b1 -> b2 -> b3;
		label = "process #2";
		color=blue
	}
	start -> a0;
	start -> b0;
	a1 -> b3;
	b2 -> a3;
	a3 -> a0;
	a3 -> end;
	b3 -> end;

	start [shape=Mdiamond];
	end [shape=Msquare];
}
'''

