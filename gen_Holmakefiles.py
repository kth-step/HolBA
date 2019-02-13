#!/usr/bin/python


import sys,os


out_filename = "Holmakefile"
gen_filename = out_filename + ".gen"

root         = "./src"

gen_files = []
for path, subdirs, files in os.walk(root):
  for f in files:
    if f == gen_filename:
      gen_files.append(path)

for p_d in gen_files:
  p     = os.path.join(p_d, out_filename)
  p_gen = os.path.join(p_d, gen_filename)

  print p

  result = ""
  with open(p_gen) as f_gen:
    for line in f_gen:
      if line.startswith("-include "):
        l_inc = line.split(" ")
        assert(len(l_inc) == 2)
        p_inc = os.path.join(p_d, l_inc[1].strip())
        assert(os.path.isfile(p_inc))
        with open(p_inc) as f_inc:
          line = "".join(f_inc.readlines())

      result = result + line

  with open(p, 'w') as f:
    f.write(result)


