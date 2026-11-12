#!/usr/bin/env python3
"""Check that the tables in Hashtree/GoGeneric.lean are those of sha256_1_generic.go."""
import os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
go = open(os.path.join(here, "..", "..", "sha256_1_generic.go")).read()
lean = open(os.path.join(here, "Hashtree", "GoGeneric.lean")).read()

def go_tab(name):
    m = re.search(r"var " + name + r" = \[\]uint32\{(.*?)\}", go, re.S)
    return [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", m.group(1))]

def lean_tab(name):
    m = re.search(r"def " + name + r" : List Word := \[(.*?)\]", lean, re.S)
    return [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", m.group(1))]

go_init = [int(x, 16) for x in re.findall(r"init\d = uint32\((0x[0-9A-Fa-f]+)\)", go)]
ok = True
for gname, lname, gv in [("_P", "Ptab", go_tab("_P")), ("_K", "Ktab", go_tab("_K")), ("init", "initTab", go_init)]:
    lv = lean_tab(lname)
    same = gv == lv and len(gv) > 0
    print(f"{gname:5} ({len(gv)} words) == {lname}: {same}")
    ok &= same
sys.exit(0 if ok else 1)
