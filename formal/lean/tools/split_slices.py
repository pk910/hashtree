"""Split generated slice files P{c}.lean into D{c}.lean (cut definitions K{c+1}, L{c+1}, T{c}) and P{c}.lean
(slice check, lemmas, step), so that the P files only import D files and build in parallel."""
import sys, os, re
d, ns = sys.argv[1], sys.argv[2]
ps = sorted(int(m.group(1)) for f in os.listdir(d) for m in [re.match(r"P(\d+)\.lean$", f)] if m)
for c in ps:
    p = f"{d}/P{c}.lean"
    s = open(p).read()
    if f"import {ns}.D{c}\n" in s: continue
    head_end = s.index(f"namespace {ns}\n") + len(f"namespace {ns}\n")
    head = s[:head_end]
    imports = [l for l in head.split("\n") if l.startswith("import ")]
    rest = head[len("\n".join(imports)):]
    base_imports = [l for l in imports if not l.startswith(f"import {ns}.")]
    i_slice = s.index(f"theorem slice{c} ")
    defs = s[head_end:i_slice]
    body = s[i_slice:]
    dtext = "\n".join(base_imports) + rest + defs + f"end {ns}\n"
    pimps = base_imports + ([f"import {ns}.D{c-1}"] if c > 0 else []) + [f"import {ns}.D{c}"]
    ptext = "\n".join(pimps) + rest + body
    open(f"{d}/D{c}.lean", "w").write(dtext)
    open(p, "w").write(ptext)
f = f"{d}/Final.lean"
s = open(f).read()
lines = s.split("\n")
lines = [l for l in lines if not l.startswith(f"import {ns}.")]
s = "\n".join([f"import {ns}.P{c}" for c in ps] + lines)
open(f, "w").write(s)
print("split", len(ps))
