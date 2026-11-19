#!/usr/bin/env python3
"""Generate the W-mode (wrapper call state) body proofs of the windows avx2_x8 kernel, per residue.

The pilot `Hashtree/Gen/WinAvx2X8P` checks the windows kernel at count 8 from `entrySW 24`.  At
the wrapper's call state the frame sits at the alignment residue `r = (σ 9 - 16) % 32`
(`Hashtree/Proofs/WinAvx2X8WShift`), and `WinAvx2X8W.shiftK8 r` rebases a pilot cut on it.
This script emits, for one residue `r` (8 or 24, the residues the wrapper ABI allows):

  Hashtree/Proofs/WinAvx2X8WBodyR{r}P{1..4}.lean  the 208 body slices 3..210 re-checked at the
                                                   rebased cuts (`decide +kernel`), four files
  Hashtree/Proofs/WinAvx2X8WBodyR{r}.lean          the environment chain and the composed first
                                                   pass `body_runW` / `body_memW` (from the
                                                   rebased loop head `K3` to the rebased `K211`)

and with --pass2 the later-pass files on the stripped cuts (`WinAvx2X8WStrip.stripK8 r`, push
memory `m8P r`):

  Hashtree/Proofs/WinAvx2X8WBodyR{r}S{1..4}.lean  slices 6..210 (the head slices 3, 4, 5 run
                                                   from the replayed cuts `KHs`/`KH4s`/`KH5s`
                                                   and are part of `stripOk r`)
  Hashtree/Proofs/WinAvx2X8WBodyR{r}S.lean         `bodyS_runW` / `bodyS_memW`

Usage:  python3 tools/winx8w.py <r> [--pass2]

The slice lengths and tree lists are read from the pilot files; no new `decide` is introduced
beyond the per-slice re-checks.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN = os.path.join(ROOT, "Hashtree", "Gen", "WinAvx2X8P")
PROOFS = os.path.join(ROOT, "Hashtree", "Proofs")

HEADER = """set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinAvx2X8W
"""

FIRST, LAST = 3, 210          # body slices K3 -> K211
PARTS = 4
BODYLEN = 6039


def read_slices():
    pat = re.compile(r"theorem slice(\d+) : sliceCheck prog 4 m0q \(fun pc => decide \(pc ∈ "
                     r"\((\[[0-9, ]*\]) : List Nat\)\)\) (\d+) K(\d+) K(\d+) T(\d+)")
    slices = {}
    for name in os.listdir(GEN):
        if not (name.startswith("P") and name.endswith(".lean")):
            continue
        for m in pat.finditer(open(os.path.join(GEN, name)).read()):
            j = int(m.group(1))
            slices[j] = dict(orc=m.group(2), n=int(m.group(3)), k0=int(m.group(4)),
                             k1=int(m.group(5)), t=int(m.group(6)))
    for j in range(FIRST, LAST + 1):
        s = slices[j]
        assert s["orc"] == "[]" and s["k0"] == j and s["k1"] == j + 1 and s["t"] == j, (j, s)
    assert sum(slices[j]["n"] for j in range(FIRST, LAST + 1)) == BODYLEN
    return slices


def rsum(ns):
    if len(ns) == 1:
        return str(ns[0])
    return "%d + (%s)" % (ns[0], rsum(ns[1:]))


def part_ranges(first):
    n = LAST - first + 1
    per = (n + PARTS - 1) // PARTS
    out = []
    j = first
    while j <= LAST:
        out.append((j, min(j + per - 1, LAST)))
        j += per
    return out


def chain(a, G, mem, kq, h0name, start, cuts, slices, total, theo, memtheo, doc, memdoc):
    """cuts: list of (j, cutname_j, cutname_{j+1}, slicethm) for j in the pass."""
    a.append(f"""{doc}
theorem {theo} (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel ({G}{FIRST} env1) σ {mem} mem0c) (hge : 8 ≤ σ 2) :
    run prog 4 mem0c orcC BODYLEN (mapState ({G}{FIRST} env1) σ ({start})) =
      mapState ({G}{LAST + 1} env1) σ ({cuts[-1][2]}) := by
  rw [show BODYLEN = ({total}) from rfl]
  have kq : MemKeyed {mem} := {kq}
  have hm{FIRST} : Mem0Rel ({G}{FIRST} env1) σ {mem} mem0c := h0""")
    for j in range(FIRST, LAST + 1):
        a.append(f"  have hm{j + 1} : Mem0Rel ({G}{j + 1} env1) σ {mem} mem0c := "
                 f"mem0Rel_envAbs _ σ _ mem0c kq hm{j} _")
    for (j, c0, c1, thm) in cuts:
        n = slices[j]["n"]
        a.append(f"  have r{j} : run prog 4 mem0c orcC {n} (mapState ({G}{j} env1) σ ({c0})) = "
                 f"mapState ({G}{j + 1} env1) σ ({c1}) := "
                 f"(slice_sound ({G}{j} env1) σ {mem} mem0c hm{j} prog 4 orcB orcC {n} ({c0}) "
                 f"({c1}) T{j} {thm} rfl (assumeOk_of σ ({c1}) A0 rfl (asmge σ hge))).1")
    for j in range(FIRST, LAST):
        a.append(f"  rw [run_add, r{j}]")
    a.append(f"  exact r{LAST}\n")
    a.append(f"""{memdoc}
theorem {memtheo} (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (h0 : Mem0Rel ({G}{FIRST} env1) σ {mem} mem0c) : Mem0Rel ({G}{LAST + 1} env1) σ {mem} mem0c := by
  have kq : MemKeyed {mem} := {kq}
  have hm{FIRST} : Mem0Rel ({G}{FIRST} env1) σ {mem} mem0c := h0""")
    for j in range(FIRST, LAST + 1):
        a.append(f"  have hm{j + 1} : Mem0Rel ({G}{j + 1} env1) σ {mem} mem0c := "
                 f"mem0Rel_envAbs _ σ _ mem0c kq hm{j} _")
    a.append(f"  exact hm{LAST + 1}\n")


def emit_part(r, lo, hi, slices, pass2):
    a = []
    a.append("import Hashtree.Proofs.WinAvx2X8WStripDefs" if pass2 else
             "import Hashtree.Proofs.WinAvx2X8WShift")
    for j in range(lo - 1, hi + 1):      # D_{j-1} holds K_j, D_j holds K_{j+1} and T_j
        a.append(f"import Hashtree.Gen.WinAvx2X8P.D{j}")
    a.append(HEADER)
    if pass2:
        a.append("open Hashtree.Proofs.WinAvx2X8WStrip\n")
        a.append(f"/-! The windows avx2_x8 body slices {lo}..{hi} of a later pass (saved cells stripped,"
                 f" served from the push list), residue {r} (generated by tools/winx8w.py). -/")
        a.append(f"namespace Hashtree.Proofs.WinAvx2X8WBodyR{r}S\n")
        for j in range(lo, hi + 1):
            a.append(f"theorem sliceS_{j} : sliceCheck prog 4 (m8P {r}) orcB {slices[j]['n']} "
                     f"(stripK8 {r} K{j}) (stripK8 {r} K{j + 1}) T{j} = true := by\n  decide +kernel\n")
        a.append(f"end Hashtree.Proofs.WinAvx2X8WBodyR{r}S\n")
    else:
        a.append(f"/-! The windows avx2_x8 body slices {lo}..{hi} at the wrapper call state, residue {r}"
                 f" (generated by tools/winx8w.py). -/")
        a.append(f"namespace Hashtree.Proofs.WinAvx2X8WBodyR{r}\n")
        for j in range(lo, hi + 1):
            a.append(f"theorem sliceW_{j} : sliceCheck prog 4 m8W orcB {slices[j]['n']} "
                     f"(shiftK8 {r} K{j}) (shiftK8 {r} K{j + 1}) T{j} = true := by\n  decide +kernel\n")
        a.append(f"end Hashtree.Proofs.WinAvx2X8WBodyR{r}\n")
    return "\n".join(a)


def emit_main(r, ranges, slices):
    a = []
    for p in range(len(ranges)):
        a.append(f"import Hashtree.Proofs.WinAvx2X8WBodyR{r}P{p + 1}")
    a.append(HEADER)
    a.append(f"""/-!
# The windows avx2_x8 body at the wrapper call state, first pass, residue {r}

The pilot's 208 branch-free body slices `K3 .. K211` (`BODYLEN` = {BODYLEN} instructions)
re-checked at the cuts rebased by `shiftK8 {r}` (the parts `P1..P4`, generated by
`tools/winx8w.py`) and composed: `body_runW`, the first pass from the rebased loop head `K3`
(reached by the entry, `WinAvx2X8WShift.shiftOk`), at any count `c = σ 2 ≥ 8`.
-/""")
    a.append(f"namespace Hashtree.Proofs.WinAvx2X8WBodyR{r}\n")
    a.append(f"def G{FIRST} (env1 : Key → W32) : Key → W32 := env1")
    for j in range(FIRST, LAST + 1):
        a.append(f"def G{j + 1} (env1 : Key → W32) : Key → W32 := "
                 f"envAbs (G{j} env1) (run prog 4 m8W orcB {slices[j]['n']} (shiftK8 {r} K{j}))")
    a.append("")
    total = rsum([slices[j]["n"] for j in range(FIRST, LAST + 1)])
    cuts = [(j, f"shiftK8 {r} K{j}", f"shiftK8 {r} K{j + 1}", f"sliceW_{j}")
            for j in range(FIRST, LAST + 1)]
    chain(a, "G", "m8W", "m8W_keyed", "h0", f"shiftK8 {r} K{FIRST}", cuts, slices, total,
          "body_runW", "body_memW",
          f"/-- **The first pass of the body, residue {r}.**  From the rebased `K3` to the rebased\n"
          f"`K211`, `BODYLEN` instructions, at any count `c ≥ 8`. -/",
          "/-- The memory relation carried along the first pass. -/")
    a.append(f"end Hashtree.Proofs.WinAvx2X8WBodyR{r}\n")
    return "\n".join(a)


def emit_main2(r, ranges, slices):
    a = []
    for p in range(len(ranges)):
        a.append(f"import Hashtree.Proofs.WinAvx2X8WBodyR{r}S{p + 1}")
    a.append(f"import Hashtree.Proofs.WinAvx2X8WStrip{r}")
    a.append(HEADER)
    a.append("open Hashtree.Proofs.WinAvx2X8WStrip\n")
    a.append(f"""/-!
# The windows avx2_x8 body of a later pass, residue {r}

The 208 body slices `K3 .. K211` of a second or later pass: the cuts are stripped of the 368
saved cells (`stripK8 {r}`), which the symbolic memory `m8P {r}` serves from its push list; the
first three cuts carry the loop-carried vector registers (`KHs {r}`, `KH4s {r}`, `KH5s {r}`;
their slices are read off `WinAvx2X8WStrip.stripFacts {r}`).  `bodyS_runW` composes them from
the stripped invariant head to the stripped `K211` (generated by `tools/winx8w.py`).
-/""")
    a.append(f"namespace Hashtree.Proofs.WinAvx2X8WBodyR{r}S\n")
    a.append(f"theorem sliceV3s : sliceCheck prog 4 (m8P {r}) orcB {slices[3]['n']} (KHs {r}) (KH4s {r}) T3 = true :=")
    a.append(f"  (stripFacts {r} stripOk_{r}).2.1")
    a.append(f"theorem sliceV4s : sliceCheck prog 4 (m8P {r}) orcB {slices[4]['n']} (KH4s {r}) (KH5s {r}) T4 = true :=")
    a.append(f"  (stripFacts {r} stripOk_{r}).2.2.1")
    a.append(f"theorem sliceV5s : sliceCheck prog 4 (m8P {r}) orcB {slices[5]['n']} (KH5s {r}) (stripK8 {r} K6) T5 = true :=")
    a.append(f"  (stripFacts {r} stripOk_{r}).2.2.2.1\n")
    heads = {3: f"KHs {r}", 4: f"KH4s {r}", 5: f"KH5s {r}"}
    cut = lambda j: heads.get(j, f"stripK8 {r} K{j}")
    a.append(f"def GS{FIRST} (env1 : Key → W32) : Key → W32 := env1")
    for j in range(FIRST, LAST + 1):
        a.append(f"def GS{j + 1} (env1 : Key → W32) : Key → W32 := "
                 f"envAbs (GS{j} env1) (run prog 4 (m8P {r}) orcB {slices[j]['n']} ({cut(j)}))")
    a.append("")
    total = rsum([slices[j]["n"] for j in range(FIRST, LAST + 1)])
    cuts = [(j, cut(j), cut(j + 1), f"sliceV{j}s" if j in heads else f"sliceS_{j}")
            for j in range(FIRST, LAST + 1)]
    chain(a, "GS", f"(m8P {r})", f"m8P_keyed_{r}", "h0", f"KHs {r}", cuts, slices, total,
          "bodyS_runW", "bodyS_memW",
          f"/-- **A later pass of the body, residue {r}.**  From the stripped invariant head to the\n"
          f"stripped `K211`, `BODYLEN` instructions, at any count `c ≥ 8`, over the push memory. -/",
          "/-- The memory relation carried along a later pass. -/")
    a.append(f"end Hashtree.Proofs.WinAvx2X8WBodyR{r}S\n")
    return "\n".join(a)


def main():
    if len(sys.argv) not in (2, 3) or sys.argv[1] not in ("8", "24"):
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    r = int(sys.argv[1])
    pass2 = len(sys.argv) == 3 and sys.argv[2] == "--pass2"
    slices = read_slices()
    ranges = part_ranges(6 if pass2 else FIRST)
    tag = "S" if pass2 else "P"
    for p, (lo, hi) in enumerate(ranges):
        path = os.path.join(PROOFS, f"WinAvx2X8WBodyR{r}{tag}{p + 1}.lean")
        open(path, "w").write(emit_part(r, lo, hi, slices, pass2))
        print("wrote", path, f"slices {lo}..{hi}")
    path = os.path.join(PROOFS, f"WinAvx2X8WBodyR{r}{'S' if pass2 else ''}.lean")
    open(path, "w").write(emit_main2(r, ranges, slices) if pass2 else emit_main(r, ranges, slices))
    print("wrote", path)


if __name__ == "__main__":
    main()
