#!/usr/bin/env python3
"""Generate the R2c windows x8 modules (windows avx2_x8 W-mode loop, output correctness):
  WinAvx2X8WOutLab.lean           lab8w_k : T_k.map fst = L_{k+1}.map fst (k = 3..211)
  WinAvx2X8WOutTab.lean           the 256 output cells, the pass-log shape, outOk_tab8w (from the pilot's out_final)
  WinAvx2X8WOut{Chk,Cel,Shp}{T,X,TS,XS}{8,24}.lean
                                  per tail cut: the tail re-checked WITH T211, its output cells, its log shape
                                  (one `decide +kernel` per file: one kernel evaluation of the cut each)
  WinAvx2X8WOutInvR{8,24}.lean    the pilot's InvC chain lifted to the W cuts (first pass, later pass, tails)
The pilot (`Gen.WinAvx2X8P`) tracks nothing up to `K4` (`L3 = L4 = []`), so the chains start at `L3`.
Its exit slice 211 (`K211 -> K212`, 42 steps, `jb` at pc 24 taken) holds the digest stores; the exit tails
`KTE r` / `KTEs r` have the same length, the turn tails `KT r` / `KTs r` (24 steps) are lifted with
`invC_lift'`.  Optional `--bad i,j,..`: register labels to drop from `T211` / `L212` for the tails
(`T211t` / `L212t`, as in the linux x8 module); default none.
Usage (from formal/lean): gen_r2c_x8w.py Hashtree/Gen/WinAvx2X8P/Final.lean Hashtree/Gen/WinAvx2X8P/D211.lean [--bad ..]"""
import re, sys

args = sys.argv[1:]
BAD = []
if "--bad" in args:
    i = args.index("--bad")
    BAD = [int(x) for x in args[i + 1].split(",") if x]
    del args[i:i + 2]
src = open(args[0]).read().splitlines()

l212 = None
for l in open(args[1]):
    if l.startswith("def L212 : List (Nat × Q) := ["):
        body = l[l.index(":= [") + 4:l.rindex("]")]
        l212, depth, start = [], 0, None
        for ci, ch in enumerate(body):
            if ch == "(":
                if depth == 0:
                    start = ci
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    el = body[start + 1:ci]
                    id_, q = el.split(", ", 1)
                    l212.append((id_, q))
assert l212 and len(l212) == 1200, len(l212 or [])
badIdx = {i for i, (id_, q) in enumerate(l212) if int(id_) in BAD}
assert len(badIdx) == len(BAD)
FILT = bool(BAD)
TT = "T211t" if FILT else "T211"
LT = "L212t" if FILT else "L212"

# slice lengths of the pilot: def E{k+1} ... (run prog 4 m0q ORC n K{k})
nlen = {}
for l in src:
    m = re.match(r"def E(\d+) \(env0 : Key → W32\) : Key → W32 := envAbs \(E\d+ env0\) \(run prog 4 m0q \(fun pc => decide \(pc ∈ \(\[[^\]]*\] : List Nat\)\)\) (\d+) K(\d+)\)", l)
    if m:
        assert int(m.group(1)) == int(m.group(3)) + 1
        nlen[int(m.group(3))] = int(m.group(2))
assert all(k in nlen for k in range(1, 212)), sorted(set(range(1, 212)) - set(nlen))
assert nlen[211] == 42 and nlen[3] == 8 and nlen[4] == 8 and nlen[5] == 8
assert sum(nlen[k] for k in range(3, 211)) == 6039

HEAD = """set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
"""
OPENS = """open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip
"""
NS = "Hashtree.Proofs.WinAvx2X8WOut"
D = "Hashtree/Proofs/"
RES = (8, 24)

def w(name, parts):
    open(D + name + ".lean", "w").write("".join(parts))

# ---------- Lab ----------
out = ["import Hashtree.Proofs.Avx512X16WOutBase\n",
       "".join(f"import Hashtree.Gen.WinAvx2X8P.D{k}\n" for k in range(2, 212)),
       "\n/-! R2c windows x8 — the pilot's tree lists track exactly the next cut's labels (generated; `decide +kernel`). -/\n\n",
       HEAD, "\nopen Hashtree.Asm Hashtree.Gen.WinAvx2X8P\n\n", f"namespace {NS}\n\n"]
for k in range(3, 212):
    out.append(f"theorem lab8w_{k} : T{k}.map (·.1) = L{k+1}.map (·.1) := by decide +kernel\n")
out.append(f"\nend {NS}\n")
w("WinAvx2X8WOutLab", out)

# ---------- Tab: the 256 output cells of the pilot, generic in the cut ----------
gl = [l for l in src if re.match(r"\s*have g\d+ := hF\.1; have hF := hF\.2", l)]
cases = []
i = 0
while i < len(src):
    m = re.match(r"\s*\| (\d+), (\d+), (\d+), _, _, _ => exact ⟨E212 env0 \(\.n (\d+)\), outCell_sound _ σ K212 (\d+) (\d+) (\d+) \(by decide\),", src[i])
    if m:
        m2 = re.match(r"\s*by rw \[show E212 env0 \(\.n (\d+)\) = qv inp \(\.HB (\d+) (\d+)\) from g(\d+),", src[i + 1])
        assert m2, src[i + 1]
        cases.append((m.groups(), m2.groups(), src[i + 2].strip()))
        i += 3
    else:
        i += 1
assert len(cases) == 256 and len(gl) == 1200, (len(cases), len(gl))
assert all(re.match(rf"\s*have g{i} :=", l) for i, l in enumerate(gl))

tab = ", ".join(f"({o}, {id_}, {b})" for ((n, i_, b, id_, o, id2, b2), _, _) in cases)
out = ["import Hashtree.Proofs.Avx512X16WOutBase\nimport Hashtree.Proofs.WinLogW\nimport Hashtree.Gen.WinAvx2X8P.D211\n",
       "\n/-! R2c windows x8 — the 256 output cells of a pass, the shape of a pass's log, and the eight digests from\nthe invariant at the pilot's last labels, for any cut whose cells are the pilot's (generated from the pilot's `out_final`). -/\n\n",
       HEAD, "\nopen Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW\nopen Hashtree.Asm.SpecQ Hashtree.Spec\nopen Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Gen.WinAvx2X8P\nopen Hashtree.Proofs.Avx512X16WOut (OutOk)\n",
       f"\nnamespace {NS}\n\n"]
if FILT:
    L212t = "[" + ", ".join(f"({id_}, {q})" for i, (id_, q) in enumerate(l212) if i not in badIdx) + "]"
    out.append(f"""/-- Register labels of the pilot's exit cut that a turn tail does not reproduce. -/
def badT8w : List Nat := {BAD}

def T211t : List (Nat × E) := T211.filter (fun p => !decide (p.1 ∈ badT8w))

def L212t : List (Nat × Q) := {L212t}

theorem L212t_eq : L212t = L212.filter (fun p => !decide (p.1 ∈ badT8w)) := by
  decide +kernel

theorem lab8w_211t : T211t.map (·.1) = L212t.map (·.1) := by
  decide +kernel

theorem invC_sub8w (inp : Nat → Byte) (e : Key → W32) (h : InvC inp e L212) : InvC inp e L212t := by
  rw [invC_iff] at h ⊢
  intro p hp
  rw [L212t_eq] at hp
  exact h p (List.mem_filter.mp hp).1

theorem sliceCheck_filter8w (prog : Array Instr) (ro : Region) (mem0 : Addr Lin → Cell E Lin)
    (orc : Nat → Bool) (n : Nat) (K K' : State E Lin) (T : List (Nat × E)) (f : Nat × E → Bool)
    (h : sliceCheck prog ro mem0 orc n K K' T = true) :
    sliceCheck prog ro mem0 orc n K K' (T.filter f) = true := by
  simp only [sliceCheck, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun p hp => h.2 p (List.mem_filter.mp hp).1⟩

""")
out.append(f"""/-- The 256 `(o, id, b)` output cells of the pilot's final cut `K212`. -/
def tab8w : List (Nat × Nat × Nat) := [{tab}]

/-- Every logged cell is an output cell at `sym 1 + o`, `o < 256`, or a stack cell `sAt k`,
`-1296 ≤ k < 0` (the kernel's frame). -/
def outShape8W (K : State E Lin) : Bool :=
  K.mem.all fun p =>
    (p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 256)) ||
    (p.1.region == rStack && p.1.off.c == Hashtree.Asm.X86SymW.stkC && decide (-1296 ≤ p.1.off.k) && decide (p.1.off.k < 0))

theorem out_eval8w (σ : Nat → Int) (k : Int) : (⟨k, [0, 1]⟩ : Lin).eval σ = σ 1 + k := by
  show k + (0 * σ 0 + (1 * σ (0 + 1) + 0)) = σ 1 + k
  rw [show (0 + 1 : Nat) = 1 from rfl]
  omega

theorem outShape8W_sound (K : State E Lin) (h : outShape8W K = true) (e : Key → W32) (σ : Nat → Int) :
    ∀ p ∈ (mapState e σ K).mem,
      (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
      (p.1.region = rStack ∧ σ 9 - 1296 ≤ p.1.off ∧ p.1.off < σ 9) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [outShape8W, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨qr, qk, qc⟩, qcell⟩ := q
  rcases h _ hq with ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩ | ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    left
    show rOut = rOut ∧ σ 1 ≤ (⟨qk, [0, 1]⟩ : Lin).eval σ ∧ (⟨qk, [0, 1]⟩ : Lin).eval σ < σ 1 + 256
    rw [out_eval8w]
    exact ⟨rfl, by omega, by omega⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    right
    show rStack = rStack ∧ σ 9 - 1296 ≤ (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ ∧
      (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ < σ 9
    rw [Hashtree.Proofs.WinLogW.sAtW_eval]
    exact ⟨rfl, by omega, by omega⟩

/-- **The eight digests.**  A cut whose output cells are the pilot's (`tab8w`), at an environment
satisfying the pilot's final invariant (`{LT}`), holds the SHA-256 bytes of the 8 input blocks. -/
theorem outOk_tab8w (K : State E Lin) (hK : tab8w.all (fun t => outCell K t.1 t.2.1 t.2.2) = true)
    (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e {LT}) :
    OutOk inp (σ 1) 8 (mapState e σ K).mem := by
  have hc : ∀ o id b, (o, id, b) ∈ tab8w → outCell K o id b = true :=
    fun o id b h => List.all_eq_true.mp hK (o, id, b) h
  have hF := hI
""")
gused = set(int(gk) for (_, (_, _, _, gk), _) in cases)
assert not (gused & badIdx)
out += [l + "\n" for i, l in enumerate(gl) if i not in badIdx]
out.append("  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n")
for ((n, i_, b, id_, o, id2, b2), (id3, hn, hi, gk), l3) in cases:
    assert id_ == id2 == id3 and b == b2
    out.append(f"  | {n}, {i_}, {b}, _, _, _ => exact ⟨e (.n {id_}), outCell_sound _ σ K {o} {id_} {b} (hc _ _ _ (by decide)),\n")
    out.append(f"      by rw [show e (.n {id_}) = qv inp (.HB {hn} {hi}) from g{gk},\n        {l3}\n")
out.append("  | _ + 8, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n")
out.append(f"\nend {NS}\n")
w("WinAvx2X8WOutTab", out)

# ---------- Cut files: one kernel evaluation each ----------
def cuts(r):
    # tag, memory, oracle, steps, start cut, end cut
    return [("T", "m8W", "orcB", 24, f"(shiftK8 {r} K211)", f"(KT {r})"),
            ("X", "m8W", "orcEx", 42, f"(shiftK8 {r} K211)", f"(KTE {r})"),
            ("TS", f"(m8P {r})", "orcB", 24, f"(stripK8 {r} K211)", f"(KTs {r})"),
            ("XS", f"(m8P {r})", "orcEx", 42, f"(stripK8 {r} K211)", f"(KTEs {r})")]

for r in RES:
    for (tag, mem, orc, nn, st, K) in cuts(r):
        pre = ["import Hashtree.Proofs.WinAvx2X8WOutTab\nimport Hashtree.Proofs.WinAvx2X8WStripDefs\n"]
        def body(kind, thm):
            return pre + [f"\n/-! R2c windows x8 — the cut `{K[1:-1]}`: {kind} (generated; one `decide +kernel`). -/\n\n",
                          HEAD, "\n", OPENS, f"\nnamespace {NS}\n\n", thm, f"end {NS}\n"]
        w(f"WinAvx2X8WOutChk{tag}{r}", body(f"its tail slice re-checked with the pilot's trees `{TT}`",
          f"theorem chk{tag}_{r} : sliceCheck prog 4 {mem} {orc} {nn} {st} {K} {TT} = true := by\n  decide +kernel\n\n"))
        w(f"WinAvx2X8WOutCel{tag}{r}", body("its 256 output cells",
          f"theorem cells{tag}_{r} : tab8w.all (fun t => outCell {K} t.1 t.2.1 t.2.2) = true := by\n  decide +kernel\n\n"))
        w(f"WinAvx2X8WOutShp{tag}{r}", body("the shape of its log",
          f"theorem shape{tag}_{r} : outShape8W {K} = true := by\n  decide +kernel\n\n"))

# ---------- Inv files ----------
for r in RES:
    BW = f"Hashtree.Proofs.WinAvx2X8WBodyR{r}"
    BS = f"Hashtree.Proofs.WinAvx2X8WBodyR{r}S"
    out = ["import Hashtree.Proofs.WinAvx2X8WOutLab\n",
           "".join(f"import Hashtree.Proofs.WinAvx2X8WOutChk{t}{r}\n" for t in ("T", "X", "TS", "XS")),
           f"import {BW}\nimport {BS}\n",
           "".join(f"import Hashtree.Gen.WinAvx2X8P.P{k}\n" for k in range(3, 212)),
           f"\n/-! R2c windows x8 — the pilot's invariant chain lifted to the W cuts at residue {r} (generated):\nthe first pass (`{BW}.G211`), a later pass (`{BS}.GS211`), and the four tails. -/\n\n",
           HEAD, "\n", OPENS, "open Hashtree.Proofs.Avx512X16WOut (invC_lift invC_lift')\n", f"\nnamespace {NS}\n\n"]
    # first pass
    for k in range(3, 211):
        n = nlen[k]
        out.append(f"""theorem stepW{r}_{k} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{k}) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8W orcB {n} (shiftK8 {r} K{k}))) L{k+1} :=
  invC_lift inp env prog 4 m0q m8W _ _ {n} K{k} K{k+1} (shiftK8 {r} K{k}) (shiftK8 {r} K{k+1}) T{k} L{k+1}
    slice{k} {BW}.sliceW_{k} lab8w_{k} (step{k} inp env hI hm)

""")
    # later pass
    for k in range(3, 211):
        n = nlen[k]
        if k == 3:
            a, b_, s = f"(KHs {r})", f"(KH4s {r})", f"{BS}.sliceV3s"
        elif k == 4:
            a, b_, s = f"(KH4s {r})", f"(KH5s {r})", f"{BS}.sliceV4s"
        elif k == 5:
            a, b_, s = f"(KH5s {r})", f"(stripK8 {r} K6)", f"{BS}.sliceV5s"
        else:
            a, b_, s = f"(stripK8 {r} K{k})", f"(stripK8 {r} K{k+1})", f"{BS}.sliceS_{k}"
        out.append(f"""theorem stepS{r}_{k} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{k}) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P {r}) orcB {n} {a})) L{k+1} :=
  invC_lift inp env prog 4 m0q (m8P {r}) _ _ {n} K{k} K{k+1} {a} {b_} T{k} L{k+1}
    slice{k} {s} lab8w_{k} (step{k} inp env hI hm)

""")
    # tails
    s211 = "(sliceCheck_filter8w _ _ _ _ _ _ _ _ _ slice211)" if FILT else "slice211"
    lab = "lab8w_211t" if FILT else "lab8w_211"
    st211 = "(invC_sub8w inp _ (step211 inp env hI hm))" if FILT else "(step211 inp env hI hm)"
    for (tag, mem, orc, nn, st, K) in cuts(r):
        if nn == 42:
            bd = f"invC_lift inp env prog 4 m0q {mem} _ {orc} 42 K211 K212 {st} {K} {TT} {LT}\n    {s211} chk{tag}_{r} {lab} {st211}"
        else:
            bd = f"invC_lift' inp env prog 4 m0q _ 42 K211 K212 {mem} {orc} {nn} {st} {K} {TT} {LT}\n    {s211} chk{tag}_{r} {lab} {st211}"
        out.append(f"""theorem step{tag}{r} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L211) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 {mem} {orc} {nn} {st})) {LT} :=
  {bd}

""")
    # chains
    for (pfx, G, nm) in (("W", f"{BW}.G", "invW"), ("S", f"{BS}.GS", "invS")):
        out.append(f"""/-- The {'first' if pfx == 'W' else 'later'}-pass chain: from the empty invariant at the pass head to `L211`. -/
theorem {nm}{r}_body (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp ({G}211 env1) L211 := by
  have i3 : InvC inp ({G}3 env1) L3 := True.intro
""")
        for k in range(3, 211):
            out.append(f"  have i{k+1} : InvC inp ({G}{k+1} env1) L{k+1} := step{pfx}{r}_{k} inp ({G}{k} env1) i{k} hm\n")
        out.append("  exact i211\n\n")
    for (tag, mem, orc, nn, st, K) in cuts(r):
        G = f"{BS}.GS211" if tag.endswith("S") else f"{BW}.G211"
        nm = "invS" if tag.endswith("S") else "invW"
        out.append(f"""theorem inv{tag}{r} (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (envAbs ({G} env1) (run prog 4 {mem} {orc} {nn} {st})) {LT} :=
  step{tag}{r} inp ({G} env1) ({nm}{r}_body inp env1 hm) hm

""")
    out.append(f"end {NS}\n")
    w(f"WinAvx2X8WOutInvR{r}", out)

print("written: lab", 209, "cases", len(cases), "g", len(gl), "bad", BAD)
