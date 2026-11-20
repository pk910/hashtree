#!/usr/bin/env python3
"""Generate the R2c x8 modules (avx2_x8 W-mode loop, output correctness):
  Avx2X8WOutLab.lean        lab8_k : T_k.map fst = L_{k+1}.map fst (k = 2..210)
  Avx2X8WOutTab.lean        the 256 output cells, the turn-log shape, outOk_tab (from the pilot's out_final)
  Avx2X8WOutCut{T,X,TS,XS}{0,16}.lean  per exit/turn cut: the tail re-checked WITH T210, its cells, its shape
  Avx2X8WOutInvR{0,16}.lean the pilot's InvC chain lifted to the W cuts (first pass, later pass, tails)
The turn tails (`KT r`, `KTs r`) reload the IV into the vector registers that hold the digests of
blocks 0 and 1 in the pilot's exit cut, so the 16 register labels `badT` are dropped: the tails are
lifted with `T210t` / `L211t` (the pilot's `T210` / `L211` without them); the output cells are
memory labels and stay.
Usage (from formal/lean): gen_r2c_x8.py Hashtree/Gen/Avx2X8P/Final.lean Hashtree/Gen/Avx2X8P/D210.lean"""
import re, sys

src = open(sys.argv[1]).read().splitlines()
BAD = list(range(100, 108)) + list(range(116, 124))
l211 = None
for l in open(sys.argv[2]):
    if l.startswith("def L211 : List (Nat × Q) := ["):
        body = l[l.index(":= [") + 4:l.rindex("]")]
        l211, depth, start = [], 0, None
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
                    l211.append((id_, q))
assert l211 and len(l211) == 1224, len(l211 or [])
badIdx = {i for i, (id_, q) in enumerate(l211) if int(id_) in BAD}
assert len(badIdx) == 16
L211t = "[" + ", ".join(f"({id_}, {q})" for i, (id_, q) in enumerate(l211) if i not in badIdx) + "]"

# slice lengths of the pilot: def E{k+1} ... (run prog 4 m0q ORC n K{k})
nlen = {}
for l in src:
    m = re.match(r"def E(\d+) \(env0 : Key → W32\) : Key → W32 := envAbs \(E\d+ env0\) \(run prog 4 m0q \(fun pc => decide \(pc ∈ \(\[[^\]]*\] : List Nat\)\)\) (\d+) K(\d+)\)", l)
    if m:
        assert int(m.group(1)) == int(m.group(3)) + 1
        nlen[int(m.group(3))] = int(m.group(2))
assert all(k in nlen for k in range(1, 211)), sorted(set(range(1, 211)) - set(nlen))
assert nlen[210] == 31

HEAD = """set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
"""
OPENS = """open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.Avx2X8 Hashtree.Gen.Avx2X8P
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip
"""
NS = "Hashtree.Proofs.Avx2X8WOut"
D = "Hashtree/Proofs/"

def w(name, parts):
    open(D + name + ".lean", "w").write("".join(parts))

# ---------- Lab ----------
out = ["import Hashtree.Proofs.Avx512X16WOutBase\nimport Hashtree.Gen.Avx2X8P.Final\n",
       "\n/-! R2c x8 — the pilot's tree lists track exactly the next cut's labels (generated; `decide`). -/\n\n",
       HEAD, "\nopen Hashtree.Asm Hashtree.Gen.Avx2X8P\n\n", f"namespace {NS}\n\n"]
for k in range(2, 210):
    out.append(f"theorem lab8_{k} : T{k}.map (·.1) = L{k+1}.map (·.1) := by decide\n")
out.append(f"\nend {NS}\n")
w("Avx2X8WOutLab", out)

# ---------- Tab: the 256 output cells of the pilot, generic in the cut ----------
gl = [l for l in src if re.match(r"\s*have g\d+ := hF\.1; have hF := hF\.2", l)]
cases = []
i = 0
while i < len(src):
    m = re.match(r"\s*\| (\d+), (\d+), (\d+), _, _, _ => exact ⟨E211 env0 \(\.n (\d+)\), outCell_sound _ σ K211 (\d+) (\d+) (\d+) \(by decide\),", src[i])
    if m:
        m2 = re.match(r"\s*by rw \[show E211 env0 \(\.n (\d+)\) = qv inp \(\.HB (\d+) (\d+)\) from g(\d+),", src[i + 1])
        assert m2, src[i + 1]
        cases.append((m.groups(), m2.groups(), src[i + 2].strip()))
        i += 3
    else:
        i += 1
assert len(cases) == 256 and len(gl) == 1224, (len(cases), len(gl))

tab = ", ".join(f"({o}, {id_}, {b})" for ((n, i_, b, id_, o, id2, b2), _, _) in cases)
out = ["import Hashtree.Proofs.Avx512X16WOutBase\nimport Hashtree.Proofs.AvxX4LoopWFrame\nimport Hashtree.Gen.Avx2X8P.Final\n",
       "\n/-! R2c x8 — the 256 output cells of a pass, the shape of a pass's log, and the eight digests from the\ninvariant at `L211t` for any cut whose cells are the pilot's (generated from the pilot's `out_final`). -/\n\n",
       HEAD, "\nopen Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW\nopen Hashtree.Asm.SpecQ Hashtree.Spec\nopen Hashtree.Kernels.X86.Avx2X8 Hashtree.Gen.Avx2X8P\nopen Hashtree.Proofs.Avx512X16WOut (OutOk)\n",
       f"\nnamespace {NS}\n\n"]
out.append(f"""/-- The register labels of the digests of blocks 0 and 1 in the pilot's exit cut; a turn tail
overwrites those registers with the IV. -/
def badT : List Nat := {BAD}

/-- The pilot's `T210` without the `badT` labels. -/
def T210t : List (Nat × E) := T210.filter (fun p => !decide (p.1 ∈ badT))

/-- The pilot's `L211` without the `badT` labels (literal). -/
def L211t : List (Nat × Q) := {L211t}

theorem L211t_eq : L211t = L211.filter (fun p => !decide (p.1 ∈ badT)) := by
  decide +kernel

theorem lab8_210t : T210t.map (·.1) = L211t.map (·.1) := by
  decide +kernel

theorem invC_sub (inp : Nat → Byte) (e : Key → W32) (h : InvC inp e L211) : InvC inp e L211t := by
  rw [invC_iff] at h ⊢
  intro p hp
  rw [L211t_eq] at hp
  exact h p (List.mem_filter.mp hp).1

theorem sliceCheck_filter (prog : Array Instr) (ro : Region) (mem0 : Addr Lin → Cell E Lin)
    (orc : Nat → Bool) (n : Nat) (K K' : State E Lin) (T : List (Nat × E)) (f : Nat × E → Bool)
    (h : sliceCheck prog ro mem0 orc n K K' T = true) :
    sliceCheck prog ro mem0 orc n K K' (T.filter f) = true := by
  simp only [sliceCheck, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun p hp => h.2 p (List.mem_filter.mp hp).1⟩

/-- The pilot's exit slice with the reduced trees. -/
theorem slice210t : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([13] : List Nat))) 31 K210 K211 T210t = true :=
  sliceCheck_filter _ _ _ _ _ _ _ _ _ slice210

/-- The 256 `(o, id, b)` output cells of the pilot's final cut `K211`. -/
def tab8 : List (Nat × Nat × Nat) := [{tab}]

/-- Every logged cell is an output cell at `sym 1 + o`, `o < 256`, or a stack cell `sAt k`,
`-984 ≤ k < 0`. -/
def outShape8 (K : State E Lin) : Bool :=
  K.mem.all fun p =>
    (p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 256)) ||
    (p.1.region == rStack && p.1.off.c == Hashtree.Asm.X86SymW.stkC && decide (-984 ≤ p.1.off.k) && decide (p.1.off.k < 0))

theorem out_eval8 (σ : Nat → Int) (k : Int) : (⟨k, [0, 1]⟩ : Lin).eval σ = σ 1 + k := by
  show k + (0 * σ 0 + (1 * σ (0 + 1) + 0)) = σ 1 + k
  rw [show (0 + 1 : Nat) = 1 from rfl]
  omega

theorem outShape8_sound (K : State E Lin) (h : outShape8 K = true) (e : Key → W32) (σ : Nat → Int) :
    ∀ p ∈ (mapState e σ K).mem,
      (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
      (p.1.region = rStack ∧ σ 9 - 984 ≤ p.1.off ∧ p.1.off < σ 9) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [outShape8, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨qr, qk, qc⟩, qcell⟩ := q
  rcases h _ hq with ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩ | ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    left
    show rOut = rOut ∧ σ 1 ≤ (⟨qk, [0, 1]⟩ : Lin).eval σ ∧ (⟨qk, [0, 1]⟩ : Lin).eval σ < σ 1 + 256
    rw [out_eval8]
    exact ⟨rfl, by omega, by omega⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    right
    show rStack = rStack ∧ σ 9 - 984 ≤ (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ ∧
      (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ < σ 9
    rw [Hashtree.Proofs.AvxX4LoopWFrame.sAt_eval]
    exact ⟨rfl, by omega, by omega⟩

/-- **The eight digests.**  A cut whose output cells are the pilot's (`tab8`), at an environment
satisfying the pilot's final invariant (without `badT`, `L211t`), holds the SHA-256 bytes of the 8 input blocks. -/
theorem outOk_tab (K : State E Lin) (hK : tab8.all (fun t => outCell K t.1 t.2.1 t.2.2) = true)
    (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L211t) :
    OutOk inp (σ 1) 8 (mapState e σ K).mem := by
  have hc : ∀ o id b, (o, id, b) ∈ tab8 → outCell K o id b = true :=
    fun o id b h => List.all_eq_true.mp hK (o, id, b) h
  have hF := hI
""")
gused = set()
for (_, (_, _, _, gk), _) in cases:
    gused.add(int(gk))
assert not (gused & badIdx)
out += [l + "\n" for i, l in enumerate(gl) if i not in badIdx]
assert all(re.match(rf"\s*have g{i} :=", l) for i, l in enumerate(gl))
out.append("  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n")
for ((n, i_, b, id_, o, id2, b2), (id3, hn, hi, gk), l3) in cases:
    assert id_ == id2 == id3 and b == b2
    out.append(f"  | {n}, {i_}, {b}, _, _, _ => exact ⟨e (.n {id_}), outCell_sound _ σ K {o} {id_} {b} (hc _ _ _ (by decide)),\n")
    out.append(f"      by rw [show e (.n {id_}) = qv inp (.HB {hn} {hi}) from g{gk},\n        {l3}\n")
out.append("  | _ + 8, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n")
out.append(f"\nend {NS}\n")
w("Avx2X8WOutTab", out)

# ---------- Cut files ----------
def cuts(r):
    return [("T", f"m8 orcB 27 (shiftK8 {r} K210)", f"(KT {r})"),
            ("X", f"m8 orcEx 31 (shiftK8 {r} K210)", f"(KTE {r})"),
            ("TS", f"(m8P {r}) orcB 27 (stripK8 {r} K210)", f"(KTs {r})"),
            ("XS", f"(m8P {r}) orcEx 31 (stripK8 {r} K210)", f"(KTEs {r})")]

for r in (0, 16):
    for (tag, sl, K) in cuts(r):
        out = ["import Hashtree.Proofs.Avx2X8WOutTab\nimport Hashtree.Proofs.Avx2X8WStripDefs\n",
               f"\n/-! R2c x8 — the cut `{K[1:-1]}`: its tail slice re-checked with the pilot's trees `T210`,\nits output cells and the shape of its log (generated). -/\n\n",
               HEAD, "\n", OPENS, f"\nnamespace {NS}\n\n"]
        out.append(f"theorem chk{tag}_{r} : sliceCheck prog 4 {sl} {K} T210t = true := by\n  decide +kernel\n\n")
        out.append(f"theorem cells{tag}_{r} : tab8.all (fun t => outCell {K} t.1 t.2.1 t.2.2) = true := by\n  decide +kernel\n\n")
        out.append(f"theorem shape{tag}_{r} : outShape8 {K} = true := by\n  decide +kernel\n\n")
        out.append(f"end {NS}\n")
        w(f"Avx2X8WOutCut{tag}{r}", out)

# ---------- Inv files ----------
def orcS(k):
    return "_"

for r in (0, 16):
    BW = f"Hashtree.Proofs.Avx2X8WBodyR{r}"
    BS = f"Hashtree.Proofs.Avx2X8WBodyR{r}S"
    out = ["import Hashtree.Proofs.Avx2X8WOutLab\n",
           "".join(f"import Hashtree.Proofs.Avx2X8WOutCut{t}{r}\n" for t in ("T", "X", "TS", "XS")),
           f"import {BW}\nimport {BS}\n",
           f"\n/-! R2c x8 — the pilot's invariant chain lifted to the W cuts at residue {r} (generated):\nthe first pass (`{BW}.G210`), a later pass (`{BS}.GS210`), and the four tails. -/\n\n",
           HEAD, "\n", OPENS, "open Hashtree.Proofs.Avx512X16WOut (invC_lift invC_lift')\n", f"\nnamespace {NS}\n\n"]
    # first pass
    for k in range(2, 210):
        n = nlen[k]
        out.append(f"""theorem stepW{r}_{k} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{k}) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB {n} (shiftK8 {r} K{k}))) L{k+1} :=
  invC_lift inp env prog 4 m0q m8 _ _ {n} K{k} K{k+1} (shiftK8 {r} K{k}) (shiftK8 {r} K{k+1}) T{k} L{k+1}
    slice{k} {BW}.sliceW_{k} lab8_{k} (step{k} inp env hI hm)

""")
    # later pass
    for k in range(2, 210):
        n = nlen[k]
        if k == 2:
            a, b_, s = f"(KHs {r})", f"(KH3s {r})", f"{BS}.sliceV2s"
        elif k == 3:
            a, b_, s = f"(KH3s {r})", f"(stripK8 {r} K4)", f"{BS}.sliceV3s"
        else:
            a, b_, s = f"(stripK8 {r} K{k})", f"(stripK8 {r} K{k+1})", f"{BS}.sliceS_{k}"
        out.append(f"""theorem stepS{r}_{k} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{k}) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P {r}) orcB {n} {a})) L{k+1} :=
  invC_lift inp env prog 4 m0q (m8P {r}) _ _ {n} K{k} K{k+1} {a} {b_} T{k} L{k+1}
    slice{k} {s} lab8_{k} (step{k} inp env hI hm)

""")
    # tails
    for (tag, sl, K) in cuts(r):
        parts = sl.split(" ")
        if sl.startswith("("):
            mem = f"(m8P {r})"; rest = sl[len(mem) + 1:]
        else:
            mem = "m8"; rest = sl[3:]
        orc, nn, *st = rest.split(" ", 2)
        st = st[0]
        if nn == "31":
            body = f"invC_lift inp env prog 4 m0q {mem} _ {orc} 31 K210 K211 {st} {K} T210t L211t\n    slice210t chk{tag}_{r} lab8_210t (invC_sub inp _ (step210 inp env hI hm))"
        else:
            body = f"invC_lift' inp env prog 4 m0q _ 31 K210 K211 {mem} {orc} {nn} {st} {K} T210t L211t\n    slice210t chk{tag}_{r} lab8_210t (invC_sub inp _ (step210 inp env hI hm))"
        out.append(f"""theorem step{tag}{r} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L210) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 {sl})) L211t :=
  {body}

""")
    # chains
    for (pfx, G, nm) in (("W", f"{BW}.G", "invW"), ("S", f"{BS}.GS", "invS")):
        out.append(f"""/-- The {'first' if pfx == 'W' else 'later'}-pass chain: from the empty invariant at the pass head to `L210`. -/
theorem {nm}{r}_body (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp ({G}210 env1) L210 := by
  have i2 : InvC inp ({G}2 env1) L2 := True.intro
""")
        for k in range(2, 210):
            out.append(f"  have i{k+1} : InvC inp ({G}{k+1} env1) L{k+1} := step{pfx}{r}_{k} inp ({G}{k} env1) i{k} hm\n")
        out.append("  exact i210\n\n")
    for (tag, sl, K) in cuts(r):
        G = f"{BS}.GS210" if tag.endswith("S") else f"{BW}.G210"
        nm = "invW" if not tag.endswith("S") else "invS"
        out.append(f"""theorem inv{tag}{r} (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (envAbs ({G} env1) (run prog 4 {sl})) L211t :=
  step{tag}{r} inp ({G} env1) ({nm}{r}_body inp env1 hm) hm

""")
    out.append(f"end {NS}\n")
    w(f"Avx2X8WOutInvR{r}", out)

print("written: lab", 209, "cases", len(cases), "g", len(gl))
