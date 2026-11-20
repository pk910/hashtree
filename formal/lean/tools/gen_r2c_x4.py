#!/usr/bin/env python3
"""Generate the R2c x4 modules (avx_x4 W-mode loop, output correctness):
  AvxX4LoopWOutLab.lean     lab4_k : T_k.map fst = L_{k+1}.map fst (k = 0..200)
  AvxX4LoopWOutChk{1..8}.lean  the W slices re-checked WITH the pilot's trees
  AvxX4LoopWOutInv.lean     the InvC lifts and chains (entry pass, loop pass)
  AvxX4LoopWOutTail.lean    the shape of a turn's log and the 128 digest cases (from the pilot's out_final)
Usage: gen_r2c_x4.py <slice table> <pilot out_final text>"""
import re, sys

table = {}
L = r"(\[[^\]]*\])"
for line in open(sys.argv[1]):
    k = int(line.split()[0])
    s = re.search(r"S:" + L + r":(\d+)", line)
    table[k] = {"orcS": s.group(1), "n": int(s.group(2))}

HEAD = """set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
"""
OPENS = """open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.AvxX4 Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W (entryWx shiftK)
open Hashtree.Proofs.AvxX4LoopW (m0W KHL2W KHpW)
open Hashtree.Proofs.AvxX4LoopWExit (orcW orcExitW K201W)
"""
NS = "Hashtree.Proofs.AvxX4LoopWOut"

def orc(l): return f"(fun pc => decide (pc ∈ ({l} : List Nat)))"

# ---------- Lab ----------
out = ["import Hashtree.Proofs.Avx512X16WOutBase\nimport Hashtree.Gen.AvxX4P.Final\n",
       "\n/-! R2c x4 — the pilot's tree lists track exactly the next cut's labels (generated; `decide`). -/\n",
       HEAD, "open Hashtree.Asm Hashtree.Gen.AvxX4P\n\n", f"namespace {NS}\n\n"]
for k in range(0, 201):
    out.append(f"theorem lab4_{k} : T{k}.map (·.1) = L{k+1}.map (·.1) := by decide\n")
out.append(f"\nend {NS}\n")
open("Hashtree/Proofs/AvxX4LoopWOutLab.lean", "w").write("".join(out))

# ---------- Chk files: the W slices with the pilot's trees ----------
# the W cuts: K_kW = shiftK K_k (AvxX4LoopW), entry entryWx -> K1W (72, orcW), head KHL2W -> K1W (68),
# body K_kW -> K_{k+1}W (k = 1..199), turn tail K200W -> KHpW (23), exit K200W -> K201W (27, orcExitW)
checks = []  # (name, statement)
checks.append(("chkT_entry", "sliceCheck prog 4 m0W orcW 72 entryWx Hashtree.Proofs.AvxX4LoopW.K1W T0 = true"))
checks.append(("chkT_head", "sliceCheck prog 4 m0W (fun _ => false) 68 KHL2W Hashtree.Proofs.AvxX4LoopW.K1W T0 = true"))
for k in range(1, 200):
    n = table[k]["n"]
    checks.append((f"chkT_{k}", f"sliceCheck prog 4 m0W (fun _ => false) {n} Hashtree.Proofs.AvxX4LoopW.K{k}W Hashtree.Proofs.AvxX4LoopW.K{k+1}W T{k} = true"))
checks.append(("chkT_turn", "sliceCheck prog 4 m0W (fun _ => false) 23 Hashtree.Proofs.AvxX4LoopW.K200W KHpW T200 = true"))
checks.append(("chkT_exit", "sliceCheck prog 4 m0W orcExitW 27 Hashtree.Proofs.AvxX4LoopW.K200W K201W T200 = true"))
NF = 8
per = (len(checks) + NF - 1) // NF
for f in range(NF):
    part = checks[f * per:(f + 1) * per]
    out = ["import Hashtree.Proofs.AvxX4LoopWOutLab\nimport Hashtree.Proofs.AvxX4LoopWEntry\n",
           f"\n/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part {f+1}/{NF} (generated). -/\n",
           HEAD, OPENS, f"\nnamespace {NS}\n\n"]
    for (name, stmt) in part:
        out.append(f"theorem {name} : {stmt} := by\n  decide +kernel\n\n")
    out.append(f"end {NS}\n")
    open(f"Hashtree/Proofs/AvxX4LoopWOutChk{f+1}.lean", "w").write("".join(out))

# ---------- Inv ----------
out = ["".join(f"import Hashtree.Proofs.AvxX4LoopWOutChk{f+1}\n" for f in range(NF)),
       "\n/-! R2c x4 — the pilot's invariant chain lifted to the W cuts (generated). -/\n",
       HEAD, OPENS, "open Hashtree.Proofs.Avx512X16WOut (OutOk invC_lift invC_lift')\n", f"\nnamespace {NS}\n\n"]
out.append(f"""theorem stepW4_entry (inp : Nat → Byte) (env : Key → W32) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W orcW 72 entryWx)) L1 :=
  invC_lift inp env prog 4 m0q m0W _ _ 72 (entryS 24) K1 entryWx Hashtree.Proofs.AvxX4LoopW.K1W T0 L1
    slice0 chkT_entry lab4_0 (step0 inp env True.intro hm)

theorem stepW4_head (inp : Nat → Byte) (env : Key → W32) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)) L1 :=
  invC_lift' inp env prog 4 m0q _ 72 (entryS 24) K1 m0W (fun _ => false) 68 KHL2W Hashtree.Proofs.AvxX4LoopW.K1W T0 L1
    slice0 chkT_head lab4_0 (step0 inp env True.intro hm)

""")
for k in range(1, 200):
    n = table[k]["n"]
    out.append(f"""theorem stepW4_{k} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{k}) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W {orc('[]')} {n} Hashtree.Proofs.AvxX4LoopW.K{k}W)) L{k+1} :=
  invC_lift inp env prog 4 m0q m0W _ _ {n} K{k} K{k+1} Hashtree.Proofs.AvxX4LoopW.K{k}W Hashtree.Proofs.AvxX4LoopW.K{k+1}W T{k} L{k+1}
    slice{k} chkT_{k} lab4_{k} (step{k} inp env hI hm)

""")
out.append(f"""theorem stepW4_turn (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L200) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W (fun _ => false) 23 Hashtree.Proofs.AvxX4LoopW.K200W)) L201 :=
  invC_lift' inp env prog 4 m0q _ 27 K200 K201 m0W (fun _ => false) 23 Hashtree.Proofs.AvxX4LoopW.K200W KHpW T200 L201
    slice200 chkT_turn lab4_200 (step200 inp env hI hm)

theorem stepW4_exit (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L200) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0W orcExitW 27 Hashtree.Proofs.AvxX4LoopW.K200W)) L201 :=
  invC_lift inp env prog 4 m0q m0W _ _ 27 K200 K201 Hashtree.Proofs.AvxX4LoopW.K200W K201W T200 L201
    slice200 chkT_exit lab4_200 (step200 inp env hI hm)

/-- The body chain: from the invariant at `K1W` (in `G1W env1 = env1`) to `L200` at `K200W`. -/
theorem invW4_body (inp : Nat → Byte) (env1 : Key → W32) (hI : InvC inp env1 L1) (hm : HMem 256 inp env1) :
    InvC inp (Hashtree.Proofs.AvxX4LoopW.G200W env1) L200 := by
  have i1 : InvC inp (Hashtree.Proofs.AvxX4LoopW.G1W env1) L1 := hI
""")
for k in range(1, 200):
    out.append(f"  have i{k+1} : InvC inp (Hashtree.Proofs.AvxX4LoopW.G{k+1}W env1) L{k+1} := stepW4_{k} inp (Hashtree.Proofs.AvxX4LoopW.G{k}W env1) i{k} hm\n")
out.append(f"  exact i200\n\nend {NS}\n")
open("Hashtree/Proofs/AvxX4LoopWOutInv.lean", "w").write("".join(out))

# ---------- Tail ----------
src = open(sys.argv[2]).read().splitlines()
gl = [l for l in src if re.match(r"\s*have g\d+ := hF\.1; have hF := hF\.2", l)]
cases = []
i = 0
while i < len(src):
    m = re.match(r"\s*\| (\d+), (\d+), (\d+), _, _, _ => exact ⟨E201 env0 \(\.n (\d+)\), outCell_sound _ σ K201 (\d+) (\d+) (\d+) \(by decide\),", src[i])
    if m:
        m2 = re.match(r"\s*by rw \[show E201 env0 \(\.n (\d+)\) = qv inp \(\.HB (\d+) (\d+)\) from g(\d+),", src[i + 1])
        assert m2, src[i + 1]
        cases.append((m.groups(), m2.groups(), src[i + 2].strip()))
        i += 3
    else:
        i += 1
assert len(cases) == 128 and len(gl) == 1324, (len(cases), len(gl))

def outOk_thm(K):
    tab = ", ".join(f"({o}, {id_}, {b})" for ((n, i_, b, id_, o, id2, b2), _, _) in cases)
    s = [f"""/-- The 128 `(o, id, b)` output cells of `{K}`, checked once. -/
def {K}_tab : List (Nat × Nat × Nat) := [{tab}]

theorem {K}_cells : {K}_tab.all (fun t => outCell {K} t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem {K}_cell (o id b : Nat) (h : (o, id, b) ∈ {K}_tab) : outCell {K} o id b = true :=
  List.all_eq_true.mp {K}_cells (o, id, b) h

/-- The write log of a turn ending in `{K}` holds the 4 digests, from the invariant at `L201`. -/
theorem outOk_{K} (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L201) :
    OutOk inp (σ 1) 4 (mapState e σ {K}).mem := by
  have hF := hI
"""]
    s += [l + "\n" for l in gl]
    s.append("  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n")
    for ((n, i_, b, id_, o, id2, b2), (id3, hn, hi, gk), l3) in cases:
        assert id_ == id2 == id3 and b == b2
        s.append(f"  | {n}, {i_}, {b}, _, _, _ => exact ⟨e (.n {id_}), outCell_sound _ σ {K} {o} {id_} {b} ({K}_cell _ _ _ (by decide)),\n")
        s.append(f"      by rw [show e (.n {id_}) = qv inp (.HB {hn} {hi}) from g{gk},\n        {l3}\n")
    s.append("  | _ + 4, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n")
    return "".join(s)

out = ["import Hashtree.Proofs.AvxX4LoopWOutInv\nimport Hashtree.Proofs.AvxX4LoopWFrame\n",
       "\n/-! R2c x4 — the shape of a turn's write log and its four digests (generated). -/\n",
       HEAD, OPENS, "open Hashtree.Proofs.Avx512X16WOut (OutOk invC_lift invC_lift')\n", f"\nnamespace {NS}\n\n"]
out.append("""/-- Every logged cell is an output cell at `sym 1 + o`, `o < 128`, or a stack cell `sAt k`,
`-568 ≤ k < 0`. -/
def outShape4 (K : State E Lin) : Bool :=
  K.mem.all fun p =>
    (p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 128)) ||
    (p.1.region == rStack && p.1.off.c == Hashtree.Asm.X86SymW.stkC && decide (-568 ≤ p.1.off.k) && decide (p.1.off.k < 0))

theorem KHpW_outShape4 : outShape4 KHpW = true := by decide +kernel
theorem K201W_outShape4 : outShape4 K201W = true := by decide +kernel

theorem out_eval4 (σ : Nat → Int) (k : Int) : (⟨k, [0, 1]⟩ : Lin).eval σ = σ 1 + k := by
  show k + (0 * σ 0 + (1 * σ (0 + 1) + 0)) = σ 1 + k
  rw [show (0 + 1 : Nat) = 1 from rfl]
  omega

theorem outShape4_sound (K : State E Lin) (h : outShape4 K = true) (e : Key → W32) (σ : Nat → Int) :
    ∀ p ∈ (mapState e σ K).mem,
      (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128) ∨
      (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [outShape4, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨qr, qk, qc⟩, qcell⟩ := q
  rcases h _ hq with ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩ | ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    left
    show rOut = rOut ∧ σ 1 ≤ (⟨qk, [0, 1]⟩ : Lin).eval σ ∧ (⟨qk, [0, 1]⟩ : Lin).eval σ < σ 1 + 128
    rw [out_eval4]
    exact ⟨rfl, by omega, by omega⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    right
    show rStack = rStack ∧ σ 9 - 568 ≤ (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ ∧
      (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ < σ 9
    rw [Hashtree.Proofs.AvxX4LoopWFrame.sAt_eval]
    exact ⟨rfl, by omega, by omega⟩

""")
out.append(outOk_thm("KHpW"))
out.append(outOk_thm("K201W"))
out.append(f"end {NS}\n")
open("Hashtree/Proofs/AvxX4LoopWOutTail.lean", "w").write("".join(out))
print("written: lab", 201, "checks", len(checks), "cases", len(cases))
