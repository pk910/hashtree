#!/usr/bin/env python3
"""Generate the R2c windows-x4 modules (windows avx_x4 W-mode loop, output correctness).
Run from formal/lean.  Reads the pilot (Gen/WinAvxX4P) and R2's W slices (WinAvxX4WBodyP*,
WinAvxX4WBodyS*), writes:
  WinAvxX4WOutLab.lean        w4lab_k : T_k.map fst = L_{k+1}.map fst (k = 3..203)
  WinAvxX4WOutInvW.lean       pass-1 body: lifted steps w4stepW_k, chain w4invW_body (L3 -> L203)
  WinAvxX4WOutInvS.lean       later-pass body (stripped cuts): w4stepS_k, w4invS_body
  WinAvxX4WOutChk1/2.lean     the four tails re-checked WITH the pilot's T203 (W: KT/KTE, S: KTs/KTEs)
  WinAvxX4WOutCells1/2.lean   log shapes of the four tail cuts + the (o,id,b) output-cell tables
  WinAvxX4WOutDig1/2.lean     the 4 digests of each tail cut from InvC .. L204 (pilot out_final cases)
  WinAvxX4WOutTail.lean       the four lifted tail steps (L203 -> L204)
The slices 0..2 of the pilot track nothing (L1 = L2 = L3 = []), so the chains start at L3.
Usage: gen_r2c_x4w.py"""
import re, glob

G = "Hashtree/Gen/WinAvxX4P"
P = "Hashtree/Proofs"
NS = "Hashtree.Proofs.WinAvxX4WOut"
HEAD = """set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
"""
OPENS = """open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4 Hashtree.Gen.WinAvxX4P
open Hashtree.Proofs.WinAvxX4W (m0W shiftKW orcB orcEx KT KTE)
"""
STRIP = "open Hashtree.Proofs.WinAvxX4WStrip (m0WP stripKW KHs KH3s KTs KTEs)\n"

# ---------- the pilot slices ----------
pil = {}
for k in range(1, 204):
    s = open(f"{G}/P{k}.lean").read()
    m = re.search(rf"theorem slice{k} : sliceCheck prog 4 m0q (\(fun pc => decide \(pc ∈ \(\[[^\]]*\] : List Nat\)\)\)) (\d+) K{k} K{k+1} T{k} = true", s)
    assert m, k
    pil[k] = (m.group(1), int(m.group(2)))

# ---------- R2's W slices (pass 1) and S slices (later passes) ----------
wsl, ssl = {}, {}
for f in sorted(glob.glob(f"{P}/WinAvxX4WBodyP*.lean")):
    for m in re.finditer(r"theorem sliceW_(\d+) : sliceCheck prog 4 m0W (\(fun pc => decide \(pc ∈ \(\[[^\]]*\] : List Nat\)\)\)) (\d+) \(shiftKW K(\d+)\) \(shiftKW K(\d+)\) T(\d+) = true", open(f).read()):
        k = int(m.group(1)); assert int(m.group(4)) == k and int(m.group(5)) == k + 1 and int(m.group(6)) == k
        wsl[k] = (m.group(2), int(m.group(3)))
for f in sorted(glob.glob(f"{P}/WinAvxX4WBodyS[0-9].lean")):
    for m in re.finditer(r"theorem sliceS_(\d+) : sliceCheck prog 4 m0WP (\(fun pc => decide \(pc ∈ \(\[[^\]]*\] : List Nat\)\)\)) (\d+) \(stripKW K(\d+)\) \(stripKW K(\d+)\) T(\d+) = true", open(f).read()):
        k = int(m.group(1)); assert int(m.group(4)) == k and int(m.group(5)) == k + 1 and int(m.group(6)) == k
        ssl[k] = (m.group(2), int(m.group(3)))
assert sorted(wsl) == list(range(2, 203)), sorted(wsl)[:3]
assert sorted(ssl) == list(range(4, 203)), sorted(ssl)[:3]
for k in range(3, 203):
    assert wsl[k][1] == pil[k][1], k
for k in range(4, 203):
    assert ssl[k][1] == pil[k][1], k

def W(name, body):
    open(f"{P}/{name}.lean", "w").write(body)

# ---------- Lab ----------
out = ["import Hashtree.Proofs.Avx512X16WOutBase\n", "".join(f"import Hashtree.Gen.WinAvxX4P.D{k}\n" for k in range(2, 204)),
       "\n/-! R2c windows x4 — the pilot's tree lists track exactly the next cut's labels (generated; `decide`). -/\n\n",
       HEAD, "\nopen Hashtree.Asm Hashtree.Gen.WinAvxX4P\n\n", f"namespace {NS}\n\n"]
for k in range(3, 204):
    out.append(f"theorem w4lab_{k} : T{k}.map (·.1) = L{k+1}.map (·.1) := by decide\n")
out.append(f"\nend {NS}\n")
W("WinAvxX4WOutLab", "".join(out))

# ---------- Inv (W: pass 1, S: later passes) ----------
LIFT = "open Hashtree.Proofs.Avx512X16WOut (invC_lift invC_lift')\n"
def inv_file(mode):
    imps = ["import Hashtree.Proofs.WinAvxX4WOutLab\n",
            "import Hashtree.Proofs.WinAvxX4WBody\n" if mode == "W" else "import Hashtree.Proofs.WinAvxX4WBodyS\n"]
    imps += [f"import Hashtree.Gen.WinAvxX4P.P{k}\n" for k in range(3, 203)]
    what = "pass-1 body (`WinAvxX4WBody`, from `shiftKW K3`)" if mode == "W" else \
        "later-pass body (`WinAvxX4WBodyS`, stripped cuts, from `KH3s`)"
    out = ["".join(imps), f"\n/-! R2c windows x4 — the pilot's invariant chain lifted to the {what} (generated). -/\n\n",
           HEAD, "\n", OPENS, STRIP if mode == "S" else "", LIFT, f"\nnamespace {NS}\n\n"]
    for k in range(3, 203):
        orcS, n = pil[k]
        if mode == "W":
            orcW, _ = wsl[k]
            KW, KW1, mem, sl = f"(shiftKW K{k})", f"(shiftKW K{k+1})", "m0W", f"Hashtree.Proofs.WinAvxX4WBody.sliceW_{k}"
        else:
            if k == 3:
                orcW, KW, KW1, sl = "orcB", "KH3s", "(stripKW K4)", "Hashtree.Proofs.WinAvxX4WBodyS.sliceV3s"
            else:
                orcW, _ = ssl[k]
                KW, KW1, sl = f"(stripKW K{k})", f"(stripKW K{k+1})", f"Hashtree.Proofs.WinAvxX4WBodyS.sliceS_{k}"
            mem = "m0WP"
        out.append(f"""theorem w4step{mode}_{k} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{k}) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 {mem} {orcW} {n} {KW})) L{k+1} :=
  invC_lift inp env prog 4 m0q {mem} _ _ {n} K{k} K{k+1} {KW} {KW1} T{k} L{k+1}
    slice{k} {sl} w4lab_{k} (step{k} inp env hI hm)

""")
    Gm = "Hashtree.Proofs.WinAvxX4WBody.G" if mode == "W" else "Hashtree.Proofs.WinAvxX4WBodyS.GS"
    out.append(f"""/-- The body chain: from `{Gm}3 env1` (`L3 = []`) to `L203` at `{Gm}203 env1`. -/
theorem w4inv{mode}_body (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 256 inp env1) :
    InvC inp ({Gm}203 env1) L203 := by
  have i3 : InvC inp ({Gm}3 env1) L3 := True.intro
""")
    for k in range(3, 203):
        out.append(f"  have i{k+1} : InvC inp ({Gm}{k+1} env1) L{k+1} := w4step{mode}_{k} inp ({Gm}{k} env1) i{k} hm\n")
    out.append(f"  exact i203\n\nend {NS}\n")
    W(f"WinAvxX4WOutInv{mode}", "".join(out))
inv_file("W")
inv_file("S")

# ---------- Chk: the tails with the pilot's trees ----------
CHKS = {
    "1": ("import Hashtree.Proofs.WinAvxX4WShift\nimport Hashtree.Gen.WinAvxX4P.D203\n",
          [("w4chkT_turn", "sliceCheck prog 4 m0W orcB 25 (shiftKW K203) KT T203 = true"),
           ("w4chkT_exit", "sliceCheck prog 4 m0W orcEx 37 (shiftKW K203) KTE T203 = true")]),
    "2": ("import Hashtree.Proofs.WinAvxX4WStripDefs\nimport Hashtree.Gen.WinAvxX4P.D203\n",
          [("w4chkT_turnS", "sliceCheck prog 4 m0WP orcB 25 (stripKW K203) KTs T203 = true"),
           ("w4chkT_exitS", "sliceCheck prog 4 m0WP orcEx 37 (stripKW K203) KTEs T203 = true")]),
}
for f, (imp, chks) in CHKS.items():
    out = [imp, f"\n/-! R2c windows x4 — the loop tails re-checked with the pilot's trees `T203`, part {f} (generated). -/\n\n",
           HEAD, "\n", OPENS, STRIP if f == "2" else "", f"\nnamespace {NS}\n\n"]
    for (name, st) in chks:
        out.append(f"theorem {name} : {st} := by\n  decide +kernel\n\n")
    out.append(f"end {NS}\n")
    W(f"WinAvxX4WOutChk{f}", "".join(out))

# ---------- the pilot's out_final cases ----------
src = open(f"{G}/Final.lean").read().splitlines()
gl = [l for l in src if re.match(r"\s*have g\d+ := hF\.1; have hF := hF\.2", l)]
cases = []
i = 0
while i < len(src):
    m = re.match(r"\s*\| (\d+), (\d+), (\d+), _, _, _ => exact ⟨E204 env0 \(\.n (\d+)\), outCell_sound _ σ K204 (\d+) (\d+) (\d+) \(by decide\),", src[i])
    if m:
        m2 = re.match(r"\s*by rw \[show E204 env0 \(\.n (\d+)\) = qv inp \(\.HB (\d+) (\d+)\) from g(\d+),", src[i + 1])
        assert m2, src[i + 1]
        cases.append((m.groups(), m2.groups(), src[i + 2].strip()))
        i += 3
    else:
        i += 1
assert len(cases) == 128 and len(gl) == 536, (len(cases), len(gl))
tab = ", ".join(f"({o}, {id_}, {b})" for ((n, i_, b, id_, o, id2, b2), _, _) in cases)

SHAPE = """/-- Every logged cell of a tail cut is an output cell at `sym 1 + o`, `o < 128`, or a stack
cell `sAt k`, `-568 ≤ k < 0` (the kernel's own frame). -/
def outShapeW4 (K : State E Lin) : Bool :=
  K.mem.all fun p =>
    (p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 128)) ||
    (p.1.region == rStack && p.1.off.c == Hashtree.Asm.X86SymW.stkC && decide (-568 ≤ p.1.off.k) && decide (p.1.off.k < 0))

/-- The 128 `(o, id, b)` output cells of a tail cut (the pilot's `out_final` table). -/
def w4tab : List (Nat × Nat × Nat) := [""" + tab + """]

"""
CELLS = {"1": ("import Hashtree.Proofs.WinAvxX4WShift\n", ["KT", "KTE"], True),
         "2": ("import Hashtree.Proofs.WinAvxX4WOutCells1\nimport Hashtree.Proofs.WinAvxX4WStripDefs\n", ["KTs", "KTEs"], False)}
for f, (imp, Ks, first) in CELLS.items():
    out = [imp, f"\n/-! R2c windows x4 — the tail cuts' log shapes and output-cell tables, part {f} (generated; one `decide +kernel` per fact). -/\n\n",
           HEAD, "\n", OPENS, "" if first else STRIP, f"\nnamespace {NS}\n\n"]
    if first:
        out.append(SHAPE)
    for K in Ks:
        out.append(f"""theorem w4shape_{K} : outShapeW4 {K} = true := by decide +kernel

theorem w4cells_{K} : w4tab.all (fun t => outCell {K} t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem w4cell_{K} (o id b : Nat) (h : (o, id, b) ∈ w4tab) : outCell {K} o id b = true :=
  List.all_eq_true.mp w4cells_{K} (o, id, b) h

""")
    out.append(f"end {NS}\n")
    W(f"WinAvxX4WOutCells{f}", "".join(out))

# ---------- Dig: the digests ----------
def outOk_thm(K):
    s = [f"""/-- The write log of a tail ending in `{K}` holds the 4 digests, from the invariant at `L204`. -/
theorem w4outOk_{K} (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L204) :
    OutOk inp (σ 1) 4 (mapState e σ {K}).mem := by
  have hF := hI
"""]
    s += [l + "\n" for l in gl]
    s.append("  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n")
    for ((n, i_, b, id_, o, id2, b2), (id3, hn, hi, gk), l3) in cases:
        assert id_ == id2 == id3 and b == b2
        s.append(f"  | {n}, {i_}, {b}, _, _, _ => exact ⟨e (.n {id_}), outCell_sound _ σ {K} {o} {id_} {b} (w4cell_{K} _ _ _ (by decide)),\n")
        s.append(f"      by rw [show e (.n {id_}) = qv inp (.HB {hn} {hi}) from g{gk},\n        {l3}\n")
    s.append("  | _ + 4, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n")
    return "".join(s)
for f, Ks in [("1", ["KT", "KTE"]), ("2", ["KTs", "KTEs"])]:
    out = [f"import Hashtree.Proofs.WinAvxX4WOutCells{f}\nimport Hashtree.Proofs.Avx512X16WOutBase\nimport Hashtree.Gen.WinAvxX4P.D203\n",
           f"\n/-! R2c windows x4 — the four digests of a tail cut from the invariant at `L204`, part {f} (generated). -/\n\n",
           HEAD, "\n", OPENS, STRIP if f == "2" else "", "open Hashtree.Proofs.Avx512X16WOut (OutOk)\n", f"\nnamespace {NS}\n\n"]
    for K in Ks:
        out.append(outOk_thm(K))
    out.append(f"end {NS}\n")
    W(f"WinAvxX4WOutDig{f}", "".join(out))

# ---------- Tail: the lifted tail steps ----------
orc203, n203 = pil[203]
assert n203 == 37
out = ["import Hashtree.Proofs.WinAvxX4WOutInvW\nimport Hashtree.Proofs.WinAvxX4WOutInvS\n",
       "import Hashtree.Proofs.WinAvxX4WOutChk1\nimport Hashtree.Proofs.WinAvxX4WOutChk2\nimport Hashtree.Gen.WinAvxX4P.P203\n",
       "\n/-! R2c windows x4 — the pilot's last step (`K203 → K204`, the exit with the digest stores) lifted to the\nfour loop tails (generated). -/\n\n",
       HEAD, "\n", OPENS, STRIP, LIFT, f"\nnamespace {NS}\n\n"]
for (nm, mem, orc, n, KW, KW1, chk, lift) in [
        ("turn", "m0W", "orcB", 25, "(shiftKW K203)", "KT", "w4chkT_turn", "'"),
        ("exit", "m0W", "orcEx", 37, "(shiftKW K203)", "KTE", "w4chkT_exit", ""),
        ("turnS", "m0WP", "orcB", 25, "(stripKW K203)", "KTs", "w4chkT_turnS", "'"),
        ("exitS", "m0WP", "orcEx", 37, "(stripKW K203)", "KTEs", "w4chkT_exitS", "")]:
    if lift == "'":
        call = f"invC_lift' inp env prog 4 m0q _ 37 K203 K204 {mem} {orc} {n} {KW} {KW1} T203 L204"
    else:
        call = f"invC_lift inp env prog 4 m0q {mem} _ _ 37 K203 K204 {KW} {KW1} T203 L204"
    out.append(f"""theorem w4stepT_{nm} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 {mem} {orc} {n} {KW})) L204 :=
  {call}
    slice203 {chk} w4lab_203 (step203 inp env hI hm)

""")
out.append(f"end {NS}\n")
W("WinAvxX4WOutTail", "".join(out))
print("written: lab", 201, "W steps", 200, "S steps", 200, "cases", len(cases), "g", len(gl))
