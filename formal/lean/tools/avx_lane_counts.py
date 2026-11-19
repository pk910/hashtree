import re, glob

ROOT = "/root/ht/hashtree-x8x16/formal/lean"
slices = {}
for f in sorted(glob.glob(ROOT + "/Hashtree/Gen/Avx512X16P/P*.lean")):
    txt = open(f).read()
    for m in re.finditer(r"theorem slice(\d+) : sliceCheck prog 4 m0q \(fun pc => decide \(pc ∈ \((\[[0-9, ]*\] : List Nat)\)\)\) (\d+) (K\d+) (K\d+) (T\d+) = true", txt):
        j = int(m.group(1))
        slices[j] = dict(orc=m.group(2), n=int(m.group(3)), k0=m.group(4), k1=m.group(5), T=m.group(6))
for j in range(1, 216):
    assert j in slices and slices[j]['k0'] == 'K%d' % j and slices[j]['k1'] == 'K%d' % (j + 1)
    assert slices[j]['orc'] == '[] : List Nat' and slices[j]['T'] == 'T%d' % j

EMPTY = "(fun pc => decide (pc ∈ ([] : List Nat)))"
NS = "Hashtree.Proofs.Avx512X16WBody"

def rsum(ns):
    if len(ns) == 1:
        return str(ns[0])
    return "%d + (%s)" % (ns[0], rsum(ns[1:]))

out = []
out.append("""import Hashtree.Gen.Avx512X16P.P215
import Hashtree.Asm.X86SymW
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
  Hashtree.Kernels.X86.Avx512X16
namespace %s
open Hashtree.Gen.Avx512X16P

/-!
# The body of the AVX-512 16-lane kernel in the wrapper's call state, at every count

`Hashtree/Proofs/Avx512X16Body` proves the 215 branch-free body slices (`K1 .. K216`) at an
arbitrary environment and count `c = σ 2 >= 16`, but from the system V entry state
`entryS 24`, whose stack pointer is the constant offset `24` and whose dead registers hold
numbered variables.

The wrapper calls the kernel at `entryW` (`Hashtree/Asm/X86SymW`), whose caller-saved
registers point into the wrapper's frame and whose stack cells are addressed relative to the
symbol `9`.  This file replays the same 215 instructions from that call state.  The kernel
pushes nothing (`mem0sW 4 rodata []`) and never reads the registers that distinguish the two
call states, so the body semantics are unchanged and every slice re-checks.

`wcutH` is the loop-head form of a pilot cut: `rbx, rsp, rbp, r12..r15` carry the caller's
values (the body leaves them alone), and `rax`'s spare copy of the output pointer is frozen
on the symbol `10` (the loop substitution `tau` only renames `0`, `1`, `2`, so it survives
every turn).  `wcutE` is the same cut with `rax` still holding the wrapper's
`ptr <rOut, sym 1>`; the entry slice establishes it and `Avx512X16WEntry` bridges it to the
loop head.

`body_runW` and `body_memW` are the count-general body results at the global region 4.
-/

/-- Register `i` of the wrapper's call state (numbered variables beyond the sixteen). -/
def ew (i : Nat) : Val E Lin := entryW.gpr.getD i (.num (.var (.n 0)) (.var (.n 0)))

/-- The loop-head form of a pilot cut. -/
def wcutH (s : State E Lin) : State E Lin :=
  { s with gpr := s.gpr.set 0 (.ptr (⟨rOut, Lin.sym 10⟩ : Addr Lin))
      |>.set 3 (ew 3) |>.set 4 (ew 4) |>.set 5 (ew 5)
      |>.set 12 (ew 12) |>.set 13 (ew 13) |>.set 14 (ew 14) |>.set 15 (ew 15) }

/-- The entry form of a pilot cut (`rax` still holds the wrapper's output pointer). -/
def wcutE (s : State E Lin) : State E Lin :=
  { wcutH s with gpr := (wcutH s).gpr.set 0 (ew 0) }

/-- The initial memory of a call to the kernel at region 4 (nothing is pushed). -/
def mW : Addr Lin → Cell E Lin := mem0sW 4 rodata []

theorem mW_keyed : MemKeyed mW := mem0sW_keyed 4 rodata [] (by decide)
""" % NS)

# slice theorems 1..215
out.append("")
out.append("/-! ## The 215 branch-free body slices at the wrapper's call state -/\n")
for j in range(1, 216):
    s = slices[j]
    out.append("theorem sliceW_%d : sliceCheck prog 4 mW %s %d (wcutH %s) (wcutH %s) %s = true := by\n  decide +kernel\n"
               % (j, EMPTY, s['n'], s['k0'], s['k1'], s['T']))

# A0 and asmge
out.append("""
/-! ## The two entry conditions hold for every remaining count -/

def A0 : List (Cond Lin × Bool) := [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), false), ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem asmge (σ : Nat → Int) (hge : 16 ≤ σ 2) :
    ∀ p ∈ A0, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
""")

# env chain
out.append("/-! ## The environment chain through the body -/\n")
out.append("def G1 (env1 : Key → W32) : Key → W32 := env1")
for j in range(1, 216):
    s = slices[j]
    out.append("def G%d (env1 : Key → W32) : Key → W32 := envAbs (G%d env1) (run prog 4 mW %s %d (wcutH %s))"
               % (j + 1, j, EMPTY, s['n'], s['k0']))

# body_run
nums = [slices[j]['n'] for j in range(1, 216)]
total = rsum(nums)
out.append("""
/-- **The body at every count, at the wrapper's call state.**  The 215 branch-free slices
run from the loop head `wcutH K1` to `wcutH K216` at any count `c >= 16`, using only the
pilot's two entry conditions. -/
theorem body_runW (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel (G1 env1) σ mW mem0c) (hge : 16 ≤ σ 2) :
    run prog 4 mem0c orcC (%s) (mapState (G1 env1) σ (wcutH K1)) =
      mapState (G216 env1) σ (wcutH K216) := by
  have kq : MemKeyed mW := mW_keyed
  have m1 : Mem0Rel (G1 env1) σ mW mem0c := h0""" % total)
for j in range(1, 216):
    out.append("  have m%d : Mem0Rel (G%d env1) σ mW mem0c := mem0Rel_envAbs _ σ _ mem0c kq m%d _"
               % (j + 1, j + 1, j))
for j in range(1, 216):
    s = slices[j]
    out.append("  have r%d : run prog 4 mem0c orcC %d (mapState (G%d env1) σ (wcutH %s)) = mapState (G%d env1) σ (wcutH %s) := (slice_sound (G%d env1) σ mW mem0c m%d prog 4 %s orcC %d (wcutH %s) (wcutH %s) %s sliceW_%d rfl (assumeOk_of σ (wcutH %s) A0 rfl (asmge σ hge))).1"
               % (j, s['n'], j, s['k0'], j + 1, s['k1'], j, j, EMPTY, s['n'], s['k0'], s['k1'], s['T'], j, s['k1']))
for j in range(1, 215):
    out.append("  rw [run_add, r%d]" % j)
out.append("  exact r215\n")

# body_mem
out.append("""
/-- The memory relation is carried along the same chain. -/
theorem body_memW (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (h0 : Mem0Rel (G1 env1) σ mW mem0c) :
    Mem0Rel (G216 env1) σ mW mem0c := by
  have kq : MemKeyed mW := mW_keyed
  have m1 : Mem0Rel (G1 env1) σ mW mem0c := h0""")
for j in range(1, 216):
    out.append("  have m%d : Mem0Rel (G%d env1) σ mW mem0c := mem0Rel_envAbs _ σ _ mem0c kq m%d _"
               % (j + 1, j + 1, j))
out.append("  exact m216\n")
out.append("end %s\n" % NS)

open(ROOT + "/Hashtree/Proofs/Avx512X16WBody.lean", "w").write("\n".join(out))
print("wrote", sum(len(x) for x in out), "chars")
