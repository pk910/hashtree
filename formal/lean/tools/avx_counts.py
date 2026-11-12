#!/usr/bin/env python3
"""Generate the count-general body and loop-turn proofs for the x86 multi-lane kernels.

The generated `Hashtree/Gen/Avx*` pilots check each multi-lane kernel at exactly one count
(4, 8 or 16 blocks).  Their *first* slices up to the last body cut contain no taken branch
(only the entry slice and the exit slice branch), and every body slice records the same
assumption list.  Since `slice_sound` is stated for an arbitrary `σ : Nat → Int`, those
slice checks can be composed at any count for which the recorded conditions hold, which
gives the count-general body segment.  The x4 loop turn additionally composes the 68-step
head slice and the branch-free 23-step loop tail (`add rsi,256; add rdi,128; sub rdx,4;
jmp 5`), and proves the turn's end state is a substitution instance of the loop invariant
head (`KHL2_shape`) for `mapState_reached`.

Usage:

  python3 tools/avx_counts.py body x8 209  > Hashtree/Proofs/Avx2X8Body.lean
  python3 tools/avx_counts.py body x16 215 > Hashtree/Proofs/Avx512X16Body.lean
  python3 tools/avx_counts.py turn 199     > Hashtree/Proofs/AvxX4LoopTurn.lean

Output goes to stdout; the slices and cuts are read from the committed pilot trees.
These files are pure compositions of the pilot's slice lemmas -- no new `decide` proofs.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN = os.path.join(ROOT, "Hashtree", "Gen")

BODY_CFG = {
    "x8": dict(dir="Avx2X8P", W=8, asm="asm1", Alist="A1",
               A='[((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), false), '
                 '((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]',
               ns="Avx2X8Body", kernel="Avx2X8", desc="AVX2 8-lane"),
    "x16": dict(dir="Avx512X16P", W=16, asm="asm0", Alist="A0",
                A='[((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), false), '
                  '((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]',
                ns="Avx512X16Body", kernel="Avx512X16", desc="AVX-512 16-lane"),
}


def parse_final(dirname):
    final = os.path.join(GEN, dirname, "Final.lean")
    lines = open(final).read().splitlines()
    edefs, mlines, rlines = {}, {}, {}
    for ln in lines:
        m = re.match(r"def E(\d+) \(env0 : Key → W32\) : Key → W32 := (.*)$", ln)
        if m:
            edefs[int(m.group(1))] = m.group(2)
        m = re.match(r"\s*have m(\d+) : (Mem0Rel \(E(\d+) env0\) σ m0q mem0c := .*)$", ln)
        if m:
            assert int(m.group(1)) == int(m.group(3))
            mlines[int(m.group(1))] = m.group(2)
        m = re.match(r"\s*have r(\d+) : (.*)$", ln)
        if m:
            rlines[int(m.group(1))] = m.group(2)
    assert 1 in edefs, sorted(edefs)[:3]
    assert 1 in mlines and 1 in rlines
    return edefs, mlines, rlines


def lens_of(rlines, M):
    lens = {}
    for j in range(1, M + 1):
        m = re.search(r"run prog \S+ mem0c orcC (\d+) ", rlines[j])
        assert m, rlines[j][:120]
        lens[j] = int(m.group(1))
    return lens


def nested_sum(lens, M):
    """Final.lean states composed run lengths as a right-nested binary `+`, so that
    `rw [run_add, r{j}]` can split off the first slice; keep that syntax."""
    s = str(lens[M])
    for j in range(M - 1, 0, -1):
        s = f"{lens[j]} + ({s})"
    return s


HEADER_FOOTER = []


def emit_body(name, M):
    cfg = BODY_CFG[name]
    W = cfg["W"]
    edefs, mlines, rlines = parse_final(cfg["dir"])
    assert (M + 1) in edefs, sorted(edefs)[-3:]
    assert M in mlines and M in rlines
    lens = lens_of(rlines, M)
    total = sum(lens.values())
    sumexpr = nested_sum(lens, M)
    Kc = f"K{M+1}"

    out = []
    a = out.append
    a("import Hashtree.Asm.Chain")
    if name == "x8":
        # x8's cut states live in the D modules, and each P module imports only its own
        # D{j}/D{j-1}; import every P module up to M to have K1 .. K{M+1} in scope.
        for j in range(M + 1):
            a(f"import Hashtree.Gen.{cfg['dir']}.P{j}")
    else:
        a(f"import Hashtree.Gen.{cfg['dir']}.P{M}")
    a("set_option maxRecDepth 200000")
    a("set_option maxHeartbeats 0")
    a("set_option linter.unusedVariables false")
    a("set_option linter.unusedSimpArgs false")
    a("")
    a(f"open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.{cfg['kernel']}")
    a(f"namespace Hashtree.Proofs.{cfg['ns']}")
    a(f"open Hashtree.Gen.{cfg['dir']}")
    a("")
    a("/-!")
    a(f"# The branch-free body of the {cfg['desc']} kernel at every count")
    a("")
    a(f"The pilot tree `Hashtree/Gen/{cfg['dir']}` checks the kernel at count {W}.  Its slices")
    a(f"`1 .. {M}` contain no taken branch (only the entry slice `0` and the exit slice `{M+1}`")
    a(f"branch), and their recorded assumption lists are all `{cfg['Alist']}`, which hold for")
    a(f"every count `c ≥ {W}`.  `body_run` composes those {M} slice checks at an arbitrary")
    a(f"symbolic environment `env1` and an arbitrary `σ` with `{W} ≤ σ 2`, from the pilot's cut")
    a(f"`K1` to `{Kc}`; `body_mem` carries the memory-relation invariant along the same chain.")
    a("")
    a("This shows that the body's lane semantics do not depend on the count.  It is not a")
    a("`KSpec`: the kernel leaves through a tail call to the next kernel down (and the")
    a(f"`c < lane width` exit path at slice `{M+1}` is excluded), and neither the loop")
    a("iteration/framing nor the tail chain is modelled here.")
    a("-/")
    a("")
    a("def G1 (env1 : Key → W32) : Key → W32 := env1")
    for j in range(2, M + 2):
        body = edefs[j].replace(f"(E{j-1} env0)", f"(G{j-1} env1)")
        assert "env0" not in body, body[:200]
        a(f"def G{j} (env1 : Key → W32) : Key → W32 := {body}")
    a("")
    a(f"/-- The pilot's `{cfg['Alist']}` at an arbitrary remaining count `c ≥ {W}`. -/")
    a(f"def {cfg['Alist']} : List (Cond Lin × Bool) := {cfg['A']}")
    a("")
    a(f"theorem asmge (σ : Nat → Int) (hge : {W} ≤ σ 2) :")
    a(f"    ∀ p ∈ {cfg['Alist']}, (mapCond σ p.1).decideC = some p.2 := by")
    a("  intro p hp")
    a(f"  simp only [{cfg['Alist']}, List.mem_cons, List.mem_nil_iff, or_false] at hp")
    a("  rcases hp with rfl | rfl")
    a("  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]")
    a("    omega")
    a("  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]")
    a("    omega")
    a("")
    mchain = ["  have m1 : Mem0Rel (G1 env1) σ m0q mem0c := h0"]
    for j in range(2, M + 2):
        ml = mlines[j].replace(f"Mem0Rel (E{j} env0)", f"Mem0Rel (G{j} env1)")
        assert "env0" not in ml, ml[:200]
        mchain.append(f"  have m{j} : {ml}")

    a(f"/-- The pilot's {M} branch-free body slices, composed at an arbitrary environment and")
    a(f"for every remaining count `c ≥ {W}` (only `{cfg['Alist']}` is used). -/")
    a("theorem body_run (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)")
    a("    (orcC : Nat → Bool) (h0 : Mem0Rel (G1 env1) σ m0q mem0c) (hge : %d ≤ σ 2) :" % W)
    a(f"    run prog 4 mem0c orcC ({sumexpr}) (mapState (G1 env1) σ K1) =")
    a(f"      mapState (G{M+1} env1) σ {Kc} := by")
    a("  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24")
    for ln in mchain:
        a(ln)
    for j in range(1, M + 1):
        rl = re.sub(r"\(E(\d+) env0\)", r"(G\1 env1)", rlines[j])
        rl = rl.replace(f"({cfg['asm']} σ hσ)", "(asmge σ hge)")
        assert "env0" not in rl and "hσ" not in rl, rl[:300]
        a(f"  have r{j} : {rl}")
    for j in range(1, M):
        a(f"  rw [run_add, r{j}]")
    a(f"  exact r{M}")
    a("")
    a("theorem body_mem (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)")
    a("    (h0 : Mem0Rel (G1 env1) σ m0q mem0c) :")
    a(f"    Mem0Rel (G{M+1} env1) σ m0q mem0c := by")
    a("  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24")
    for ln in mchain:
        a(ln)
    a(f"  exact m{M+1}")
    a("")
    a(f"end Hashtree.Proofs.{cfg['ns']}")
    return "\n".join(out) + "\n", total


def emit_turn(M):
    edefs, mlines, rlines = parse_final("AvxX4P")
    assert (M + 1) in edefs and 1 in edefs, sorted(edefs)[-3:]
    assert M in mlines and M in rlines
    lens = lens_of(rlines, M)
    total = sum(lens.values())
    sumexpr = nested_sum(lens, M)
    Kc, Kp = f"K{M+1}", "KH'"

    out = []
    a = out.append
    a("import Hashtree.Asm.Chain")
    a("import Hashtree.Asm.Subst")
    a("import Hashtree.Asm.X86Loop")
    a("import Hashtree.Proofs.AvxX4LoopHead")
    a(f"import Hashtree.Gen.AvxX4P.P{M}")
    a("set_option maxRecDepth 200000")
    a("set_option maxHeartbeats 0")
    a("set_option linter.unusedVariables false")
    a("set_option linter.unusedSimpArgs false")
    a("")
    a("open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.AvxX4")
    a("namespace Hashtree.Proofs.AvxX4LoopTurn")
    a("open Hashtree.Gen.AvxX4P")
    a("")
    a("/-!")
    a("# The avx_x4 loop turn at every count")
    a("")
    a("The pilot tree `Hashtree/Gen/AvxX4P` checks the kernel at count 4.  `KHL2` is the loop")
    a("invariant head at pc 5 (`KHL` from `Hashtree/Proofs/AvxX4LoopHead` with the digest lanes")
    a("of the end-of-body cut, which the body overwrites before reading).  One turn is the")
    a("68-step head slice, the 199 branch-free body slices and the 23-step loop tail")
    a("(`add rsi,256; add rdi,128; sub rdx,4; jmp 5`).  `turn_run` proves that turn from the")
    a("pilot's concrete memory for every count `c = σ 2 ≥ 4`, using only the entry conditions")
    a("`A0` (`c < 4` false, `c ≠ 0` true); `turn_step` rewrites the reached state as an")
    a("instance of `KHL2` under `sigmaOf tau σ`, seen through the turn's memory log.")
    a("")
    a("This is a single-turn result: iterating it over a symbolic count needs a framing")
    a("lemma that replays a slice under an already accumulated memory log.  Together with the")
    a("tail chain (x4 -> x1), that is what a `KSpec` for arbitrary counts still requires.")
    a("-/")
    a("")
    a("/-- The environment chain at the loop head: `G1` is the head environment, `G{j+1}` the")
    a("env after slice `j` (the pilot's `E{j+1}` with the entry segment removed). -/")
    a("def G1 (env1 : Key → W32) : Key → W32 := env1")
    for j in range(2, M + 2):
        body = edefs[j].replace(f"(E{j-1} env0)", f"(G{j-1} env1)")
        assert "env0" not in body, body[:200]
        a(f"def G{j} (env1 : Key → W32) : Key → W32 := {body}")
    a("")
    a("/-- The pilot's two entry conditions (slice 0); identical to `AvxX4P.Final`'s `A0`. -/")
    a("def A0 : List (Cond Lin × Bool) := "
      "[((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), false), "
      "((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]")
    a("")
    a("/-- The two entry conditions `A0` hold for every remaining count at least the lane width. -/")
    a("theorem asm0ge (σ : Nat → Int) (hge : 4 ≤ σ 2) :")
    a("    ∀ p ∈ A0, (mapCond σ p.1).decideC = some p.2 := by")
    a("  intro p hp")
    a("  simp only [A0, List.mem_cons, List.mem_nil_iff, or_false] at hp")
    a("  rcases hp with rfl | rfl")
    a("  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]")
    a("    omega")
    a("  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]")
    a("    omega")
    a("")
    mchain = ["  have m1 : Mem0Rel (G1 env1) σ m0q mem0c := h0"]
    for j in range(2, M + 2):
        ml = mlines[j].replace(f"Mem0Rel (E{j} env0)", f"Mem0Rel (G{j} env1)")
        assert "env0" not in ml, ml[:200]
        mchain.append(f"  have m{j} : {ml}")

    a(f"/-- The pilot's body slices `1 .. {M}` composed at an arbitrary environment: from")
    a(f"`K1` to `{Kc}`, for every count at least the lane width. -/")
    a("theorem body_run (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)")
    a("    (orcC : Nat → Bool) (h0 : Mem0Rel (G1 env1) σ m0q mem0c) (hge : 4 ≤ σ 2) :")
    a(f"    run prog 4 mem0c orcC ({sumexpr}) (mapState (G1 env1) σ K1) =")
    a(f"      mapState (G{M+1} env1) σ {Kc} := by")
    a("  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24")
    for ln in mchain:
        a(ln)
    for j in range(1, M + 1):
        rl = re.sub(r"\(E(\d+) env0\)", r"(G\1 env1)", rlines[j])
        rl = rl.replace("(asm0 σ hσ)", "(asm0ge σ hge)")
        assert "env0" not in rl and "hσ" not in rl, rl[:300]
        a(f"  have r{j} : {rl}")
    for j in range(1, M):
        a(f"  rw [run_add, r{j}]")
    a(f"  exact r{M}")
    a("")
    a("/-- The memory invariant carried by the same chain (needed to enter the tail). -/")
    a("theorem body_mem (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)")
    a("    (h0 : Mem0Rel (G1 env1) σ m0q mem0c) :")
    a(f"    Mem0Rel (G{M+1} env1) σ m0q mem0c := by")
    a("  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24")
    for ln in mchain:
        a(ln)
    a(f"  exact m{M+1}")
    a("")
    a("/-! ## The 23-instruction loop tail (branch-free, independent of the count) -/")
    a("")
    a(f"/-- The loop head reached from `{Kc}`: `add rsi,256; add rdi,128; sub rdx,4; jmp 5`. -/")
    a(f"def {Kp} : State E Lin := abstract (run prog 4 m0q (fun _ => false) 23 {Kc})")
    a("")
    a(f"theorem {Kp}_slice : sliceCheck prog 4 m0q (fun _ => false) 23 {Kc} {Kp} [] = true := by")
    a("  decide +kernel")
    a(f"theorem {Kp}_pc : {Kp}.pc = 5 := by decide +kernel")
    a(f"theorem {Kp}_halted : {Kp}.halted = false := by decide +kernel")
    a(f"theorem {Kp}_tail : {Kp}.tail = none := by decide +kernel")
    a(f"theorem {Kp}_assume : {Kp}.assume = A0 := by decide +kernel")
    a(f"theorem {Kc}_err : {Kc}.err = none := by decide +kernel")
    a("")
    a("/-- The loop substitution: next input, next output, four blocks fewer, fresh flags. -/")
    a("def tau : List Lin :=")
    a(f"  match {Kp}.flags with")
    a("  | some (a, b) => [⟨256, [1]⟩, ⟨128, [0, 1]⟩, ⟨-4, [0, 0, 1]⟩, a, b]")
    a("  | none => [⟨256, [1]⟩, ⟨128, [0, 1]⟩, ⟨-4, [0, 0, 1]⟩, Lin.sym 3, Lin.sym 4]")
    a("")
    a("/-- The loop invariant head: the pilot's `KHL` with the digest lanes of the loop tail.")
    a("The body overwrites these lanes before reading them, so both the head slice and the")
    a("entry/exit slices check unchanged. -/")
    a(f"def KHL2 : State E Lin := {{ KHL with vr := {Kp}.vr }}")
    a("")
    a("theorem KHL2_head : sliceCheck prog 4 m0q (fun _ => false) 68 KHL2 K1 [] = true := by")
    a("  decide +kernel")
    a("theorem KHL2_err : KHL2.err = none := by decide +kernel")
    a("/-- One full turn ends in a substitution instance of the invariant head. -/")
    a(f"theorem KHL2_shape : ({{ {Kp} with mem := [], assume := [] }} : State E Lin) =")
    a("    KHL2.substL tau := by")
    a("  decide +kernel")
    a("")
    a("/-- The loop step in the concrete state space: the state after a turn is an instance")
    a("of `KHL2` under `sigmaOf tau σ`, seen through the turn's memory log. -/")
    a(f"theorem turn_step (e : Key → W32) (σ : Nat → Int) :")
    a(f"    mapState e σ {Kp} =")
    a(f"      fr ({Kp}.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)))")
    a("        (mapState e (sigmaOf tau σ) KHL2) :=")
    a(f"  mapState_reached e σ {Kp} KHL2 tau KHL2_shape")
    a("")
    a("/-- **One loop turn at an arbitrary count.**  From the invariant head (with the pilot's")
    a("concrete memory `mem0c` and any oracle) the 68-step head slice, the 199 branch-free")
    a("body slices and the 23-step tail reach `KH'`, for every count `c = σ 2 ≥ 4`.  The only")
    a("count conditions used are `A0` (`c < 4` false, `c ≠ 0` true), so the lane semantics do")
    a("not depend on the count; each turn lowers the count by four. -/")
    a("theorem turn_run (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)")
    a("    (orcC : Nat → Bool) (h0 : Mem0Rel env σ m0q mem0c) (hge : 4 ≤ σ 2) :")
    a(f"    run prog 4 mem0c orcC (68 + ({sumexpr} + 23)) (mapState env σ KHL2) =")
    a(f"      mapState (envAbs (G{M+1} (envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2)))")
    a(f"        (run prog 4 m0q (fun _ => false) 23 {Kc})) σ {Kp} := by")
    a("  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24")
    a("  have hHead := (slice_sound env σ m0q mem0c h0 prog 4 (fun _ => false)")
    a("    orcC 68 KHL2 K1 [] KHL2_head KHL2_err")
    a("    (assumeOk_of σ K1 A0 rfl (asm0ge σ hge))).1")
    a("  have hHeadG : run prog 4 mem0c orcC 68 (mapState env σ KHL2) =")
    a("      mapState (G1 (envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2))) σ K1 := hHead")
    a(f"  have hm : Mem0Rel (envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2)) σ m0q mem0c :=")
    a("    mem0Rel_envAbs env σ m0q mem0c kq h0 _")
    a(f"  have hBody := body_run (envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2)) σ")
    a("    mem0c orcC hm hge")
    a(f"  have hm2 := body_mem (envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2)) σ mem0c hm")
    a(f"  have hTail := (slice_sound (G{M+1} (envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2)))")
    a(f"    σ m0q mem0c hm2 prog 4 (fun _ => false) orcC 23 {Kc} {Kp} []")
    a(f"    {Kp}_slice {Kc}_err (assumeOk_of σ {Kp} A0 {Kp}_assume (asm0ge σ hge))).1")
    a("  rw [run_add, hHeadG]")
    a("  rw [run_add, hBody]")
    a("  exact hTail")
    a("")
    a("end Hashtree.Proofs.AvxX4LoopTurn")
    return "\n".join(out) + "\n", total


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    what = sys.argv[1]
    if what == "body":
        if len(sys.argv) != 4:
            print(__doc__)
            return 2
        text, total = emit_body(sys.argv[2], int(sys.argv[3]))
    elif what == "turn":
        if len(sys.argv) != 3:
            print(__doc__)
            return 2
        text, total = emit_turn(int(sys.argv[2]))
    else:
        print(__doc__)
        return 2
    sys.stdout.write(text)
    print(f"-- generated: {what} ({total} steps)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
