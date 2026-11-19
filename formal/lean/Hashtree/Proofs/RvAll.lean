import Hashtree.Asm.RiscvSym
import Hashtree.Asm.RiscvSlice
import Hashtree.Asm.RiscvFrame
import Hashtree.Asm.X86Loop
import Hashtree.Spec

/-!
# Induction over the RV64 kernels' block loop

Shared part of the every-count proofs of `hashtree_sha256_riscv_x1`, `..._zbb_x1` and
`..._crypto`.  A kernel is covered by three generated segments:

* the prologue up to the loop-head cut `KH` (one slice, no branches);
* one iteration, from `KH` back to `KH` (pointers advanced by 64/32, count −1), its final cut
  reopened as `KH` by `Hashtree.Asm.mapState_reached_vars`;
* the exit for count 0, which reads the prologue's save slots.

This file contains the memory/output invariants, the log lemmas, the `HMem` shift for the
iteration's own input block, the `Mem0Rel` of the exit's symbolic save slots, and `rv_loop`: the
induction on the remaining count, parameterized by the segments' facts (so that all three
kernels share it).
-/

set_option maxRecDepth 10000

namespace Hashtree.Proofs.Rv
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym Hashtree.Asm.X86 Hashtree.Asm.SpecQ
  Hashtree.Spec

/-- Concrete memory logs (`X86.CLog` and `Riscv.CLog` are the same type). -/
abbrev CLog := List (Addr Int × Cell W32 Int)
/-- Concrete machine states. -/
abbrev CState := State W32 Int

/-- The first `nblk` output blocks (base `ob`) hold the SHA-256 bytes of the input blocks. -/
def OutOk (inp : Nat → Byte) (ob : Int) (nblk : Nat) (M : CLog) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

/-- Every logged write is an output byte in `[ob, ob + len)` or a byte of the kernel's 80-byte
frame below the entry stack pointer (`sp = -80`; the save slots `[-16,0)` are the prologue's). -/
def InRange (ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ -80 ≤ p.1.off ∧ p.1.off < 0)

theorem outLog_of (ob : Int) (len : Nat) (M : CLog) (h : InRange ob len M) : OutLog M := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, by omega⟩

theorem inRange_shift (ob ob' : Int) (k len : Nat) (L : CLog) (h : InRange ob' len L)
    (hob : ob' = ob + 32 * k) : InRange ob (32 * k + len) L := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, by omega, by omega⟩
  · exact Or.inr h

theorem above_of (ob : Int) (len : Nat) (L : CLog) (h : InRange ob len L) :
    ∀ p ∈ L, p.1.region ≠ rOut ∨ ob ≤ p.1.off := by
  intro p hp
  rcases h p hp with ⟨_, h2, _⟩ | ⟨h1, _⟩
  · exact Or.inr h2
  · exact Or.inl (by rw [h1]; decide)

theorem fr_fr (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

theorem fr_nil (s : CState) : fr [] s = s := by
  simp only [fr, List.append_nil]

theorem blk_shift (inp : Nat → Byte) (k n : Nat) : blk (fun o => inp (64 * k + o)) n = blk inp (k + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-- The input bytes of iteration `k`, relative to its input pointer. -/
theorem hmem_k (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (k : Nat) (e : Key → W32) (σ' : Nat → Int) (h0 : σ' 0 = σ0 + 64 * k) (M : CLog) (hM : OutLog M) :
    HMem 128 (fun o => inp (64 * k + o)) (ecomb e σ' (view M mem0c)) := by
  intro o _
  simp only [ecomb]
  rw [view_other M mem0c _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
    fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
  have ha : (⟨rIn, (⟨(o : Int), [1]⟩ : Lin).eval σ'⟩ : Addr Int) = ⟨rIn, σ0 + ((64 * k + o : Nat) : Int)⟩ := by
    simp only [Lin.eval, dotC, Addr.mk.injEq, true_and]
    omega
  rw [ha, hin]
  rfl

/-- The loop-head cut denotes the same with the memory keys re-read from memory. -/
theorem head_ecomb (e : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int) (K : State E Lin)
    (hK : K.nOnly = true) :
    mapState e σ' K = mapState (ecomb e σ' m) σ' K :=
  mapState_nOnly e (ecomb e σ' m) σ' (fun _ => rfl) K hK

/-- A log of a segment's writes: output bytes in `[σ' 1, σ' 1 + len)`, stack bytes strictly
below the prologue's save slots. -/
def TLog (σ' : Nat → Int) (len : Nat) (L : CLog) : Prop :=
  ∀ p ∈ L, (p.1.region = rOut ∧ σ' 1 ≤ p.1.off ∧ p.1.off < σ' 1 + len) ∨
    (p.1.region = rStack ∧ -80 ≤ p.1.off ∧ p.1.off < -16)

/-- A segment's log is disjoint from the prologue's save slots. -/
theorem log_ne_save (σ' : Nat → Int) {len : Nat} (L : CLog) (hL : TLog σ' len L) (a : Addr Int)
    (ha : a.region ≠ rOut ∧ (a.region = rStack → -16 ≤ a.off)) : ∀ p ∈ L, p.1 ≠ a := by
  intro p hp heq
  rcases hL p hp with ⟨h1, _, _⟩ | ⟨h1, _, h2⟩
  · rw [heq] at h1; exact ha.1 h1
  · rw [heq] at h1 h2; have := ha.2 h1; omega

/-- The mapped log of a segment, from its symbolic form. -/
theorem tlog_map (e : Key → W32) (σ' : Nat → Int) (L : List (Addr Lin × Cell E Lin)) (len : Nat)
    (hl : ∀ p ∈ L, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < len) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -80 ≤ p.1.off.k ∧ p.1.off.k < -16)) :
    TLog σ' len (L.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
    exact ⟨trivial, by omega, by omega⟩
  · right
    simp only [mapAddr, Lin.eval, h2, dotC, h1]
    exact ⟨trivial, by omega, by omega⟩

theorem inRange_map (e : Key → W32) (σ' : Nat → Int) (L : List (Addr Lin × Cell E Lin)) (len : Nat)
    (hl : ∀ p ∈ L, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < len) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -80 ≤ p.1.off.k ∧ p.1.off.k < -16)) :
    InRange (σ' 1) len (L.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases hl q hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    simp only [mapAddr, Lin.eval, h2, dotC, h1, Nat.zero_add]
    exact ⟨trivial, by omega, by omega⟩
  · right
    simp only [mapAddr, Lin.eval, h2, dotC, h1]
    exact ⟨trivial, by omega, by omega⟩

/-- The prologue's log: the save slots `[-16,0)` of the stack. -/
theorem inRange_map_save (e : Key → W32) (σ' : Nat → Int) (L : List (Addr Lin × Cell E Lin))
    (hl : ∀ p ∈ L, p.1.region = rStack ∧ p.1.off.c = [] ∧ -16 ≤ p.1.off.k ∧ p.1.off.k < 0) :
    InRange (σ' 1) 0 (L.map (fun p => (mapAddr σ' p.1, mapCell e σ' p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨h1, h2, h3, h4⟩ := hl q hq
  right
  simp only [mapAddr, Lin.eval, h2, dotC, h1]
  exact ⟨trivial, by omega, by omega⟩

theorem inRange_mono (ob : Int) (a b : Nat) (hab : a ≤ b) (M : CLog) (h : InRange ob a M) :
    InRange ob b M := by
  intro p hp
  rcases h p hp with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, h2, by omega⟩
  · exact Or.inr h

theorem inRange_app (ob : Int) (len : Nat) (L M : CLog) (hL : InRange ob len L) (hM : InRange ob len M) :
    InRange ob len (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- Output blocks below `lo` are not touched by a log above it. -/
theorem outOk_app (inp : Nat → Byte) (ob : Int) (n0 : Nat) (L M : CLog)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off) (hM : OutOk inp ob n0 M) :
    ∀ n i b, n < n0 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) (L ++ M) = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by
  intro n i b hn hi hb
  rw [lookup_app_right]
  · exact hM n i b hn hi hb
  · intro p hp heq
    rcases hL p hp with h | h
    · rw [heq] at h; exact h rfl
    · rw [heq] at h; simp only at h; omega

/-- The segment's new blocks, at block offset `n0`. -/
theorem outOk_new (inp : Nat → Byte) (ob : Int) (n0 nb : Nat) (L M : CLog) (σ1 : Int)
    (hσ1 : σ1 = ob + 32 * (n0 : Int))
    (hnew : ∀ n i b, n < nb → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) L = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp (n0 + n))).getD (4 * i + b) 0).zeroExtend 32)
    (hL : ∀ p ∈ L, p.1.region ≠ rOut ∨ ob + 32 * (n0 : Int) ≤ p.1.off) (hM : OutOk inp ob n0 M) :
    OutOk inp ob (n0 + nb) (L ++ M) := by
  intro n i b hn hi hb
  by_cases h : n < n0
  · exact outOk_app inp ob n0 L M hL hM n i b h hi hb
  · obtain ⟨x, hx, hv⟩ := hnew (n - n0) i b (by omega) hi hb
    refine ⟨x, ?_, ?_⟩
    · apply lookup_app_left
      rw [show ob + ((32 * n + 4 * i + b : Nat) : Int) = σ1 + ((32 * (n - n0) + 4 * i + b : Nat) : Int) by omega]
      exact hx
    · rw [show n = n0 + (n - n0) by omega]; exact hv

/-- `WfMemR` through a log (the log never holds input/rodata/GOT bytes). -/
theorem wf_viewR (rodata : List Nat) (gotT : List (Region × Int)) (m : Addr Int → Cell W32 Int) (M : CLog)
    (hM : OutLog M) (hw : WfMemR 10 11 rodata gotT m) : WfMemR 10 11 rodata gotT (view M m) := by
  obtain ⟨h1, h3, h5, hro, hgot, hin⟩ := hw
  have v10 : ∀ o, view M m ⟨10, o⟩ = m ⟨10, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show (10 : Region) ≠ rOut by decide,
      fun h => absurd (show (10 : Region) = rStack from h) (by decide)⟩)
  have v11 : ∀ o, view M m ⟨11, o⟩ = m ⟨11, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show (11 : Region) ≠ rOut by decide,
      fun h => absurd (show (11 : Region) = rStack from h) (by decide)⟩)
  have v1 : ∀ o, view M m ⟨rIn, o⟩ = m ⟨rIn, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
      fun h => absurd (show rIn = rStack from h) (by decide)⟩)
  refine ⟨h1, h3, h5, ?_, ?_, ?_⟩
  · intro o; rw [v10]; exact hro o
  · intro o r k ho hg; rw [v11]; exact hgot o r k ho hg
  · intro o; rw [v1]; exact hin o

/-- The exit segment's symbolic memory: `Mem0Rel` against the loop's accumulated log, given the
prologue's save slots (which the epilogue reads back). -/
theorem mem0RelT0 (rodata : List Nat) (gotT : List (Region × Int)) (saves : List Int)
    (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (M : CLog)
    (hw : WfMemR 10 11 rodata gotT mem0c) (hM : OutLog M)
    (hsave : ∀ o ∈ saves, ∃ x, view M mem0c ⟨rStack, o⟩ = .dat x (((o + 16) % 4).toNat)) :
    Mem0Rel (ecomb e σ (view M mem0c)) σ (mem0sT 10 11 rodata gotT saves) (view M mem0c) := by
  have hbase : Mem0Rel (ecomb e σ (view M mem0c)) σ (mem0s 10 11 rodata gotT) (view M mem0c) :=
    mem0RelR_of_wf 10 11 rodata gotT _ σ _ (wf_viewR rodata gotT mem0c M hM hw)
      (envMem_ecomb e σ (view M mem0c))
  intro a ha
  obtain ⟨r, off⟩ := a
  by_cases hreg : r = rStack
  · subst hreg
    have hbase' := hbase (⟨rStack, off⟩ : Addr Lin)
    cases hass : off.asInt with
    | none =>
      have hT : mem0sT 10 11 rodata gotT saves (⟨rStack, off⟩ : Addr Lin)
          = mem0s 10 11 rodata gotT (⟨rStack, off⟩ : Addr Lin) := by
        simp only [mem0sT, hass]
      rw [hT] at ha ⊢
      exact hbase' ha
    | some o =>
      by_cases hc : saves.contains o = true
      · have hT : mem0sT 10 11 rodata gotT saves (⟨rStack, off⟩ : Addr Lin)
            = .dat (.var (.m rStack off)) (((o + 16) % 4).toNat) := by
          simp only [mem0sT, hass]
          rw [if_pos (show True ∧ saves.contains o = true from ⟨trivial, hc⟩)]
        obtain ⟨x, hx⟩ := hsave o (List.contains_iff_mem.mp hc)
        rw [hT] at ha ⊢
        simp only [mapCell, E.eval, ecomb, mapAddr]
        rw [Lin.eval_asInt σ off o hass, hx]
        rfl
      · have hT : mem0sT 10 11 rodata gotT saves (⟨rStack, off⟩ : Addr Lin)
            = mem0s 10 11 rodata gotT (⟨rStack, off⟩ : Addr Lin) := by
          simp only [mem0sT, hass]
          rw [if_neg (by intro h; exact hc h.2)]
        rw [hT] at ha ⊢
        exact hbase' ha
  · have hbase' := hbase (⟨r, off⟩ : Addr Lin)
    cases hass : off.asInt with
    | none =>
      have hT : mem0sT 10 11 rodata gotT saves (⟨r, off⟩ : Addr Lin)
          = mem0s 10 11 rodata gotT (⟨r, off⟩ : Addr Lin) := by
        simp only [mem0sT, hass]
      rw [hT] at ha ⊢
      exact hbase' ha
    | some o =>
      have hT : mem0sT 10 11 rodata gotT saves (⟨r, off⟩ : Addr Lin)
          = mem0s 10 11 rodata gotT (⟨r, off⟩ : Addr Lin) := by
        simp only [mem0sT, hass]
        rw [if_neg (by intro h; exact hreg h.1)]
      rw [hT] at ha ⊢
      exact hbase' ha

/-- Induction over a kernel's block loop.  Segments: the prologue to the loop-head cut `KH`, one
iteration back to `KH` (reopened with `mapState_reached_vars`, substitution `tauE`), and the exit
for count 0.  Invariants: the log is in range, the first `k` output blocks are SHA-256 bytes, and
the prologue's save slots still hold what the prologue stored. -/
theorem rv_loop (prog : Array Riscv.Instr) (pe : Env)
    (rodata : List Nat) (gotT : List (Region × Int)) (SAVES : List Int)
    (KH KF Rlast : State E Lin) (tauE : List Lin)
    (EF envC : (Key → W32) → Key → W32) (itNS t0NS : Nat)
    (KH_len : KH.gpr.length = 32) (KH_vr : KH.vr = [])
    (tau0 : ∀ σ : Nat → Int, sigmaOf tauE σ 0 = 64 + σ 0)
    (tau1 : ∀ σ : Nat → Int, sigmaOf tauE σ 1 = 32 + σ 1)
    (tau2 : ∀ σ : Nat → Int, sigmaOf tauE σ 2 = -1 + σ 2)
    (SAVES_lo : ∀ o ∈ SAVES, -16 ≤ o)
    (KH_fl : KH.flags = none) (KH_mem : KH.mem = []) (KH_nOnly : KH.nOnly = true)
    (itRun : ∀ (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool),
      Mem0Rel e σ (mem0s 10 11 rodata gotT) mem0c → 0 < σ 2 →
        Riscv.run prog pe mem0c orcC itNS (mapState e σ KH) = mapState (EF e) σ KF)
    (itReach : ∀ (e : Key → W32) (σ : Nat → Int),
      mapState (EF e) σ KF =
        fr (Rlast.mem.map (fun p => (mapAddr σ p.1, mapCell (envC e) σ p.2)))
          (mapState (EF e) (sigmaOf tauE σ) KH))
    (itOut : ∀ (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int), HMem 128 inp e →
      ∀ n i b, n < 1 → i < 8 → b < 4 → ∃ x,
        lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)
          (mapState (EF e) σ KF).mem = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32)
    (logLast : ∀ p ∈ Rlast.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 32) ∨
      (p.1.region = rStack ∧ p.1.off.c = [] ∧ -80 ≤ p.1.off.k ∧ p.1.off.k < -16))
    (PRES : List Nat) (ENTRY : State E Lin)
    (entrySt : ∀ (e : Key → W32) (σ' : Nat → Int) (r : Nat), r ∈ PRES →
      (mapState (EF e) (sigmaOf tauE σ') ENTRY).getG r = (mapState e σ' ENTRY).getG r)
    (entryComb : ∀ (e : Key → W32) (σ₁ σ₂ σ₃ : Nat → Int)
      (m : Addr Int → Cell W32 Int) (r : Nat), r ∈ PRES →
      (mapState (ecomb e σ₁ m) σ₂ ENTRY).getG r = (mapState e σ₃ ENTRY).getG r)
    (t0Res : ∀ (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool),
      Mem0Rel e σ (mem0sT 10 11 rodata gotT SAVES) mem0c → σ 2 = 0 →
        ∃ S : CState, Riscv.run prog pe mem0c orcC t0NS (mapState e σ KH) = S ∧
          S.halted = true ∧ S.err = none ∧ S.tail = none ∧ S.mem = [] ∧
          ∀ r ∈ PRES, S.getG r = (mapState e σ ENTRY).getG r)
    (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int)
    (hw : WfMemR 10 11 rodata gotT mem0c) (σ0 σ1 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (orcC : Nat → Bool) :
    ∀ (j k : Nat) (σ' : Nat → Int) (e : Key → W32) (M : CLog),
      σ' 0 = σ0 + 64 * k → σ' 1 = σ1 + 32 * k → σ' 2 = j →
      InRange σ1 (32 * k) M → OutOk inp σ1 k M →
      (∀ o ∈ SAVES, ∃ x, view M mem0c ⟨rStack, o⟩ = .dat x (((o + 16) % 4).toNat)) →
      let fin := Riscv.run prog pe mem0c orcC (j * itNS + t0NS) (fr M (mapState e σ' KH))
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        InRange σ1 (32 * k + 32 * j) fin.mem ∧ OutOk inp σ1 (k + j) fin.mem ∧
        ∀ r ∈ PRES, fin.getG r = (mapState e σ' ENTRY).getG r := by
  intro j
  induction j with
  | zero =>
    intro k σ' e M h0 h1 h2 hR hO hsave
    have hM : OutLog M := outLog_of _ _ M hR
    let E := ecomb e σ' (view M mem0c)
    obtain ⟨S, hS, hhalt, herr, htail, hmem, hreg⟩ :=
      t0Res E σ' (view M mem0c) orcC
        (mem0RelT0 rodata gotT SAVES e σ' mem0c M hw hM hsave) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [Riscv.run_fr, head_ecomb e σ' (view M mem0c) KH KH_nOnly, hS]
    refine ⟨hhalt, herr, htail, ?_, ?_, ?_⟩
    · show InRange σ1 (32 * k) (fr M S).mem
      simp only [fr, hmem, List.nil_append]
      exact hR
    · show OutOk inp σ1 (k + 0) (fr M S).mem
      simp only [fr, hmem, List.nil_append, Nat.add_zero]
      exact hO
    · intro r hr
      show (fr M S).getG r = (mapState e σ' ENTRY).getG r
      rw [show (fr M S).getG r = S.getG r from rfl, hreg r hr]
      exact entryComb e σ' σ' σ' (view M mem0c) r hr
  | succ j ih =>
    intro k σ' e M h0 h1 h2 hR hO hsave
    have hM : OutLog M := outLog_of _ _ M hR
    let E := ecomb e σ' (view M mem0c)
    have hrel : Mem0Rel E σ' (mem0s 10 11 rodata gotT) (view M mem0c) :=
      mem0RelR_of_wf 10 11 rodata gotT E σ' _ (wf_viewR rodata gotT mem0c M hM hw)
        (envMem_ecomb e σ' (view M mem0c))
    rw [show (j + 1) * itNS + t0NS = itNS + (j * itNS + t0NS) by rw [Nat.succ_mul]; omega, rvRun_add]
    rw [Riscv.run_fr, head_ecomb e σ' (view M mem0c) KH KH_nOnly,
      itRun E σ' (view M mem0c) orcC hrel (by omega), itReach E σ', fr_fr]
    have hL : TLog σ' 32 (Rlast.mem.map (fun p => (mapAddr σ' p.1, mapCell (envC E) σ' p.2))) :=
      tlog_map (envC E) σ' Rlast.mem 32 logLast
    have hLrange := inRange_map (envC E) σ' Rlast.mem 32 logLast
    have hKHm : (mapState (EF E) (sigmaOf tauE σ') KH).mem = [] := by
      simp only [mapState, KH_mem, List.map_nil]
    have hnew := itOut (fun o => inp (64 * k + o)) E σ'
      (hmem_k inp mem0c σ0 hin k e σ' h0 M hM)
    have hnew' := hnew
    rw [itReach E σ'] at hnew'
    simp only [fr, hKHm, List.nil_append] at hnew'
    have hsave' : ∀ o ∈ SAVES, ∃ x,
        view (Rlast.mem.map (fun p => (mapAddr σ' p.1, mapCell (envC E) σ' p.2)) ++ M) mem0c
          ⟨rStack, o⟩ = .dat x (((o + 16) % 4).toNat) := by
      intro o ho
      obtain ⟨x, hx⟩ := hsave o ho
      have hne : ∀ p ∈ Rlast.mem.map (fun p => (mapAddr σ' p.1, mapCell (envC E) σ' p.2)),
          p.1 ≠ (⟨rStack, o⟩ : Addr Int) :=
        log_ne_save _ _ hL _ ⟨by show (rStack : Region) ≠ rOut; decide,
          fun _ => by have := SAVES_lo o ho; omega⟩
      have hl : lookup (⟨rStack, o⟩ : Addr Int)
          (Rlast.mem.map (fun p => (mapAddr σ' p.1, mapCell (envC E) σ' p.2)) ++ M) =
          lookup (⟨rStack, o⟩ : Addr Int) M := lookup_app_right _ _ _ hne
      exact ⟨x, by simpa only [view, hl] using hx⟩
    have := ih (k + 1) (sigmaOf tauE σ') (EF E) (Rlast.mem.map (fun p => (mapAddr σ' p.1, mapCell (envC E) σ' p.2)) ++ M)
      (by rw [tau0]; omega)
      (by rw [tau1]; omega)
      (by rw [tau2]; omega)
      (by
        apply inRange_app
        · exact inRange_mono _ _ _ (by omega) _
            (inRange_shift σ1 (σ' 1) k 32 _ hLrange h1)
        · exact inRange_mono _ _ _ (by omega) M hR)
      (by
        have := outOk_new inp σ1 k 1 _ M (σ' 1) h1
          (by
            intro n i b hn hi hb
            obtain ⟨x, hx, hv⟩ := hnew' n i b hn hi hb
            refine ⟨x, hx, ?_⟩
            rw [hv, blk_shift])
          (by
            intro p hp
            rcases above_of _ _ _ hLrange p hp with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)) hO
        exact this)
      hsave'
    obtain ⟨a, b, c, d, f, g⟩ := this
    refine ⟨a, b, c, ?_, ?_, ?_⟩
    · rw [show 32 * k + 32 * (j + 1) = 32 * (k + 1) + 32 * j by omega]; exact d
    · rw [show k + (j + 1) = (k + 1) + j by omega]; exact f
    · intro r hr
      rw [g r hr, entrySt E σ' r hr]
      exact entryComb e σ' σ' σ' (view M mem0c) r hr

end Hashtree.Proofs.Rv
