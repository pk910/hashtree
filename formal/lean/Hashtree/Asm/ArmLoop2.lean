import Hashtree.Asm.ArmFrame
import Hashtree.Asm.ArmSym
import Hashtree.Asm.X86Loop2
import Hashtree.Asm.ArmSlice

/-!
# Loop heads of AArch64 kernels whose prologue saves registers on the stack

The AArch64 counterpart of `Hashtree.Asm.X86Loop2`.  A kernel that spills callee-saved
registers in its prologue reads them back in its epilogue.  When a proof restarts at the loop
head, those spills are part of the older log, i.e. of the initial memory of the restarted
segment.  `mem0sH` makes that spill area `[lo, sp0)` readable: unknowns keyed by address, as byte
`o % 4` of a spilled lane (a spill stores 4-aligned lanes).  `WfMemH` is the matching concrete
condition; `wfH_view` establishes it from the prologue's log; `pushOk` checks the symbolic log.

No return address is on the stack in AAPCS64 (it is in `x30`), so bytes at or above the entry
stack pointer are never read back and stay poison.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Hashtree.Asm.Arm
open Hashtree.Asm Hashtree.Asm.ArmSym

/-! ## Logs that only hold output bytes and frame bytes -/

/-- Older writes: output bytes, or stack bytes below the entry stack offset `sp0`. -/
def OutLog (sp0 : Int) (M : CLog) : Prop :=
  ∀ p ∈ M, p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off < sp0)

theorem lookup_none_ne (a : Addr Int) : ∀ (M : CLog), (∀ p ∈ M, p.1 ≠ a) → lookup a M = .ok none
  | [], _ => rfl
  | (b, c) :: rest, h => by
    have hb : b ≠ a := h (b, c) (List.mem_cons_self ..)
    simp only [lookup, AddrEq.same]
    have : (a.region == b.region && a.off == b.off) = false := by
      obtain ⟨ra, oa⟩ := a
      obtain ⟨rb, ob⟩ := b
      simp only [ne_eq, Addr.mk.injEq] at hb
      by_cases hr : ra = rb
      · subst hr
        have : oa ≠ ob := fun h => hb ⟨rfl, h.symm⟩
        simp [this]
      · simp [hr]
    rw [this]
    exact lookup_none_ne a rest (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem view_other (M : CLog) (m : Addr Int → Cell W32 Int) (a : Addr Int) (ha : ∀ p ∈ M, p.1 ≠ a) :
    view M m a = m a := by
  simp only [view, lookup_none_ne a M ha]

theorem outLog_ne (sp0 : Int) (M : CLog) (hM : OutLog sp0 M) (a : Addr Int)
    (ha : a.region ≠ rOut ∧ (a.region = rStack → sp0 ≤ a.off)) : ∀ p ∈ M, p.1 ≠ a := by
  intro p hp heq
  rcases hM p hp with h | ⟨h1, h2⟩
  · rw [heq] at h; exact ha.1 h
  · rw [heq] at h1 h2; have := ha.2 h1; omega

theorem wf_view (ro : Region) (rodata : List Nat) (sp0 : Int) (m : Addr Int → Cell W32 Int)
    (M : CLog) (hM : OutLog sp0 M) (hro : ro ≠ rOut) (hw : WfMem ro rodata m) :
    WfMem ro rodata (view M m) := by
  obtain ⟨h1, h2, hro', hin⟩ := hw
  have vr : ∀ o, view M m ⟨ro, o⟩ = m ⟨ro, o⟩ := fun o =>
    view_other M m _ (outLog_ne sp0 M hM _ ⟨hro, fun h => absurd h h2⟩)
  have vI : ∀ o, view M m ⟨rIn, o⟩ = m ⟨rIn, o⟩ := fun o =>
    view_other M m _ (outLog_ne sp0 M hM _ ⟨show rIn ≠ rOut from by decide, fun h => absurd h (show rIn ≠ rStack from by decide)⟩)
  refine ⟨h1, h2, ?_, ?_⟩
  · intro o; rw [vr]; exact hro' o
  · intro o; rw [vI]; exact hin o

/-- Numbered variables from `e`, memory keys re-read from memory `m` under `σ`. -/
def ecomb (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Key → W32
  | .n i => e (.n i)
  | .m r off => cellX (m ⟨r, off.eval σ⟩)

theorem envMem_ecomb (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) :
    EnvMem (ecomb e σ m) σ m :=
  fun _ _ => rfl

/-! ## A readable spill area -/

/-- Base address of the 4-byte lane holding byte offset `o`. -/
def laneBase (o : Int) : Int := o - o % 4

/-- Stack bytes in `[lo, sp0)` are readable: byte `o % 4` of a lane keyed by the lane base. -/
def mem0sH (ro : Region) (rodata : List Nat) (sp0 lo : Int) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rStack then
    match a.off.asInt with
    | some o =>
      if lo ≤ o ∧ o < sp0 then
        .dat (.var (.m a.region (Lin.ofInt (laneBase o)))) (o % 4).toNat
      else mem0s ro rodata a
    | none => mem0s ro rodata a
  else mem0s ro rodata a

/-- The matching concrete condition: every byte of a spilled lane is byte `o % 4` of the lane. -/
def WfMemH (ro : Region) (rodata : List Nat) (sp0 lo : Int) (m : Addr Int → Cell W32 Int) : Prop :=
  WfMem ro rodata m ∧ ∀ o, lo ≤ o → o < sp0 →
    m ⟨rStack, o⟩ = .dat (cellX (m ⟨rStack, laneBase o⟩)) (o % 4).toNat

theorem mem0RelH_of_wf (ro : Region) (rodata : List Nat) (sp0 lo : Int) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemH ro rodata sp0 lo m) (he : EnvMem env σ m) :
    Mem0Rel env σ (mem0sH ro rodata sp0 lo) m := by
  have h0 := mem0Rel_of_wf ro rodata env σ m hw.1 he
  intro a ha
  obtain ⟨r, off⟩ := a
  by_cases hr : r = rStack
  · subst hr
    cases hk : off.asInt with
    | none =>
      have e : mem0sH ro rodata sp0 lo ⟨rStack, off⟩ = mem0s ro rodata ⟨rStack, off⟩ := by
        simp only [mem0sH, ite_true, hk]
      rw [e] at ha ⊢; exact h0 _ ha
    | some o =>
      by_cases hlo : lo ≤ o ∧ o < sp0
      · have e : mem0sH ro rodata sp0 lo ⟨rStack, off⟩ =
            .dat (.var (.m rStack (Lin.ofInt (laneBase o)))) (o % 4).toNat := by
          simp only [mem0sH, ite_true, hk, hlo, and_self]
        rw [e]
        have hev : off.eval σ = o := Lin.eval_asInt σ off o hk
        simp only [mapCell, E.eval]
        rw [he]
        simp only [mapAddr]
        have hlin : Lin.eval σ (Lin.ofInt (laneBase o)) = laneBase o := by
          simp [Lin.ofInt, Lin.eval, dotC]
        rw [hlin]
        rw [show (⟨rStack, Lin.eval σ off⟩ : Addr Int) = ⟨rStack, o⟩ from by rw [hev]]
        exact hw.2 o hlo.1 hlo.2
      · have e : mem0sH ro rodata sp0 lo ⟨rStack, off⟩ = mem0s ro rodata ⟨rStack, off⟩ := by
          simp only [mem0sH, ite_true, hk, hlo, ite_false]
        rw [e] at ha ⊢; exact h0 _ ha
  · have e : mem0sH ro rodata sp0 lo ⟨r, off⟩ = mem0s ro rodata ⟨r, off⟩ := by
      simp only [mem0sH, hr, ite_false]
    rw [e] at ha ⊢; exact h0 _ ha

theorem mem0sH_keyed (ro : Region) (rodata : List Nat) (sp0 lo : Int) :
    MemKeyed (mem0sH ro rodata sp0 lo) := by
  intro a
  have hk := mem0s_keyed ro rodata a
  simp only [mem0sH]
  split
  · split
    · split
      · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
      · exact hk
    · exact hk
  · exact hk

theorem wfH_view (ro : Region) (rodata : List Nat) (sp0 lo : Int) (m : Addr Int → Cell W32 Int)
    (M : CLog) (hM : OutLog sp0 M) (hro : ro ≠ rOut) (hw : WfMem ro rodata m)
    (hp : ∀ o, lo ≤ o → o < sp0 → ∃ x,
      lookup (⟨rStack, o⟩ : Addr Int) M = .ok (some (.dat x (o % 4).toNat)) ∧
      lookup (⟨rStack, laneBase o⟩ : Addr Int) M = .ok (some (.dat x 0))) :
    WfMemH ro rodata sp0 lo (view M m) := by
  refine ⟨wf_view ro rodata sp0 m M hM hro hw, fun o h1 h2 => ?_⟩
  obtain ⟨x, hx, hl⟩ := hp o h1 h2
  have v1 : view M m ⟨rStack, o⟩ = .dat x (o % 4).toNat := by simp only [view, hx]
  have v2 : view M m ⟨rStack, laneBase o⟩ = .dat x 0 := by simp only [view, hl]
  rw [v1, v2]
  rfl

/-- The spill area of a symbolic log, byte by byte: byte `o` and its lane base hold the same
stored lane, in the right byte position. -/
def pushOk (K : State E Lin) (sp0 lo : Int) : Bool :=
  (List.range (sp0 - lo).toNat).all fun i =>
    let o := lo + (i : Int)
    match lookup (⟨rStack, Lin.ofInt o⟩ : Addr Lin) K.mem,
        lookup (⟨rStack, Lin.ofInt (laneBase o)⟩ : Addr Lin) K.mem with
    | .ok (some (.dat x k)), .ok (some (.dat y 0)) => x == y && k == (o % 4).toNat
    | _, _ => false

theorem pushOk_sound (e : Key → W32) (σ : Nat → Int) (K : State E Lin) (sp0 lo : Int)
    (h : pushOk K sp0 lo = true) :
    ∀ o, lo ≤ o → o < sp0 → ∃ x,
      lookup (⟨rStack, o⟩ : Addr Int)
        (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) = .ok (some (.dat x (o % 4).toNat)) ∧
      lookup (⟨rStack, laneBase o⟩ : Addr Int)
        (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) = .ok (some (.dat x 0)) := by
  intro o h1 h2
  simp only [pushOk, List.all_eq_true, List.mem_range] at h
  have hi := h (o - lo).toNat (by omega)
  rw [show lo + (((o - lo).toNat : Nat) : Int) = o by omega] at hi
  cases hx0 : lookup (⟨rStack, Lin.ofInt o⟩ : Addr Lin) K.mem with
  | error e => simp only [hx0] at hi; cases hi
  | ok v1 =>
    cases v1 with
    | none => simp only [hx0] at hi; cases hi
    | some c1 =>
      cases c1 with
      | pb a k => simp only [hx0] at hi; cases hi
      | dat x k =>
        cases hy0 : lookup (⟨rStack, Lin.ofInt (laneBase o)⟩ : Addr Lin) K.mem with
        | error e => simp only [hx0, hy0] at hi; cases hi
        | ok v2 =>
          cases v2 with
          | none => simp only [hx0, hy0] at hi; cases hi
          | some c2 =>
            cases c2 with
            | pb a k0 => simp only [hx0, hy0] at hi; cases hi
            | dat y k0 =>
              cases k0 with
              | zero =>
                simp only [hx0, hy0, Bool.and_eq_true, beq_iff_eq] at hi
                obtain ⟨rfl, rfl⟩ := hi
                have hx' : lookup (⟨rStack, o⟩ : Addr Int)
                    (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) =
                      .ok (some (.dat (x.eval e) (o % 4).toNat)) := by
                  have := lookup_hom e σ _ K.mem _ hx0
                  have ha : mapAddr σ (⟨rStack, Lin.ofInt o⟩ : Addr Lin) = ⟨rStack, o⟩ := by
                    simp [mapAddr, Lin.ofInt, Lin.eval, dotC]
                  rw [ha] at this
                  rw [this]
                  rfl
                have hy' : lookup (⟨rStack, laneBase o⟩ : Addr Int)
                    (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) =
                      .ok (some (.dat (x.eval e) 0)) := by
                  have := lookup_hom e σ _ K.mem _ hy0
                  have ha : mapAddr σ (⟨rStack, Lin.ofInt (laneBase o)⟩ : Addr Lin) =
                      ⟨rStack, laneBase o⟩ := by
                    simp [mapAddr, Lin.ofInt, Lin.eval, dotC]
                  rw [ha] at this
                  rw [this]
                  rfl
                exact ⟨x.eval e, hx', hy'⟩
              | succ k0 => simp only [hx0, hy0] at hi; cases hi

/-! ## A cut that is an instance of another -/

theorem mapState_vrInst (env : Key → W32) (σ : Nat → Int) (prog : Array Instr) (ro : Region)
    (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool) (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hs : Hashtree.Asm.ArmSlice.sliceCheck prog ro mem0 orc n K K' trees = true) (W : List (List E))
    (hW : Hashtree.Asm.X86.vrRel 0 W K'.vr = true) :
    mapState (envAbs env (run prog ro mem0 orc n K)) σ K' =
      mapState (envAbs env (run prog ro mem0 orc n K)) σ { K' with vr := W } := by
  simp only [Hashtree.Asm.ArmSlice.sliceCheck, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨_, hcut⟩, habs⟩, _⟩ := hs
  subst habs
  have := Hashtree.Asm.X86.vr_eval env _ hcut 0 W (run prog ro mem0 orc n K).vr (fun j => by simp) hW
  simp only [mapState]
  simp only [abstract] at this ⊢
  rw [this]

theorem mapState_inst (env : Key → W32) (σ : Nat → Int) (prog : Array Instr) (ro : Region)
    (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool) (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hs : Hashtree.Asm.ArmSlice.sliceCheck prog ro mem0 orc n K K' trees = true) (G : List (Val E Lin))
    (W : List (List E)) (hG : Hashtree.Asm.X86.gprRel 0 G K'.gpr = true)
    (hW : Hashtree.Asm.X86.vrRel 0 W K'.vr = true) :
    mapState (envAbs env (run prog ro mem0 orc n K)) σ K' =
      mapState (envAbs env (run prog ro mem0 orc n K)) σ { K' with gpr := G, vr := W } := by
  have hv := mapState_vrInst env σ prog ro mem0 orc n K K' trees hs W hW
  simp only [Hashtree.Asm.ArmSlice.sliceCheck, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨_, hcut⟩, habs⟩, _⟩ := hs
  subst habs
  have hg := Hashtree.Asm.X86.gpr_eval env σ _ hcut 0 G (run prog ro mem0 orc n K).gpr (fun j => by simp) hG
  rw [hv]
  simp only [mapState]
  simp only [abstract] at hg ⊢
  rw [hg]

end Hashtree.Asm.Arm
