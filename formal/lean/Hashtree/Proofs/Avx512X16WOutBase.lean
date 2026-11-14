import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Asm.X86Frame
import Hashtree.Asm.X86Loop
import Hashtree.Asm.X86SymW

/-!
# R2c — output correctness of the `avx512_x16` W-mode loop: generic part

Definitions and kernel-independent lemmas for `Avx512X16WOut`:

* `OutOk` — the output statement, textually `WinWrapper.OutOk` / `ShaniW.OutOk` (R5 consumes
  `TurnOut`, which is stated with it);
* the `InvC` lift: a checked slice whose trees `T` are the trees of another checked slice gives
  the same labelled variable values, so the S-mode invariant chain of `Gen.Avx512X16P`
  transfers to the W cuts without re-checking (`invC_lift`);
* write-log lemmas: `lookup` through a prefix that does not touch the address, `OutOk` on
  appended logs, and the block re-indexing of a turn's output (`outOk_shift`);
* the input bytes: `HMem` from the concrete input cells, for the entry environment
  (`Mem0Rel`) and for the turn environments (`EnvMem`).
-/

namespace Hashtree.Proofs.Avx512X16WOut

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec

/-- The first `nblk` output blocks (base `ob`) hold the SHA-256 bytes of the input blocks
(the same text as `Hashtree.Proofs.ShaniW.OutOk` / `WinWrapper.OutOk`). -/
def OutOk (inp : Nat → Byte) (ob : Int) (nblk : Nat) (M : CLog) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

/-! ## The `InvC` lift -/

/-- `InvC` only reads the labelled variables. -/
theorem invC_congr (inp : Nat → Byte) (e1 e2 : Key → W32) :
    ∀ L : List (Nat × Q), (∀ p ∈ L, e1 (.n p.1) = e2 (.n p.1)) → InvC inp e1 L → InvC inp e2 L
  | [], _, _ => trivial
  | p :: ps, h, ⟨h1, h2⟩ =>
    ⟨by rw [← h p (List.mem_cons_self ..)]; exact h1,
     invC_congr inp e1 e2 ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) h2⟩

/-- Two environments that take the same tree values agree on every label whose id is a tree id. -/
theorem agree_of_trees (env e1 e2 : Key → W32) (T : List (Nat × E)) (L : List (Nat × Q))
    (hT : T.map (·.1) = L.map (·.1))
    (h1 : ∀ p ∈ T, e1 (.n p.1) = p.2.eval env) (h2 : ∀ p ∈ T, e2 (.n p.1) = p.2.eval env) :
    ∀ p ∈ L, e1 (.n p.1) = e2 (.n p.1) := by
  intro p hp
  have hm : p.1 ∈ T.map (·.1) := by rw [hT]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hm
  rw [← hq1, h1 q hq, h2 q hq]

/-- **The lift.**  If the S-mode slice (`KS` to `KS'`) and the W-mode slice (`KW` to `KW'`) are
both checked with the same trees `T`, and `T` tracks exactly the labels `L`, then the invariant
after the S-mode slice is the invariant after the W-mode slice. -/
theorem invC_lift (inp : Nat → Byte) (env : Key → W32) (prog : Array Instr) (ro : Region)
    (memS memW : Addr Lin → Cell E Lin) (orcS orcW : Nat → Bool) (n : Nat)
    (KS KS' KW KW' : State E Lin) (T : List (Nat × E)) (L : List (Nat × Q))
    (hS : sliceCheck prog ro memS orcS n KS KS' T = true)
    (hW : sliceCheck prog ro memW orcW n KW KW' T = true)
    (hT : T.map (·.1) = L.map (·.1))
    (h : InvC inp (envAbs env (run prog ro memS orcS n KS)) L) :
    InvC inp (envAbs env (run prog ro memW orcW n KW)) L :=
  invC_congr inp _ _ L
    (agree_of_trees env _ _ T L hT (slice_trees_mem prog ro memS orcS n KS KS' T hS env)
      (slice_trees_mem prog ro memW orcW n KW KW' T hW env)) h

/-! ## Write-log lemmas -/

theorem same_int_false (a b : Addr Int) (h : b ≠ a) : AddrEq.same a b = some false := by
  show some (a.region == b.region && a.off == b.off) = some false
  obtain ⟨ar, ao⟩ := a
  obtain ⟨br, bo⟩ := b
  simp only [Option.some.injEq, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  by_cases h1 : ar = br
  · right
    intro h2
    subst h1
    subst h2
    exact h rfl
  · left
    exact h1

theorem same_int_true (a : Addr Int) : AddrEq.same a a = some true := by
  show some (a.region == a.region && a.off == a.off) = some true
  simp

/-- A prefix that never writes `a` is transparent to `lookup a`. -/
theorem lookup_append_notin (a : Addr Int) :
    ∀ (N M : CLog), (∀ p ∈ N, p.1 ≠ a) → lookup a (N ++ M) = lookup a M
  | [], _, _ => rfl
  | p :: N, M, h => by
    obtain ⟨b, c⟩ := p
    simp only [List.cons_append, lookup]
    rw [same_int_false a b (h (b, c) (List.mem_cons_self ..))]
    exact lookup_append_notin a N M (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- A write found in the prefix is found in the whole log. -/
theorem lookup_append_found (a : Addr Int) :
    ∀ (N M : CLog) (c : Cell W32 Int), lookup a N = .ok (some c) → lookup a (N ++ M) = .ok (some c)
  | [], _, _, h => by simp [lookup] at h
  | p :: N, M, c, h => by
    obtain ⟨b, d⟩ := p
    simp only [List.cons_append, lookup] at h ⊢
    split at h
    · rename_i heq
      try simp only [heq]
      exact h
    · rename_i heq
      try simp only [heq]
      exact lookup_append_found a N M c h
    · simp at h

/-- `OutOk` of a prefix persists. -/
theorem outOk_append_left (inp : Nat → Byte) (ob : Int) (k : Nat) (N M : CLog)
    (h : OutOk inp ob k N) : OutOk inp ob k (N ++ M) := by
  intro n i b hn hi hb
  obtain ⟨x, hx, hbx⟩ := h n i b hn hi hb
  exact ⟨x, lookup_append_found _ N M _ hx, hbx⟩

/-- `OutOk` of the older log persists under a prefix that writes only above the `k` blocks. -/
theorem outOk_append_right (inp : Nat → Byte) (ob : Int) (k : Nat) (N M : CLog)
    (hN : ∀ p ∈ N, p.1.region = rOut → ob + 32 * (k : Int) ≤ p.1.off)
    (h : OutOk inp ob k M) : OutOk inp ob k (N ++ M) := by
  intro n i b hn hi hb
  obtain ⟨x, hx, hbx⟩ := h n i b hn hi hb
  refine ⟨x, ?_, hbx⟩
  rw [lookup_append_notin _ N M]
  · exact hx
  · intro p hp heq
    have hr : p.1.region = rOut := by rw [heq]
    have h1 := hN p hp hr
    rw [heq] at h1
    simp only at h1
    have : (32 * n + 4 * i + b : Nat) < 32 * k := by omega
    omega

/-- The blocks of the shifted input are the later blocks of the input. -/
theorem blk_shift (inp : Nat → Byte) (j n : Nat) :
    blk (fun o => inp (1024 * j + o)) n = blk inp (16 * j + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-- A turn's output, stated for its own 16 blocks at its own base, re-indexed to the caller's
input and base. -/
theorem outOk_shift (inp : Nat → Byte) (ob : Int) (j : Nat) (N : CLog)
    (h : OutOk (fun o => inp (1024 * j + o)) (ob + 512 * (j : Int)) 16 N) :
    ∀ n i b, 16 * j ≤ n → n < 16 * j + 16 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) N = .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by
  intro n i b hlo hhi hi hb
  obtain ⟨x, hx, hbx⟩ := h (n - 16 * j) i b (by omega) hi hb
  refine ⟨x, ?_, ?_⟩
  · have : ob + 512 * (j : Int) + ((32 * (n - 16 * j) + 4 * i + b : Nat) : Int) =
        ob + ((32 * n + 4 * i + b : Nat) : Int) := by
      have : 16 * j ≤ n := hlo
      push_cast [Nat.sub_mul, Nat.mul_sub]
      omega
    rw [← this]; exact hx
  · rw [hbx, blk_shift, show 16 * j + (n - 16 * j) = n by omega]

/-- Composition: the older log holds blocks `< 16 j`, the new prefix holds blocks
`16 j .. 16 j + 15` and writes nothing below; together they hold `16 (j + 1)` blocks. -/
theorem outOk_step (inp : Nat → Byte) (ob : Int) (j : Nat) (N M : CLog)
    (hN : ∀ p ∈ N, p.1.region = rOut → ob + 32 * ((16 * j : Nat) : Int) ≤ p.1.off)
    (hM : OutOk inp ob (16 * j) M)
    (hT : OutOk (fun o => inp (1024 * j + o)) (ob + 512 * (j : Int)) 16 N) :
    OutOk inp ob (16 * (j + 1)) (N ++ M) := by
  intro n i b hn hi hb
  by_cases hlt : n < 16 * j
  · exact outOk_append_right inp ob (16 * j) N M hN hM n i b hlt hi hb
  · obtain ⟨x, hx, hbx⟩ := outOk_shift inp ob j N hT n i b (by omega) (by omega) hi hb
    exact ⟨x, lookup_append_found _ N M _ hx, hbx⟩

/-- The blocks of the input shifted by one turn. -/
theorem blk_shift1 (inp : Nat → Byte) (n : Nat) :
    blk (fun o => inp (1024 + o)) n = blk inp (16 + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-- Composition the other way round: the older log `N1` holds the first 16 blocks, the newer
prefix `N2` holds the next `m` blocks of the input shifted by one turn, at base `ob + 512`. -/
theorem outOk_glue (inp : Nat → Byte) (ob : Int) (m : Nat) (N2 N1 : CLog)
    (hlo : ∀ p ∈ N2, p.1.region = rOut → ob + 512 ≤ p.1.off)
    (h1 : OutOk inp ob 16 N1)
    (h2 : OutOk (fun o => inp (1024 + o)) (ob + 512) m N2) :
    OutOk inp ob (16 + m) (N2 ++ N1) := by
  intro n i b hn hi hb
  by_cases hlt : n < 16
  · refine outOk_append_right inp ob 16 N2 N1 ?_ h1 n i b hlt hi hb
    intro p hp hr
    have := hlo p hp hr
    push_cast
    omega
  · obtain ⟨n', rfl⟩ : ∃ n', n = 16 + n' := ⟨n - 16, by omega⟩
    obtain ⟨x, hx, hbx⟩ := h2 n' i b (by omega) hi hb
    refine ⟨x, ?_, ?_⟩
    · have : ob + 512 + ((32 * n' + 4 * i + b : Nat) : Int) =
          ob + ((32 * (16 + n') + 4 * i + b : Nat) : Int) := by
        push_cast
        omega
      rw [← this]
      exact lookup_append_found _ N2 N1 _ hx
    · rw [hbx, blk_shift1]

/-- A log that never writes `a` does not resolve `a`. -/
theorem lookup_none (a : Addr Int) :
    ∀ M : CLog, (∀ p ∈ M, p.1 ≠ a) → lookup a M = .ok none
  | [], _ => rfl
  | p :: M, h => by
    obtain ⟨b, c⟩ := p
    simp only [lookup]
    rw [same_int_false a b (h (b, c) (List.mem_cons_self ..))]
    exact lookup_none a M (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- An output/stack log is transparent on the input region. -/
theorem view_rIn (M : CLog) (m : Addr Int → Cell W32 Int) (a : Int) (hM : OutLog M) :
    view M m ⟨rIn, a⟩ = m ⟨rIn, a⟩ := by
  have hn : lookup (⟨rIn, a⟩ : Addr Int) M = .ok none := by
    refine lookup_none _ M ?_
    intro p hp heq
    rcases hM p hp with h | ⟨h, _⟩
    · rw [heq] at h; simp [rIn, rOut] at h
    · rw [heq] at h; simp [rIn, rStack] at h
  simp only [view, hn]

/-! ## The input bytes -/

/-- The symbolic input cell `o` evaluates at the concrete address `σ 0 + o`. -/
theorem in_eval (σ : Nat → Int) (o : Nat) : (⟨(o : Int), [1]⟩ : Lin).eval σ = σ 0 + (o : Int) := by
  simp only [Lin.eval, dotC]
  omega

/-- `HMem` for an environment that reads the concrete memory (`EnvMem`). -/
theorem hmem_of_envMem (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (n : Nat) (he : EnvMem e σ m)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem n inp e := by
  intro o _
  rw [he rIn ⟨(o : Int), [1]⟩, in_eval, hin o]
  rfl

/-- `HMem` for the turn environments, which read the concrete memory behind an output log. -/
theorem hmem_view (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLog M)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 1024 inp (ecomb e σ (view M m)) :=
  hmem_of_envMem _ σ _ inp 1024 (envMem_ecomb e σ (view M m))
    (fun o => by rw [view_rIn M m _ hM]; exact hin o)

end Hashtree.Proofs.Avx512X16WOut
