import Hashtree.Proofs.WinAvx512Live
import Hashtree.Proofs.WinAvx2X8Live
import Hashtree.Proofs.WinChain
import Hashtree.Proofs.WinWrapper
import Hashtree.Asm.RunAgree
import Hashtree.Proofs.ShaniW
import Hashtree.Proofs.Avx512X16WLoop

/-!
# R5: the windows chain link `avx512_x16 -> avx2_x8` — the statement

The per-link obligation of `X86Chain.KSpecC` for the first link of the shipped windows chain,
stated in the shape the following links consume.  Definitions only (the proof is the next
increment and depends on the linux per-link certificate of the avx512 loop).

* `PostLink`: a link that *returns* meets the whole windows kernel contract (`KSpecW`'s
  conclusion shape, with its own stack depth `D`).
* `PreLink env σ c d r L s`: the state handed to a link after `d` blocks are done and `r`
  remain: on the registers the link reads before writing (its entry live set `L`) it is the
  wrapper call state `entryWin` with the symbols advanced (`shift`), under some vector
  environment (U6: the vector file is whatever the previous link left — `entryWin`'s lanes are
  distinct symbols, so every vector file is an instance), on top of the previous links' output
  log `M'` (output-only, the first `d` blocks correct).  The flags are not constrained (`Agree L
  false`): every kernel sets them before reading them, which the flags bit of its liveness
  certificate records (`liveF_entry`).  **U6**: the vector environment `e'` is free on the
  vector symbols — the avx512 link clobbers `xmm6`-`xmm15` and nothing here assumes their
  preservation.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinAvx512Bridge

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RunAgree
open Hashtree.Proofs.X86Chain Hashtree.Proofs.WinChain
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)

/-- The wrapper symbols after `d` blocks: output and input pointers advanced, count `r`. -/
def shift (σ : Nat → Int) (d r : Nat) : Nat → Int := fun i =>
  if i = 0 then σ 0 + 64 * d else if i = 1 then σ 1 + 32 * d else if i = 2 then r else σ i

/-- The vector environment is free, the general-register and memory symbols are the wrapper's. -/
def SameG (env e' : Key → W32) : Prop := ∀ i j, e' (.n (gId i j)) = env (.n (gId i j))

/-- A returning link meets the windows kernel contract with stack depth `D`. -/
def PostLink (σ : Nat → Int) (c : Nat) (inp : Nat → Spec.Byte) (D : Nat) (f : CS) : Prop :=
  f.halted = true ∧ Foot (σ 9) D (σ 1) (32 * c) f.mem ∧ OutOk inp (σ 1) c f.mem ∧ RegsOkW σ f

/-- The entry state of a link with `d` blocks done and `r` remaining, on its entry live set `L`. -/
def PreLink (env : Key → W32) (σ : Nat → Int) (c d r : Nat) (inp : Nat → Spec.Byte) (L : List Nat)
    (s : CS) : Prop :=
  ∃ (e' : Key → W32) (M' : CLog), SameG env e' ∧
    Agree L false s (fr M' (mapState e' (shift σ d r) entryWin)) ∧
    OutLogW (σ 9) M' ∧ Foot (σ 9) 0 (σ 1) (32 * c) M' ∧ OutOk inp (σ 1) d M'

/-- The entry live set of the avx2_x8 link (`[8, 4, 5, 6, 12, 13, 14, 15, 2, 1]`). -/
abbrev L8 : List Nat := Hashtree.Proofs.WinAvx2X8Live.liveT.getD 0 []

/-- **The avx512_x16 link obligation** (the head clause of `KSpecC` for `winSpecs`): from the
wrapper's call state, after `s512 c` steps the link has no error and either returned (only when
`c = 0`; it writes nothing, depth 0) or tail-called `hashtree_sha256_avx2_x8` with the first
`c - c % 16` blocks done and `c % 16` remaining, in the shape the avx2_x8 link reads.
`24 ≤ σ 9` is the explicit hypothesis of R2b's loop certificate (`x16_loop`: its `OutLog`
places stack writes below the absolute offset 24; the kernel writes no stack); it is to be
removed when R2b restates `OutLog` output-only. -/
def KSpecC512 (s512 : Nat → Nat) (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) : Prop :=
  WfMemW Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0 → EnvMem env σ m0 → σ 2 = c →
  24 ≤ σ 9 →
  (∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
  ∀ s, s = mapState env σ entryWin →
    let f := run p512 4 m0 orcC (s512 c) s
    f.err = none ∧
      ((c = 0 ∧ f.tail = none ∧ PostLink σ c inp 0 f) ∨
       (c ≠ 0 ∧ f.tail = some "hashtree_sha256_avx2_x8" ∧
         PreLink env σ c (c - c % 16) (c % 16) inp L8 (resume f)))

/-- The obligation implies the `KSpecC` head clause for the windows chain with these pre/post
conditions (the shape `win_chainRun_returns` composes). -/
theorem KSpecC512_head (s512 : Nat → Nat) (env : Key → W32) (σ : Nat → Int)
    (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte)
    (hw : WfMemW Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0) (he : EnvMem env σ m0)
    (hc : σ 2 = c) (hsp : 24 ≤ σ 9) (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (h : KSpecC512 s512 env σ m0 orcC c inp) :
    ∀ s, (fun s => s = mapState env σ entryWin) s →
      let f := step m0 orcC c (linkOf "hashtree_sha256_avx512_x16" p512 s512) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp 0 f) ∨
         (f.tail = some (linkOf "hashtree_sha256_avx2_x8" p8 (fun _ => 0)).name ∧
           PreLink env σ c (c - c % 16) (c % 16) inp L8 (resume f))) := by
  intro s hs
  have := h hw he hc hsp hin s hs
  simp only [step, linkOf] at this ⊢
  rcases this with ⟨he, ⟨_, ht, hp⟩ | ⟨_, ht, hp⟩⟩
  · exact ⟨he, Or.inl ⟨ht, hp⟩⟩
  · exact ⟨he, Or.inr ⟨ht, hp⟩⟩

/-! ## The output bytes of the loop (R2c) -/

/-- **`TurnOut` (to be proved by R2c):** under the hypotheses of `Avx512X16WLoop.x16_loop` and the
input bytes, the linux avx512 loop's final write log consists of output cells of the finished
blocks only, `[σ 1, σ 1 + 32 (c - c % 16))`, holding their SHA-256 bytes.  The per-turn form
(turn `j` writes blocks `16 j .. 16 j + 15` at the W cut, `sIt j σ 1 = σ 1 + 512 j`) iterates to
this; the windows link consumes exactly this statement. -/
def TurnOut : Prop :=
  ∀ (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env0 : Key → W32) (σ : Nat → Int)
    (c : Nat) (inp : Nat → Spec.Byte),
    Mem0Rel env0 σ Hashtree.Proofs.Avx512X16WBody.mW mem0c →
    WfMemW Hashtree.Kernels.X86.Avx512X16.rodata [] env0 σ mem0c → 24 ≤ σ 9 → σ 10 = σ 1 →
    σ 2 = c → 16 ≤ c →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx512X16.prog 4 mem0c orcC (Hashtree.Proofs.Avx512X16WLoop.steps c)
        (mapState env0 σ entryW)).mem,
      p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * ((c - c % 16 : Nat) : Int)) ∧
    OutOk inp (σ 1) (c - c % 16)
      (run Hashtree.Kernels.X86.Avx512X16.prog 4 mem0c orcC (Hashtree.Proofs.Avx512X16WLoop.steps c)
        (mapState env0 σ entryW)).mem

end Hashtree.Proofs.WinAvx512Bridge
