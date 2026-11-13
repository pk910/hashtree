import Hashtree.Asm.X86Frame

/-!
# Tail-call chains of the x86 kernel models

The shipped hashtree kernels are a linear chain of tail calls: the AVX-512 kernel jumps
into the AVX2 kernel for the residual blocks, which jumps into the AVX kernel, which jumps
into the scalar kernel.  `run` stops at a tail call (`halted := true`, `tail := some name`),
and the wrapper's old `callK` discarded that tail; that is why the old single-run `KSpec`
had to require `fin.tail = none`, which only the terminal kernels satisfy.

This module is the chain-aware replacement, independent of any particular kernel:

* `Link` — one kernel image (program, rodata region, step count);
* `Spec` — a link with its pre- and post-condition on states;
* `chainRun` — runs the links in order, following a tail into the next link, on the same
  memory (a tail call shares the caller's return marker; each kernel's rodata lives in its
  own region);
* `KSpecC` — the per-link obligation: from its pre-condition a link either returns and
  meets its post-condition, or tails into the next link's pre-condition;
* `chain_sound` — if `KSpecC` holds, the whole chain returns (`err = none`, `tail = none`)
  and meets the last post-condition.

The kernel instantiations (x16 -> x8 -> x4 -> x1) supply the per-link pre/post conditions
(the entry bridges) and are the remaining proof obligation.
-/

namespace Hashtree.Proofs.X86Chain
open Hashtree.Asm Hashtree.Asm.X86

abbrev CS := CState

/-- One kernel image in a linear tail-call chain. -/
structure Link where
  /-- The tail-call name of the kernel (`hashtree_sha256_avx2_x8`, ...). -/
  name : String
  prog : Array Instr
  /-- The region holding this kernel's rodata. -/
  ro : Region
  steps : Nat
  deriving Inhabited

/-- One run of a link's program. -/
def step (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (l : Link) (s : CS) : CS :=
  run l.prog l.ro m0 orc l.steps s

/-- A link with the pre- and post-condition used by the chain composition. -/
structure Spec where
  link : Link
  pre : CS → Prop
  post : CS → Prop

/-- The state handed to the next link after a tail call: the next kernel starts at pc 0
with its own halted/tail flags cleared, on the same memory. -/
def resume (f : CS) : CS := { f with pc := 0, halted := false, tail := none }

/-- Run a linear chain, following a tail `name` into the following link.  The memory is
shared: a tail call keeps the caller's stack and return marker. -/
def chainRun (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) : List Spec → CS → CS
  | [], s => s
  | [sp], s => step m0 orc sp.link s
  | sp :: sp' :: rest, s =>
    let f := step m0 orc sp.link s
    match f.tail with
    | some t => if t = sp'.link.name then chainRun m0 orc (sp' :: rest) (resume f) else f
    | none => f

/-- The chain-aware call: start the first link at pc 0 (the caller has pushed its return
marker) and resume the caller after the chain returns.  This is the tail-following
replacement for `callK`, which discarded a tail. -/
def callChain (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (specs : List Spec)
    (s : CS) : CS :=
  let r := chainRun m0 orc specs { s with pc := 0 }
  { r with pc := 0, halted := false, tail := none }

/-- A chain run commutes with a memory log frame: the writes made before the call act as
initial memory for the whole chain, and are appended to its log.  Needed by the wrapper,
whose call state is `fr L` of the kernel entry. -/
theorem chainRun_fr (L : CLog) (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) :
    ∀ (specs : List Spec) (s : CS),
      chainRun m0 orc specs (fr L s) = fr L (chainRun (view L m0) orc specs s)
  | [], _ => rfl
  | [sp], s => by
    simp only [chainRun, step, run_fr]
  | sp :: sp' :: rest, s => by
    simp only [chainRun, step, run_fr, fr_tail]
    cases htail : (run sp.link.prog sp.link.ro (view L m0) orc sp.link.steps s).tail with
    | none => simp only [htail]
    | some t =>
      by_cases ht : t = sp'.link.name
      · simp only [htail, ht, if_pos]
        rw [show resume (fr L (run sp.link.prog sp.link.ro (view L m0) orc sp.link.steps s)) =
          fr L (resume (run sp.link.prog sp.link.ro (view L m0) orc sp.link.steps s)) from rfl]
        rw [chainRun_fr L m0 orc (sp' :: rest) (resume (run sp.link.prog sp.link.ro (view L m0)
          orc sp.link.steps s))]
      · simp [htail, ht]

/-- Per-link obligation of the chain contract.  Every link is checked from its own
pre-condition; a return must meet the post-condition, a tail must name the next link and
hand it a state satisfying its pre-condition. -/
def KSpecC (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) : List Spec → Prop
  | [] => True
  | [sp] => ∀ s, sp.pre s →
      let f := step m0 orc sp.link s
      f.err = none ∧ f.tail = none ∧ sp.post f
  | sp :: sp' :: rest =>
    (∀ s, sp.pre s →
      let f := step m0 orc sp.link s
      f.err = none ∧
        ((f.tail = none ∧ sp.post f) ∨
         (f.tail = some sp'.link.name ∧ sp'.pre (resume f)))) ∧
    KSpecC m0 orc (sp' :: rest)

/-- The end state of a chain: the last link's post-condition, or the post-condition of a
link that returned before the chain was exhausted. -/
def ChainPost : List Spec → CS → Prop
  | [] => fun _ => True
  | [sp] => sp.post
  | sp :: sp' :: rest => fun f => sp.post f ∨ ChainPost (sp' :: rest) f

/-- The first link's pre-condition. -/
def FirstPre : List Spec → CS → Prop
  | [] => fun _ => False
  | sp :: _ => sp.pre

theorem chain_sound (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) :
    ∀ (specs : List Spec) (s : CS), KSpecC m0 orc specs → FirstPre specs s →
      let f := chainRun m0 orc specs s
      f.err = none ∧ f.tail = none ∧ ChainPost specs f
  | [], _, _, hpre => by
    simp only [FirstPre] at hpre
  | [sp], s, hok, hpre => by
    simp only [KSpecC] at hok
    simpa only [chainRun, ChainPost] using hok s hpre
  | sp :: sp' :: rest, s, hok, hpre => by
    simp only [KSpecC] at hok
    obtain ⟨hhead, hrest⟩ := hok
    have hstep := hhead s hpre
    by_cases hret : (step m0 orc sp.link s).tail = none
    · have hpost : sp.post (step m0 orc sp.link s) := by
        rcases hstep.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · rw [hret] at h1
          cases h1
      simp only [chainRun, hret]
      exact ⟨hstep.1, trivial, Or.inl hpost⟩
    · rcases hstep.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 hret
      · simp only [chainRun, h1]
        obtain ⟨he, htl, hp⟩ :=
          chain_sound m0 orc (sp' :: rest) (resume (step m0 orc sp.link s)) hrest h2
        exact ⟨he, htl, Or.inr hp⟩

end Hashtree.Proofs.X86Chain
