import Hashtree.Asm.RiscvFrame
import Hashtree.Asm.X86Loop
import Hashtree.Asm.RiscvSym
import Hashtree.Proofs.RvWrapperLinux
import Hashtree.Proofs.RvDispatchInit
import Hashtree.Proofs.RvX1All
import Hashtree.Proofs.RvZbbX1All
import Hashtree.Proofs.RvCryptoAll

/-!
# Chains of the linux/riscv64 hashtree images

The shipped call path is a chain of *separate machine-code images*: the Go wrapper
`HashtreeHash` calls `hashtree_hash`, whose three instructions tail-jump into `init_and_hash`,
which answers a `riscv_hwprobe` syscall and tail-jumps into the selected SHA-256 kernel, which
returns to the wrapper's return point; the wrapper then restores `ra`/`sp` and returns to Go.

`Riscv.run` executes one program and stops at a jump into another function (`tail`), so a call
into another image and a `ret` in another image are *not* `Riscv.run` steps.  This module makes
those boundaries explicit and composes the images on one shared memory:

* `Link` — one image: its tail-call name, program, own code/rodata region, steps, and its step
  function on the chain state;
* `Spec` — a link with a pre- and post-condition;
* `chainRun` — runs the links in order, following `tail = some <next name>` on the same memory;
* `KSpecC` / `ChainPost` / `FirstPre` / `chain_sound` — the per-link obligation and the chain
  soundness theorem (as `Hashtree.Proofs.X86Chain` for the x86-64 chain);
* `return_transition` — the `ret` boundary: the callee's run ends `halted` at the shared return
  marker, and the caller resumes at its return point with the callee's register/memory effects;
* the concrete four-link composition (`wrapper` -> `hashtree_hash` -> `init_and_hash` (two
  windows around the `riscv_hwprobe` call) -> selected kernel) for each finite probe class,
  ending with the wrapper's *epilogue on the memory the callee chain actually left*, so the
  wrapper's post-return state is derived from the callee runs instead of assumed.

## Model-level and proved, precisely

Proved: every `Riscv.run` step of every image on the shared memory (tail names, halt/error
flags, the memory each link leaves, the kernel's output bytes and its `sp` preservation), the
tail-following composition, and the epilogue over the chain's memory (the saved `ra` slot is
read back from the write log the wrapper itself produced).

Model-level (stated at the link boundaries, not derived from a run):
1. a call/return into another image is not a `Riscv.run` step; the transfer is the explicit
   `resume`/`returned` boundary (`return_transition` records exactly what it preserves);
2. the `riscv_hwprobe` answer is the harness stub `syscallStub` (a link that is not a program);
3. the *ABI register hand-off* at the kernel entry: the dispatcher saves `a0`-`a2` in
   `s3`/`s2`/`s1` and restores them before the tail jump, and the kernel link enters at the
   declared LP64D entry (`a0 = output`, `a1 = input`, `a2 = count`, `sp = 0`, `ra = <rRet,0>`)
   with the constants the wrapper passed (`cOut`, `cIn`, `3`, proven at link 1); the
   *mechanized* form of that restore is not available because `State.getG` on a concrete run
   state whose registers are written by `List.set` does not reduce (`List.set` is
   `List.brecOn`-defined); the dispatcher's own selection/canary facts are proved separately
   (`Proofs.RvDispatchInit`);
4. the kernel's own code/rodata/GOT regions are the per-kernel model's (10/11/12), so the
   per-class chain carries the selected kernel's rodata; the dispatcher links never read them.

The finite-probe limitation is unchanged: the chain is instantiated for each tested probe class
(none / `0`, `0x10`, `0x2100`, plus `ih_select_bits` for the 8 tested-bit combinations); a
symbolic probe value is not expressible in the model (`Ctl.asConst` on a register value).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.RvChain
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvRun Hashtree.Asm.X86

/-- A chain state. -/
abbrev CS := State W32 Int

/-! ## The chain framework -/

/-- One image in a call/tail-call chain.  `step` is the link's semantics on the chain state: it
runs the image with the state's write log as the newest layer of the shared memory and returns
the state the next link continues from (its log keeps the caller's writes). -/
structure Link where
  /-- The tail-call name the previous image jumps to (`hashtree_hash`, `init_and_hash`, a kernel). -/
  name : String
  prog : Array Riscv.Instr
  /-- The image's own code region. -/
  ro : Region
  /-- Instruction count of this image for the chain's block count. -/
  steps : Nat
  step : (Addr Int → Cell W32 Int) → CS → CS

/-- A link with the pre- and post-condition of the chain composition. -/
structure Spec where
  link : Link
  pre : CS → Prop
  post : CS → Prop

/-- The state handed to the next image after a tail call: start at `pc 0` with the flags
cleared, on the same memory (a tail call shares the caller's return marker and stack). -/
def resume (s : CS) : CS := { s with pc := 0, halted := false, tail := none }

/-- Run a chain, following a tail `name` into the following link, on one shared memory. -/
def chainRun (mm : Addr Int → Cell W32 Int) : List Spec → CS → CS
  | [], s => s
  | [sp], s => sp.link.step mm s
  | sp :: sp' :: rest, s =>
    let f := sp.link.step mm s
    match f.tail with
    | some t => if t = sp'.link.name then chainRun mm (sp' :: rest) (resume f) else f
    | none => f

/-- Per-link obligation.  A link is checked from its own pre-condition: a return must meet the
post-condition, a tail must name the next link and hand it a state satisfying its
pre-condition. -/
def KSpecC (mm : Addr Int → Cell W32 Int) : List Spec → Prop
  | [] => True
  | [sp] => ∀ s, sp.pre s →
      let f := sp.link.step mm s
      f.err = none ∧ f.tail = none ∧ sp.post f
  | sp :: sp' :: rest =>
    (∀ s, sp.pre s →
      let f := sp.link.step mm s
      f.err = none ∧
        ((f.tail = none ∧ sp.post f) ∨
         (f.tail = some sp'.link.name ∧ sp'.pre (resume f)))) ∧
    KSpecC mm (sp' :: rest)

/-- The end state of a chain: the post-condition of the link that returned. -/
def ChainPost : List Spec → CS → Prop
  | [] => fun _ => True
  | [sp] => sp.post
  | sp :: sp' :: rest => fun f => sp.post f ∨ ChainPost (sp' :: rest) f

/-- The first link's pre-condition. -/
def FirstPre : List Spec → CS → Prop
  | [] => fun _ => False
  | sp :: _ => sp.pre

/-- **Chain soundness.**  If every link meets `KSpecC`, the chain returns (`err = none`,
`tail = none`) and meets the post-condition of the link that returned. -/
theorem chain_sound (mm : Addr Int → Cell W32 Int) :
    ∀ (specs : List Spec) (s : CS), KSpecC mm specs → FirstPre specs s →
      let f := chainRun mm specs s
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
    by_cases hret : (sp.link.step mm s).tail = none
    · have hpost : sp.post (sp.link.step mm s) := by
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
          chain_sound mm (sp' :: rest) (resume (sp.link.step mm s)) hrest h2
        exact ⟨he, htl, Or.inr hp⟩

/-! ## The `ret` boundary -/

/-- The return point of the Go wrapper (`pc` after `jalr ra, ra, 0`). -/
def retPc : Nat := 8

/-- Resuming the caller at its return point with the callee's register/memory effects. -/
def returned (s : CS) : CS := { s with pc := retPc, halted := false, tail := none }

/-- **The return transition.**  A `ret` in another image is not a `Riscv.run` step: the callee's
run ends with `halted = true` (a jump to the shared return marker `<rRet, 0>`), and the caller
resumes at `pc = 8` with the callee's registers and memory, its own error state, and cleared
halt/tail flags.  This lemma records exactly what the transfer preserves, so a chain proof can
continue in the caller's image with the callee's post-state. -/
theorem return_transition (s : CS) (_hh : s.halted = true) (_ht : s.tail = none) (he : s.err = none) :
    (returned s).halted = false ∧ (returned s).tail = none ∧ (returned s).pc = retPc ∧
      (returned s).err = none ∧ (returned s).mem = s.mem ∧ (returned s).gpr = s.gpr ∧
      (∀ r, (returned s).getG r = s.getG r) :=
  ⟨rfl, rfl, rfl, he ▸ rfl, rfl, rfl, fun _ => rfl⟩

/-- The callee's halt at the shared marker is exactly what `returned` starts from. -/
theorem returned_halted (s : CS) : (returned s).halted = false := rfl


/-! ## Runs preserve the register-file length

`State.getG` reads with a default, so facts about a register need the index in range.  Every
`Hashtree.Asm.Riscv.exec` of the RISC-V instruction set only ever changes `gpr` through `List.set`, so the register
file's length is preserved by a Hashtree.Asm.Riscv.run; this is what lets the chain's epilogue reload `ra` (`ld ra`)
and bump `sp` (`addi sp, sp, 8`) on the state the kernel left. -/

theorem len_next (s : State W32 Int) : s.next.gpr.length = s.gpr.length := rfl

theorem len_fail (s : State W32 Int) (m : String) : (s.fail m).gpr.length = s.gpr.length := by
  unfold State.fail; split <;> rfl

theorem len_halt (s : State W32 Int) : (Hashtree.Asm.Riscv.halt s).gpr.length = s.gpr.length := rfl

theorem len_haltTail (s : State W32 Int) (n : String) : (Hashtree.Asm.Riscv.haltTail s n).gpr.length = s.gpr.length := rfl

theorem len_setPc (s : State W32 Int) (k : Nat) : (Hashtree.Asm.Riscv.setPc s k).gpr.length = s.gpr.length := rfl

theorem callOut_len' (s : State W32 Int) (pc : Nat) (n : String) :
    (Hashtree.Asm.Riscv.callOut s pc n).gpr.length = s.gpr.length := rfl

theorem len_assumeC (s : State W32 Int) (cs : List (Cond Int × Bool)) :
    (Hashtree.Asm.Riscv.assumeC s cs).gpr.length = s.gpr.length := rfl

theorem len_storeLane (s : State W32 Int) (a : Addr Int) (x : W32) :
    (storeLane s a x).gpr.length = s.gpr.length := rfl

theorem len_storeVal (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    (storeVal s a v).gpr.length = s.gpr.length := by
  unfold storeVal
  split
  · rw [len_storeLane, len_storeLane]
  · rfl

theorem len_branch (orc : Nat → Bool) (s : State W32 Int) (c : Cond Int) (t : Nat) :
    (s.branch orc c t).gpr.length = s.gpr.length := by
  unfold State.branch
  cases h : c.decideC with
  | some b =>
    simp only [h]
    split <;> rfl
  | none =>
    simp only [h]
    split <;> rfl

theorem len_rset (s : State W32 Int) (d : Nat) (v : Val W32 Int) :
    (Hashtree.Asm.Riscv.rset s d v).gpr.length = s.gpr.length := by
  unfold Hashtree.Asm.Riscv.rset
  split
  · rfl
  · simp only [State.setG, List.length_set]

theorem len_rset_next (s : State W32 Int) (d : Nat) (v : Val W32 Int) :
    (Hashtree.Asm.Riscv.rset s d v).next.gpr.length = s.gpr.length := by rw [len_next, len_rset]

theorem len_link (env : Env) (s : State W32 Int) (d : Nat) :
    (Hashtree.Asm.Riscv.link env s d).gpr.length = s.gpr.length := by
  unfold Hashtree.Asm.Riscv.link; exact len_rset s d _

theorem len_okOr (s : State W32 Int) (r : Except String (State W32 Int))
    (h : ∀ s', r = .ok s' → s'.gpr.length = s.gpr.length) :
    (Hashtree.Asm.Riscv.okOr s r).gpr.length = s.gpr.length := by
  cases r with
  | ok s' => exact h s' rfl
  | error e =>
    show (s.fail e).gpr.length = s.gpr.length
    exact len_fail s e

theorem len_pure (s : State W32 Int) (x : State W32 Int) (hx : x.gpr.length = s.gpr.length) :
    ∀ s', (pure x : Except String (State W32 Int)) = .ok s' → s'.gpr.length = s.gpr.length := by
  intro s' h
  cases h
  exact hx

theorem len_bind {α : Type} (s : State W32 Int) (x : Except String α)
    (f : α → Except String (State W32 Int))
    (hf : ∀ v s', f v = .ok s' → s'.gpr.length = s.gpr.length) :
    ∀ s', (x >>= f) = .ok s' → s'.gpr.length = s.gpr.length := by
  intro s' h
  cases x with
  | ok v => exact hf v s' h
  | error e => cases h

theorem len_jumpTo (env : Env) (s : State W32 Int) (d : Nat) (t : Addr Int) :
    ∀ s', Hashtree.Asm.Riscv.jumpTo env s d t = .ok s' → s'.gpr.length = s.gpr.length := by
  intro s' h
  unfold Hashtree.Asm.Riscv.jumpTo at h
  by_cases hr : t.region = rRet
  · rw [if_pos hr] at h
    by_cases hd : d = 0
    · rw [if_pos hd] at h
      cases h
      exact len_halt s
    · rw [if_neg hd] at h
      cases h
  · rw [if_neg hr] at h
    by_cases hc : t.region = env.code
    · rw [if_pos hc] at h
      cases hk : Ctl.asInt t.off with
      | some k =>
        simp only [hk] at h
        by_cases h0 : k ≥ 0
        · rw [if_pos h0] at h
          cases h
          rw [len_setPc, len_link]
        · rw [if_neg h0] at h
          cases h
      | none =>
        simp only [hk] at h
        cases h
    · rw [if_neg hc] at h
      cases hn : env.nameOf t.region with
      | some name =>
        cases hk : Ctl.asInt t.off with
        | some k =>
          simp only [hn, hk] at h
          by_cases hk0 : k = 0
          · rw [if_pos hk0] at h
            by_cases hd : d = 0
            · rw [if_pos hd] at h
              cases h
              exact len_haltTail s _
            · rw [if_neg hd] at h
              cases h
              rw [callOut_len', len_link]
          · rw [if_neg hk0] at h
            cases h
        | none =>
          simp only [hn, hk] at h
          cases h
      | none =>
        cases hk : Ctl.asInt t.off <;> simp only [hn, hk] at h <;> cases h

theorem len_slliV (s : State W32 Int) (d : Nat) (v : Val W32 Int) (n : Nat) :
    ∀ s', Hashtree.Asm.Riscv.slliV s d v n = .ok s' → s'.gpr.length = s.gpr.length := by
  intro s' h
  unfold Hashtree.Asm.Riscv.slliV at h
  cases v with
  | num lo hi =>
    dsimp only at h
    cases h
    exact len_rset_next s d _
  | ptr a =>
    obtain ⟨r0, off⟩ := a
    cases r0 with
    | zero =>
      dsimp only at h
      cases hk : Ctl.asInt (Ctl.smul (2 ^ n) off) with
      | some w =>
        simp only [hk] at h
        by_cases hw : w ≥ 2 ^ 63 ∨ w < -(2 ^ 63)
        · rw [if_pos hw] at h
          cases h
        · rw [if_neg hw] at h
          cases h
          exact len_rset_next s d _
      | none =>
        simp only [hk] at h
        cases h
        exact len_rset_next _ _ _
    | succ r0 =>
      dsimp only at h
      cases h

theorem exec_len (env : Env) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Hashtree.Asm.Riscv.Instr) (s : State W32 Int) : (Hashtree.Asm.Riscv.exec env mem0 orc i s).gpr.length = s.gpr.length := by
  cases i with
  | nop =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_next s
  | unimp =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_fail s "illegal instruction"
  | lui d imm20 =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_rset_next s d _
  | auipc d t =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun a s' h => len_pure s _ (len_rset_next s d _) s' h))
  | addi d r imm =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun v s' h => len_pure s _ (len_rset_next s d _) s' h))
  | add d a b =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · refine len_okOr s _ (fun s' h => ?_)
      split at h
      · exact len_bind s _ _ (fun v s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h
      · split at h
        · exact len_bind s _ _ (fun v s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h
        · exact len_bind s _ _ (fun v s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h
  | bop op d a b =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _
        (fun x s' h => len_bind s _ _
          (fun y s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h))
  | bopi op d a imm =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun x s' h => len_pure s _ (len_rset_next s d _) s' h))
  | slli d r n =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (fun s' h => by
        split at h
        · cases h
        · exact len_slliV s d _ n s' h)
  | srai d r n =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (fun s' h => by
        split at h
        · cases h
        · exact len_bind s _ _ (fun y s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h)
  | wop op d r n =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (fun s' h => by
        split at h
        · cases h
        · exact len_bind s _ _ (fun x s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h)
  | addw d a b =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _
        (fun x s' h => len_bind s _ _
          (fun y s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h))
  | rev8 d r =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun x s' h => len_pure s _ (len_rset_next s d _) s' h))
  | sha op d r =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun x s' h => len_pure s _ (len_rset_next s d _) s' h))
  | lwu d b off =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _
        (fun a s' h => len_bind s _ _
          (fun w s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h))
  | ld d b off =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _
        (fun a s' h => len_bind s _ _
          (fun w s'' h2 => len_pure s _ (len_rset_next s d _) s'' h2) s' h))
  | sw src b off =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun a s' h => len_bind s _ _
        (fun _ s'' h2 => len_bind s _ _
          (fun x s''' h3 => len_pure s _ (by rw [len_next, len_storeLane]) s''' h3) s'' h2) s' h))
  | sd src b off =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _
        (fun a s' h => len_bind s _ _
          (fun _ s'' h2 => len_pure s _ (by rw [len_next, len_storeVal]) s'' h2) s' h))
  | br c a b t =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun x s' h => len_bind s _ _
        (fun y s'' h2 => len_bind s _ _
          (fun e s''' h3 => len_pure s _ (len_branch orc s _ _) s''' h3) s'' h2) s' h))
  | jal d t =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · rw [len_setPc, len_link]
  | jalr d r off =>
    unfold Hashtree.Asm.Riscv.exec; split
    · rfl
    · exact len_okOr s _ (len_bind s _ _ (fun t s' h => len_jumpTo env s d (t.plusI off) s' h))

theorem run_len (prog : Array Hashtree.Asm.Riscv.Instr) (env : Env) (mem0 : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (n : Nat) (s : State W32 Int) :
    (Hashtree.Asm.Riscv.run prog env mem0 orc n s).gpr.length = s.gpr.length := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold Hashtree.Asm.Riscv.run
    split
    · rfl
    · split
      · rename_i i hi
        exact (ih (Hashtree.Asm.Riscv.exec env mem0 orc i s)).trans (exec_len env mem0 orc i s)
      · exact len_fail s "pc out of program"



/-! # The concrete chain: wrapper → `hashtree_hash` → `init_and_hash` → kernel → epilogue

All images run on one shared memory (`chainMem`): the wrapper's ABI0 frame and the stack, the
`.data.rel.local` slot, the `init_and_hash` object (its rodata/GOT/code regions and canary), the
selected kernel's rodata/GOT with the input bytes, and zero data elsewhere.  Each image has its
own static environment (its own region numbering, as the model gives each image), so the
composition is on the *memory*, not on a shared address space; the region conventions are listed
in `chainMem` above.

The call path is two `chainRun`s with the `riscv_hwprobe` syscall between them: a syscall return
resumes the *caller* at its call instruction (`pc = 25`), whereas `resume` starts a tail-called
image at `pc = 0`, so the syscall is a chain boundary, not a link.  The kernel's `ret` is the
second boundary (`returned`), and the wrapper's epilogue then runs on the memory the kernel
actually left. -/

section Concrete
open Hashtree.Spec Hashtree.Asm.RiscvSym Hashtree.Asm.SpecQ Hashtree.Kernels.Riscv.WrapperLinux
open Hashtree.Proofs.RvWrapperLinux Hashtree.Proofs.RvDispatchInit Hashtree.Proofs.Rv

/-- The chain's branch oracle: every undecided branch takes its fall-through. -/
def orc : Nat → Bool := fun _ => false

/-- `init_and_hash`'s program (its own code region 24). -/
def dprog : Array Riscv.Instr := Hashtree.Kernels.Riscv.DispInitAndHash.prog

/-- **The chain's shared memory** (one memory for the whole Go-side path): the ABI0 frame and the
stack region (`memC`), the `.data.rel.local` slot (region 60, `cMem`), and `init_and_hash`'s
object — its GOT, canary and `.data.rel.local` slot, zero data elsewhere (`ihMem`).  Every link
reads through the shared write log first (`view s.mem ·`), so the three images see one memory.
The base is *closed* on purpose: a closed base memory lets `Riscv.run` be evaluated
definitionally, a parameterized one does not. -/
def chainMem : Addr Int → Cell W32 Int := fun a =>
  if a.region = rStack ∨ a.region = 60 then cMem a else ihMem a

/-- The ABI0 entry state (`sp = 8`: `ra` = the return marker, the callee stack pointer `0`, and the
three argument words of the frame). -/
def entryChain : CS := entryC

/-! ## The stages

A `Riscv.run` stops at a jump into another image (`tail`); the chain resumes the next image at its
own `pc 0`.  The `riscv_hwprobe` boundary is *inside* `init_and_hash`: the harness resumes the
same program at the instruction after the `ecall` (`pc = 25`), so that stage pins `pc 25` itself
instead of using the tail-call resume.

Each step below is written to take the state the chain actually hands it, which is the previous
run's state already `resume`d at `pc = 0` (the chain does the resume exactly once, at the tail-call
boundary).  The step therefore does *not* resume again: this keeps the canonical states `t1`, `d1`,
`s1`, `d2` syntactically identical to the terms the chain evaluates, so the per-link pre/post
obligations are decided by `rfl` rather than by re-evaluating the previous image's run. -/

/-- The wrapper's 8 instructions up to the `CALL hashtree_hash`. -/
def wrapStep (s : CS) : CS := Riscv.run prog wenv chainMem orc 8 s

/-- The `hashtree_hash` stub's three instructions (they read the `.data.rel.local` slot). -/
def stubStep (s : CS) : CS := Riscv.run sprog senv (view s.mem chainMem) orc 3 s

/-- `init_and_hash` up to the `riscv_hwprobe` call (25 instructions). -/
def dispAStep (s : CS) : CS := Riscv.run dprog ihEnv (view s.mem chainMem) orc 25 s

/-- The `riscv_hwprobe` syscall (a boundary, not a run): the harness stub answers and the program
resumes at the instruction after the `ecall`. -/
def sysStep (p : Probe) (s : CS) : CS :=
  { syscallStub p (view s.mem chainMem) { s with halted := false, tail := none } with pc := 25 }

/-- The rest of `init_and_hash` from the syscall return point: the kernel selection, the canary
check and the tail jump (34 instructions). -/
def dispBStep (s : CS) : CS :=
  Riscv.run dprog ihEnv (view s.mem chainMem) orc 34 { s with pc := 25, halted := false, tail := none }

/-- The wrapper's call state. -/
def w1 : CS := wrapStep entryChain
/-- The stub's call state (`tail = some "init_and_hash"`); its input is the wrapper's state at the
tail-call boundary, resumed at `pc = 0`. -/
def t1 : CS := stubStep (resume w1)
/-- `init_and_hash` at the `riscv_hwprobe` call. -/
def d1 : CS := dispAStep (resume t1)
/-- The state after the syscall, resumed at `pc = 25`. -/
def s1 (p : Probe) : CS := sysStep p (resume d1)
/-- The selection's result: `tail = some <selected kernel>`. -/
def d2 (p : Probe) : CS := dispBStep (s1 p)

/-! ## The selected kernel -/

/-- The kernel program selected by the probe answer. -/
def kprog : Probe → Array Riscv.Instr
  | none => Hashtree.Kernels.Riscv.X1.prog
  | some 0x10 => Hashtree.Kernels.Riscv.ZbbX1.prog
  | some 0x2100 => Hashtree.Kernels.Riscv.Crypto.prog
  | some _ => Hashtree.Kernels.Riscv.X1.prog

/-- The selected kernel's own static environment (rodata 10, GOT 11, code 12 in every kernel). -/
def kpe : Probe → Env
  | none => Hashtree.Gen.RvX1L.pe
  | some 0x10 => Hashtree.Gen.RvZbbX1L.pe
  | some 0x2100 => Hashtree.Gen.RvCryptoL.pe
  | some _ => Hashtree.Gen.RvX1L.pe

/-- The selected kernel's instruction count for `c` blocks. -/
def ksteps : Probe → Nat → Nat
  | none, c => Hashtree.Proofs.RvX1L.steps c
  | some 0x10, c => Hashtree.Proofs.RvZbbX1L.steps c
  | some 0x2100, c => Hashtree.Proofs.RvCryptoL.steps c
  | some _, c => Hashtree.Proofs.RvX1L.steps c

/-- The selected kernel's rodata (its symbolic-memory constant). -/
def krodata : Probe → List Nat
  | none => Hashtree.Kernels.Riscv.X1.rodata
  | some 0x10 => Hashtree.Kernels.Riscv.ZbbX1.rodata
  | some 0x2100 => Hashtree.Kernels.Riscv.Crypto.rodata
  | some _ => Hashtree.Kernels.Riscv.X1.rodata

/-- The selected kernel's GOT layout (its symbolic-memory constant). -/
def kgotT : Probe → List (Region × Int)
  | none => Hashtree.Gen.RvX1L.gotT
  | some 0x10 => Hashtree.Gen.RvZbbX1L.gotT
  | some 0x2100 => Hashtree.Gen.RvCryptoL.gotT
  | some _ => Hashtree.Gen.RvX1L.gotT

/-- **The selected kernel's run.**  The kernel is a separate machine-code image with its own
address space: it is entered at its declared LP64D entry (`a0` = output, `a1` = input, `a2` =
count, `ra` = the shared return marker, `sp = 0`) and runs on its own memory `kMem`.

This is the *model-level* part of the composition.  What the chain proves is the ABI hand-off and
the selection: after the dispatcher returns from the syscall it has `a0 = ⟨rOut,8⟩`,
`a1 = ⟨rIn,0⟩`, `a2 = 3` (`link_d2_*`) and tail-jumps to the kernel named by `kSel` of the probe
answer.  What is *assumed* here is that the kernel's declared entry is the state it is entered in
and that its own memory `kMem` (its rodata/GOT, its input buffer and its output buffer) satisfies
the kernel's interface conditions `hw`/`he`/`hin`.  The kernel's run itself is not assumed: its
facts are the kernel's proved correctness theorem (`RvX1L.correct` / `RvZbbX1L.correct` /
`RvCryptoL.correct`), applied to `kMem`. -/
def kerRun (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) : CS :=
  Riscv.run (kprog p) (kpe p) kMem orcK (ksteps p c) (mapState env0 σ (entryS 0))

/-! ## The links' concrete facts -/

/-- **Link 1** — the wrapper prefix at the ABI0 entry: after 8 instructions the wrapper is at the
`CALL hashtree_hash` with the three arguments in `a0`-`a2` and the callee stack pointer
`8 + (-8) = 0` (B7-aligned). -/
theorem link_wrapper :
    w1.halted = true ∧ w1.tail = some "call:hashtree_hash" ∧ w1.err = none ∧ w1.pc = 8 ∧
      w1.getG 1 = .ptr ⟨rWcode, 8⟩ ∧ w1.getG 2 = .ptr ⟨rStack, 8 + (-8)⟩ ∧
      w1.getG 10 = .ptr cOut ∧ w1.getG 11 = .ptr cIn ∧ w1.getG 12 = .ptr ⟨rNum, cCount⟩ ∧
      w1.gpr.length = 32 :=
  wrapper_prefix chainMem orc 8 cOut cIn cCount entryC
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl)

/-- The wrapper's write log does not shadow the `.data.rel.local` slot: the stub reads a pointer to
`init_and_hash` through the wrapper's memory (the wrapper wrote only its stack frame). -/
theorem w1_slot : loadVal (view w1.mem chainMem) w1 (⟨60, 0⟩ : Addr Int) =
    .ok (.ptr (⟨6, 0⟩ : Addr Int)) := by
  rfl

/-- **Link 2** — the `hashtree_hash` stub tail-jumps to `init_and_hash` without writing memory and
without changing `ra`, `sp` or the three argument registers. -/
theorem link_stub :
    t1.halted = true ∧ t1.tail = some "init_and_hash" ∧ t1.err = none ∧ t1.mem = w1.mem ∧
      t1.getG 1 = w1.getG 1 ∧ t1.getG 2 = w1.getG 2 ∧ t1.getG 10 = w1.getG 10 ∧
      t1.getG 11 = w1.getG 11 ∧ t1.getG 12 = w1.getG 12 := by
  obtain ⟨-, -, h3, -, -, -, -, -, -, hglen⟩ := link_wrapper
  have h := stub_run (view w1.mem chainMem) orc (resume w1) (by rfl) (by rfl)
    (by rw [show (resume w1).gpr.length = w1.gpr.length from rfl]; exact hglen) w1_slot
  exact ⟨h.1, h.2.1, h.2.2.1.trans h3, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- **Link 3** — `init_and_hash` reaches the `riscv_hwprobe` call after 25 instructions, naming
the syscall in `tail`. -/
theorem link_dispA :
    d1.halted = true ∧ d1.tail = some "call:syscall" ∧ d1.err = none ∧ d1.pc = 25 :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **Link 4a** — with the syscall failed, `init_and_hash` selects the plain x1 kernel. -/
theorem link_d2_none :
    (d2 none).halted = true ∧ (d2 none).tail = some kX1 ∧ (d2 none).err = none ∧
      (d2 none).getG 10 = .ptr cOut ∧ (d2 none).getG 11 = .ptr cIn ∧
      (d2 none).getG 12 = .ptr ⟨rNum, 3⟩ :=
  ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- **Link 4b** — with `(v &&& 16) ≠ 0` (here `v = 0x10`), `init_and_hash` selects the zbb
kernel. -/
theorem link_d2_zbb :
    (d2 (some 0x10)).halted = true ∧ (d2 (some 0x10)).tail = some kZbb ∧
      (d2 (some 0x10)).err = none ∧ (d2 (some 0x10)).getG 10 = .ptr cOut ∧
      (d2 (some 0x10)).getG 11 = .ptr cIn ∧ (d2 (some 0x10)).getG 12 = .ptr ⟨rNum, 3⟩ :=
  ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- **Link 4c** — with `(v &&& 0x2100) = 0x2100` (here `v = 0x2100`), `init_and_hash` selects the
crypto kernel. -/
theorem link_d2_crypto :
    (d2 (some 0x2100)).halted = true ∧ (d2 (some 0x2100)).tail = some kCrypto ∧
      (d2 (some 0x2100)).err = none ∧ (d2 (some 0x2100)).getG 10 = .ptr cOut ∧
      (d2 (some 0x2100)).getG 11 = .ptr cIn ∧ (d2 (some 0x2100)).getG 12 = .ptr ⟨rNum, 3⟩ :=
  ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-! ## The kernel entry facts -/

/-- The kernel entry's stack pointer is the shared frame base `<rStack, 0>`. -/
theorem entryS_sp (env0 : Key → W32) (σ : Nat → Int) :
    (mapState env0 σ (entryS 0)).getG 2 = .ptr (⟨rStack, 0⟩ : Addr Int) := by
  rw [getG_hom]
  simp only [State.getG, entryS, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.map_cons, List.map_nil, mapVal,
    mapAddr, Lin.ofInt, Lin.eval, dotC]
  rfl

/-- The kernel entry's register file has all 32 registers. -/
theorem entryS_len (K : State E Lin) (h : K = entryS 0) : (K.gpr.length = 32) := by
  subst h
  simp only [entryS, List.length_map, List.length_range]

/-- `mapState` preserves the register-file length. -/
theorem mapState_len (env0 : Key → W32) (σ : Nat → Int) (K : State E Lin) :
    (mapState env0 σ K).gpr.length = K.gpr.length := by
  simp only [mapState, List.length_map]

/-! ## `resume` projections -/

theorem resume_gpr (s : CS) : (resume s).gpr = s.gpr := rfl
theorem resume_mem (s : CS) : (resume s).mem = s.mem := rfl
theorem resume_getG (s : CS) (r : Nat) : (resume s).getG r = s.getG r := rfl
theorem resume_halted (s : CS) : (resume s).halted = false := rfl
theorem resume_pc (s : CS) : (resume s).pc = 0 := rfl
theorem resume_tail (s : CS) : (resume s).tail = none := rfl
theorem resume_err (s : CS) : (resume s).err = s.err := rfl

/-! ## The chain -/

/-- The selected kernel's name (`hashtree_sha256_riscv_x1` when the probe fails; the two tested
bits select the other two). -/
def kSel : Probe → String
  | none => kX1
  | some 0x2100 => kCrypto
  | some 0x10 => kZbb
  | some _ => kX1

/-- The chain: wrapper -> `hashtree_hash` -> `init_and_hash` (up to the syscall) ->
`init_and_hash` (syscall and selection) -> the selected kernel.  Each link's `pre` pins the state
its own facts were proved from (the previous stage) and its `post` is that stage's computed state;
the stages' semantic facts are `link_wrapper` … `link_d2_*` and the kernel's correctness theorem,
so the chain's end state is the kernel's proved run reached through the whole Go-side path. -/
def specs (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) : List Spec :=
  [ { link := { name := "wrapper", prog := prog, ro := rWcode, steps := 8,
                step := fun _ s => wrapStep s },
      pre := fun s => s = entryChain, post := fun s => s = w1 },
    { link := { name := "call:hashtree_hash", prog := sprog, ro := 6, steps := 3,
                step := fun _ s => stubStep s },
      pre := fun s => s = resume w1, post := fun s => s = t1 },
    { link := { name := "init_and_hash", prog := dprog, ro := 24, steps := 25,
                step := fun _ s => dispAStep s },
      pre := fun s => s = resume t1, post := fun s => s = d1 },
    { link := { name := "call:syscall", prog := dprog, ro := 24, steps := 59,
                step := fun _ s => dispBStep (sysStep p s) },
      pre := fun s => s = resume d1, post := fun s => s = d2 p },
    { link := { name := kSel p, prog := kprog p, ro := 12, steps := 0,
                step := fun _ _ => kerRun p c env0 σ kMem orcK },
      pre := fun _ => True,
      post := fun s => s.halted = true ∧ s.tail = none ∧ s.err = none } ]

/-- The chain's end state is the selected kernel's run: the tail-following composition evaluates
through the four Go-side links and stops at the kernel image (none of the four Go-side links
returns; each names the next). -/
theorem chainRun_none (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) :
    chainRun cMem (specs none c env0 σ kMem orcK) entryChain =
      kerRun none c env0 σ kMem orcK := by
  rfl

theorem chainRun_zbb (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) :
    chainRun cMem (specs (some 0x10) c env0 σ kMem orcK) entryChain =
      kerRun (some 0x10) c env0 σ kMem orcK := by
  rfl

theorem chainRun_crypto (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) :
    chainRun cMem (specs (some 0x2100) c env0 σ kMem orcK) entryChain =
      kerRun (some 0x2100) c env0 σ kMem orcK := by
  rfl

/-- **The chain obligation, x1 class.** -/
theorem specs_KSpecC_none (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata none) (kgotT none) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    KSpecC cMem (specs none c env0 σ kMem orcK) := by
  obtain ⟨-, h2, h3, -, -, -, -, -, -, -⟩ := link_wrapper
  obtain ⟨-, h5, h6, -, -, -, -, -, -⟩ := link_stub
  obtain ⟨-, h8, h9, -⟩ := link_dispA
  obtain ⟨-, h11, h12, -, -, -⟩ := link_d2_none
  obtain ⟨k1, k2, k3, -, -, -⟩ :=
    Hashtree.Proofs.RvX1L.correct c inp env0 σ kMem orcK hw he hc hσ0 hb hin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hs]
    exact ⟨h3, Or.inr ⟨h2, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h6, Or.inr ⟨h5, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h9, Or.inr ⟨h8, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h12, Or.inr ⟨h11, trivial⟩⟩
  · intro s _
    exact ⟨k2, k3, k1, k3, k2⟩

/-- **The chain obligation, zbb class.** -/
theorem specs_KSpecC_zbb (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x10)) (kgotT (some 0x10)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    KSpecC cMem (specs (some 0x10) c env0 σ kMem orcK) := by
  obtain ⟨-, h2, h3, -, -, -, -, -, -, -⟩ := link_wrapper
  obtain ⟨-, h5, h6, -, -, -, -, -, -⟩ := link_stub
  obtain ⟨-, h8, h9, -⟩ := link_dispA
  obtain ⟨-, h11, h12, -, -, -⟩ := link_d2_zbb
  obtain ⟨k1, k2, k3, -, -, -⟩ :=
    Hashtree.Proofs.RvZbbX1L.correct c inp env0 σ kMem orcK hw he hc hσ0 hb hin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hs]
    exact ⟨h3, Or.inr ⟨h2, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h6, Or.inr ⟨h5, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h9, Or.inr ⟨h8, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h12, Or.inr ⟨h11, trivial⟩⟩
  · intro s _
    exact ⟨k2, k3, k1, k3, k2⟩

/-- **The chain obligation, crypto class.** -/
theorem specs_KSpecC_crypto (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x2100)) (kgotT (some 0x2100)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    KSpecC cMem (specs (some 0x2100) c env0 σ kMem orcK) := by
  obtain ⟨-, h2, h3, -, -, -, -, -, -, -⟩ := link_wrapper
  obtain ⟨-, h5, h6, -, -, -, -, -, -⟩ := link_stub
  obtain ⟨-, h8, h9, -⟩ := link_dispA
  obtain ⟨-, h11, h12, -, -, -⟩ := link_d2_crypto
  obtain ⟨k1, k2, k3, -, -, -⟩ :=
    Hashtree.Proofs.RvCryptoL.correct c inp env0 σ kMem orcK hw he hc hσ0 hb hin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hs]
    exact ⟨h3, Or.inr ⟨h2, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h6, Or.inr ⟨h5, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h9, Or.inr ⟨h8, rfl⟩⟩
  · intro s hs
    rw [hs]
    exact ⟨h12, Or.inr ⟨h11, trivial⟩⟩
  · intro s _
    exact ⟨k2, k3, k1, k3, k2⟩

/-- **Chain soundness, x1 class.**  Every link meets its obligation, so the chain returns
(`err = none`, `tail = none`) and its end state meets the post-condition of the link that
returned (the selected kernel's halt). -/
theorem chain_sound_none (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata none) (kgotT none) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let f := chainRun cMem (specs none c env0 σ kMem orcK) entryChain
    f.err = none ∧ f.tail = none ∧ ChainPost (specs none c env0 σ kMem orcK) f :=
  chain_sound cMem (specs none c env0 σ kMem orcK) entryChain
    (specs_KSpecC_none c inp env0 σ kMem orcK hw he hc hσ0 hb hin) rfl

/-- **The chain, x1 class.**  The chain's end state is the x1 kernel's proved run (through the
four Go-side links), and the kernel's correctness theorem gives its halt, its output, and the
stack pointer the epilogue resumes from. -/
theorem chain_none (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata none) (kgotT none) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (kerRun none c env0 σ kMem orcK).halted = true ∧
      (kerRun none c env0 σ kMem orcK).err = none ∧
      (kerRun none c env0 σ kMem orcK).tail = none ∧
      (kerRun none c env0 σ kMem orcK).getG 2 = .ptr ⟨rStack, 0⟩ ∧
      InRange (σ 1) (32 * c) (kerRun none c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun none c env0 σ kMem orcK).mem := by
  obtain ⟨hfin, hmem⟩ :
      ((kerRun none c env0 σ kMem orcK).halted = true ∧
        (kerRun none c env0 σ kMem orcK).err = none ∧
        (kerRun none c env0 σ kMem orcK).tail = none ∧
        InRange (σ 1) (32 * c) (kerRun none c env0 σ kMem orcK).mem ∧
        OutOk inp (σ 1) c (kerRun none c env0 σ kMem orcK).mem) ∧
      (kerRun none c env0 σ kMem orcK).getG 2 = .ptr ⟨rStack, 0⟩ := by
    obtain ⟨k1, k2, k3, k5, k6, k4⟩ :=
      Hashtree.Proofs.RvX1L.correct c inp env0 σ kMem orcK hw he hc hσ0 hb hin
    exact ⟨⟨k1, k2, k3, k5, k6⟩, (k4 2 (by simp)).trans (entryS_sp env0 σ)⟩
  exact ⟨hfin.1, hfin.2.1, hfin.2.2.1, hmem, hfin.2.2.2.1, hfin.2.2.2.2⟩


theorem chain_sound_zbb (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x10)) (kgotT (some 0x10)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let f := chainRun cMem (specs (some 0x10) c env0 σ kMem orcK) entryChain
    f.err = none ∧ f.tail = none ∧ ChainPost (specs (some 0x10) c env0 σ kMem orcK) f :=
  chain_sound cMem (specs (some 0x10) c env0 σ kMem orcK) entryChain
    (specs_KSpecC_zbb c inp env0 σ kMem orcK hw he hc hσ0 hb hin) rfl


theorem chain_sound_crypto (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x2100)) (kgotT (some 0x2100)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let f := chainRun cMem (specs (some 0x2100) c env0 σ kMem orcK) entryChain
    f.err = none ∧ f.tail = none ∧ ChainPost (specs (some 0x2100) c env0 σ kMem orcK) f :=
  chain_sound cMem (specs (some 0x2100) c env0 σ kMem orcK) entryChain
    (specs_KSpecC_crypto c inp env0 σ kMem orcK hw he hc hσ0 hb hin) rfl


/-- **The chain, zbb class.**  The chain's end state is the zbb kernel's proved run (through the
four Go-side links), and the kernel's correctness theorem gives its halt, its output, and the
stack pointer the epilogue resumes from. -/
theorem chain_zbb (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x10)) (kgotT (some 0x10)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (kerRun (some 0x10) c env0 σ kMem orcK).halted = true ∧
      (kerRun (some 0x10) c env0 σ kMem orcK).err = none ∧
      (kerRun (some 0x10) c env0 σ kMem orcK).tail = none ∧
      (kerRun (some 0x10) c env0 σ kMem orcK).getG 2 = .ptr ⟨rStack, 0⟩ ∧
      InRange (σ 1) (32 * c) (kerRun (some 0x10) c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun (some 0x10) c env0 σ kMem orcK).mem := by
  obtain ⟨hfin, hmem⟩ :
      ((kerRun (some 0x10) c env0 σ kMem orcK).halted = true ∧
        (kerRun (some 0x10) c env0 σ kMem orcK).err = none ∧
        (kerRun (some 0x10) c env0 σ kMem orcK).tail = none ∧
        InRange (σ 1) (32 * c) (kerRun (some 0x10) c env0 σ kMem orcK).mem ∧
        OutOk inp (σ 1) c (kerRun (some 0x10) c env0 σ kMem orcK).mem) ∧
      (kerRun (some 0x10) c env0 σ kMem orcK).getG 2 = .ptr ⟨rStack, 0⟩ := by
    obtain ⟨k1, k2, k3, k5, k6, k4⟩ :=
      Hashtree.Proofs.RvZbbX1L.correct c inp env0 σ kMem orcK hw he hc hσ0 hb hin
    exact ⟨⟨k1, k2, k3, k5, k6⟩, (k4 2 (by simp)).trans (entryS_sp env0 σ)⟩
  exact ⟨hfin.1, hfin.2.1, hfin.2.2.1, hmem, hfin.2.2.2.1, hfin.2.2.2.2⟩


/-- **The chain, crypto class.**  The chain's end state is the crypto kernel's proved run (through the
four Go-side links), and the kernel's correctness theorem gives its halt, its output, and the
stack pointer the epilogue resumes from. -/
theorem chain_crypto (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x2100)) (kgotT (some 0x2100)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (kerRun (some 0x2100) c env0 σ kMem orcK).halted = true ∧
      (kerRun (some 0x2100) c env0 σ kMem orcK).err = none ∧
      (kerRun (some 0x2100) c env0 σ kMem orcK).tail = none ∧
      (kerRun (some 0x2100) c env0 σ kMem orcK).getG 2 = .ptr ⟨rStack, 0⟩ ∧
      InRange (σ 1) (32 * c) (kerRun (some 0x2100) c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun (some 0x2100) c env0 σ kMem orcK).mem := by
  obtain ⟨hfin, hmem⟩ :
      ((kerRun (some 0x2100) c env0 σ kMem orcK).halted = true ∧
        (kerRun (some 0x2100) c env0 σ kMem orcK).err = none ∧
        (kerRun (some 0x2100) c env0 σ kMem orcK).tail = none ∧
        InRange (σ 1) (32 * c) (kerRun (some 0x2100) c env0 σ kMem orcK).mem ∧
        OutOk inp (σ 1) c (kerRun (some 0x2100) c env0 σ kMem orcK).mem) ∧
      (kerRun (some 0x2100) c env0 σ kMem orcK).getG 2 = .ptr ⟨rStack, 0⟩ := by
    obtain ⟨k1, k2, k3, k5, k6, k4⟩ :=
      Hashtree.Proofs.RvCryptoL.correct c inp env0 σ kMem orcK hw he hc hσ0 hb hin
    exact ⟨⟨k1, k2, k3, k5, k6⟩, (k4 2 (by simp)).trans (entryS_sp env0 σ)⟩
  exact ⟨hfin.1, hfin.2.1, hfin.2.2.1, hmem, hfin.2.2.2.1, hfin.2.2.2.2⟩


/-! ## The return transition and the wrapper's epilogue -/

/-- The memory after the kernel returns: its write log replayed over the Go-side memory it was
entered with. -/
def postMem (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) : Addr Int → Cell W32 Int :=
  view (kerRun p c env0 σ kMem orcK).mem (view (d2 p).mem chainMem)

/-- The wrapper's post-return state: the caller resumed at `pc = 8` with the callee's registers
and memory (`return_transition`). -/
def sret (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) : CS :=
  returned (kerRun p c env0 σ kMem orcK)

theorem plusI_zero (a : Addr Int) : a.plusI (0 : Int) = a := by
  obtain ⟨r, o⟩ := a
  simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]

theorem addr_plusI (a : Addr Int) (m n : Int) : (a.plusI m).plusI n = a.plusI (m + n) := by
  obtain ⟨r, o⟩ := a
  simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
  omega

theorem except_bind_congr {ε α β : Type} (X : Except ε α) (F G : α → Except ε β)
    (hF : ∀ x, F x = G x) : (X >>= F) = (X >>= G) := by
  cases X with
  | error e => rfl
  | ok a => exact hF a

/-- `readCell` agrees at a byte when both logs miss it and the base memories agree there. -/
theorem readCell_congr (mm1 mm2 : Addr Int → Cell W32 Int) (s1 s2 : State W32 Int) (a : Addr Int)
    (hm : mm1 a = mm2 a) (h1 : lookup a s1.mem = .ok none) (h2 : lookup a s2.mem = .ok none) :
    readCell mm1 s1 a = readCell mm2 s2 a := by
  rw [readCell, readCell, h1, h2, hm]

theorem pbRest_congr (mm1 mm2 : Addr Int → Cell W32 Int) (s1 s2 : State W32 Int) (p a : Addr Int)
    (h : ∀ k : Int, 0 ≤ k → k < 8 → readCell mm1 s1 (a.plusI k) = readCell mm2 s2 (a.plusI k)) :
    ∀ (n k : Nat), k + n ≤ 8 → pbRest mm1 s1 p a n k = pbRest mm2 s2 p a n k := by
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    have hk8 : (k : Int) < 8 := by omega
    simp only [pbRest]
    rw [h (k : Int) (by omega) hk8]
    refine except_bind_congr _ _ _ (fun c => ?_)
    split
    · exact ih (k + 1) (by omega)
    · rfl

theorem loadLane_congr (mm1 mm2 : Addr Int → Cell W32 Int) (s1 s2 : State W32 Int) (a : Addr Int)
    (h : ∀ k : Int, 0 ≤ k → k < 4 → readCell mm1 s1 (a.plusI k) = readCell mm2 s2 (a.plusI k)) :
    loadLane mm1 s1 a = loadLane mm2 s2 a := by
  simp only [loadLane]
  rw [show readCell mm1 s1 a = readCell mm2 s2 a from (plusI_zero a) ▸ h 0 (by omega) (by omega),
    h 1 (by omega) (by omega), h 2 (by omega) (by omega), h 3 (by omega) (by omega)]

theorem loadVal_congr (mm1 mm2 : Addr Int → Cell W32 Int) (s1 s2 : State W32 Int) (a : Addr Int)
    (h : ∀ k : Int, 0 ≤ k → k < 8 → readCell mm1 s1 (a.plusI k) = readCell mm2 s2 (a.plusI k)) :
    loadVal mm1 s1 a = loadVal mm2 s2 a := by
  have h0 : readCell mm1 s1 a = readCell mm2 s2 a := (plusI_zero a) ▸ h 0 (by omega) (by omega)
  have hrest : ∀ p : Addr Int, pbRest mm1 s1 p a 7 1 = pbRest mm2 s2 p a 7 1 := fun p =>
    pbRest_congr mm1 mm2 s1 s2 p a (fun j _ _ => h j (by omega) (by omega)) 7 1 (by omega)
  have hl1 : loadLane mm1 s1 a = loadLane mm2 s2 a :=
    loadLane_congr mm1 mm2 s1 s2 a (fun j _ _ => h j (by omega) (by omega))
  have hl2 : loadLane mm1 s1 (a.plusI 4) = loadLane mm2 s2 (a.plusI 4) :=
    loadLane_congr mm1 mm2 s1 s2 (a.plusI 4) (fun j _ _ => by
      rw [addr_plusI]; exact h (4 + j) (by omega) (by omega))
  simp only [loadVal]
  rw [h0]
  refine except_bind_congr _ _ _ (fun c0 => ?_)
  split
  · rw [hrest _]
  · rw [hl1, hl2]


/-- `InRange` misses every byte of the frame slot `⟨rStack, 0⟩ + o` for `0 ≤ o < 8` (the ra slot
the wrapper reloads): the kernel's writes are output bytes or its own frame below `sp`. -/
theorem inRange_ne_slot (M : List (Addr Int × Cell W32 Int)) (ob : Int) (len : Nat) (h : InRange ob len M)
    (o : Int) (h0 : 0 ≤ o) (h8 : o < 8) :
    ∀ p ∈ M, p.1 ≠ ((⟨rStack, 0⟩ : Addr Int).plusI o) := by
  intro p hp heq
  have hpo : ((⟨rStack, 0⟩ : Addr Int).plusI o) = (⟨rStack, o⟩ : Addr Int) := by
    simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
  rw [hpo] at heq
  rcases h p hp with ⟨h1, -, -⟩ | ⟨-, -, h3⟩
  · have h1' : rStack = rOut := by rw [heq] at h1; simpa using h1
    exact absurd h1' (by decide)
  · have h3' : o < 0 := by rw [heq] at h3; simpa using h3
    omega

/-- The ra slot as the Go-side path leaves it: the wrapper's own save is the last write. -/
theorem ra_slot_go_none :
    loadVal (view (d2 none).mem chainMem) entryC (⟨rStack, 0⟩ : Addr Int) =
      .ok (.ptr (⟨rRet, 0⟩ : Addr Int)) := by
  rfl

theorem ra_slot_go_zbb :
    loadVal (view (d2 (some 0x10)).mem chainMem) entryC (⟨rStack, 0⟩ : Addr Int) =
      .ok (.ptr (⟨rRet, 0⟩ : Addr Int)) := by
  rfl

theorem ra_slot_go_crypto :
    loadVal (view (d2 (some 0x2100)).mem chainMem) entryC (⟨rStack, 0⟩ : Addr Int) =
      .ok (.ptr (⟨rRet, 0⟩ : Addr Int)) := by
  rfl

/-- A byte of the ra slot reads the same through the kernel's post-return memory and the Go-side
memory: the kernel's writes miss the slot (`InRange`) and both logs miss it. -/
theorem readCell_post (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hIn : InRange (σ 1) (32 * c) (kerRun p c env0 σ kMem orcK).mem)
    (k : Int) (h0 : 0 ≤ k) (h8 : k < 8) :
    readCell (postMem p c env0 σ kMem orcK) (sret p c env0 σ kMem orcK)
        ((⟨rStack, 0⟩ : Addr Int).plusI k) =
      readCell (view (d2 p).mem chainMem) entryC ((⟨rStack, 0⟩ : Addr Int).plusI k) := by
  have hne : ∀ q ∈ (kerRun p c env0 σ kMem orcK).mem,
      q.1 ≠ ((⟨rStack, 0⟩ : Addr Int).plusI k) :=
    inRange_ne_slot _ (σ 1) (32 * c) hIn k h0 h8
  refine readCell_congr _ _ _ _ _ ?_ ?_ ?_
  · exact view_other _ _ _ hne
  · exact lookup_none_ne _ _ hne
  · rfl

/-- The wrapper's ra slot survives the callee: `hsave` is derived from the kernel's own
correctness theorem, not assumed. -/
theorem ra_slot_post (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hIn : InRange (σ 1) (32 * c) (kerRun p c env0 σ kMem orcK).mem)
    (hgo : loadVal (view (d2 p).mem chainMem) entryC (⟨rStack, 0⟩ : Addr Int) =
      .ok (.ptr (⟨rRet, 0⟩ : Addr Int))) :
    loadVal (postMem p c env0 σ kMem orcK) (sret p c env0 σ kMem orcK)
        (⟨rStack, 0⟩ : Addr Int) = .ok (.ptr (⟨rRet, 0⟩ : Addr Int)) :=
  (loadVal_congr _ _ _ _ _ (fun k h0 h8 => readCell_post p c env0 σ kMem orcK hIn k h0 h8)).trans hgo

/-- The kernel's run keeps the register file at 32 entries. -/
theorem kerRun_len (p : Probe) (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool) :
    (kerRun p c env0 σ kMem orcK).gpr.length = 32 := by
  rw [kerRun, run_len]
  simp only [mapState, List.length_map, entryS, List.length_map, List.length_range]

/-- Address of output byte `32*n + 4*i + b` for output base `ob`. -/
def outAddr (ob : Int) (n i b : Nat) : Addr Int :=
  ⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩

/-- The digest as the caller observes it in a *memory*: every output byte holds the SHA-256 value.
`OutOk` states this about the kernel's write log; `OutOkMem` states it about the memory the caller
actually reads. -/
def OutOkMem (inp : Nat → Byte) (ob : Int) (nblk : Nat) (mem : Addr Int → Cell W32 Int) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    mem (outAddr ob n i b) = .dat x b ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

/-- **Transport from the log to the visible memory.**  `view` prefers the newest logged write, and
`OutOk` says that write is the SHA-256 byte at every output address; the bytes therefore come from
the log, so no coverage hypothesis on the base memory is needed. -/
theorem outOk_view (inp : Nat → Byte) (ob : Int) (nblk : Nat)
    (M : List (Addr Int × Cell W32 Int))
    (mem0 : Addr Int → Cell W32 Int) (h : OutOk inp ob nblk M) :
    OutOkMem inp ob nblk (view M mem0) := by
  intro n i b hn hi hb
  obtain ⟨x, hx, hby⟩ := h n i b hn hi hb
  refine ⟨x, ?_, hby⟩
  delta outAddr
  simp only [view]
  rw [hx]

/-- **The Go caller sees the digest.**  `postMem` is the memory the wrapper's epilogue runs on
(the kernel's write log replayed over the Go-side memory), so the kernel's output theorem holds
there. -/
theorem outOk_postMem (p : Probe) (c : Nat) (inp : Nat → Byte) (env0 : Key → W32)
    (σ : Nat → Int) (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (h : OutOk inp (σ 1) c (kerRun p c env0 σ kMem orcK).mem) :
    OutOkMem inp (σ 1) c (postMem p c env0 σ kMem orcK) :=
  outOk_view inp (σ 1) c (kerRun p c env0 σ kMem orcK).mem (view (d2 p).mem chainMem) h

/-- **The wrapper's post-return state, derived from the callee's run.**  Given the chain's end
state (the selected kernel's run, with its proved halt/error/tail, its stack pointer and its
output) and the ra slot as the Go-side path left it, the return transition plus the wrapper's
three epilogue instructions halt with `ra` reloaded, `sp` restored to the ABI0 entry `8`, and the
digest present in the memory the epilogue runs on (`postMem`, the caller-visible memory). -/
theorem end2end_of (p : Probe) (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hk : (kerRun p c env0 σ kMem orcK).halted = true ∧
      (kerRun p c env0 σ kMem orcK).err = none ∧
      (kerRun p c env0 σ kMem orcK).tail = none ∧
      (kerRun p c env0 σ kMem orcK).getG 2 = .ptr (⟨rStack, 0⟩ : Addr Int) ∧
      InRange (σ 1) (32 * c) (kerRun p c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun p c env0 σ kMem orcK).mem)
    (hgo : loadVal (view (d2 p).mem chainMem) entryC (⟨rStack, 0⟩ : Addr Int) =
      .ok (.ptr (⟨rRet, 0⟩ : Addr Int))) :
    (Riscv.run prog wenv (postMem p c env0 σ kMem orcK) orc 3
        (sret p c env0 σ kMem orcK)).halted = true ∧
      (Riscv.run prog wenv (postMem p c env0 σ kMem orcK) orc 3
        (sret p c env0 σ kMem orcK)).tail = none ∧
      (Riscv.run prog wenv (postMem p c env0 σ kMem orcK) orc 3
        (sret p c env0 σ kMem orcK)).err = none ∧
      (Riscv.run prog wenv (postMem p c env0 σ kMem orcK) orc 3
        (sret p c env0 σ kMem orcK)).getG 1 = .ptr (⟨rRet, 0⟩ : Addr Int) ∧
      (Riscv.run prog wenv (postMem p c env0 σ kMem orcK) orc 3
        (sret p c env0 σ kMem orcK)).getG 2 = .ptr (⟨rStack, 8⟩ : Addr Int) ∧
      InRange (σ 1) (32 * c) (kerRun p c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun p c env0 σ kMem orcK).mem ∧
      OutOkMem inp (σ 1) c (postMem p c env0 σ kMem orcK) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk
  have hsave := ra_slot_post p c env0 σ kMem orcK h5 hgo
  have hglen : (sret p c env0 σ kMem orcK).gpr.length = 32 := by
    show (returned (kerRun p c env0 σ kMem orcK)).gpr.length = 32
    rw [show (returned (kerRun p c env0 σ kMem orcK)).gpr.length =
      (kerRun p c env0 σ kMem orcK).gpr.length from rfl]
    exact kerRun_len p c env0 σ kMem orcK
  have hepi := wrapper_epilogue (postMem p c env0 σ kMem orcK) orc
    (sret p c env0 σ kMem orcK) 8 0
    (by show (returned (kerRun p c env0 σ kMem orcK)).halted = false; rfl)
    (by show (returned (kerRun p c env0 σ kMem orcK)).pc = 8; rfl)
    (by show (returned (kerRun p c env0 σ kMem orcK)).tail = none; rfl)
    (by show (returned (kerRun p c env0 σ kMem orcK)).err = none; exact h2)
    hglen
    (by show (returned (kerRun p c env0 σ kMem orcK)).getG 2 = .ptr (⟨rStack, 0⟩ : Addr Int)
        exact h4)
    hsave (by decide)
  exact ⟨hepi.1, hepi.2.1, hepi.2.2.1, hepi.2.2.2.1, hepi.2.2.2.2, h5, h6,
    outOk_postMem p c inp env0 σ kMem orcK h6⟩

/-- **End to end, x1 class**: the composed run (chain -> kernel -> return -> epilogue) halts with
`ra` and `sp` restored and the kernel's proved output, visible in the memory the caller reads
(`postMem`). -/
theorem end2end_none (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata none) (kgotT none) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (Riscv.run prog wenv (postMem none c env0 σ kMem orcK) orc 3
        (sret none c env0 σ kMem orcK)).halted = true ∧
      (Riscv.run prog wenv (postMem none c env0 σ kMem orcK) orc 3
        (sret none c env0 σ kMem orcK)).tail = none ∧
      (Riscv.run prog wenv (postMem none c env0 σ kMem orcK) orc 3
        (sret none c env0 σ kMem orcK)).err = none ∧
      (Riscv.run prog wenv (postMem none c env0 σ kMem orcK) orc 3
        (sret none c env0 σ kMem orcK)).getG 1 = .ptr (⟨rRet, 0⟩ : Addr Int) ∧
      (Riscv.run prog wenv (postMem none c env0 σ kMem orcK) orc 3
        (sret none c env0 σ kMem orcK)).getG 2 = .ptr (⟨rStack, 8⟩ : Addr Int) ∧
      InRange (σ 1) (32 * c) (kerRun none c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun none c env0 σ kMem orcK).mem ∧
      OutOkMem inp (σ 1) c (postMem none c env0 σ kMem orcK) :=
  end2end_of none c inp env0 σ kMem orcK
    (chain_none c inp env0 σ kMem orcK hw he hc hσ0 hb hin) ra_slot_go_none


/-- **End to end, zbb class**: the composed run (chain -> kernel -> return -> epilogue) halts with
`ra` and `sp` restored and the kernel's proved output, visible in the memory the caller reads
(`postMem`). -/
theorem end2end_zbb (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x10)) (kgotT (some 0x10)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (Riscv.run prog wenv (postMem (some 0x10) c env0 σ kMem orcK) orc 3
        (sret (some 0x10) c env0 σ kMem orcK)).halted = true ∧
      (Riscv.run prog wenv (postMem (some 0x10) c env0 σ kMem orcK) orc 3
        (sret (some 0x10) c env0 σ kMem orcK)).tail = none ∧
      (Riscv.run prog wenv (postMem (some 0x10) c env0 σ kMem orcK) orc 3
        (sret (some 0x10) c env0 σ kMem orcK)).err = none ∧
      (Riscv.run prog wenv (postMem (some 0x10) c env0 σ kMem orcK) orc 3
        (sret (some 0x10) c env0 σ kMem orcK)).getG 1 = .ptr (⟨rRet, 0⟩ : Addr Int) ∧
      (Riscv.run prog wenv (postMem (some 0x10) c env0 σ kMem orcK) orc 3
        (sret (some 0x10) c env0 σ kMem orcK)).getG 2 = .ptr (⟨rStack, 8⟩ : Addr Int) ∧
      InRange (σ 1) (32 * c) (kerRun (some 0x10) c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun (some 0x10) c env0 σ kMem orcK).mem ∧
      OutOkMem inp (σ 1) c (postMem (some 0x10) c env0 σ kMem orcK) :=
  end2end_of (some 0x10) c inp env0 σ kMem orcK
    (chain_zbb c inp env0 σ kMem orcK hw he hc hσ0 hb hin) ra_slot_go_zbb


/-- **End to end, crypto class**: the composed run (chain -> kernel -> return -> epilogue) halts with
`ra` and `sp` restored and the kernel's proved output, visible in the memory the caller reads
(`postMem`). -/
theorem end2end_crypto (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (kMem : Addr Int → Cell W32 Int) (orcK : Nat → Bool)
    (hw : WfMemR 10 11 (krodata (some 0x2100)) (kgotT (some 0x2100)) kMem)
    (he : Hashtree.Asm.X86Sym.EnvMem env0 σ kMem) (hc : σ 2 = c)
    (hσ0 : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63)
    (hin : ∀ o : Nat, kMem ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (Riscv.run prog wenv (postMem (some 0x2100) c env0 σ kMem orcK) orc 3
        (sret (some 0x2100) c env0 σ kMem orcK)).halted = true ∧
      (Riscv.run prog wenv (postMem (some 0x2100) c env0 σ kMem orcK) orc 3
        (sret (some 0x2100) c env0 σ kMem orcK)).tail = none ∧
      (Riscv.run prog wenv (postMem (some 0x2100) c env0 σ kMem orcK) orc 3
        (sret (some 0x2100) c env0 σ kMem orcK)).err = none ∧
      (Riscv.run prog wenv (postMem (some 0x2100) c env0 σ kMem orcK) orc 3
        (sret (some 0x2100) c env0 σ kMem orcK)).getG 1 = .ptr (⟨rRet, 0⟩ : Addr Int) ∧
      (Riscv.run prog wenv (postMem (some 0x2100) c env0 σ kMem orcK) orc 3
        (sret (some 0x2100) c env0 σ kMem orcK)).getG 2 = .ptr (⟨rStack, 8⟩ : Addr Int) ∧
      InRange (σ 1) (32 * c) (kerRun (some 0x2100) c env0 σ kMem orcK).mem ∧
      OutOk inp (σ 1) c (kerRun (some 0x2100) c env0 σ kMem orcK).mem ∧
      OutOkMem inp (σ 1) c (postMem (some 0x2100) c env0 σ kMem orcK) :=
  end2end_of (some 0x2100) c inp env0 σ kMem orcK
    (chain_crypto c inp env0 σ kMem orcK hw he hc hσ0 hb hin) ra_slot_go_crypto


end Concrete

end Hashtree.Proofs.RvChain
