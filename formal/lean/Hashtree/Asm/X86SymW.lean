import Hashtree.Asm.X86Sym
import Hashtree.Asm.Subst

/-!
# The kernel call state of the Go wrapper (linux/amd64 `HashtreeHash`)

The wrapper (`wrapper_linux_amd64.s`, go1.26) calls a kernel with: rdi = output, rsi = input,
rdx = count (loaded from its argument slots), rax = output and rcx = count (the ABIInternal
argument registers, unchanged), rbx = the wrapper's stack pointer, rbp = its frame pointer,
r12 = the stack-check pointer, r14 = g, rsp = an arbitrary stack address (the return address).
`entryW` is that state with symbols: 0 input, 1 output, 2 count, (3, 4 flags at loop heads),
5 rbx, 6 rbp, 7 r12, 8 g, 9 the entry stack pointer, 11 r13, 12 r15 (the caller's values of the
callee-saved r13, r15, as integers: `rNum`-tagged).  The other general registers (r8–r11) carry
caller data, modelled as numbers.  Stack addresses are relative to symbol 9.

`mem0sW`: the return address at `[s9, s9 + 8)`, the bytes listed in `push` (a kernel's saved
registers, when a proof restarts after its prologue), everything else on the stack poison;
other regions as `mem0s`.
-/

namespace Hashtree.Asm.X86SymW
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym

/-- The g region (the goroutine descriptor r14 points to). -/
def rG : Region := 6

def stkC : List Int := List.replicate 9 0 ++ [1]

/-- A stack address relative to the entry stack pointer (symbol 9). -/
def sAt (k : Int) : Lin := ⟨k, stkC⟩

def entryW : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 7 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 6 then Val.ptr ⟨rIn, Lin.sym 0⟩
    else if i = 2 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else if i = 4 then Val.ptr ⟨rStack, sAt 0⟩
    else if i = 0 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 1 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else if i = 3 then Val.ptr ⟨rStack, Lin.sym 5⟩
    else if i = 5 then Val.ptr ⟨rStack, Lin.sym 6⟩
    else if i = 12 then Val.ptr ⟨rStack, Lin.sym 7⟩
    else if i = 14 then Val.ptr ⟨rG, Lin.sym 8⟩
    else if i = 13 then Val.ptr ⟨rNum, Lin.sym 11⟩
    else if i = 15 then Val.ptr ⟨rNum, Lin.sym 12⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

/-- The offset of a stack address relative to symbol 9. -/
def stackRel (l : Lin) : Option Int := if trimC l.c = stkC then some l.k else none

theorem stackRel_eval (σ : Nat → Int) (l : Lin) (k : Int) (h : stackRel l = some k) : l.eval σ = σ 9 + k := by
  simp only [stackRel] at h
  split at h
  · rename_i hc
    cases h
    have : l.eval σ = (Lin.trim l).eval σ := (Lin.eval_trim σ l).symm
    rw [this]
    simp only [Lin.trim, Lin.eval, hc, stkC]
    simp [dotC, List.replicate]
    omega
  · cases h

def plookup (k : Int) : List (Int × Cell E Lin) → Option (Cell E Lin)
  | [] => none
  | (k', c) :: rest => if k = k' then some c else plookup k rest

theorem plookup_mem (k : Int) : ∀ (l : List (Int × Cell E Lin)) (c : Cell E Lin), plookup k l = some c → (k, c) ∈ l
  | [], _, h => by cases h
  | (k', c') :: rest, c, h => by
    simp only [plookup] at h
    split at h
    · cases h; rename_i hk; subst hk; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (plookup_mem k rest c h)

/-- Symbolic initial memory of a kernel called from the wrapper. -/
def mem0sW (ro : Region) (rodata : List Nat) (push : List (Int × Cell E Lin)) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rStack then
    match stackRel a.off with
    | some k =>
      if 0 ≤ k ∧ k < 8 then .pb ⟨rRet, Lin.ofInt 0⟩ k.toNat
      else match plookup k push with
        | some c => c
        | none => poison
    | none => poison
  else mem0s ro rodata 24 a

/-- Push lists whose data bytes are keyed by their stack address. -/
def pushKeyed (push : List (Int × Cell E Lin)) : Bool :=
  push.all fun p => match p.2 with
    | .dat (.var (.m r l)) _ => r == rStack && l == sAt p.1
    | .pb _ k => k < 8
    | _ => false

theorem mem0sW_keyed (ro : Region) (rodata : List Nat) (push : List (Int × Cell E Lin)) (hp : pushKeyed push = true) :
    MemKeyed (mem0sW ro rodata push) := by
  intro a
  simp only [mem0sW]
  split
  · split
    · split
      · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
      · split
        · rename_i c hc
          simp only [pushKeyed, List.all_eq_true] at hp
          have := hp _ (plookup_mem _ push c hc)
          simp only at this
          revert this
          cases c with
          | dat x j =>
            cases x with
            | var key =>
              cases key with
              | m r l => intro; exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
              | n i => simp
            | _ => simp
          | pb q j => intro; exact Or.inr (Or.inr ⟨_, _, rfl⟩)
        · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  · exact mem0s_keyed ro rodata 24 a

/-- The concrete initial memory of a kernel call: rodata, the return address at `σ 9`, input bytes,
and the listed stack bytes. -/
def WfMemW (rodata : List Nat) (push : List (Int × Cell E Lin)) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) : Prop :=
  (∀ o, m ⟨4, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) ∧
  (∀ k : Int, 0 ≤ k → k < 8 → m ⟨rStack, σ 9 + k⟩ = .pb ⟨rRet, 0⟩ k.toNat) ∧
  (∀ o, m ⟨rIn, o⟩ = .dat (cellX (m ⟨rIn, o⟩)) 0) ∧
  (∀ k c, plookup k push = some c → ¬ (0 ≤ k ∧ k < 8) → Cell.okC c → m ⟨rStack, σ 9 + k⟩ = mapCell env σ c)

theorem mem0RelW_of_wf (rodata : List Nat) (push : List (Int × Cell E Lin)) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata push env σ m) (he : EnvMem env σ m) :
    Mem0Rel env σ (mem0sW 4 rodata push) m := by
  obtain ⟨hro, hret, hin, hpush⟩ := hw
  intro a ha
  obtain ⟨r, off⟩ := a
  by_cases hs : r = rStack
  · subst hs
    simp only [mem0sW, ite_true] at ha ⊢
    cases hk : stackRel off with
    | none => simp only [hk] at ha; simp [poison, Cell.okC] at ha
    | some k =>
      simp only [hk] at ha ⊢
      have hev := stackRel_eval σ off k hk
      by_cases h8 : 0 ≤ k ∧ k < 8
      · simp only [h8, and_self, ite_true, mapCell, mapAddr, hev]
        rw [hret k h8.1 h8.2]; rfl
      · simp only [h8, ite_false] at ha ⊢
        cases hl : plookup k push with
        | none => simp only [hl] at ha; simp [poison, Cell.okC] at ha
        | some c =>
          simp only [hl] at ha ⊢
          simp only [mapAddr, hev]
          exact hpush k c hl h8 ha
  · have e : mem0sW 4 rodata push ⟨r, off⟩ = mem0s 4 rodata 24 ⟨r, off⟩ := by simp only [mem0sW, hs, ite_false]
    rw [e] at ha ⊢
    simp only [mem0s] at ha ⊢
    by_cases hi : r = rIn
    · subst hi
      simp only [ite_true, mapCell, E.eval, mapAddr]
      rw [he]; exact hin _
    · simp only [hi, ite_false] at ha ⊢
      cases hk : off.asInt with
      | none => simp only [hk] at ha; simp [poison, Cell.okC] at ha
      | some o =>
        simp only [hk] at ha ⊢
        have hev : off.eval σ = o := Lin.eval_asInt σ off o hk
        by_cases h4 : r = 4
        · subst h4
          simp only [ite_true, mapCell, E.eval, mapAddr, hev]
          exact hro o
        · simp only [h4, ite_false] at ha ⊢
          simp only [hs, ite_false] at ha
          simp [poison, Cell.okC] at ha

/-- Callee-saved registers that hold caller numbers at a wrapper call: none (r13, r15 are `rNum`-tagged). -/
def keepIdsW : List Nat := []

end Hashtree.Asm.X86SymW
