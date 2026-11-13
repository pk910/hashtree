import Hashtree.Proofs.X86Chain
import Hashtree.Kernels.X86Win.Avx512X16
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Kernels.X86Win.AvxX1

/-!
# R5: the windows COFF tail-call chain, on R2's `X86Chain` contract

The four windows multi-lane kernels are the same tail chain as on linux:
`avx512_x16 -> avx2_x8 -> avx_x4 -> avx_x1`, on the shipped COFF streams (the tail
instructions are at windows pcs 8, 6103 and 4162; pcs 0..3 of each stream are the
`endbr64`/`cmp`/`jcc`/`ret` small-count entry path).  This file instantiates
`Hashtree.Proofs.X86Chain` (R2, commit `6d27a36`) for those streams; it does not
introduce a parallel chain layer.

What is proved here (over the shipped arrays, by kernel `decide`):

* `win_chain_names` -- the four links are named exactly as the tail instructions name
  them, so `chainRun`'s `tail = some name` matching can succeed;
* `win_chain_tails` -- the tail instruction of each multi-lane stream, at its concrete
  pc, names the next link;
* `win_small_exit` -- the small-count entry path of each multi-lane stream returns at
  pc 3, so a link may also return before the chain is exhausted (`ChainPost`).

The composition theorems:

* `win_callChain_returns` -- if every link meets its `KSpecC` obligation, the wrapper's
  `callChain` returns with `err = none`, `tail = none`, `halted = false`, `pc = 0` and
  the chain post-condition, provided the post-condition is stable under `resume`
  (memory/register contracts are);
* `win_callChain_fr` -- the chain call commutes with a memory-log frame, i.e. the
  wrapper's earlier writes are the chain's initial memory and are appended to its log
  (`chainRun_fr`, R2).

Not proved here: the per-link `KSpecC` obligations (they need a windows functional
contract per kernel: avx512_x16 has one at count 16, `Proofs.WinAvx512.win_out`; the
three frame kernels have ABI/frame models only, see `Proofs/WinSseX1`,
`Proofs/WinAvxX1`, `Proofs/WinShani` and `formal/notes/R5.md` section 6) and a Lean
model of the Go wrapper text itself.  All four links currently use rodata region 4;
per-link regions need R2's region-renaming lemma (`WfMemAt`/rho simulation).
-/

namespace Hashtree.Proofs.WinChain
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Proofs.X86Chain

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev p512 : Array Instr := Hashtree.Kernels.X86Win.Avx512X16.prog
abbrev p8 : Array Instr := Hashtree.Kernels.X86Win.Avx2X8.prog
abbrev p4 : Array Instr := Hashtree.Kernels.X86Win.AvxX4.prog
abbrev p1 : Array Instr := Hashtree.Kernels.X86Win.AvxX1.prog

/-- A link of the shipped windows chain: its program, its tail-call name and its step
function.  The rodata region is `4` (`rRo`) for every link; see the note above. -/
def linkOf (name : String) (prog : Array Instr) (steps : Nat → Nat) : Link :=
  { name := name, prog := prog, ro := 4, steps := steps }

/-- The shipped windows chain in tail order, with caller-supplied per-link pre/post
conditions and step functions. -/
def winSpecs (s512 s8 s4 s1 : Nat → Nat)
    (P512 Q512 P8 Q8 P4 Q4 P1 Q1 : CS → Prop) : List Spec :=
  [ ⟨linkOf "hashtree_sha256_avx512_x16" p512 s512, P512, Q512⟩,
    ⟨linkOf "hashtree_sha256_avx2_x8" p8 s8, P8, Q8⟩,
    ⟨linkOf "hashtree_sha256_avx_x4" p4 s4, P4, Q4⟩,
    ⟨linkOf "hashtree_sha256_avx_x1" p1 s1, P1, Q1⟩ ]

/-- The four link names are exactly the names used by the tail instructions. -/
theorem win_chain_names :
    (winSpecs (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)
      (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)).map
      (fun sp => sp.link.name)
      = ["hashtree_sha256_avx512_x16", "hashtree_sha256_avx2_x8",
         "hashtree_sha256_avx_x4", "hashtree_sha256_avx_x1"] := rfl

/-- The tail instruction of each multi-lane shipped stream, at its concrete windows pc. -/
theorem win_chain_tails :
    p512[8]? = some (.jccTail .b "hashtree_sha256_avx2_x8")
      ∧ p8[6103]? = some (.jmpTail "hashtree_sha256_avx_x4")
      ∧ p4[4162]? = some (.jmpTail "hashtree_sha256_avx_x1") := by
  decide

/-- The small-count entry path of each multi-lane shipped stream returns at pc 3. -/
theorem win_small_exit :
    p512[3]? = some .ret ∧ p8[3]? = some .ret ∧ p4[3]? = some .ret := by
  decide

/-- Chain soundness for the windows chain: per-link obligations compose into a returning
chain that meets the chain post-condition.  (Specialisation of `chain_sound`.) -/
theorem win_chainRun_returns (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (c : Nat)
    (s512 s8 s4 s1 : Nat → Nat)
    (P512 Q512 P8 Q8 P4 Q4 P1 Q1 : CS → Prop) (s : CS)
    (hK : KSpecC m0 orc c (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1))
    (hpre : FirstPre (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) s) :
    let f := chainRun m0 orc c (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) s
    f.err = none ∧ f.tail = none
      ∧ ChainPost (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) f :=
  chain_sound m0 orc c _ s hK hpre

/-- The wrapper's call: `callChain` starts the first link at pc 0 (the caller has pushed
its return marker) and resumes the caller after the chain returns.  From the per-link
obligations the caller gets back a normal state (`err = none`, `tail = none`, `halted =
false`, `pc = 0`) satisfying the chain post-condition, which only has to be stable under
`resume` (memory/output contracts are). -/
theorem win_callChain_returns (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (c : Nat)
    (s512 s8 s4 s1 : Nat → Nat)
    (P512 Q512 P8 Q8 P4 Q4 P1 Q1 : CS → Prop) (s : CS)
    (hK : KSpecC m0 orc c (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1))
    (hpre : FirstPre (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) { s with pc := 0 })
    (hres : ∀ f, ChainPost (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) f →
      ChainPost (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) (resume f)) :
    let r := callChain m0 orc c (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) s
    r.err = none ∧ r.tail = none ∧ r.halted = false ∧ r.pc = 0
      ∧ ChainPost (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) r := by
  have h := chain_sound m0 orc c (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1)
    { s with pc := 0 } hK hpre
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · simp only [callChain, h.2.1]
  · simp only [callChain]
  · simp only [callChain]
  · have hres' := hres
      (chainRun m0 orc c (winSpecs s512 s8 s4 s1 P512 Q512 P8 Q8 P4 Q4 P1 Q1) { s with pc := 0 })
      h.2.2
    simpa only [callChain, resume] using hres'

/-- The chain call commutes with a memory-log frame: the wrapper's earlier writes are the
chain's initial memory and are appended to its log (`chainRun_fr`, R2). -/
theorem win_callChain_fr (L : CLog) (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (c : Nat) (specs : List Spec) (s : CS) :
    callChain m0 orc c specs (fr L s) = fr L (callChain (view L m0) orc c specs s) := by
  simp only [callChain]
  rw [show ({ fr L s with pc := 0 } : CS) = fr L { s with pc := 0 } from rfl]
  rw [chainRun_fr]
  rfl

end Hashtree.Proofs.WinChain
