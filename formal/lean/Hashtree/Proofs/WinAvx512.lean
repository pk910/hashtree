import Hashtree.Proofs.Win64
import Hashtree.Gen.Avx512X16P.Final
import Hashtree.Kernels.X86Win.Avx512X16

/-!
# R5: functional contract for the windows `avx512_x16` kernel

This file transfers the linux/amd64 body proof `Gen.Avx512X16P.Final.out_final` to the shipped
windows/COFF instruction stream `Kernels.X86Win.Avx512X16.prog`.

The windows stream is the linux one under a permutation of the general registers (`F`, `G` below):

| linux | windows | role |
|---|---|---|
| `rdi` (7) | `rcx` (1) | output |
| `rsi` (6) | `rdx` (2) | input |
| `rdx` (2) | `r8`  (8) | count |
| `rcx` (1) | `r9`  (9) | rodata base 0 |
| `r8`  (8) | `r10` (10) | rodata base 4160 |

`windows_prog_correspondence` records the per-instruction identity of the *shipped* streams; it is
checked externally by `formal/ci/relcheck` (3247/3247 instructions match under the rename, and
`formal/ci/x86identity`/`x86check` re-validate both models against the objects on every CI run).

Everything else is machine-checked here:

* `win_run`: the windows run of `STEPS` instructions, starting from the renamed symbolic state,
  reaches the rename of the linux final symbolic state `K217`;
* `win_out`: every output byte is the SHA-256 byte of its block (the Go-facing contract);
* `u6_witness` / `win_no_rsp` / `win_no_stack_access`: observation U6 -- this kernel uses **no
  stack at all** and therefore cannot save or restore `xmm6`-`xmm15`.  A caller-facing contract
  for it must not assume that the callee-saved vector registers survive the call.

## Win64 state model

The call is entered with the Go-facing arguments in `rcx`, `rdx`, `r8` (shadow space and return
address live above `rsp`).  Unlike `shani`/`avx_x4`/`sse_x1`/`avx_x1`/`avx2_x8`, the shipped
avx512 kernel has no prologue: it neither reserves a frame nor spills `xmm6`-`xmm15`.  The entry
state used below is therefore the plain register permutation of the linux symbolic entry state --
no frame relation is needed, and `WinFrame`/the shadow-space predicate are vacuous for it.  See
`Proofs.Win64` for the reusable frame/state vocabulary (`WinFrame`, `WinCalleeSaved`, shadow
space, `exec_ren`/`run_ren_upto`).
-/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.SpecQ Hashtree.Spec
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvx512

open Hashtree.Asm.X86

open Hashtree.Gen.Avx512X16P
open Hashtree.Kernels.X86.Avx512X16 (rodata)

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Avx512X16.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Avx512X16.prog

/-! ## The register permutation -/

/-- linux -> windows general register numbering. -/
def F : Nat → Nat
  | 1 => 9 | 2 => 8 | 6 => 2 | 7 => 1 | 8 => 10 | 9 => 6 | 10 => 7 | j => j

/-- windows -> linux general register numbering (the inverse of `F`). -/
def G : Nat → Nat
  | 1 => 7 | 2 => 6 | 6 => 9 | 7 => 10 | 8 => 2 | 9 => 1 | 10 => 8 | j => j

theorem all_fin {p : Nat → Prop} [DecidablePred p]
    (h : ((List.range 16).all (fun j => decide (p j))) = true) :
    ∀ j, j < 16 → p j := by
  intro j hj
  have hm : j ∈ List.range 16 := List.mem_range.mpr hj
  have h1 := List.all_eq_true.mp h j hm
  simpa using h1

theorem f_lt : ∀ j, j < 16 → F j < 16 := by apply all_fin; decide

theorem gf : ∀ j, j < 16 → G (F j) = j := by apply all_fin; decide

theorem fg : ∀ j, j < 16 → F (G j) = j := by apply all_fin; decide

theorem renPerm : RenPerm F G := ⟨f_lt, gf, fg, rfl⟩

/-! ## The syntactic side condition of the simulation -/

instance instDecMemOk (m : MemRef) : Decidable (memOk m) := by unfold memOk; infer_instance
instance instDecGsrc (s : GSrc) : Decidable (gsrcOk s) := by
  cases s <;> dsimp only [gsrcOk] <;> infer_instance
instance instDecVsrc (s : VSrc) : Decidable (vsrcOk s) := by
  cases s <;> dsimp only [vsrcOk] <;> infer_instance
instance instDecOkI (i : Instr) : Decidable (okI i) := by
  cases i <;> dsimp only [okI] <;> infer_instance

theorem linuxProg_ok_all : linuxProg.toList.all (fun i => decide (okI i)) = true := by
  decide +kernel

theorem linuxProg_ok (pc : Nat) (x : Instr) (hx : linuxProg[pc]? = some x) : okI x := by
  have hm : x ∈ linuxProg.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hx
    rw [Array.mem_toList_iff, ← hget]
    exact Array.getElem_mem hlt
  have h1 := List.all_eq_true.mp linuxProg_ok_all x hm
  simpa using h1

/-! ## The transfer engine -/

/-- The windows stream is the renamed linux stream, instruction for instruction.  This is the
external, tools-checked input of the transfer (the streams are generated from the shipped
objects; `formal/ci` rechecks the identity of both models against the binaries). -/
def windows_prog_correspondence : Prop :=
  ∀ j, j < linuxProg.size → winProg[j]? = (linuxProg[j]?).map (rlI F)

/-- Simulate a linux run of `n` steps on the windows program. -/
theorem win_transfer {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (hprog : windows_prog_correspondence) (n : Nat) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (hs : s.err = none) (hf : (run linuxProg ro mem0 orc n s).err = none) :
    run winProg ro mem0 orc n (renSt F G s) = renSt F G (run linuxProg ro mem0 orc n s) :=
  run_ren_upto renPerm linuxProg winProg hprog linuxProg_ok n s hlen
    (run_pc_upto linuxProg n s hs hf)

/-! ## The body proof of the linux kernel, restated on the windows stream -/

/-- Number of instructions the linux body proof runs (`Gen.Avx512X16P.Final.run_final`). -/
def STEPS : Nat := (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1 + (22)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem STEPS_eq : STEPS = (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1 + (22))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := rfl

theorem win_run (hprog : windows_prog_correspondence) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel env0 σ (mem0s 4 rodata 24) mem0c) (hσ : σ 2 = 16) :
    run winProg 4 mem0c orcC STEPS (renSt F G (mapState env0 σ (entryS 24)))
      = renSt F G (mapState (E217 env0) σ K217) := by
  have hlen : (mapState env0 σ (entryS 24)).gpr.length = 16 := by simp [mapState, entryS]
  have hs : (mapState env0 σ (entryS 24)).err = none := rfl
  have hf : (run linuxProg 4 mem0c orcC STEPS (mapState env0 σ (entryS 24))).err = none := by
    rw [STEPS_eq, run_final env0 σ mem0c orcC h0 hσ]
    rfl
  have h := win_transfer (ro := 4) (mem0 := mem0c) (orc := orcC) hprog STEPS
    (mapState env0 σ (entryS 24)) hlen hs hf
  rw [STEPS_eq, run_final env0 σ mem0c orcC h0 hσ] at h
  rw [STEPS_eq]
  exact h

/-- Go-facing output contract of the windows `avx512_x16` body: every output byte is the SHA-256
byte of its block.  Same statement as the linux `Gen.Avx512X16P.Final.out_final`, on the windows
instruction stream. -/
theorem win_out (hprog : windows_prog_correspondence) (inp : Nat → Byte) (env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (he : EnvMem env0 σ mem0c) (hσ : σ 2 = 16)
    (hm : HMem 1024 inp env0) :
    ∀ n i b, n < 16 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)
        (run winProg 4 mem0c orcC STEPS (renSt F G (mapState env0 σ (entryS 24)))).mem
          = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by
  intro n i b hn hi hb
  obtain ⟨x, hx, hb'⟩ :=
    out_final inp env0 σ mem0c orcC hw he hσ hm n i b hn hi hb
  have hx' :
      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)
        (mapState (E217 env0) σ K217).mem = .ok (some (.dat x b)) := by
    rw [run_final env0 σ mem0c orcC
      (mem0Rel_of_wf 4 rodata 24 env0 σ mem0c hw he) hσ] at hx
    exact hx
  refine ⟨x, ?_, hb'⟩
  rw [win_run hprog env0 σ mem0c orcC (mem0Rel_of_wf 4 rodata 24 env0 σ mem0c hw he) hσ,
    renSt_mem]
  exact hx'

/-! ## U6: the kernel clobbers the callee-saved vector registers

`mentionsRsp i` is true when an instruction reads or writes `rsp` (as a base/index register, as a
source/destination general register, or implicitly through `push`/`pop`).  A kernel that never
mentions `rsp` cannot adjust a stack frame and cannot save or restore a callee-saved vector
register.  The syntactic scan below proves that the *shipped* avx512 stream never mentions `rsp`,
and `u6_witness` exhibits a concrete prefix on which `xmm6` is destroyed.  Together these
discharge the negative half of the Win64 contract: `xmm6`-`xmm15` may not be assumed preserved
across a call to this kernel (observation U6 of the roadmap). -/

/-- Does the memory operand address through `rsp`? -/
def memRsp (m : MemRef) : Bool := m.base.any (· = 4) || m.index.any (· = 4)

/-- Does the general-register operand mention `rsp`? -/
def gsrcRsp : GSrc → Bool
  | .reg i => decide (i = 4)
  | .imm _ => false
  | .mem m => memRsp m

/-- Does the instruction read or write `rsp`? -/
def mentionsRsp : Instr → Bool
  | .nop => false
  | .vop _ _ _ _ _ _ => false
  | .vshift _ _ _ _ _ _ => false
  | .vshiftq _ _ _ _ _ => false
  | .vror _ _ _ _ => false
  | .vtern _ _ _ _ _ => false
  | .vload _ _ _ (.mem m) => memRsp m
  | .vload _ _ _ (.reg _) => false
  | .vstore _ m _ => memRsp m
  | .pshufd _ _ _ _ => false
  | .pshufb _ _ _ _ _ => false
  | .palignr _ _ _ _ _ => false
  | .pblendw _ _ _ => false
  | .shufps _ _ _ _ _ => false
  | .perm2f128 _ _ _ _ => false
  | .inserti128 _ _ m _ => memRsp m
  | .inserti64x4 _ _ m _ => memRsp m
  | .permi2d _ _ _ => false
  | .permi2q _ _ _ => false
  | .sha256rnds2 _ _ => false
  | .sha256msg1 _ _ => false
  | .sha256msg2 _ _ => false
  | .mov _ d s => decide (d = 4) || gsrcRsp s
  | .movst _ m _ => memRsp m
  | .alu _ _ d s => decide (d = 4) || gsrcRsp s
  | .sub _ d s => decide (d = 4) || gsrcRsp s
  | .lea d m => decide (d = 4) || memRsp m
  | .ror _ d _ => decide (d = 4)
  | .shld _ d s _ => decide (d = 4) || decide (s = 4)
  | .shl _ d _ => decide (d = 4)
  | .bswap _ d => decide (d = 4)
  | .push _ => true
  | .pop _ => true
  | .cmp _ a b => decide (a = 4) || gsrcRsp b
  | .test _ a b => decide (a = 4) || decide (b = 4)
  | .jcc _ _ => false
  | .jmp _ => false
  | .jccTail _ _ => false
  | .jmpTail _ => false
  | .ret => false

/-- The shipped windows avx512 stream never mentions `rsp`: it has no stack frame. -/
theorem win_no_rsp : winProg.toList.all (fun i => !mentionsRsp i) = true := by
  decide +kernel

/-- Every instruction of the shipped kernel is `rsp`-free. -/
theorem win_no_stack_access (pc : Nat) (x : Instr) (hx : winProg[pc]? = some x) :
    mentionsRsp x = false := by
  have hm : x ∈ winProg.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hx
    rw [Array.mem_toList_iff, ← hget]
    exact Array.getElem_mem hlt
  have h := List.all_eq_true.mp win_no_rsp x hm
  simpa using h

/-- A concrete entry state: `r8 = 16` (two blocks), `xmm6` all ones, everything else zero. -/
def u6s0 : State W32 Int :=
  { gpr := (List.range 16).map (fun i => if i = 8 then Val.num (16 : W32) 0 else Val.num 0 0)
    vr := (List.range 32).map (fun i => if i = 6 then List.replicate 16 (1 : W32)
      else List.replicate 16 0)
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

/-- Any memory; the kernel runs on it without touching the stack. -/
def u6mem : Addr Int → Cell W32 Int := fun _ => .dat 0 0

/-- U6 witness: after only 15 instructions of the shipped kernel (pc 0..14 are the message loads
and the first rounds), `xmm6` has been overwritten with zeros.  The kernel destroys the
callee-saved vector registers and never restores them. -/
theorem u6_witness :
    State.getV (run winProg 4 u6mem (fun _ => false) 15 u6s0) 6
      ≠ State.getV u6s0 6 := by
  decide +kernel

end Hashtree.Proofs.WinAvx512
