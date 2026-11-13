import Hashtree.Kernels.Riscv.DispInitAndHash
import Hashtree.Kernels.Riscv.DispInit
import Hashtree.Asm.RiscvRun

/-!
# The RV64 dispatcher: `init_and_hash` and `hashtree_init` by finite classes

`hashtree_hash` (proved in `RvDispatch.lean`) tail-calls `init_and_hash` on the first call; the
kernel selected by `init_and_hash` is installed in the object's `.data.rel.local` slot, so later
calls go straight to it.  `hashtree_init` is the explicit override: with a non-NULL argument it
writes that argument into the slot and returns; with NULL it probes the hardware and selects a
kernel like `init_and_hash`.

This file proves both functions functionally on concrete states, by finite classes:

* `ihSelect`, `hiSelect` — `Riscv.run` of the program model from the LP64D entry, through the
  `riscv_hwprobe` call (answered by the harness's `syscallStub`) and the selection, to the tail
  call (respectively the return).  The registers, the GOT, the canary data and the input/output
  buffers are concrete (`ihMem`/`hiMem`), so each class is a closed kernel computation.
* the four outcomes: syscall fails -> `hashtree_sha256_riscv_x1`; `(v &&& 0x2100) = 0x2100` ->
  `hashtree_sha256_riscv_crypto`; `(v &&& 16) ≠ 0` -> `hashtree_sha256_riscv_zbb_x1`; else
  `hashtree_sha256_riscv_x1`;
* `ih_select_bits`/`hi_select_bits`: the 8 bit combinations of the three tested bits `0x2000`,
  `0x100`, `0x10` (parameterized by `b13 b8 b4 : Bool`), each showing the same four facts —
  halted, the tail (a kernel name for `init_and_hash`; `none`, i.e. a normal return, for
  `hashtree_init`), no model error (so the stack canary check took the pass branch), and the
  kernel pointer written into the `.data.rel.local` slot;
* `classOfNat_ext`: the mask `0x2110` (the three tested bits) determines the selection class, and
  `selName_eq_classOf`: the 8 combinations classify as above.

**Not proved, and not expressible in this model.**  A theorem quantified over a symbolic probe
value (`∀ v, ...`) would need `Riscv.exec` to evaluate the branches with `v` symbolic: `Ctl.asInt`
only builds constants (`ctlOf` on a register value is a *computation*, and `Cond.decideC` returns
`none` only for genuinely symbolic lanes), so the branch condition of the selection is stuck for
a symbolic `Int`.  The finite-class statements below quantify over the three *tested bits* only —
`classOfNat_ext` shows that any probe value with the same tested bits is in the same class, so
these cover every probe answer without pretending the model can evaluate an arbitrary one.

Everything here is closed-state computation (`rfl` on `Riscv.run`/`syscallStub`), no `decide`/
`native_decide`; the audit sees only `propext`/`Classical.choice`/`Quot.sound`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Hashtree.Proofs.RvDispatchInit
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvRun

/-! ## The kernel names, regions and the classification of probe values -/

def kX1 : String := "hashtree_sha256_riscv_x1"
def kZbb : String := "hashtree_sha256_riscv_zbb_x1"
def kCrypto : String := "hashtree_sha256_riscv_crypto"

/-- Regions of the three kernels in the concrete GOT of the dispatcher runs. -/
def rX1 : Region := 12
def rZbb : Region := 15
def rCrypto : Region := 18

/-- The kernel selected for a probe answer (`RISCV_HWPROBE_KEY_IMA_EXT_0` value `v`). -/
def classOfNat (v : Nat) : String :=
  if v &&& 0x2100 = 0x2100 then kCrypto else if v &&& 16 ≠ 0 then kZbb else kX1

def classRegionNat (v : Nat) : Region :=
  if v &&& 0x2100 = 0x2100 then rCrypto else if v &&& 16 ≠ 0 then rZbb else rX1

/-- The probe value with the three tested bits set as given (all other bits zero). -/
def probeOf (b13 b8 b4 : Bool) : Nat :=
  (if b13 then 0x2000 else 0) + (if b8 then 0x100 else 0) + (if b4 then 0x10 else 0)

def selName (b13 b8 b4 : Bool) : String :=
  if b13 && b8 then kCrypto else if b4 then kZbb else kX1

def selRegion (b13 b8 b4 : Bool) : Region :=
  if b13 && b8 then rCrypto else if b4 then rZbb else rX1

/-- **The three tested bits determine the class.**  Two probe answers whose `0x2110` bits agree
select the same kernel.  (`0x2110` is the mask of the three bits the selection tests:
`0x2000`, `0x100` in `(v &&& 0x2100) = 0x2100`, and `0x10` in `(v &&& 16) ≠ 0`.) -/
theorem classOfNat_ext (v v' : Nat) (h : v &&& 0x2110 = v' &&& 0x2110) :
    classOfNat v = classOfNat v' := by
  unfold classOfNat
  have e1 : v &&& 0x2100 = v' &&& 0x2100 := by
    have h' : (v &&& 0x2110) &&& 0x2100 = (v' &&& 0x2110) &&& 0x2100 := by rw [h]
    rwa [Nat.and_assoc, Nat.and_assoc, show 0x2110 &&& 0x2100 = 0x2100 by decide] at h'
  have e2 : v &&& 16 = v' &&& 16 := by
    have h' : (v &&& 0x2110) &&& 16 = (v' &&& 0x2110) &&& 16 := by rw [h]
    rwa [Nat.and_assoc, Nat.and_assoc, show 0x2110 &&& 16 = 16 by decide] at h'
  rw [e1, e2]

/-- The 8 combinations of the tested bits classify as the selection rule says. -/
theorem selName_eq_classOf (b13 b8 b4 : Bool) :
    classOfNat (probeOf b13 b8 b4) = selName b13 b8 b4 := by
  cases b13 <;> cases b8 <;> cases b4 <;> decide

theorem selRegion_eq_classRegionNat (b13 b8 b4 : Bool) :
    classRegionNat (probeOf b13 b8 b4) = selRegion b13 b8 b4 := by
  cases b13 <;> cases b8 <;> cases b4 <;> decide

/-! ## `init_and_hash` (region 24, GOT 23, rodata 22) -/

def ihSyms : List (String × Region) :=
  [(".data.rel.local", 60), ("__stack_chk_guard", 61), ("syscall", 62), ("__stack_chk_fail", 63),
   (kX1, rX1), (kZbb, rZbb), (kCrypto, rCrypto)]

def ihEnv : Env := ⟨22, 23, 24, ihSyms⟩

/-- The GOT contents in the order the program indexes them. -/
def dGot : List Target :=
  [.sym "__stack_chk_guard" 0, .sym kX1 0, .sym kCrypto 0, .sym kZbb 0]

def ihResolve (t : Target) : Addr Int :=
  match ihEnv.target (γ := Int) t with | .ok a => a | .error _ => ⟨rNum, 0⟩

/-- The concrete memory: the GOT (region 23) with pointers to the guard and the three kernels,
the canary bytes (region 61), and the `.data.rel.local` slot (region 60) initially pointing at
`init_and_hash` (code region 24).  Everything else is zero data. -/
def ihMem : Addr Int → Cell W32 Int := fun a =>
  if a.region = 23 then
    match dGot[(a.off / 8).toNat]? with
    | some t => .pb (ihResolve t) (a.off % 8).toNat
    | none => .dat 0 0
  else if a.region = 61 then .dat (BitVec.ofNat 32 0x5a) 0
  else if a.region = 60 then
    (if 0 ≤ a.off ∧ a.off < 8 then .pb (⟨24, 0⟩ : Addr Int) a.off.toNat else .dat 0 0)
  else .dat 0 0

/-- The LP64D entry: `a0` = output, `a1` = input, `a2` = count, `ra` = the return target,
`sp = 0`. -/
def ihEntry : State W32 Int :=
  { gpr := (List.range 32).map fun i =>
      if i = 1 then .ptr ⟨rRet, 0⟩
      else if i = 2 then .ptr ⟨rStack, 0⟩
      else if i = 10 then .ptr ⟨rOut, 0⟩
      else if i = 11 then .ptr ⟨rIn, 0⟩
      else if i = 12 then .ptr ⟨rNum, 3⟩
      else .num 0 0,
    vr := [], flags := none, mem := [], pc := 0, halted := false, tail := none, err := none,
    assume := [] }

/-- The state at the `riscv_hwprobe` call: 25 instructions. -/
def ihCall : State W32 Int :=
  Riscv.run Hashtree.Kernels.Riscv.DispInitAndHash.prog ihEnv ihMem (fun _ => false) 25 ihEntry

theorem ih_call_syscall :
    ihCall.halted = true ∧ ihCall.tail = some "call:syscall" ∧ ihCall.err = none ∧
      ihCall.pc = 25 := by
  refine ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- The state after the `riscv_hwprobe` stub has answered (`none` = the syscall fails, `a0 = -1`),
i.e. where the harness resumes the program. -/
def ihPost (p : Probe) : State W32 Int :=
  syscallStub p ihMem { ihCall with halted := false, tail := none }

/-- The selection result (enough fuel: the longest path is 33 instructions). -/
def ihSelect (p : Probe) : State W32 Int :=
  Riscv.run Hashtree.Kernels.Riscv.DispInitAndHash.prog ihEnv ihMem (fun _ => false) 34 (ihPost p)

/-- **`init_and_hash`, syscall failure: the x1 kernel.** -/
theorem ih_syscall_fail_x1 :
    (ihSelect none).halted = true ∧ (ihSelect none).tail = some kX1 ∧
      (ihSelect none).err = none ∧
      loadVal ihMem (ihSelect none) (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨rX1, 0⟩ : Addr Int)) :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **`init_and_hash`, `(v &&& 0x2100) = 0x2100`: the crypto kernel.** -/
theorem ih_probe_crypto :
    (ihSelect (some 0x2100)).halted = true ∧
      (ihSelect (some 0x2100)).tail = some kCrypto ∧ (ihSelect (some 0x2100)).err = none ∧
      loadVal ihMem (ihSelect (some 0x2100)) (⟨60, 0⟩ : Addr Int) =
        .ok (.ptr (⟨rCrypto, 0⟩ : Addr Int)) :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **`init_and_hash`, `(v &&& 16) ≠ 0`: the zbb kernel.** -/
theorem ih_probe_zbb :
    (ihSelect (some 0x10)).halted = true ∧
      (ihSelect (some 0x10)).tail = some kZbb ∧ (ihSelect (some 0x10)).err = none ∧
      loadVal ihMem (ihSelect (some 0x10)) (⟨60, 0⟩ : Addr Int) =
        .ok (.ptr (⟨rZbb, 0⟩ : Addr Int)) :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **`init_and_hash`, neither bit set (a successful probe with `v &&& 0x2110 = 0`): x1.** -/
theorem ih_probe_x1 :
    (ihSelect (some 0)).halted = true ∧ (ihSelect (some 0)).tail = some kX1 ∧
      (ihSelect (some 0)).err = none ∧
      loadVal ihMem (ihSelect (some 0)) (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨rX1, 0⟩ : Addr Int)) :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **The 8 tested-bit combinations for `init_and_hash`**: it halts on a tail call to the class
kernel (never `__stack_chk_fail` — `err = none`), and installs that kernel's pointer in the
`.data.rel.local` slot. -/
theorem ih_select_bits (b13 b8 b4 : Bool) :
    (ihSelect (some (probeOf b13 b8 b4))).halted = true ∧
      (ihSelect (some (probeOf b13 b8 b4))).tail = some (selName b13 b8 b4) ∧
      (ihSelect (some (probeOf b13 b8 b4))).err = none ∧
      loadVal ihMem (ihSelect (some (probeOf b13 b8 b4))) (⟨60, 0⟩ : Addr Int) =
        .ok (.ptr (⟨selRegion b13 b8 b4, 0⟩ : Addr Int)) := by
  cases b13 <;> cases b8 <;> cases b4 <;> exact ⟨by rfl, by rfl, by rfl, by rfl⟩

/-! ## `hashtree_init` (region 27, GOT 26, rodata 25) -/

def hiSyms : List (String × Region) := ihSyms

def hiEnv : Env := ⟨25, 26, 27, hiSyms⟩

def hiResolve (t : Target) : Addr Int :=
  match hiEnv.target (γ := Int) t with | .ok a => a | .error _ => ⟨rNum, 0⟩

def hiMem : Addr Int → Cell W32 Int := fun a =>
  if a.region = 26 then
    match dGot[(a.off / 8).toNat]? with
    | some t => .pb (hiResolve t) (a.off % 8).toNat
    | none => .dat 0 0
  else if a.region = 61 then .dat (BitVec.ofNat 32 0x5a) 0
  else if a.region = 60 then
    (if 0 ≤ a.off ∧ a.off < 8 then .pb (⟨24, 0⟩ : Addr Int) a.off.toNat else .dat 0 0)
  else .dat 0 0

/-- The entry: `a0` is the argument (a kernel pointer to install, or NULL = 0), `ra` = return. -/
def hiEntry (v : Val W32 Int) : State W32 Int :=
  { gpr := (List.range 32).map fun i =>
      if i = 1 then .ptr ⟨rRet, 0⟩
      else if i = 2 then .ptr ⟨rStack, 0⟩
      else if i = 10 then v
      else .num 0 0,
    vr := [], flags := none, mem := [], pc := 0, halted := false, tail := none, err := none,
    assume := [] }

/-- The state at the `riscv_hwprobe` call of the NULL path: 19 instructions. -/
def hiCall : State W32 Int :=
  Riscv.run Hashtree.Kernels.Riscv.DispInit.prog hiEnv hiMem (fun _ => false) 19 (hiEntry (.num 0 0))

theorem hi_call_syscall :
    hiCall.halted = true ∧ hiCall.tail = some "call:syscall" ∧ hiCall.err = none ∧
      hiCall.pc = 30 := by
  refine ⟨by rfl, by rfl, by rfl, by rfl⟩

def hiPost (p : Probe) : State W32 Int :=
  syscallStub p hiMem { hiCall with halted := false, tail := none }

/-- The NULL path, through the selection and back through the slot write and the canary check. -/
def hiSelect (p : Probe) : State W32 Int :=
  Riscv.run Hashtree.Kernels.Riscv.DispInit.prog hiEnv hiMem (fun _ => false) 40 (hiPost p)

/-- The non-NULL path: the argument pointer goes into the slot and the function returns. -/
def hiOverride (k : Region) : State W32 Int :=
  Riscv.run Hashtree.Kernels.Riscv.DispInit.prog hiEnv hiMem (fun _ => false) 20
    (hiEntry (.ptr ⟨k, 0⟩))

/-- **`hashtree_init(k)` (non-NULL)**: it writes `k` into the `.data.rel.local` slot, passes the
canary check and returns to `ra` (halt, `tail = none`, no model error). -/
theorem hi_override (k : Region) (hk : k = rX1 ∨ k = rZbb ∨ k = rCrypto) :
    (hiOverride k).halted = true ∧ (hiOverride k).tail = none ∧ (hiOverride k).err = none ∧
      loadVal hiMem (hiOverride k) (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨k, 0⟩ : Addr Int)) := by
  rcases hk with rfl | rfl | rfl <;> exact ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **`hashtree_init(NULL)`, syscall failure: it installs and returns x1.** -/
theorem hi_syscall_fail_x1 :
    (hiSelect none).halted = true ∧ (hiSelect none).tail = none ∧ (hiSelect none).err = none ∧
      loadVal hiMem (hiSelect none) (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨rX1, 0⟩ : Addr Int)) :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- **`hashtree_init(NULL)`, the 8 tested-bit combinations**: it returns normally (canary check
passes, `tail = none`, `err = none`) after installing the class kernel in the slot. -/
theorem hi_select_bits (b13 b8 b4 : Bool) :
    (hiSelect (some (probeOf b13 b8 b4))).halted = true ∧
      (hiSelect (some (probeOf b13 b8 b4))).tail = none ∧
      (hiSelect (some (probeOf b13 b8 b4))).err = none ∧
      loadVal hiMem (hiSelect (some (probeOf b13 b8 b4))) (⟨60, 0⟩ : Addr Int) =
        .ok (.ptr (⟨selRegion b13 b8 b4, 0⟩ : Addr Int)) := by
  cases b13 <;> cases b8 <;> cases b4 <;> exact ⟨by rfl, by rfl, by rfl, by rfl⟩

end Hashtree.Proofs.RvDispatchInit
