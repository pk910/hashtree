import Hashtree.Asm.Print
import Hashtree.Asm.ArmSlice
import Hashtree.Asm.Chain
import Hashtree.Asm.ArmSym
import Hashtree.Asm.ArmRun
import Hashtree.Asm.Scan
import Hashtree.Kernels.Arm.ShaX1
import Hashtree.Kernels.Arm.NeonX1
import Hashtree.Kernels.Arm.NeonX4

/-!
Shared definitions for the AArch64 proof generators (`ArmProof`, `ArmLoop1`): kernel
configurations, label/quote printing, the per-leaf `derive` rewrite search, and the concrete
state sizing and perturbation helpers used to pick cut points.

No theorem is stated here; the generators instantiate these definitions at concrete states.
-/

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmSym Hashtree.Asm.Scan

structure Cfg where
  /-- symbol name -/
  sym : String
  /-- kernel module / namespace suffix (`Hashtree.Kernels.Arm.<mod>`) -/
  mod : String
  /-- generated namespace suffix (`Hashtree.Gen.<gen>`) -/
  gen : String
  prog : Array Instr
  ro : Region
  rodata : List Nat
  /-- cut after a step from this instruction to the next -/
  cutAt : Option Instr → Option Instr → Bool
  /-- choose cuts adaptively (longest clean slice of at most `maxLen` steps) -/
  adaptive : Bool := false
  maxLen : Nat := 40
  /-- bound on the total tree size of a slice's end state (adaptive cuts) -/
  maxSize : Nat := 40000
  /-- the loop is headed by a comparison of the count register `x2` with `4` (multi-lane kernel) -/
  countHead : Bool := false

def isSha : Option Instr → Bool
  | some (.sha256h _ _ _) | some (.sha256h2 _ _ _) => true
  | _ => false

def progsLinux : List Hashtree.Asm.ArmRun.Prog := [
  ⟨"hashtree_sha256_sha_x1", Hashtree.Kernels.Arm.ShaX1.prog, 4, Hashtree.Kernels.Arm.ShaX1.rodata.toArray⟩,
  ⟨"hashtree_sha256_neon_x4", Hashtree.Kernels.Arm.NeonX4.prog, 6, Hashtree.Kernels.Arm.NeonX4.rodata.toArray⟩,
  ⟨"hashtree_sha256_neon_x1", Hashtree.Kernels.Arm.NeonX1.prog, 7, Hashtree.Kernels.Arm.NeonX1.rodata.toArray⟩]

def cfgs : List (String × Cfg) := [
  ("sha_x1", ⟨"hashtree_sha256_sha_x1", "ShaX1", "ArmShaX1P", Hashtree.Kernels.Arm.ShaX1.prog, 4,
    Hashtree.Kernels.Arm.ShaX1.rodata, fun a b => isSha a || isSha b, false, 40, 40000, false⟩),
  ("neon_x1", ⟨"hashtree_sha256_neon_x1", "NeonX1", "ArmNeonX1P", Hashtree.Kernels.Arm.NeonX1.prog, 7,
    Hashtree.Kernels.Arm.NeonX1.rodata, fun _ _ => false, true, 40, 40000, false⟩),
  ("neon_x4", ⟨"hashtree_sha256_neon_x4", "NeonX4", "ArmNeonX4P", Hashtree.Kernels.Arm.NeonX4.prog, 6,
    Hashtree.Kernels.Arm.NeonX4.rodata, fun _ _ => false, true, 40, 40000, true⟩)]

def randInput (seed n : Nat) : Array Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut a : Array Nat := #[]
  for _ in [0:n] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    a := a.push ((x >>> 33) % 256)
  return a

def qText : Q → String
  | .A n r t => s!"(.A {n} {r} ({t}))" | .E n r t => s!"(.E {n} {r} ({t}))"
  | .W n r t => s!"(.W {n} {r} {t})" | .KW n r t => s!"(.KW {n} {r} {t})" | .R n t => s!"(.R {n} {t})"
  | .H n r i => s!"(.H {n} {r} {i})" | .M1 n r t => s!"(.M1 {n} {r} {t})" | .M2 n r t => s!"(.M2 {n} {r} {t})"
  | .HB n i => s!"(.HB {n} {i})"

/-- Var-id labels of a concrete state (only ids whose symbolic lane is not a constant). -/
def cutLabels (t1 t2 : Std.HashMap W32 (List Q)) (K : State E Lin) (s1 s2 : Hashtree.Asm.ArmRun.CS) :
    List (Nat × List Q) := Id.run do
  let common (x y : W32) : List Q := (t1.getD x []).filter ((t2.getD y []).contains ·)
  let isVar (e : E) : Bool := match e with | .var _ => true | _ => false
  let mut out : List (Nat × List Q) := []
  for g in [0:32] do
    match s1.getG g, s2.getG g, K.getG g with
    | .num lo1 hi1, .num lo2 hi2, .num a b =>
      if isVar a then let c := common lo1 lo2; if !c.isEmpty then out := (gId g 0, c) :: out
      if isVar b then let c := common hi1 hi2; if !c.isEmpty then out := (gId g 1, c) :: out
    | _, _, _ => pure ()
  for i in [0:32] do
    for l in [0:16] do
      if isVar ((K.getV i).getD l (.const 0)) then
        let c := common ((s1.getV i).getD l 0) ((s2.getV i).getD l 0)
        if !c.isEmpty then out := (vId i l, c) :: out
  let mut j := 0
  for ((_, c1), (_, c2)) in s1.mem.zip s2.mem do
    match c1, c2, (K.mem[j]? : Option (Addr Lin × Cell E Lin)) with
    | Cell.dat x _, Cell.dat y _, some (_, Cell.dat e _) =>
      if isVar e then let c := common x y; if !c.isEmpty then out := (mId j, c) :: out
    | _, _, _ => pure ()
    j := j + 1
  return out

/-- One equation step: its proof (instantiated at `qv inp`) and its statement over a valuation `V`. -/
structure Eqn where
  proof : String
  stmt : String
  /-- the value, for a closed quantity (`V q = value`) -/
  val : Option Nat := none
  deriving BEq

def vq (q : Q) : String := s!"V {qText q}"

/-- Equations that rewrite `q` down to atoms or closed quantities, or `none`.  Candidate equations
are tried in order; input bytes (`R`) only when `bytes`. -/
partial def derive (atoms : List Q) (bytes : Bool) (q : Q) (fuel : Nat) : Option (List Eqn) :=
  if atoms.contains q then some [] else if fuel = 0 then none else
  let sub (proof rhs : String) (leaves : List Q) : Option (List Eqn) := do
    let rest ← leaves.mapM (fun l => derive atoms bytes l (fuel - 1))
    pure (⟨proof, s!"{vq q} = {rhs}", none⟩ :: rest.flatten)
  -- closed quantities; `abs`: its value becomes a parameter of the core lemma (padding-block K+W / W,
  -- which reach the trees as loaded constants); H0 words stay literal (constant folding mixes them)
  let closed (proof : String) (v : Nat) (abs : Bool := true) : Option (List Eqn) :=
    some [⟨proof, s!"{vq q} = {v}#32", if abs then some v else none⟩]
  let first (cands : List (Unit → Option (List Eqn))) : Option (List Eqn) :=
    cands.foldl (fun acc f => match acc with | some r => some r | none => f ()) none
  match q with
  | .A n r t =>
    if t ≥ 1 then
      let u := t - 1
      let t1 := s!"({vq (.E n r (u - 3))} + Sigma1 ({vq (.E n r u)}) + Ch ({vq (.E n r u)}) ({vq (.E n r (u - 1))}) ({vq (.E n r (u - 2))}) + {vq (.KW n r u.toNat)})"
      let t2 := s!"(Sigma0 ({vq (.A n r u)}) + Maj ({vq (.A n r u)}) ({vq (.A n r (u - 1))}) ({vq (.A n r (u - 2))}))"
      sub s!"(qA_succI inp {n} {r} ({u}) (by decide))" s!"{t1} + {t2}"
        [.E n r (u - 3), .E n r u, .E n r (u - 1), .E n r (u - 2), .KW n r u.toNat, .A n r u, .A n r (u - 1), .A n r (u - 2)]
    else sub s!"(qA_initI inp {n} {r} {(-t).toNat} ({t}) (by decide) (by decide))" (vq (.H n r (-t).toNat)) [.H n r (-t).toNat]
  | .E n r t =>
    if t ≥ 1 then
      let u := t - 1
      let t1 := s!"({vq (.E n r (u - 3))} + Sigma1 ({vq (.E n r u)}) + Ch ({vq (.E n r u)}) ({vq (.E n r (u - 1))}) ({vq (.E n r (u - 2))}) + {vq (.KW n r u.toNat)})"
      sub s!"(qE_succI inp {n} {r} ({u}) (by decide))" s!"{vq (.A n r (u - 3))} + {t1}"
        [.A n r (u - 3), .E n r (u - 3), .E n r u, .E n r (u - 1), .E n r (u - 2), .KW n r u.toNat]
    else sub s!"(qE_initI inp {n} {r} {(-t).toNat} ({t}) (by decide) (by decide))" (vq (.H n r ((-t).toNat + 4))) [.H n r ((-t).toNat + 4)]
  | .W n r t =>
    if r = 1 then closed s!"((qW1T inp {n} {t} (by decide)).trans rfl)" (Hashtree.Spec.W Hashtree.Spec.padBlock t).toNat
    else if t < 16 then (if bytes then sub s!"(qW_R inp {n} {t} (by decide))" s!"bswap ({vq (.R n t)})" [.R n t] else none)
    else first [
      fun _ => sub s!"(qW_recM2 inp {n} {r} {t} (by decide) (by decide))" s!"sigma1 ({vq (.W n r (t - 2))}) + {vq (.M2 n r (t - 16))}" [.W n r (t - 2), .M2 n r (t - 16)],
      fun _ => sub s!"(qW_recM inp {n} {r} {t} (by decide) (by decide))" s!"sigma1 ({vq (.W n r (t - 2))}) + {vq (.W n r (t - 7))} + {vq (.M1 n r (t - 16))}" [.W n r (t - 2), .W n r (t - 7), .M1 n r (t - 16)],
      fun _ => sub s!"(qW_rec inp {n} {r} {t} (by decide) (by decide))" s!"sigma1 ({vq (.W n r (t - 2))}) + {vq (.W n r (t - 7))} + sigma0 ({vq (.W n r (t - 15))}) + {vq (.W n r (t - 16))}" [.W n r (t - 2), .W n r (t - 7), .W n r (t - 15), .W n r (t - 16)]]
  | .KW n r t =>
    if r = 1 then closed s!"((qKW1T inp {n} {t} (by decide)).trans rfl)" (Hashtree.Spec.K t + Hashtree.Spec.W Hashtree.Spec.padBlock t).toNat
    else
      let k := (Hashtree.Spec.K t).toNat
      sub s!"((qKW inp {n} {r} {t}).trans (by rw [show Spec.K {t} = {k}#32 from by decide]))" s!"{k}#32 + {vq (.W n r t)}" [.W n r t]
  | .H n r i =>
    if r = 0 then closed s!"((qH0 inp {n} {i}).trans (by decide : fld H0 {i} = {(stWord Hashtree.Spec.H0 i).toNat}#32))" (stWord Hashtree.Spec.H0 i).toNat false
    else if i < 4 && atoms.contains (.A n r (-(i : Int))) then
      sub s!"(qH_ofA inp {n} {r} {i} ({-(i : Int)}) (by decide) (by decide))" (vq (.A n r (-(i : Int)))) [.A n r (-(i : Int))]
    else if i ≥ 4 && i < 8 && atoms.contains (.E n r (-((i - 4 : Nat) : Int))) then
      sub s!"(qH_ofE inp {n} {r} {i - 4} ({-((i - 4 : Nat) : Int)}) (by decide) (by decide))" (vq (.E n r (-((i - 4 : Nat) : Int)))) [.E n r (-((i - 4 : Nat) : Int))]
    else if i < 4 then
      let t : Int := 64 - (i : Int)
      sub s!"(qH_succA inp {n} {r - 1} {i} ({t}) (by decide) (by decide) (by decide))" s!"{vq (.H n (r - 1) i)} + {vq (.A n (r - 1) t)}" [.H n (r - 1) i, .A n (r - 1) t]
    else
      let t : Int := 64 - ((i - 4 : Nat) : Int)
      sub s!"(qH_succE inp {n} {r - 1} {i} ({t}) (by decide) (by decide) (by decide))" s!"{vq (.H n (r - 1) i)} + {vq (.E n (r - 1) t)}" [.H n (r - 1) i, .E n (r - 1) t]
  | .M1 n r t => sub s!"(qM1 inp {n} {r} {t})" s!"{vq (.W n r t)} + sigma0 ({vq (.W n r (t + 1))})" [.W n r t, .W n r (t + 1)]
  | .M2 n r t => sub s!"(qM2 inp {n} {r} {t})" s!"{vq (.M1 n r t)} + {vq (.W n r (t + 9))}" [.M1 n r t, .W n r (t + 9)]
  | .HB n i => sub s!"(qHB inp {n} {i})" s!"bswap ({vq (.H n 2 i)})" [.H n 2 i]
  | .R n t =>
    if bytes then
      let o := 64 * n + 4 * t
      some [⟨s!"(qR inp {n} {t})", s!"{vq q} = ((((0 : Word) ||| (inp {o}).zeroExtend 32 <<< 0) ||| (inp {o + 1}).zeroExtend 32 <<< 8) ||| (inp {o + 2}).zeroExtend 32 <<< 16) ||| (inp {o + 3}).zeroExtend 32 <<< 24", none⟩]
    else none

/-- Variables (numbered) and memory keys of a tree. -/
partial def Hashtree.Asm.E.keys : E → List Key
  | .var k => [k]
  | .const _ => []
  | .add a b | .xor a b | .and a b | .or a b => a.keys ++ b.keys
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.keys
  | .tern _ a b c => a.keys ++ b.keys ++ c.keys


abbrev CS := Hashtree.Asm.ArmRun.CS

/-- Tree size (as printed, without sharing), counting stops at `cap`. -/
partial def esz (cap : Nat) (acc : Nat) : E → Nat
  | e => if acc ≥ cap then acc else match e with
    | .var _ | .const _ => acc + 1
    | .add a b | .xor a b | .and a b | .or a b => esz cap (esz cap (acc + 1) a) b
    | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => esz cap (acc + 1) a
    | .tern _ a b c => esz cap (esz cap (esz cap (acc + 1) a) b) c

/-- Total tree size of the data lanes of a symbolic state (capped). -/
def stateSize (cap : Nat) (R : State E Lin) : Nat := Id.run do
  let mut acc := 0
  for v in R.gpr do
    match v with
    | .num lo hi => acc := esz cap (esz cap acc lo) hi
    | _ => pure ()
  for v in R.vr do
    for x in v do acc := esz cap acc x
  for (_, c) in R.mem do
    match c with
    | .dat x _ => acc := esz cap acc x
    | _ => pure ()
  return acc

/-- Output bytes after running a concrete state to the end (`none` on error / no halt). -/
def finishOut (prog : Array Instr) (ro : Region) (m : Addr Int → Cell W32 Int) (count : Nat) (s : CS) :
    Option (List Nat) :=
  let s' := run prog ro m (fun _ => false) 2000000 s
  if s'.err.isSome || !s'.halted then none else Hashtree.Asm.ArmRun.outBytes m s' (32 * count)

/-- Change every data location of `s` whose cut lane (in `K`) is a variable and not kept. -/
def perturb (keep : Nat → Bool) (K : State E Lin) (s : CS) (salt : Nat) : CS :=
  let isVar (e : E) : Bool := match e with | .var _ => true | _ => false
  let r (id : Nat) : W32 := BitVec.ofNat 32 (((id + salt) * 2654435761 + 40503) % 2 ^ 32) ||| 0x01010101
  let gpr := s.gpr.mapIdx fun g v => match v, K.getG g with
    | .num lo hi, .num a b =>
      Val.num (if isVar a && !keep (gId g 0) then lo ^^^ r (gId g 0) else lo)
        (if isVar b && !keep (gId g 1) then hi ^^^ r (gId g 1) else hi)
    | v, _ => v
  let vr := s.vr.mapIdx fun i v => v.mapIdx fun l x =>
    if isVar ((K.getV i).getD l (.const 0)) && !keep (vId i l) then x ^^^ r (vId i l) else x
  let mem := s.mem.mapIdx fun j (p : Addr Int × Cell W32 Int) => match p.2, K.mem[j]? with
    | .dat x k, some (_, .dat e _) => if isVar e && !keep (mId j) then (p.1, .dat (x ^^^ r (mId j)) k) else p
    | _, _ => p
  { s with gpr := gpr, vr := vr, mem := mem }
