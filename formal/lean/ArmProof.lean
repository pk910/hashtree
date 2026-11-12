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
`armproof <kernel> <count> <outdir> <first> <last>`: generate the proof files `P{c}.lean` and
`Final.lean` for one AArch64 kernel (Linux ELF object) called on `count` blocks: per slice the next
cut, the tracked trees, the kernel-checked slice and one lemma per labelled lane of the next cut;
`Final.lean` chains the slices into `out_final` (every output byte is the SHA-256 byte of its block).
Kernels: `sha_x1`, `neon_x1`, `neon_x4`.
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

def isSha : Option Instr → Bool
  | some (.sha256h _ _ _) | some (.sha256h2 _ _ _) => true
  | _ => false

def progsLinux : List Hashtree.Asm.ArmRun.Prog := [
  ⟨"hashtree_sha256_sha_x1", Hashtree.Kernels.Arm.ShaX1.prog, 4, Hashtree.Kernels.Arm.ShaX1.rodata.toArray⟩,
  ⟨"hashtree_sha256_neon_x4", Hashtree.Kernels.Arm.NeonX4.prog, 6, Hashtree.Kernels.Arm.NeonX4.rodata.toArray⟩,
  ⟨"hashtree_sha256_neon_x1", Hashtree.Kernels.Arm.NeonX1.prog, 7, Hashtree.Kernels.Arm.NeonX1.rodata.toArray⟩]

def cfgs : List (String × Cfg) := [
  ("sha_x1", ⟨"hashtree_sha256_sha_x1", "ShaX1", "ArmShaX1P", Hashtree.Kernels.Arm.ShaX1.prog, 4,
    Hashtree.Kernels.Arm.ShaX1.rodata, fun a b => isSha a || isSha b, false, 40, 40000⟩),
  ("neon_x1", ⟨"hashtree_sha256_neon_x1", "NeonX1", "ArmNeonX1P", Hashtree.Kernels.Arm.NeonX1.prog, 7,
    Hashtree.Kernels.Arm.NeonX1.rodata, fun _ _ => false, true, 40, 40000⟩),
  ("neon_x4", ⟨"hashtree_sha256_neon_x4", "NeonX4", "ArmNeonX4P", Hashtree.Kernels.Arm.NeonX4.prog, 6,
    Hashtree.Kernels.Arm.NeonX4.rodata, fun _ _ => false, true, 40, 40000⟩)]

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

/-- Adaptive cuts: from each cut, the longest slice (≤ `maxLen` steps) ending in a clean state —
every variable lane without a label is dead (changing them all leaves the output unchanged). -/
def adaptiveCuts (cfg : Cfg) (count : Nat) (t1 t2 : Std.HashMap W32 (List Q))
    (m0 : Addr Lin → Cell E Lin) (m1 m2 : Addr Int → Cell W32 Int) : IO (List Nat) := do
  let prog := cfg.prog
  let ro := cfg.ro
  let ref := finishOut prog ro m1 count (Hashtree.Asm.ArmRun.entry count 0)
  let mut K := entryS 0
  let mut c1 := Hashtree.Asm.ArmRun.entry count 0
  let mut c2 := Hashtree.Asm.ArmRun.entry count 0
  let mut cuts : List Nat := []
  let mut pos := 0
  let mut unclean := 0
  while !c1.halted && pos < 1000000 do
    -- candidate states after 1..maxLen steps (following the concrete branches)
    let mut cands : Array (State E Lin × CS × CS) := #[]
    let mut R := K
    let mut a := c1
    let mut b := c2
    for _ in [0:cfg.maxLen] do
      if a.halted then break
      let pc0 := a.pc
      let a' := run prog ro m1 (fun _ => false) 1 a
      let tk := match prog[pc0]? with | some (.bcc _ _) => a'.pc != pc0 + 1 || a'.halted | _ => false
      R := run prog ro m0 (fun pc => pc == pc0 && tk) 1 R
      a := a'
      b := run prog ro m2 (fun _ => false) 1 b
      cands := cands.push (R, a, b)
    let mut pick := cands.size
    let mut found := false
    let mut j := cands.size
    while j > 0 && !found do
      let (Rj, aj, bj) := cands[j - 1]!
      if aj.halted then found := true; pick := j
      else if stateSize (cfg.maxSize + 1) Rj > cfg.maxSize then pure ()
      else
        let Kj := abstract Rj
        let labs := cutLabels t1 t2 Kj aj bj
        let keep (id : Nat) : Bool := labs.any (·.1 == id)
        if finishOut prog ro m1 count (perturb keep Kj aj 7) == ref &&
            finishOut prog ro m1 count (perturb keep Kj aj 99) == ref then
          found := true; pick := j
      j := j - 1
    -- none clean within the size bound: the shortest clean slice
    if !found then
      let mut j2 := 1
      while j2 ≤ cands.size && !found do
        let (Rj, aj, bj) := cands[j2 - 1]!
        if aj.halted then found := true; pick := j2
        else
          let Kj := abstract Rj
          let labs := cutLabels t1 t2 Kj aj bj
          let keep (id : Nat) : Bool := labs.any (·.1 == id)
          if finishOut prog ro m1 count (perturb keep Kj aj 7) == ref &&
              finishOut prog ro m1 count (perturb keep Kj aj 99) == ref then
            found := true; pick := j2
        j2 := j2 + 1
    if !found then unclean := unclean + 1
    let (Rp, ap, bp) := cands[pick - 1]!
    K := abstract Rp
    c1 := ap
    c2 := bp
    pos := pos + pick
    cuts := cuts ++ [pos]
    if cuts.length % 25 == 0 then
      IO.println s!"  cut {cuts.length} at step {pos} (slice {pick}, size {stateSize 100000000 (cands[pick - 1]!).1}, unclean so far {unclean})"
      (← IO.getStdout).flush
  IO.println s!"adaptive cuts: {cuts.length} slices, {unclean} without a clean end"
  return cuts

def main (args : List String) : IO Unit := do
  let kname := args.headD "sha_x1"
  let some cfg := cfgs.lookup kname | throw (IO.userError s!"unknown kernel {kname}")
  let count := (args.getD 1 "2").toNat!
  let dir := args.getD 2 "Gen"
  let first := (args.getD 3 "0").toNat!
  let last := (args.getD 4 "1000000").toNat!
  let extraCuts : List Nat := ((args.getD 5 "").splitOn ",").filterMap String.toNat?
  let cfg := match (args.getD 6 "").toNat? with | some m => { cfg with maxLen := m } | none => cfg
  let cfg := match (args.getD 7 "").toNat? with | some m => { cfg with maxSize := m } | none => cfg
  let prog := cfg.prog
  let ro := cfg.ro
  let nb := 64 * count
  let m0 := mem0s ro cfg.rodata
  let roT := s!"{ro}"
  let memT := s!"(mem0s {ro} rodata)"
  let ns := s!"Hashtree.Gen.{cfg.gen}"
  let openT := s!"open Hashtree.Asm Hashtree.Asm.ArmSym Hashtree.Kernels.Arm.{cfg.mod} Hashtree.Asm.SpecQ Hashtree.Spec\n"
  let opts := "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"
  -- concrete runs on two inputs, labels at each cut
  let i1 := randInput 11 nb
  let i2 := randInput 22 nb
  let t1 := table i1 count
  let t2 := table i2 count
  let m1 := Hashtree.Asm.ArmRun.mem0 progsLinux i1
  let m2 := Hashtree.Asm.ArmRun.mem0 progsLinux i2
  -- cut steps from a concrete run
  let mc := Hashtree.Asm.ArmRun.mem0 progsLinux (Array.replicate nb 0)
  let mut cuts : List Nat := []
  let mut s := Hashtree.Asm.ArmRun.entry count 0
  let mut k := 0
  let mut maxDepth : Int := 0
  while !s.halted && k < 1000000 do
    let cur := prog[s.pc]?
    s := run prog ro mc (fun _ => false) 1 s
    k := k + 1
    if cfg.cutAt cur prog[s.pc]? || s.halted || extraCuts.contains k then cuts := cuts ++ [k]
  IO.println s!"concrete: {k} steps, halted {s.halted}, tail {s.tail}, err {s.err}, cuts {cuts.length}"
  if cfg.adaptive then cuts ← adaptiveCuts cfg count t1 t2 m0 m1 m2
  let mut c1 := Hashtree.Asm.ArmRun.entry count 0
  let mut c2 := Hashtree.Asm.ArmRun.entry count 0
  let mut K := entryS 0
  let mut prev := 0
  let mut chosen : List (Nat × Q) := []
  let mut stepsList : List Nat := []
  let mut orcs : List (List Nat × String) := []
  let mut asms : List (List (Cond Lin × Bool)) := []
  let mut asmIdx : List Nat := []
  let mut c := 0
  for cut in cuts do
    let n := cut - prev
    -- the branches this slice takes on the concrete run (the symbolic run must follow them)
    let mut taken : List Nat := []
    let mut cs := c1
    for _ in [0:n] do
      let pc0 := cs.pc
      let isBr := match prog[pc0]? with | some (.bcc _ _) => true | _ => false
      cs := run prog ro m1 (fun _ => false) 1 cs
      if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
    let orc : Nat → Bool := fun pc => taken.contains pc
    let orcT := s!"(fun pc => decide (pc ∈ ({taken} : List Nat)))"
    orcs := orcs ++ [(taken, orcT)]
    let R := run prog ro m0 orc n K
    if R.err.isSome then
      IO.println s!"slice {c}: symbolic error {R.err} at pc {R.pc}"
      return
    let K' := abstract R
    let A := K'.assume
    match asms.findIdx? (fun x => decide (x = A)) with
    | some j => asmIdx := asmIdx ++ [j]
    | none => asms := asms ++ [A]; asmIdx := asmIdx ++ [asms.length - 1]
    -- deepest stack offset written so far
    for (a, _) in R.mem do
      if a.region = rStack then
        match a.off.asInt with
        | some o => if o < maxDepth then maxDepth := o
        | none => pure ()
    c1 := run prog ro m1 (fun _ => false) n c1
    c2 := run prog ro m2 (fun _ => false) n c2
    let labs' := cutLabels t1 t2 K' c1 c2
    let mut chosen' : List (Nat × Q) := []
    let mut lemmas := ""
    let mut trees : List (Nat × E) := []
    let mut calls : List String := []
    let mut carryL : List (Nat × Q) := []
    let mut carryT : List (Nat × E) := []
    let mut carryC : List Nat := []
    for (id, qs) in labs' do
      let carried : Option (Nat × Q) := match treeAt R id with
        | some (.var (.n v)) => match chosen.findIdx? (·.1 == v) with
          | some j => if qs.contains (chosen[j]!).2 then some (j, (chosen[j]!).2) else none
          | none => none
        | _ => none
      match carried with
      | some (j, q0) =>
        carryL := carryL ++ [(id, q0)]
        carryT := carryT ++ [(id, .var (.n (chosen[j]!).1))]
        carryC := carryC ++ [j]
      | none =>
        match treeAt R id with
        | none => pure ()
        | some t =>
          let keys := t.keys.eraseDups
          let hyps := keys.filterMap fun key => match key with
            | .n v => (chosen.findIdx? (·.1 == v)).map fun k => (v, k, (chosen[k]!).2)
            | .m _ _ => none
          let atoms := hyps.map (·.2.2)
          let mkeys := keys.filterMap fun key => match key with
            | .m 1 l => if l.c = [1] then some l.k else none
            | _ => none
          let bytes := !mkeys.isEmpty
          match qs.find? (fun q => (derive atoms bytes q 40).isSome) with
          | none => pure ()
          | some q =>
            let eqs := (derive atoms bytes q 40).getD []
            chosen' := chosen' ++ [(id, q)]
            trees := trees ++ [(id, t)]
            let eqs := eqs.eraseDups
            let cvals := (eqs.filterMap (·.val)).eraseDups
            let pName (v : Nat) : String := s!"k{(cvals.idxOf v)}"
            let tText := cvals.foldl (fun (acc : String) v => acc.replace s!"(.const {v})" s!"(.const {pName v})") t.toLean
            let stmtOf (e : Eqn) : String := match e.val with
              | some v => s!"{e.stmt.splitOn " = " |>.head!} = {pName v}"
              | none => e.stmt
            let kArgs := String.join (cvals.map fun v => s!" ({pName v} : W32)")
            let hypArgs := String.join (hyps.map fun (v, _, q1) => s!"\n    (_ : env (.n {v}) = {vq q1})")
            let mArgs := String.join (mkeys.map fun o => s!"\n    (_ : env (.m 1 (⟨{o}, [1]⟩ : Lin)) = (inp {o.toNat}).zeroExtend 32)")
            let eqArgs := String.join (eqs.map fun e => s!"\n    (_ : {stmtOf e})")
            lemmas := lemmas ++ s!"theorem core{c}_{id} (V : Q → Word) (inp : Nat → Byte) (env : Key → W32){kArgs}{hypArgs}{mArgs}{eqArgs} :\n" ++
              s!"    E.eval env {tText} = {vq q} := by\n" ++
              "  simp_all only [E.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]\n  all_goals bv_decide (config := { timeout := 600 })\n\n"
            let callArgs := String.join (cvals.map fun v => s!" {v}#32") ++
              String.join (hyps.map fun (_, k, _) => s!" (inv_get hI {k} (by decide))") ++
              String.join (mkeys.map fun o => s!" (hm {o.toNat} (by decide))") ++
              String.join (eqs.map fun e => s!" {e.proof}")
            calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{callArgs}"]
    if first ≤ c ∧ c ≤ last then
      let kName := if c = 0 then "(entryS 0)" else s!"K{c}"
      let cases := String.join ((List.range chosen'.length).map fun k =>
        s!"  | {k}, _ => exact (ArmSlice.slice_trees prog {roT} _ _ {n} {kName} K{c + 1} T{c} slice{c} env {k} (by decide)).trans ({calls[k]!})\n")
      let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : Inv L{c} inp env) (hm : HMem {nb} inp env) :\n" ++
        s!"    Inv L{c + 1} inp (envAbs env (Arm.run prog {roT} {memT} {orcT} {n} {kName})) := by\n" ++
        s!"  have hT := ArmSlice.slice_trees_mem prog {roT} _ _ {n} {kName} K{c + 1} T{c} slice{c} env\n" ++
        s!"  refine inv_append _ _ _ _ ?_ (inv_carry L{c} inp env _ hI T{c}c L{c + 1}c C{c} (fun t ht => hT t (List.mem_append_right _ ht)) (by decide +kernel))\n" ++
        s!"  apply inv_of_get\n  intro k hk\n  match k, hk with\n" ++ cases ++
        s!"  | _ + {chosen'.length}, hk => simp only [L{c + 1}n, List.length_cons, List.length_nil] at hk; omega\n\n"
      let imports := s!"import Hashtree.Asm.Chain\nimport Hashtree.Asm.Carry\nimport Hashtree.Asm.ArmSym\nimport Hashtree.Asm.ArmSlice\nimport Hashtree.Kernels.Arm.{cfg.mod}\n" ++
        (if c = 0 then "" else s!"import {ns}.P{c - 1}\n")
      let body := imports ++ "\n" ++ openT ++ opts ++ s!"namespace {ns}\n\n" ++
        (if c = 0 then "def L0 : List (Nat × Q) := []\n\n" else "") ++
        s!"def K{c + 1} : State E Lin := {K'.toLean}\n\n" ++
        s!"def L{c + 1}n : List (Nat × Q) := {listLean (fun (p : Nat × Q) => s!"({p.1}, {qText p.2})") chosen'}\n\n" ++
        s!"def L{c + 1}c : List (Nat × Q) := {listLean (fun (p : Nat × Q) => s!"({p.1}, {qText p.2})") carryL}\n\n" ++
        s!"def L{c + 1} : List (Nat × Q) := L{c + 1}n ++ L{c + 1}c\n\n" ++
        s!"def T{c}n : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") trees}\n\n" ++
        s!"def T{c}c : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") carryT}\n\n" ++
        s!"def T{c} : List (Nat × E) := T{c}n ++ T{c}c\n\n" ++
        s!"def C{c} : List Nat := {carryC}\n\n" ++
        s!"theorem slice{c} : ArmSlice.sliceCheck prog {roT} {memT} {orcT} {n} {kName} K{c + 1} T{c} = true := by\n  decide +kernel\n\n" ++
        lemmas ++ step ++ s!"end {ns}\n"
      IO.FS.writeFile s!"{dir}/P{c}.lean" body
      IO.println s!"slice {c}: {n} steps, {labs'.length} labelled, {chosen'.length + carryL.length} proved ({carryL.length} carried)"
    chosen := chosen' ++ carryL
    stepsList := stepsList ++ [n]
    K := K'
    prev := cut
    c := c + 1
  IO.println s!"steps per slice: {stepsList}"
  IO.println s!"max stack depth (bytes below entry SP) written: {-maxDepth}; final halted {K.halted} tail {K.tail}"
  -- Final.lean
  let C := stepsList.length
  let finalK := K
  let kn (j : Nat) : String := if j = 0 then "(entryS 0)" else s!"K{j}"
  let mut fin := s!"import {ns}.P{C - 1}\n\n" ++ openT ++ opts ++ s!"namespace {ns}\n\n" ++
    "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) (Arm.run prog {roT} {memT} {(orcs[cc]!).2} {stepsList[cc]!} {kn cc})\n"
  fin := fin ++ s!"\ntheorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem {nb} inp env0) :\n    Inv L{C} inp (E{C} env0) := by\n" ++
    "  have i0 : Inv L0 inp (E0 env0) := fun p hp => by cases hp\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have i{cc + 1} : Inv L{cc + 1} inp (E{cc + 1} env0) := step{cc} inp (E{cc} env0) i{cc} hm\n"
  fin := fin ++ s!"  exact i{C}\n\n"
  for j in [0:asms.length] do
    let A := asms[j]!
    let aText := listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") A
    fin := fin ++ s!"def A{j} : List (Cond Lin × Bool) := {aText}\n" ++
      s!"theorem asm{j} (σ : Nat → Int) (hσ : σ 2 = {count}) : ∀ p ∈ A{j}, (mapCond σ p.1).decideC = some p.2 := by\n" ++
      s!"  intro p hp\n  simp only [A{j}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
      (if A.isEmpty then "  exact absurd hp id\n\n" else
        s!"  rcases hp with {" | ".intercalate ((List.range A.length).map fun _ => "rfl")} <;>\n" ++
        "    simp [mapCond, Cond.decideC, Lin.eval, dotC, hσ, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;> omega\n\n")
  let sumText : List Nat → String := fun l => l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""
  fin := fin ++ "theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)\n" ++
    s!"    (h0 : Mem0Rel env0 σ {memT} mem0c) (hσ : σ 2 = {count}) :\n" ++
    s!"    Arm.run prog {roT} mem0c orcC ({sumText stepsList}) (mapState env0 σ (entryS 0)) = mapState (E{C} env0) σ K{C} := by\n" ++
    s!"  have m0 : Mem0Rel env0 σ {memT} mem0c := h0\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ {memT} mem0c := mem0Rel_envAbs _ σ _ mem0c (mem0s_keyed {roT} rodata) m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let sl := s!"(ArmSlice.slice_sound {envc} σ {memT} mem0c m{cc} prog {roT} {(orcs[cc]!).2} orcC {stepsList[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} rfl (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then "mapState env0 σ (entryS 0)" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : Arm.run prog {roT} mem0c orcC {stepsList[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {sl}\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [ArmSlice.run_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  let tailT : String := match finalK.tail with
    | none => "none"
    | some t => "some \"" ++ t ++ "\""
  let mut cases := ""
  let mut missing := 0
  for n in [0:count] do
    for i in [0:8] do
      for b in [0:4] do
        let o := 32 * n + 4 * i + b
        match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
        | .ok (some (.dat (.var (.n id)) b')) =>
          match chosen.findIdx? (·.1 == id) with
          | some kk =>
            if (chosen[kk]!).2 == .HB n i && b' == b then
              cases := cases ++ s!"  | {n}, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), outCell_sound _ σ K{C} {o} {id} {b'} (by decide),\n" ++
                s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB n i)} from inv_get (inv_final inp env0 hm) {kk} (by decide),\n" ++
                s!"        qHB, byte_bswap _ {b} (by decide), node_byte inp {n} {i} {b} (by decide) (by decide)]; rfl⟩\n"
            else cases := cases ++ s!"  -- output {o}: unexpected label {qText (chosen[kk]!).2} / byte {b'}\n"; missing := missing + 1
          | none => cases := cases ++ s!"  -- output {o}: no label\n"; missing := missing + 1
        | _ => cases := cases ++ s!"  -- output {o}: no stored lane\n"; missing := missing + 1
  if count > 0 then fin := fin ++ s!"\n/-- `{cfg.sym}` (shipped linux_arm64 object), called on {count} blocks: every output byte is the SHA-256 byte of its block. -/\n" ++
    "theorem out_final (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)\n" ++
    s!"    (orcC : Nat → Bool) (hw : WfMem {roT} rodata mem0c) (he : EnvMem env0 σ mem0c) (hσ : σ 2 = {count}) (hm : HMem {nb} inp env0) :\n" ++
    s!"    ∀ n i b, n < {count} → i < 8 → b < 4 → ∃ x,\n" ++
    s!"      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)\n        (Arm.run prog {roT} mem0c orcC ({sumText stepsList}) (mapState env0 σ (entryS 0))).mem = .ok (some (.dat x b)) ∧\n" ++
    "      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by\n" ++
    s!"  rw [run_final env0 σ mem0c orcC (mem0Rel_of_wf {roT} rodata env0 σ mem0c hw he) hσ]\n  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n" ++ cases ++
    s!"  | _ + {count}, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n"
  fin := fin ++
    -- the final state: halted, no tail call, no error
    s!"/-- The memory hypothesis is satisfiable (for any input bytes). -/\ntheorem wf_sat (inp : Int → W32) : WfMem {roT} rodata (cmem {roT} rodata inp) := cmem_wf {roT} rodata inp (by decide) (by decide)\n\n" ++
    (if count = 0 then s!"/-- Called on no blocks, the kernel writes nothing outside the stack. -/\ntheorem only_stack_writes : (K{C}.mem.all fun p => decide (p.1.region = rStack)) = true := by decide\n\n" ++
      "/-- Called on no blocks, the kernel writes only stack bytes: no output byte, and nothing else. -/\n" ++
      "theorem only_stack_writes_run (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)\n" ++
      s!"    (orcC : Nat → Bool) (hw : WfMem {roT} rodata mem0c) (he : EnvMem env0 σ mem0c) (hσ : σ 2 = 0) :\n" ++
      s!"    ∀ p ∈ (Arm.run prog {roT} mem0c orcC ({sumText stepsList}) (mapState env0 σ (entryS 0))).mem, p.1.region = rStack := by\n" ++
      s!"  rw [run_final env0 σ mem0c orcC (mem0Rel_of_wf {roT} rodata env0 σ mem0c hw he) hσ]\n" ++
      "  have h := only_stack_writes\n  simp only [List.all_eq_true, decide_eq_true_eq] at h\n  intro p hp\n" ++
      "  simp only [mapState, List.mem_map] at hp\n  obtain ⟨q, hq, rfl⟩ := hp\n  exact h q hq\n\n" else "") ++
    s!"/-- The run ends: halted, no error, tail call as stated. -/\ntheorem final_halted : K{C}.halted = true ∧ K{C}.tail = {tailT} ∧ K{C}.err = none := ⟨rfl, rfl, rfl⟩\n\nend {ns}\n"
  IO.FS.writeFile s!"{dir}/Final.lean" fin
  IO.println s!"wrote Final.lean ({missing} output bytes without a proof)"
