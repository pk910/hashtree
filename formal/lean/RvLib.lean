import Hashtree.Asm.Print
import Hashtree.Asm.RiscvSlice
import Hashtree.Asm.RiscvSym
import Hashtree.Asm.RiscvRun
import Hashtree.Asm.SpecQ1
import Hashtree.Asm.Scan
import Hashtree.Kernels.Riscv.X1
import Hashtree.Kernels.Riscv.ZbbX1
import Hashtree.Kernels.Riscv.Crypto

/-!
# Shared helpers of the RV64 proof generators

`rvproof` (count 2, straight-line) and `rvloop` (every count, loop segments) both read the RV64
kernels, run them symbolically, label data locations by spec quantities, and emit proof files.
The kernel table, the symbolic initial memory, the equation deriver, the expression labels and
the label extraction from concrete runs live here; each executable keeps only its own `main`.
-/

open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym Hashtree.Asm.Scan

structure Kern where
  name : String      -- symbol
  ns : String        -- kernel namespace
  gen : String       -- Gen namespace / directory suffix
  prog : Array Instr
  compressed : List Nat
  got : List Target
  rodata : List Nat

def kerns : List (String × Kern) := [
  ("x1", ⟨"hashtree_sha256_riscv_x1", "Hashtree.Kernels.Riscv.X1", "RvX1P",
    Hashtree.Kernels.Riscv.X1.prog, Hashtree.Kernels.Riscv.X1.compressed, Hashtree.Kernels.Riscv.X1.got,
    Hashtree.Kernels.Riscv.X1.rodata⟩),
  ("zbb", ⟨"hashtree_sha256_riscv_zbb_x1", "Hashtree.Kernels.Riscv.ZbbX1", "RvZbbX1P",
    Hashtree.Kernels.Riscv.ZbbX1.prog, Hashtree.Kernels.Riscv.ZbbX1.compressed, Hashtree.Kernels.Riscv.ZbbX1.got,
    Hashtree.Kernels.Riscv.ZbbX1.rodata⟩),
  ("crypto", ⟨"hashtree_sha256_riscv_crypto", "Hashtree.Kernels.Riscv.Crypto", "RvCryptoP",
    Hashtree.Kernels.Riscv.Crypto.prog, Hashtree.Kernels.Riscv.Crypto.compressed, Hashtree.Kernels.Riscv.Crypto.got,
    Hashtree.Kernels.Riscv.Crypto.rodata⟩)]

/-- The program environment: rodata 10, GOT 11, code 12, no named symbols. -/
def peR : Env := ⟨10, 11, 12, []⟩

/-- GOT entries as pointers. -/
def gotPtrs (g : List Target) : List (Region × Int) :=
  g.map fun t => match t with
    | .ro o => (10, o)
    | .got k => (11, 8 * (k : Int))
    | .sym _ o => (0, o)

def gotText (l : List (Region × Int)) : String :=
  "[" ++ ", ".intercalate (l.map fun (r, k) => s!"({r}, {k})") ++ "]"

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

/-- Expression labels (generator side; `QE` in `SpecQ1.lean` is the proof side). -/
inductive L1 where
  | q (x : Q) | m (o : Nat) | c (v : W32)
  | add (a b : L1) | xor (a b : L1) | and (a b : L1) | or (a b : L1) | not (a : L1)
  | shl (a : L1) (n : Nat) | shr (a : L1) (n : Nat) | sar (a : L1) (n : Nat) | ror (a : L1) (n : Nat)
  | tern (i : Nat) (a b d : L1)
  deriving BEq, Inhabited

partial def L1.toLean : L1 → String
  | .q x => s!"(.q {qText x})" | .m o => s!"(.m {o})" | .c v => s!"(.c {v.toNat})"
  | .add a b => s!"(.add {a.toLean} {b.toLean})" | .xor a b => s!"(.xor {a.toLean} {b.toLean})"
  | .and a b => s!"(.and {a.toLean} {b.toLean})" | .or a b => s!"(.or {a.toLean} {b.toLean})"
  | .not a => s!"(.not {a.toLean})"
  | .shl a n => s!"(.shl {a.toLean} {n})" | .shr a n => s!"(.shr {a.toLean} {n})"
  | .sar a n => s!"(.sar {a.toLean} {n})" | .ror a n => s!"(.ror {a.toLean} {n})"
  | .tern i a b d => s!"(.tern {i} {a.toLean} {b.toLean} {d.toLean})"

partial def L1.size : L1 → Nat
  | .q _ | .m _ | .c _ => 1
  | .add a b | .xor a b | .and a b | .or a b => a.size + b.size + 1
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.size + 1
  | .tern _ a b d => a.size + b.size + d.size + 1

partial def L1.qs : L1 → List Q
  | .q x => [x] | .m _ | .c _ => []
  | .add a b | .xor a b | .and a b | .or a b => a.qs ++ b.qs
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.qs
  | .tern _ a b d => a.qs ++ b.qs ++ d.qs

partial def L1.hasM : L1 → Bool
  | .q _ | .c _ => false | .m _ => true
  | .add a b | .xor a b | .and a b | .or a b => a.hasM || b.hasM
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.hasM
  | .tern _ a b d => a.hasM || b.hasM || d.hasM

/-- A slice tree over the previous cut's labels. -/
partial def toL1 (lab : Nat → Option L1) : E → Option L1
  | .var (.n w) => lab w
  | .var (.m 1 l) => if l.c = [1] && l.k ≥ 0 then some (.m l.k.toNat) else none
  | .var _ => none
  | .const v => some (.c v)
  | .add a b => do pure (.add (← toL1 lab a) (← toL1 lab b))
  | .xor a b => do pure (.xor (← toL1 lab a) (← toL1 lab b))
  | .and a b => do pure (.and (← toL1 lab a) (← toL1 lab b))
  | .or a b => do pure (.or (← toL1 lab a) (← toL1 lab b))
  | .not a => do pure (.not (← toL1 lab a))
  | .shl a n => do pure (.shl (← toL1 lab a) n)
  | .shr a n => do pure (.shr (← toL1 lab a) n)
  | .sar a n => do pure (.sar (← toL1 lab a) n)
  | .ror a n => do pure (.ror (← toL1 lab a) n)
  | .tern i a b c => do pure (.tern i (← toL1 lab a) (← toL1 lab b) (← toL1 lab c))

/-- Variables (numbered) and memory keys of a tree. -/
partial def Hashtree.Asm.E.keys : E → List Key
  | .var k => [k]
  | .const _ => []
  | .add a b | .xor a b | .and a b | .or a b => a.keys ++ b.keys
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.keys
  | .tern _ a b c => a.keys ++ b.keys ++ c.keys

/-- One equation step: its proof (instantiated at `qv inp`) and its statement over a valuation `V`. -/
structure Eqn where
  proof : String
  stmt : String
  val : Option Nat := none
  deriving BEq

def vq (q : Q) : String := s!"V {qText q}"

/-- As in `X86Proof.lean`. -/
partial def derive (atoms : List Q) (bytes : Bool) (q : Q) (fuel : Nat) : Option (List Eqn) :=
  if atoms.contains q then some [] else if fuel = 0 then none else
  let sub (proof rhs : String) (leaves : List Q) : Option (List Eqn) := do
    let rest ← leaves.mapM (fun l => derive atoms bytes l (fuel - 1))
    pure (⟨proof, s!"{vq q} = {rhs}", none⟩ :: rest.flatten)
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

/-- The data location values of a concrete state, by location id (gpr halves, vector lanes,
memory log entries). -/
def locVals (s : Hashtree.Asm.RiscvRun.CS) : List (Nat × W32) := Id.run do
  let mut out : List (Nat × W32) := []
  for g in [0:32] do
    match s.getG g with
    | .num lo hi => out := (gId g 0, lo) :: (gId g 1, hi) :: out
    | _ => pure ()
  for i in [0:32] do
    let v := s.getV i
    for l in [0:v.length] do
      out := (vId i l, v.getD l 0) :: out
  let mut j := 0
  for (_, c) in s.mem do
    match c with
    | Cell.dat x _ => out := (mId j, x) :: out
    | _ => pure ()
    j := j + 1
  return out

def labelsAt (t1 t2 : Std.HashMap W32 (List Q)) (s1 s2 : Hashtree.Asm.RiscvRun.CS) : Std.HashMap Nat (List Q) := Id.run do
  let v2 : Std.HashMap Nat W32 := (locVals s2).foldl (fun m (p : Nat × W32) => m.insert p.1 p.2) {}
  let mut m : Std.HashMap Nat (List Q) := {}
  for (id, x) in locVals s1 do
    match v2.get? id with
    | some y =>
      let c := (t1.getD x []).filter ((t2.getD y []).contains ·)
      if !c.isEmpty then m := m.insert id c
    | none => pure ()
  return m

/-- A slice of the symbolic run. -/
structure Sl where
  n : Nat
  taken : List Nat
  R : State E Lin
  K' : State E Lin
  labs : Std.HashMap Nat (List Q)   -- concrete labels at the cut after the slice

instance : Inhabited Sl := ⟨⟨0, [], entryS 0, entryS 0, {}⟩⟩

