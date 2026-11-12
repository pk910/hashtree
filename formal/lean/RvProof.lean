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
`rvproof <kernel> <outdir> [first] [last]`: proof files for an RV64 kernel (`x1` =
`hashtree_sha256_riscv_x1`, `zbb` = `..._zbb_x1`, `crypto` = `..._crypto`), count 2.

The approach of `X86Proof1.lean` over `Riscv.run`: cuts after every instruction that first
produces a round's `a` word; only needed location variables are tracked (backwards from the
output bytes); variables without a derivable spec quantity get expression labels (`QE`).
The program runs alone as region base 10 (rodata 10, GOT 11, code 12); its GOT entries are the
pointers `gotT`.  Files: `Base` (environment, memory), `D{c}`, `P{c}`, `Final`.
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

def main (args : List String) : IO Unit := do
  let some kern := kerns.lookup (args.headD "x1") | throw (IO.userError "kernel: x1 | zbb | crypto")
  let dir := args.getD 1 "Gen"
  let first := (args.getD 2 "0").toNat!
  let last := (args.getD 3 "1000000").toNat!
  let prog := kern.prog
  let G := kern.gen
  let cprogs : List Hashtree.Asm.RiscvRun.Prog := [⟨kern.name, prog, kern.compressed, kern.got, [], kern.rodata.toArray, 10⟩]
  let gotT := gotPtrs kern.got
  let m0 := mem0s 10 11 kern.rodata gotT
  let L0 : Hashtree.Asm.RiscvRun.Layout := {}
  let i1 := randInput 11 128
  let i2 := randInput 22 128
  let t1 := table i1 2
  let t2 := table i2 2
  let m1 := Hashtree.Asm.RiscvRun.mem0 cprogs i1 L0
  let m2 := Hashtree.Asm.RiscvRun.mem0 cprogs i2 L0
  -- cuts: after each instruction that first produces some `A n r t`
  let mut cuts : List Nat := []
  let mut s1 := Hashtree.Asm.RiscvRun.entry 2 L0
  let mut s2 := Hashtree.Asm.RiscvRun.entry 2 L0
  let mut seen : List Q := []
  let mut k := 0
  let mut lastCut := 0
  while !s1.halted && k < 200000 do
    s1 := run prog peR m1 (fun _ => false) 1 s1
    s2 := run prog peR m2 (fun _ => false) 1 s2
    k := k + 1
    let mut newA := false
    for (_, qs) in (labelsAt t1 t2 s1 s2).toList do
      for q in qs do
        match q with
        | .A _ _ t => if t ≥ 1 && !seen.contains q then seen := q :: seen; newA := true
        | _ => pure ()
    if newA || s1.halted || k - lastCut ≥ 70 then cuts := cuts ++ [k]; lastCut := k
  IO.println s!"{kern.name}: {k} steps, {cuts.length} cuts, err {s1.err}"
  -- symbolic slices
  let mut c1 := Hashtree.Asm.RiscvRun.entry 2 L0
  let mut c2 := Hashtree.Asm.RiscvRun.entry 2 L0
  let mut K := entryS 0
  let mut prev := 0
  let mut sls : Array Sl := #[]
  for cut in cuts do
    let n := cut - prev
    let mut taken : List Nat := []
    let mut cs := c1
    for _ in [0:n] do
      let pc0 := cs.pc
      let isBr := match prog[pc0]? with | some (.br _ _ _ _) => true | _ => false
      cs := run prog peR m1 (fun _ => false) 1 cs
      if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
    let R := run prog peR m0 (fun pc => taken.contains pc) n K
    if R.err.isSome then
      IO.println s!"slice {sls.size}: symbolic error {R.err}"; return
    let K' := abstract R
    c1 := run prog peR m1 (fun _ => false) n c1
    c2 := run prog peR m2 (fun _ => false) n c2
    sls := sls.push ⟨n, taken, R, K', labelsAt t1 t2 c1 c2⟩
    K := K'
    prev := cut
  let C := sls.size
  let finalK : State E Lin := sls[C - 1]!.K'
  -- needed variables, backwards from the output bytes
  let mut outIds : List Nat := []
  for o in [0:64] do
    match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
    | .ok (some (Cell.dat (E.var (Key.n id)) _)) => outIds := outIds ++ [id]
    | _ => IO.println s!"output {o}: not a stored lane"; return
  let mut needed : Array (List Nat) := Array.replicate (C + 1) []
  needed := needed.set! C outIds.eraseDups
  for cc' in [0:C] do
    let cc := C - 1 - cc'
    let mut nd : List Nat := []
    for v in needed[cc + 1]! do
      match treeAt sls[cc]!.R v with
      | some t => for key in t.keys do
          match key with
          | .n w => if !nd.contains w then nd := w :: nd
          | _ => pure ()
      | none => IO.println s!"cut {cc + 1}: needed var {v} has no tree"; return
    needed := needed.set! cc nd
  IO.println s!"needed at entry: {needed[0]!}"
  if !needed[0]!.isEmpty then IO.println "entry variables needed"; return
  -- forward: labels and lemmas
  let hdr := s!"open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym {kern.ns} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n" ++
    s!"namespace Hashtree.Gen.{G}\n\n"
  let base := s!"import Hashtree.Gen.{G}.Base\n"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/Base.lean" (s!"import Hashtree.Asm.SpecQ1\nimport Hashtree.Asm.RiscvSlice\nimport Hashtree.Asm.RiscvSym\nimport {kern.ns}\n\n" ++
    s!"open Hashtree.Asm Hashtree.Asm.Riscv\n\nnamespace Hashtree.Gen.{G}\n\n" ++
    "/-- The program alone: rodata region 10, GOT 11, code 12. -/\ndef pe : Env := ⟨10, 11, 12, []⟩\n\n" ++
    s!"/-- The GOT entries (pointers). -/\ndef gotT : List (Region × Int) := {gotText gotT}\n\n" ++
    s!"/-- The symbolic initial memory. -/\ndef M0 : Addr Lin → Cell E Lin := RiscvSym.mem0s 10 11 {kern.ns}.rodata gotT\n\nend Hashtree.Gen.{G}\n")
  let mut labs : List (Nat × L1) := []
  let mut nQ := 0
  let mut nE := 0
  let mut maxE := 0
  for c in [0:C] do
    let sl := sls[c]!
    let n := sl.n
    let orcT := s!"(fun pc => decide (pc ∈ ({sl.taken} : List Nat)))"
    let kName := if c = 0 then "(entryS 0)" else s!"K{c}"
    let mut labs' : List (Nat × L1) := []
    let mut trees : List (Nat × E) := []
    let mut lemmas := ""
    let mut calls : List String := []
    for id in needed[c + 1]!.mergeSort (· ≤ ·) do
      let some t := treeAt sl.R id | IO.println s!"no tree {id}"; return
      let keys := t.keys.eraseDups
      let mut hyps : List (Nat × Nat × L1) := []
      let mut bad := false
      for key in keys do
        match key with
        | .n v => match labs.findIdx? (·.1 == v) with
          | some kk => hyps := hyps ++ [(v, kk, (labs[kk]!).2)]
          | none => bad := true
        | .m 1 l => if !(l.c = [1] && l.k ≥ 0) then bad := true
        | _ => bad := true
      if bad then IO.println s!"slice {c}: var {id} depends on an unlabelled location: {keys.map fun k => match k with | .n v => s!"n{v}" | .m r l => s!"m{r}:{l.k},{l.c}"}"; return
      let atoms := (hyps.flatMap (·.2.2.qs)).eraseDups
      let mkeys := keys.filterMap fun key => match key with
        | .m 1 l => some l.k
        | _ => none
      let bytes := !mkeys.isEmpty || hyps.any (·.2.2.hasM)
      let cands := sl.labs.getD id []
      let hypArgs := String.join (hyps.map fun (v, _, l) => s!"\n    (_ : env (.n {v}) = QE.eval V inp {l.toLean})")
      let mArgs := String.join (mkeys.map fun o => s!"\n    (_ : env (.m 1 (⟨{o}, [1]⟩ : Lin)) = (inp {o.toNat}).zeroExtend 32)")
      let hypCall := String.join (hyps.map fun (_, kk, _) => s!" (inv1_get hI {kk} (by decide))") ++
        String.join (mkeys.map fun o => s!" (hm {o.toNat} (by decide))")
      match cands.find? (fun q => (derive atoms bytes q 40).isSome) with
      | some q =>
        -- with input bytes around, also tie the input-word atoms to the bytes
        let link0 : List Eqn := if bytes then atoms.flatMap (fun a => match a with
          | .W _ 0 t => if t < 16 then (derive (atoms.erase a) bytes a 4).getD [] else []
          | .R _ _ => (derive (atoms.erase a) bytes a 4).getD []
          | _ => []) else []
        -- hash words that are atoms next to the round words they come from (feed-forward with
        -- partial results in expression labels): tie them to those round words
        let linkH : List Eqn := atoms.flatMap (fun a => match a with
          | .H _ r _ => if r ≥ 1 then (derive (atoms.erase a) bytes a 6).getD [] else []
          | _ => [])
        let link := link0 ++ linkH
        let eqs := ((derive atoms bytes q 40).getD [] ++ link).eraseDups
        let cvals := (eqs.filterMap (·.val)).eraseDups
        let pName (v : Nat) : String := s!"k{(cvals.idxOf v)}"
        let tText := cvals.foldl (fun (acc : String) v => acc.replace s!"(.const {v})" s!"(.const {pName v})") t.toLean
        let stmtOf (e : Eqn) : String := match e.val with
          | some v => s!"{e.stmt.splitOn " = " |>.head!} = {pName v}"
          | none => e.stmt
        let kArgs := String.join (cvals.map fun v => s!" ({pName v} : W32)")
        let eqArgs := String.join (eqs.map fun e => s!"\n    (_ : {stmtOf e})")
        lemmas := lemmas ++ s!"theorem core{c}_{id} (V : Q → Word) (inp : Nat → Byte) (env : Key → W32){kArgs}{hypArgs}{mArgs}{eqArgs} :\n" ++
          s!"    E.eval env {tText} = {vq q} := by\n" ++
          "  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]\n  all_goals bv_decide (config := { timeout := 600 })\n\n"
        let callArgs := String.join (cvals.map fun v => s!" {v}#32") ++ hypCall ++ String.join (eqs.map fun e => s!" {e.proof}")
        calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{callArgs}"]
        labs' := labs' ++ [(id, .q q)]
        nQ := nQ + 1
      | none =>
        let lab := toL1 (fun w => (labs.find? (·.1 == w)).map (·.2)) t
        let some lab := lab | IO.println s!"slice {c}: var {id}: no expression label"; return
        lemmas := lemmas ++ s!"theorem core{c}_{id} (V : Q → Word) (inp : Nat → Byte) (env : Key → W32){hypArgs}{mArgs} :\n" ++
          s!"    E.eval env {t.toLean} = QE.eval V inp {lab.toLean} := by\n" ++
          "  simp_all only [E.eval, QE.eval]\n\n"
        calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{hypCall}"]
        labs' := labs' ++ [(id, lab)]
        nE := nE + 1
        maxE := max maxE lab.size
      trees := trees ++ [(id, t)]
    if first ≤ c ∧ c ≤ last then
      let dfile := base ++ "\n" ++ hdr ++
        (if c = 0 then "def L0 : List (Nat × QE) := []\n\n" else "") ++
        s!"def K{c + 1} : State E Lin := {sl.K'.toLean}\n\n" ++
        s!"def L{c + 1} : List (Nat × QE) := {listLean (fun (p : Nat × L1) => s!"({p.1}, {p.2.toLean})") labs'}\n\n" ++
        s!"def T{c} : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") trees}\n\n" ++
        s!"end Hashtree.Gen.{G}\n"
      IO.FS.writeFile s!"{dir}/D{c}.lean" dfile
      let cases := String.join ((List.range labs'.length).map fun k =>
        s!"  | {k}, _ => exact (rvSlice_trees prog pe _ _ {n} {kName} K{c + 1} T{c} slice{c} env {k} (by decide)).trans ({calls[k]!})\n")
      let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L{c} inp env) (hm : HMem 128 inp env) :\n" ++
        s!"    Inv1 L{c + 1} inp (envAbs env (run prog pe M0 {orcT} {n} {kName})) := by\n" ++
        s!"  apply inv1_of_get\n  intro k hk\n  match k, hk with\n" ++ cases ++
        s!"  | _ + {labs'.length}, hk => simp only [L{c + 1}, List.length_cons, List.length_nil] at hk; omega\n\n"
      let pfile := s!"import Hashtree.Gen.{G}.D{c}\n" ++ (if c = 0 then "" else s!"import Hashtree.Gen.{G}.D{c - 1}\n") ++
        "import Std.Tactic.BVDecide\n\n" ++ hdr ++
        s!"theorem slice{c} : rvSliceCheck prog pe M0 {orcT} {n} {kName} K{c + 1} T{c} = true := by\n  decide +kernel\n\n" ++
        lemmas ++ step ++ s!"end Hashtree.Gen.{G}\n"
      IO.FS.writeFile s!"{dir}/P{c}.lean" pfile
    IO.println s!"slice {c}: {n} steps, {labs'.length} tracked, mem log {sl.K'.mem.length}"
    labs := labs'
  IO.println s!"labels: {nQ} quantities, {nE} expressions (max size {maxE})"
  -- Final.lean
  let kn (j : Nat) : String := if j = 0 then "(entryS 0)" else s!"K{j}"
  let orcOf (cc : Nat) : String := s!"(fun pc => decide (pc ∈ ({sls[cc]!.taken} : List Nat)))"
  let steps := (sls.map (·.n)).toList
  let mut fin := String.join ((List.range C).map fun cc => s!"import Hashtree.Gen.{G}.P{cc}\n") ++ "\n" ++ hdr ++
    "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) (run prog pe M0 {orcOf cc} {steps[cc]!} {kn cc})\n"
  fin := fin ++ s!"\ntheorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem 128 inp env0) :\n    Inv1 L{C} inp (E{C} env0) := by\n" ++
    "  have i0 : Inv1 L0 inp (E0 env0) := fun p hp => by cases hp\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have i{cc + 1} : Inv1 L{cc + 1} inp (E{cc + 1} env0) := step{cc} inp (E{cc} env0) i{cc} hm\n"
  fin := fin ++ s!"  exact i{C}\n\n"
  let mut asms : List (List (Cond Lin × Bool)) := []
  let mut asmIdx : List Nat := []
  for cc in [0:C] do
    let A := sls[cc]!.K'.assume
    match asms.findIdx? (fun x => decide (x = A)) with
    | some j => asmIdx := asmIdx ++ [j]
    | none => asms := asms ++ [A]; asmIdx := asmIdx ++ [asms.length - 1]
  for j in [0:asms.length] do
    let A := asms[j]!
    let aText := listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") A
    fin := fin ++ s!"def A{j} : List (Cond Lin × Bool) := {aText}\n" ++
      s!"theorem asm{j} (σ : Nat → Int) (hσ : σ 2 = 2) : ∀ p ∈ A{j}, (mapCond σ p.1).decideC = some p.2 := by\n" ++
      s!"  intro p hp\n  simp only [A{j}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
      (if A.isEmpty then "  exact absurd hp id\n\n" else
        s!"  rcases hp with {" | ".intercalate ((List.range A.length).map fun _ => "rfl")} <;>\n" ++
        "    simp [mapCond, Cond.decideC, Lin.eval, dotC, hσ, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;> omega\n\n")
  let sumText : List Nat → String := fun l => l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""
  fin := fin ++ "theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)\n" ++
    "    (h0 : Mem0Rel env0 σ M0 mem0c) (hσ : σ 2 = 2) :\n" ++
    s!"    run prog pe mem0c orcC ({sumText steps}) (mapState env0 σ (entryS 0)) = mapState (E{C} env0) σ K{C} := by\n" ++
    "  have m0 : Mem0Rel env0 σ M0 mem0c := h0\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ M0 mem0c := mem0Rel_envAbs _ σ _ mem0c (RiscvSym.mem0s_keyed 10 11 rodata gotT) m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let slT := s!"(rvSlice_sound {envc} σ M0 mem0c m{cc} prog pe {orcOf cc} orcC {steps[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} rfl (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then "mapState env0 σ (entryS 0)" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : run prog pe mem0c orcC {steps[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {slT}\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [rvRun_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  let mut cases := ""
  let mut bad := 0
  for n in [0:2] do
    for i in [0:8] do
      for b in [0:4] do
        let o := 32 * n + 4 * i + b
        match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
        | .ok (some (Cell.dat (E.var (Key.n id)) b')) =>
          match labs.findIdx? (·.1 == id) with
          | some kk =>
            if (labs[kk]!).2 == .q (.HB n i) && b' == b then
              cases := cases ++ s!"  | {n}, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), outCell_sound _ σ K{C} {o} {id} {b'} (by decide),\n" ++
                s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB n i)} from inv1_get (inv_final inp env0 hm) {kk} (by decide),\n" ++
                s!"        qHB, byte_bswap _ {b} (by decide), node_byte inp {n} {i} {b} (by decide) (by decide)]; rfl⟩\n"
            else cases := cases ++ s!"  -- output {o}: unexpected label {(labs[kk]!).2.toLean} / byte {b'}\n"; bad := bad + 1
          | none => cases := cases ++ s!"  -- output {o}: no label\n"; bad := bad + 1
        | _ => cases := cases ++ s!"  -- output {o}: no stored lane\n"; bad := bad + 1
  fin := fin ++ s!"\n/-- `{kern.name}`, called on two blocks: every output byte is the SHA-256 byte of its block. -/\n" ++
    "theorem out_final (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)\n" ++
    "    (orcC : Nat → Bool) (hw : WfMemR 10 11 rodata gotT mem0c) (he : X86Sym.EnvMem env0 σ mem0c) (hσ : σ 2 = 2)\n" ++
    "    (hm : HMem 128 inp env0) :\n" ++
    "    ∀ n i b, n < 2 → i < 8 → b < 4 → ∃ x,\n" ++
    s!"      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)\n        (run prog pe mem0c orcC ({sumText steps}) (mapState env0 σ (entryS 0))).mem = .ok (some (.dat x b)) ∧\n" ++
    "      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by\n" ++
    "  rw [run_final env0 σ mem0c orcC (mem0RelR_of_wf 10 11 rodata gotT env0 σ mem0c hw he) hσ]\n  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n" ++ cases ++
    s!"  | _ + 2, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n" ++
    "/-- The hypotheses of `out_final` are satisfiable for every input. -/\n" ++
    "theorem hyps_sat (inp : Nat → Byte) (σ : Nat → Int) (hσ : σ 2 = 2) :\n" ++
    "    ∃ mem0c env0, WfMemR 10 11 rodata gotT mem0c ∧ X86Sym.EnvMem env0 σ mem0c ∧ σ 2 = 2 ∧ HMem 128 inp env0 := by\n" ++
    "  obtain ⟨m, e, h1, h2, h3⟩ := hyps_satR 10 11 rodata gotT (by decide) (by decide) (by decide) inp σ 128\n" ++
    "  exact ⟨m, e, h1, h2, hσ, h3⟩\n\n" ++
    s!"end Hashtree.Gen.{G}\n"
  IO.FS.writeFile s!"{dir}/Final.lean" fin
  IO.println s!"wrote Final.lean ({bad} outputs without proof)"
