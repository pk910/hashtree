import Hashtree.Asm.Print
import Hashtree.Asm.Slice
import Hashtree.Asm.SpecQ1
import Hashtree.Asm.X86Sym
import Hashtree.Asm.X86Loop2
import Hashtree.Asm.Scan
import Hashtree.Kernels.X86.SseX1
import Hashtree.Kernels.X86.AvxX1

/-!
(Library part copied from X86Proof1.lean.)
`x86proof1 <kernel> <outdir> [first] [last]`: proof files for a single-block x86 kernel (`sse` =
`hashtree_sha256_sse_x1`, `avx` = `hashtree_sha256_avx_x1`), count 2.

Like `X86Proof.lean` (shani), with three differences:
* cuts: after every instruction that first produces a round's `a` word (`A n r t`, new `t`);
* only *needed* location variables are tracked (backwards from the output bytes);
* a needed variable without a derivable spec quantity gets an expression label (`QE`, the slice's
  tree over the previous cut's labels), so partial results (message-schedule steps spread over
  several rounds) can live across cuts.

Files: `D{c}` (the cut `K{c+1}`, labels `L{c+1}`, trees `T{c}`; independent), `P{c}` (slice
check, lane lemmas, step; imports `D{c-1}`, `D{c}`), `Final`.
-/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.Scan

structure Kern where
  name : String      -- symbol
  ns : String        -- kernel namespace
  gen : String       -- Gen namespace / directory suffix
  prog : Array Instr
  rodata : List Nat

def kerns : List (String × Kern) := [
  ("sse", ⟨"hashtree_sha256_sse_x1", "Hashtree.Kernels.X86.SseX1", "SseX1L",
    Hashtree.Kernels.X86.SseX1.prog, Hashtree.Kernels.X86.SseX1.rodata⟩),
  ("avx", ⟨"hashtree_sha256_avx_x1", "Hashtree.Kernels.X86.AvxX1", "AvxX1L",
    Hashtree.Kernels.X86.AvxX1.prog, Hashtree.Kernels.X86.AvxX1.rodata⟩)]

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
def locVals (s : Hashtree.Asm.X86Run.CS) : List (Nat × W32) := Id.run do
  let mut out : List (Nat × W32) := []
  for g in [0:16] do
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

def labelsAt (t1 t2 : Std.HashMap W32 (List Q)) (s1 s2 : Hashtree.Asm.X86Run.CS) : Std.HashMap Nat (List Q) := Id.run do
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

instance : Inhabited Sl := ⟨⟨0, [], entryS 24, entryS 24, {}⟩⟩


/-! ## Segments (loop proofs) -/

abbrev CS := Hashtree.Asm.X86Run.CS

def sumText (l : List Nat) : String := l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""

def takenOf (prog : Array Instr) (m : Addr Int → Cell W32 Int) (n : Nat) (c : CS) : List Nat := Id.run do
  let mut taken : List Nat := []
  let mut cs := c
  for _ in [0:n] do
    let pc0 := cs.pc
    let isBr := match prog[pc0]? with | some (.jcc _ _) | some (.jccTail _ _) => true | _ => false
    cs := run prog 4 m (fun _ => false) 1 cs
    if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
  return taken

/-- The sliced symbolic run of a segment: cuts from the concrete run `c1`. -/
def segRun (prog : Array Instr) (m0s : Addr Lin → Cell E Lin) (K0 : State E Lin) (c1i c2i : CS)
    (m1 m2 : Addr Int → Cell W32 Int) (t1 t2 : Std.HashMap W32 (List Q)) (total : Nat) :
    Except String (Array Sl) := Id.run do
  let mut cuts : List Nat := []
  let mut s1 := c1i
  let mut s2 := c2i
  let mut seen : List Q := []
  let mut lastCut := 0
  for k in [0:total] do
    s1 := run prog 4 m1 (fun _ => false) 1 s1
    s2 := run prog 4 m2 (fun _ => false) 1 s2
    let mut newA := false
    for (_, qs) in (labelsAt t1 t2 s1 s2).toList do
      for q in qs do
        match q with
        | .A _ _ t => if t ≥ 1 && !seen.contains q then seen := q :: seen; newA := true
        | _ => pure ()
    if newA || k + 1 = total || k + 1 - lastCut ≥ 400 then cuts := cuts ++ [k + 1]; lastCut := k + 1
  let mut c1 := c1i
  let mut c2 := c2i
  let mut K := K0
  let mut prev := 0
  let mut sls : Array Sl := #[]
  for cut in cuts do
    let n := cut - prev
    let taken := takenOf prog m1 n c1
    let R := run prog 4 m0s (fun pc => taken.contains pc) n K
    if R.err.isSome then return .error s!"slice {sls.size}: symbolic error {R.err}"
    let K' := abstract R
    c1 := run prog 4 m1 (fun _ => false) n c1
    c2 := run prog 4 m2 (fun _ => false) n c2
    sls := sls.push ⟨n, taken, R, K', labelsAt t1 t2 c1 c2⟩
    K := K'
    prev := cut
  return .ok sls

/-- Generate one segment. `memT`: the symbolic initial memory (Lean text), `keyedT`: its
`MemKeyed` proof; `nb` output blocks (0/1); `hsig`: the count hypothesis. -/
def genSeg (kern : Kern) (dir seg k0Name memT keyedT hsig : String) (sls : Array Sl) (nb : Nat)
    (spLo spHi : Int) (imp : String) : IO (State E Lin) := do
  let G := kern.gen
  let sns := s!"Hashtree.Gen.{G}.{seg}"
  let C := sls.size
  let finalK : State E Lin := sls[C - 1]!.K'
  let mut outIds : List Nat := []
  for o in [0:32 * nb] do
    match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
    | .ok (some (Cell.dat (E.var (Key.n id)) _)) => outIds := outIds ++ [id]
    | _ => throw (IO.userError s!"{seg} output {o}: not a stored lane")
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
      | none => throw (IO.userError s!"{seg} cut {cc + 1}: needed var {v} has no tree")
    needed := needed.set! cc nd
  if !needed[0]!.isEmpty then throw (IO.userError s!"{seg}: start variables needed {needed[0]!}")
  let hdr := s!"open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym {kern.ns} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n" ++
    s!"namespace {sns}\nopen Hashtree.Gen.{G}\n\n"
  let base := s!"import Hashtree.Asm.SpecQ1\nimport Hashtree.Asm.X86Loop2\nimport {kern.ns}\nimport Hashtree.Gen.{G}.Head\n"
  IO.FS.createDirAll s!"{dir}/{seg}"
  let mut labs : List (Nat × L1) := []
  for c in [0:C] do
    let sl := sls[c]!
    let n := sl.n
    let orcT := s!"(fun pc => decide (pc ∈ ({sl.taken} : List Nat)))"
    let kName := if c = 0 then k0Name else s!"K{c}"
    let mut labs' : List (Nat × L1) := []
    let mut trees : List (Nat × E) := []
    let mut lemmas := ""
    let mut calls : List String := []
    for id in needed[c + 1]!.mergeSort (· ≤ ·) do
      let some t := treeAt sl.R id | throw (IO.userError s!"no tree {id}")
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
      if bad then throw (IO.userError s!"{seg} slice {c}: var {id} depends on an unlabelled location")
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
        let link : List Eqn := if bytes then atoms.flatMap (fun a => match a with
          | .W _ 0 t => if t < 16 then (derive (atoms.erase a) bytes a 4).getD [] else []
          | .R _ _ => (derive (atoms.erase a) bytes a 4).getD []
          | _ => []) else []
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
          "  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]\n  all_goals bv_decide (timeout := 600)\n\n"
        let callArgs := String.join (cvals.map fun v => s!" {v}#32") ++ hypCall ++ String.join (eqs.map fun e => s!" {e.proof}")
        calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{callArgs}"]
        labs' := labs' ++ [(id, .q q)]
      | none =>
        let lab := toL1 (fun w => (labs.find? (·.1 == w)).map (·.2)) t
        let some lab := lab | throw (IO.userError s!"{seg} slice {c}: var {id}: no expression label")
        lemmas := lemmas ++ s!"theorem core{c}_{id} (V : Q → Word) (inp : Nat → Byte) (env : Key → W32){hypArgs}{mArgs} :\n" ++
          s!"    E.eval env {t.toLean} = QE.eval V inp {lab.toLean} := by\n" ++
          "  simp_all only [E.eval, QE.eval]\n\n"
        calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{hypCall}"]
        labs' := labs' ++ [(id, lab)]
      trees := trees ++ [(id, t)]
    let dfile := base ++ "\n" ++ hdr ++
      (if c = 0 then "def L0 : List (Nat × QE) := []\n\n" else "") ++
      s!"def K{c + 1} : State E Lin := {sl.K'.toLean}\n\n" ++
      s!"def L{c + 1} : List (Nat × QE) := {listLean (fun (p : Nat × L1) => s!"({p.1}, {p.2.toLean})") labs'}\n\n" ++
      s!"def T{c} : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") trees}\n\n" ++
      s!"end {sns}\n"
    IO.FS.writeFile s!"{dir}/{seg}/D{c}.lean" dfile
    let cases := String.join ((List.range labs'.length).map fun k =>
      s!"  | {k}, _ => exact (slice_trees prog 4 _ _ {n} {kName} K{c + 1} T{c} slice{c} env {k} (by decide)).trans ({calls[k]!})\n")
    let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L{c} inp env) (hm : HMem 128 inp env) :\n" ++
      s!"    Inv1 L{c + 1} inp (envAbs env (run prog 4 {memT} {orcT} {n} {kName})) := by\n" ++
      s!"  apply inv1_of_get\n  intro k hk\n  match k, hk with\n" ++ cases ++
      s!"  | _ + {labs'.length}, hk => simp only [L{c + 1}, List.length_cons, List.length_nil] at hk; omega\n\n"
    let pfile := s!"import {sns}.D{c}\n" ++ (if c = 0 then "" else s!"import {sns}.D{c - 1}\n") ++
      "import Std.Tactic.BVDecide\n\n" ++ hdr ++
      s!"theorem slice{c} : sliceCheck prog 4 {memT} {orcT} {n} {kName} K{c + 1} T{c} = true := by\n  decide +kernel\n\n" ++
      lemmas ++ step ++ s!"end {sns}\n"
    IO.FS.writeFile s!"{dir}/{seg}/P{c}.lean" pfile
    labs := labs'
  IO.println s!"{seg}: {C} slices, {(sls.map (·.n)).foldl (· + ·) 0} steps"
  -- Final
  let kn (j : Nat) : String := if j = 0 then k0Name else s!"K{j}"
  let orcOf (cc : Nat) : String := s!"(fun pc => decide (pc ∈ ({sls[cc]!.taken} : List Nat)))"
  let steps := (sls.map (·.n)).toList
  let mut fin := String.join ((List.range C).map fun cc => s!"import {sns}.P{cc}\n") ++ imp ++ "\n" ++ hdr ++
    "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) (run prog 4 {memT} {orcOf cc} {steps[cc]!} {kn cc})\n"
  fin := fin ++ s!"\ndef KF : State E Lin := K{C}\ndef EF (env0 : Key → W32) : Key → W32 := E{C} env0\ndef NS : Nat := {sumText steps}\n\n"
  fin := fin ++ s!"theorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem 128 inp env0) :\n    Inv1 L{C} inp (E{C} env0) := by\n" ++
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
      s!"theorem asm{j} (σ : Nat → Int) {hsig} : ∀ p ∈ A{j}, (mapCond σ p.1).decideC = some p.2 := by\n" ++
      s!"  intro p hp\n  simp only [A{j}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
      (if A.isEmpty then "  exact absurd hp id\n\n" else
        s!"  rcases hp with {" | ".intercalate ((List.range A.length).map fun _ => "rfl")} <;>\n" ++
        "    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;> omega\n\n")
  fin := fin ++ "theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)\n" ++
    s!"    (h0 : Mem0Rel env0 σ {memT} mem0c) {hsig} :\n" ++
    s!"    run prog 4 mem0c orcC NS (mapState env0 σ {k0Name}) = mapState (EF env0) σ KF := by\n" ++
    s!"  have m0 : Mem0Rel env0 σ {memT} mem0c := h0\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ {memT} mem0c := mem0Rel_envAbs _ σ _ mem0c {keyedT} m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let slT := s!"(slice_sound {envc} σ {memT} mem0c m{cc} prog 4 {orcOf cc} orcC {steps[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} rfl (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then s!"mapState env0 σ {k0Name}" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : run prog 4 mem0c orcC {steps[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {slT}\n"
  fin := fin ++ s!"  show run prog 4 mem0c orcC ({sumText steps}) (mapState env0 σ {k0Name}) = _\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [run_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  if nb > 0 then
    let mut cases := ""
    let mut bad := 0
    for i in [0:8] do
      for b in [0:4] do
        let o := 4 * i + b
        match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
        | .ok (some (Cell.dat (E.var (Key.n id)) b')) =>
          match labs.findIdx? (·.1 == id) with
          | some kk =>
            if (labs[kk]!).2 == .q (.HB 0 i) && b' == b then
              cases := cases ++ s!"  | 0, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), outCell_sound _ σ K{C} {o} {id} {b'} (by decide),\n" ++
                s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB 0 i)} from inv1_get (inv_final inp env0 hm) {kk} (by decide),\n" ++
                s!"        qHB, byte_bswap _ {b} (by decide), node_byte inp 0 {i} {b} (by decide) (by decide)]; rfl⟩\n"
            else cases := cases ++ s!"  -- output {o}: unexpected label\n"; bad := bad + 1
          | none => cases := cases ++ s!"  -- output {o}: no label\n"; bad := bad + 1
        | _ => cases := cases ++ s!"  -- output {o}: no stored lane\n"; bad := bad + 1
    IO.println s!"{seg}: {bad} outputs without proof"
    fin := fin ++ "\ntheorem out_final (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (hm : HMem 128 inp env0) :\n" ++
      "    ∀ n i b, n < 1 → i < 8 → b < 4 → ∃ x,\n" ++
      "      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) (mapState (EF env0) σ KF).mem = .ok (some (.dat x b)) ∧\n" ++
      "      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by\n" ++
      "  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n" ++ cases ++
      "  | _ + 1, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n"
  fin := fin ++ s!"theorem log_final : ∀ p ∈ KF.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < {32 * nb}) ∨\n" ++
    s!"    (p.1.region = rStack ∧ p.1.off.c = [] ∧ {spLo} ≤ p.1.off.k ∧ p.1.off.k < {spHi}) := by\n  decide\n\n"
  fin := fin ++ "theorem KF_halted : KF.halted = " ++ (if finalK.halted then "true" else "false") ++ " := by decide\n" ++
    "theorem KF_err : KF.err = none := by decide\ntheorem KF_tail : KF.tail = none := by decide\n\n"
  fin := fin ++ s!"end {sns}\n"
  IO.FS.writeFile s!"{dir}/{seg}/Final.lean" fin
  return finalK

def headPc (prog : Array Instr) : Nat := Id.run do
  let mut h := 0
  for i in prog do
    match i with
    | .jmp t => h := t
    | _ => pure ()
  return h

def ok! {α : Type} [Inhabited α] (r : Except String α) : IO α := match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let some kern := kerns.lookup (args.headD "sse") | throw (IO.userError "kernel: sse | avx")
  let dir := args.getD 1 "Gen"
  let seg := args.getD 2 "all"
  let prog := kern.prog
  let G := kern.gen
  let H := headPc prog
  let cprogs : List Hashtree.Asm.X86Run.Prog := [⟨kern.name, prog, 4, kern.rodata.toArray⟩]
  let i1 := randInput 11 128
  let i2 := randInput 22 128
  let m1 := Hashtree.Asm.X86Run.mem0 cprogs i1 24
  let m2 := Hashtree.Asm.X86Run.mem0 cprogs i2 24
  let toHead (m : Addr Int → Cell W32 Int) (s : CS) : CS × Nat := Id.run do
    let mut s := run prog 4 m (fun _ => false) 1 s
    let mut k := 1
    while s.pc != H && !s.halted && k < 100000 do
      s := run prog 4 m (fun _ => false) 1 s
      k := k + 1
    return (s, k)
  let toHalt (m : Addr Int → Cell W32 Int) (s : CS) : Nat := Id.run do
    let mut s := s
    let mut k := 0
    while !s.halted && k < 100000 do
      s := run prog 4 m (fun _ => false) 1 s
      k := k + 1
    return k
  -- prologue
  let e2 := Hashtree.Asm.X86Run.entry false 2 24
  let (h0c1, NP) := toHead m1 e2
  let (h0c2, _) := toHead m2 e2
  let KP := abstract (run prog 4 (mem0s 4 kern.rodata 24) (fun _ => false) NP (entryS 24))
  if KP.err.isSome then throw (IO.userError s!"prologue: {KP.err}")
  let lo : Int := KP.mem.foldl (fun acc p => match p.1.off.asInt with | some o => min acc o | none => acc) 24
  let KH0 : State E Lin := { KP with mem := [], flags := some (Lin.sym 3, Lin.sym 4) }
  let memT := s!"(mem0sH 4 rodata 24 ({lo}))"
  let keyedT := s!"(mem0sH_keyed rodata ({lo}))"
  let m0H := mem0sH 4 kern.rodata 24 lo
  let (h1c1, NI) := toHead m1 h0c1
  let (h1c2, _) := toHead m2 h0c2
  let tab (a : Array Nat) (o : Nat) := table (a.extract o (o + 64)) 1
  -- It0 (from KH0) gives KH1: registers that became constant pointers
  let sls0 ← ok! (segRun prog m0H KH0 h0c1 h0c2 m1 m2 (tab i1 0) (tab i2 0) NI)
  let KF0 := sls0[sls0.size - 1]!.K'
  let g1 := (List.range KH0.gpr.length).map fun g =>
    match KH0.gpr[g]!, KF0.gpr[g]! with
    | .num _ _, .ptr a => if a.off.asInt.isSome then Val.ptr a else KH0.gpr[g]!
    | _, _ => KH0.gpr[g]!
  let KH1 : State E Lin := { KH0 with gpr := g1 }
  let tauOf (KF : State E Lin) : String :=
    let off (g : Nat) : String := match KF.getG g with | .ptr a => a.off.toLean | _ => "?"
    let fl := match KF.flags with | some (a, b) => s!"{a.toLean}, {b.toLean}" | none => "?, ?"
    s!"[{off 6}, {off 7}, (⟨-1, [0, 0, 1]⟩ : Lin), {fl}]"
  let hdr := s!"open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym {kern.ns} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"
  if seg = "head" || seg = "all" then
    let flagsText := match KP.flags with
      | some (a, b) => s!"[Lin.sym 0, Lin.sym 1, Lin.sym 2, {a.toLean}, {b.toLean}]"
      | none => "[]"
    let body := s!"import Hashtree.Asm.Chain\nimport Hashtree.Asm.X86Loop2\nimport {kern.ns}\n\n" ++ hdr ++
      s!"namespace Hashtree.Gen.{G}\n\n" ++
      s!"/-- The prologue's cut at the loop head (pc {H}), {NP} steps. -/\ndef KP : State E Lin := {KP.toLean}\n\n" ++
      "/-- The first loop-head cut: the prologue's, without its log, flags as fresh symbols 3, 4. -/\n" ++
      s!"def KH0 : State E Lin := {KH0.toLean}\n\n" ++
      "/-- The loop-head cut after an iteration: registers set to constant pointers by the body. -/\n" ++
      s!"def KH1 : State E Lin := {KH1.toLean}\n\n" ++
      s!"def tauP : List Lin := {flagsText}\n\ndef NP : Nat := {NP}\ndef lo : Int := {lo}\n\n" ++
      s!"theorem slicePro : sliceCheck prog 4 (mem0s 4 rodata 24) (fun _ => false) {NP} (entryS 24) KP [] = true := by\n  decide +kernel\n\n" ++
      "theorem KP_assume : KP.assume = [] := by decide\n" ++
      "theorem KP_inst : { KP with mem := [], assume := [] } = KH0.substL tauP := by decide\n" ++
      "theorem KP_push : pushOk KP lo = true := by decide\n" ++
      "theorem KP_log : ∀ p ∈ KP.mem, p.1.region = rStack ∧ p.1.off.c = [] ∧ lo ≤ p.1.off.k ∧ p.1.off.k < 24 := by decide\n" ++
      "theorem KH0_nOnly : KH0.nOnly = true := by decide\ntheorem KH1_nOnly : KH1.nOnly = true := by decide\n\n" ++
      s!"end Hashtree.Gen.{G}\n"
    IO.FS.createDirAll dir
    IO.FS.writeFile s!"{dir}/Head.lean" body
    IO.println s!"Head: prologue {NP} steps, lo {lo}, iteration {NI} steps"
  let shapeFile (sg kh : String) (KF : State E Lin) (C : Nat) : String :=
    s!"import Hashtree.Gen.{G}.{sg}.Final\n\n" ++ hdr ++ s!"namespace Hashtree.Gen.{G}.{sg}\nopen Hashtree.Gen.{G}\n\n" ++
      s!"def tauE : List Lin := {tauOf KF}\n\n" ++
      s!"theorem KF_gpr : gprRel 0 (KH1.substL tauE).gpr KF.gpr = true := by decide\n" ++
      s!"theorem KF_vr : vrRel 0 KH1.vr KF.vr = true := by decide\n" ++
      s!"theorem KF_shape : \{ (\{ KF with gpr := (KH1.substL tauE).gpr, vr := KH1.vr } : State E Lin) with mem := [], assume := [] } = KH1.substL tauE := by decide\n\n" ++
      s!"theorem KF_inst (env0 : Key → W32) (σ : Nat → Int) :\n    mapState (EF env0) σ KF = mapState (EF env0) σ \{ KF with gpr := (KH1.substL tauE).gpr, vr := KH1.vr } :=\n" ++
      s!"  mapState_inst (E{C - 1} env0) σ _ _ _ _ _ _ _ _ slice{C - 1} (KH1.substL tauE).gpr KH1.vr KF_gpr KF_vr\n\n" ++
      s!"end Hashtree.Gen.{G}.{sg}\n"
  let spLo : Int := -200
  if seg = "it0" || seg = "all" then
    let KF ← genSeg kern dir "It0" "KH0" memT keyedT "(hσ : 1 ≤ σ 2)" sls0 1 spLo lo ""
    IO.FS.writeFile s!"{dir}/It0/Shape.lean" (shapeFile "It0" "KH0" KF sls0.size)
  if seg = "it" || seg = "all" then
    let (h2c1, _) := toHead m1 h1c1
    let _ := h2c1
    let sls ← ok! (segRun prog m0H KH1 h1c1 h1c2 m1 m2 (tab i1 64) (tab i2 64) NI)
    let KF ← genSeg kern dir "It" "KH1" memT keyedT "(hσ : 1 ≤ σ 2)" sls 1 spLo lo ""
    IO.FS.writeFile s!"{dir}/It/Shape.lean" (shapeFile "It" "KH1" KF sls.size)
  if seg = "t0a" || seg = "all" then
    let e0 := Hashtree.Asm.X86Run.entry false 0 24
    let (c1, _) := toHead m1 e0
    let (c2, _) := toHead m2 e0
    let n := toHalt m1 c1
    let sls ← ok! (segRun prog m0H KH0 c1 c2 m1 m2 (tab i1 0) (tab i2 0) n)
    let _ ← genSeg kern dir "T0a" "KH0" memT keyedT "(hσ : σ 2 = 0)" sls 0 spLo lo ""
  if seg = "t0b" || seg = "all" then
    let e1 := Hashtree.Asm.X86Run.entry false 1 24
    let (c1, _) := toHead m1 e1
    let (c2, _) := toHead m2 e1
    let (c1, _) := toHead m1 c1
    let (c2, _) := toHead m2 c2
    let n := toHalt m1 c1
    let sls ← ok! (segRun prog m0H KH1 c1 c2 m1 m2 (tab i1 64) (tab i2 64) n)
    let _ ← genSeg kern dir "T0b" "KH1" memT keyedT "(hσ : σ 2 = 0)" sls 0 spLo lo ""
  IO.println "done"
