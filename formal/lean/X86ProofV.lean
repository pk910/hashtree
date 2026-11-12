import Hashtree.Asm.Print
import Hashtree.Asm.Slice
import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Asm.X86Sym
import Hashtree.Asm.Scan
import Hashtree.Kernels.X86.AvxX4
import Hashtree.Kernels.X86.Avx2X8
import Hashtree.Kernels.X86.Avx512X16

/-!
`x86proofv <kernel> <outdir> <first> <last>`: the shani_x2 proof generator (X86Proof.lean) for the
multi-lane kernels (`x4` = avx_x4, `x8` = avx2_x8, `x16` = avx512_x16), called with one full-width
group of blocks (count = lane width).  Per slice: the next cut, the tracked trees, the kernel-checked
slice, and one lemma per labelled lane of the next cut; `Final.lean` chains them.

Cuts (found on a concrete run): after every instruction that produces a new working variable `a`
(`A r t`, `t ≥ 1`), a new digest word (`H r i`, `r ≥ 1`) or a new schedule word (`W 0 t`, `t ≥ 16`),
and at the end.  A lane whose tree refers to an unlabelled location variable of the previous cut is
not proved (reported).
-/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.Scan

structure KSel where
  key : String
  ns : String
  gen : String
  prog : Array Instr
  rodata : List Nat
  count : Nat
  desc : String

def kernels : List KSel := [
  ⟨"x4", "Hashtree.Kernels.X86.AvxX4", "AvxX4P", Hashtree.Kernels.X86.AvxX4.prog, Hashtree.Kernels.X86.AvxX4.rodata, 4,
    "The AVX 4-lane kernel (hashtree_sha256_avx_x4), called on four blocks"⟩,
  ⟨"x8", "Hashtree.Kernels.X86.Avx2X8", "Avx2X8P", Hashtree.Kernels.X86.Avx2X8.prog, Hashtree.Kernels.X86.Avx2X8.rodata, 8,
    "The AVX2 8-lane kernel (hashtree_sha256_avx2_x8), called on eight blocks"⟩,
  ⟨"x16", "Hashtree.Kernels.X86.Avx512X16", "Avx512X16P", Hashtree.Kernels.X86.Avx512X16.prog, Hashtree.Kernels.X86.Avx512X16.rodata, 16,
    "The AVX-512 16-lane kernel (hashtree_sha256_avx512_x16), called on sixteen blocks"⟩]

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
def cutLabels (t1 t2 : Std.HashMap W32 (List Q)) (K : State E Lin) (s1 s2 : Hashtree.Asm.X86Run.CS)
    (keepShadowed : Bool := false) : List (Nat × List Q) := Id.run do
  let common (x y : W32) : List Q := (t1.getD x []).filter ((t2.getD y []).contains ·)
  let isVar (e : E) : Bool := match e with | .var _ => true | _ => false
  let mut out : List (Nat × List Q) := []
  for g in [0:16] do
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
  -- a logged cell shadowed by a newer write to the same symbolic address is never read again
  let mut addrs : Std.HashSet String := {}
  for ((_, c1), (_, c2)) in s1.mem.zip s2.mem do
    let a := match (K.mem[j]? : Option (Addr Lin × Cell E Lin)) with | some (a, _) => a.toLean | none => ""
    let shadowed := addrs.contains a
    addrs := addrs.insert a
    match c1, c2, (K.mem[j]? : Option (Addr Lin × Cell E Lin)) with
    | Cell.dat x _, Cell.dat y _, some (_, Cell.dat e _) =>
      if isVar e && (keepShadowed || !shadowed) then let c := common x y; if !c.isEmpty then out := (mId j, c) :: out
    | _, _, _ => pure ()
    j := j + 1
  return out

/-- One equation step: its proof (instantiated at `qv inp`) and its statement over a valuation `V`. -/
structure Eqn where
  proof : String
  stmt : String
  /-- the value, for a closed quantity (`V q = value`) -/
  val : Option Nat := none
  /-- the spec quantities its statement mentions -/
  vs : List Q := []
  deriving BEq

def vq (q : Q) : String := s!"V {qText q}"

/-- Equations that rewrite `q` down to atoms or closed quantities, or `none`.  Candidate equations
are tried in order; input bytes (`R`) only when `bytes`. -/
partial def derive (atoms : List Q) (bytes : Bool) (q : Q) (fuel : Nat) : Option (List Eqn) :=
  if atoms.contains q then some [] else if fuel = 0 then none else
  let sub (proof rhs : String) (leaves : List Q) : Option (List Eqn) := do
    let rest ← leaves.mapM (fun l => derive atoms bytes l (fuel - 1))
    pure (⟨proof, s!"{vq q} = {rhs}", none, q :: leaves⟩ :: rest.flatten)
  -- closed quantities; `abs`: its value becomes a parameter of the core lemma (padding-block K+W / W,
  -- which reach the trees as loaded constants); H0 words stay literal (constant folding mixes them)
  let closed (proof : String) (v : Nat) (abs : Bool := true) : Option (List Eqn) :=
    some [⟨proof, s!"{vq q} = {v}#32", if abs then some v else none, [q]⟩]
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
    else if t < 16 then (if bytes || atoms.contains (.R n t) then sub s!"(qW_R inp {n} {t} (by decide))" s!"bswap ({vq (.R n t)})" [.R n t] else none)
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
      some [⟨s!"(qR inp {n} {t})", s!"{vq q} = ((((0 : Word) ||| (inp {o}).zeroExtend 32 <<< 0) ||| (inp {o + 1}).zeroExtend 32 <<< 8) ||| (inp {o + 2}).zeroExtend 32 <<< 16) ||| (inp {o + 3}).zeroExtend 32 <<< 24", none, [q]⟩]
    else none

/-- A tree as the `W32` term `E.eval env` unfolds to. -/
partial def Hashtree.Asm.E.toW : E → String
  | .var k => s!"env {k.toLean}"
  | .const v => s!"({v.toNat} : W32)"
  | .add a b => s!"({a.toW} + {b.toW})"
  | .xor a b => s!"({a.toW} ^^^ {b.toW})"
  | .and a b => s!"({a.toW} &&& {b.toW})"
  | .or a b => s!"({a.toW} ||| {b.toW})"
  | .not a => s!"(~~~{a.toW})"
  | .shl a n => s!"({a.toW} <<< ({n} : Nat))"
  | .shr a n => s!"({a.toW} >>> ({n} : Nat))"
  | .sar a n => s!"(BitVec.sshiftRight {a.toW} {n})"
  | .ror a n => s!"(BitVec.rotateRight {a.toW} {n})"
  | .tern i a b c => s!"(ternW {i} {a.toW} {b.toW} {c.toW})"

/-- The `vpternlogd` immediates of a tree. -/
partial def Hashtree.Asm.E.terns : E → List Nat
  | .var _ | .const _ => []
  | .add a b | .xor a b | .and a b | .or a b => a.terns ++ b.terns
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.terns
  | .tern i a b c => i :: (a.terns ++ b.terns ++ c.terns)

/-- `ternW imm a b c` unfolded (the fold over the 8 truth-table bits), as `ternW` computes it. -/
def ternText (imm : Nat) : String := Id.run do
  let lit (x : String) (bit : Bool) : String := if bit then x else s!"(~~~{x})"
  let mut acc := "0#32"
  for i in [0:8] do
    if imm.testBit i then
      acc := s!"({acc} ||| ({lit "a" (i.testBit 2)} &&& ({lit "b" (i.testBit 1)} &&& {lit "c" (i.testBit 0)})))"
  return acc

/-- Replace every occurrence of each `pats[i]` by `name i`. -/
def replaceAll (txt : String) (pats : List String) (name : Nat → String) : String :=
  (pats.zip (List.range pats.length)).foldl (fun acc (p, i) => acc.replace p (name i)) txt

/-- Variables (numbered) and memory keys of a tree. -/
partial def Hashtree.Asm.E.keys : E → List Key
  | .var k => [k]
  | .const _ => []
  | .add a b | .xor a b | .and a b | .or a b => a.keys ++ b.keys
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.keys
  | .tern _ a b c => a.keys ++ b.keys ++ c.keys

def main (args : List String) : IO Unit := do
  let some kp := kernels.find? (·.key == args.headD "") | IO.println "kernel: x4 | x8 | x16"
  let prog := kp.prog
  let rodata := kp.rodata
  let cnt := kp.count
  let nb := 64 * cnt
  let gns := s!"Hashtree.Gen.{kp.gen}"
  let m0 := mem0s 4 rodata 24
  let cprogs : List Hashtree.Asm.X86Run.Prog := [⟨kp.key, prog, 4, rodata.toArray⟩]
  let dir := args.getD 1 "Gen"
  let split := args.contains "--split"
  let margin := ((args.find? (·.startsWith "--margin=")).map (fun a => (String.mk (a.toList.drop 9)).toNat!)).getD 48
  let pre := ((args.find? (·.startsWith "--pre=")).map (fun a => (String.mk (a.toList.drop 6)).toNat!)).getD 8
  let first := (args.getD 2 "0").toNat!
  let last := (args.getD 3 "1000000").toNat!
  -- Ro.lean: chunked rodata, the fast symbolic initial memory of the slice checks
  let fR := rodata.length / 64 + 1
  let roC := chunksF 64 fR rodata
  IO.FS.writeFile s!"{dir}/Ro.lean" (s!"import Hashtree.Asm.SpecQV\nimport {kp.ns}\n\nopen Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym {kp.ns}\n" ++
    s!"set_option maxRecDepth 200000\n\nnamespace {gns}\n\n" ++
    s!"def roC : List (List Nat) := {listLean (fun (c : List Nat) => toString c) roC}\n\n" ++
    s!"theorem roC_eq : roC = chunksF 64 {fR} rodata := by decide +kernel\n\n" ++
    "/-- The symbolic initial memory of the slice checks (`= mem0s 4 rodata 24`). -/\n" ++
    "def m0q : Addr Lin → Cell E Lin := mem0q 4 roC 24\n\n" ++
    s!"theorem m0q_eq : m0q = mem0s 4 rodata 24 := mem0q_eq 4 rodata 24 roC {fR} roC_eq (by decide +kernel)\n\nend {gns}\n")
  -- cut steps from a concrete run
  let i1 := randInput 11 nb
  let t1 := table i1 cnt
  let mc := Hashtree.Asm.X86Run.mem0 cprogs i1 24
  let isCutQ (q : Q) : Bool := match q with
    | .A _ _ t => t ≥ 1 | .H _ r _ => r ≥ 1 | .W _ r t => r == 0 && t ≥ 16 | _ => false
  -- first step at which a new working variable (A/E, t ≥ 1) appears: the rounds start before it
  let mut firstRound := 0
  let mut s0 := Hashtree.Asm.X86Run.entry false cnt 24
  let mut k0 := 0
  while !s0.halted && k0 < 1000000 && firstRound == 0 do
    s0 := run prog 4 mc (fun _ => false) 1 s0
    k0 := k0 + 1
    for i in [0:32] do
      if (t1.getD ((s0.getV i).getD 0 0) []).any (fun q => match q with | .A _ _ t | .E _ _ t => t ≥ 1 | _ => false) then
        firstRound := k0
  let mut cuts : List Nat := []
  let mut s := Hashtree.Asm.X86Run.entry false cnt 24
  let mut k := 0
  let mut seen : Std.HashSet Q := {}
  while !s.halted && k < 1000000 do
    let s' := run prog 4 mc (fun _ => false) 1 s
    k := k + 1
    let mut hit := false
    for i in [0:32] do
      let v := (s'.getV i).getD 0 0
      let newQ := (t1.getD v []).filter (fun q => isCutQ q && !seen.contains q)
      if v != (s.getV i).getD 0 0 && !newQ.isEmpty then
        hit := true
        seen := newQ.foldl (fun acc q => acc.insert q) seen
        if args.contains "--why" then IO.println s!"cut@{k} pc {s.pc} v{i} {(t1.getD v []).filter isCutQ}"
    s := s'
    -- before the rounds (input load / transpose: every lane holds an input word) cut every
    -- `pre` instructions, so the byte-shuffle trees stay small
    let preRounds := k + margin ≤ firstRound
    let lastCut := cuts.getLastD 0
    if hit || s.halted || (preRounds && k - lastCut ≥ pre) then cuts := cuts ++ [k]
  IO.println s!"{k} steps, {cuts.length} cuts, halted {s.halted} tail {s.tail} err {s.err}"
  -- concrete runs on two inputs, labels at each cut
  let i2 := randInput 22 nb
  let t2 := table i2 cnt
  let m1 := Hashtree.Asm.X86Run.mem0 cprogs i1 24
  let m2 := Hashtree.Asm.X86Run.mem0 cprogs i2 24
  let mut c1 := Hashtree.Asm.X86Run.entry false cnt 24
  let mut c2 := Hashtree.Asm.X86Run.entry false cnt 24
  let mut K := entryS 24
  let mut prev := 0
  let mut chosen : List (Nat × Q) := []
  let mut stepsList : List Nat := []
  let mut orcs : List (List Nat × String) := []
  let mut c := 0
  let mut shapes : Std.HashMap String Nat := {}
  let mut shapeText := ""
  let mut terns : List Nat := []
  for cut in cuts do
    let n := cut - prev
    -- the branches this slice takes on the concrete run (the symbolic run must follow them)
    let mut taken : List Nat := []
    let mut cs := c1
    for _ in [0:n] do
      let pc0 := cs.pc
      let isBr := match prog[pc0]? with | some (.jcc _ _) | some (.jccTail _ _) => true | _ => false
      cs := run prog 4 m1 (fun _ => false) 1 cs
      if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
    let orc : Nat → Bool := fun pc => taken.contains pc
    let orcT := s!"(fun pc => decide (pc ∈ ({taken} : List Nat)))"
    orcs := orcs ++ [(taken, orcT)]
    let R := run prog 4 m0 orc n K
    let K' := abstract R
    c1 := run prog 4 m1 (fun _ => false) n c1
    c2 := run prog 4 m2 (fun _ => false) n c2
    let labs' := cutLabels t1 t2 K' c1 c2 (args.contains "--keep-shadowed")
    -- the next cut's chosen labels: per labelled variable, the first label derivable from this cut's
    let mut chosen' : List (Nat × Q) := []
    let mut lemmas := ""
    let mut trees : List (Nat × E) := []
    let mut calls : List String := []
    for (id, qs) in labs' do
      match treeAt R id with
      | none => pure ()
      | some t =>
        let keys := t.keys.eraseDups
        let hyps := keys.filterMap fun key => match key with
          | .n v => (chosen.findIdx? (·.1 == v)).map fun k => (v, k, (chosen[k]!).2)
          | .m _ _ => none
        let atoms := hyps.map (·.2.2)
        let unl := keys.filter fun key => match key with
          | .n v => !(chosen.any (·.1 == v))
          | .m _ _ => false
        if !unl.isEmpty then IO.println s!"  slice {c}: lane {id} {qs} refers to unlabelled {unl.map Key.toLean}"
        else do
          let mkeys := keys.filterMap fun key => match key with
            | .m 1 l => if l.c = [1] then some l.k else none
            | _ => none
          let bytes := !mkeys.isEmpty
          -- a copied / unchanged lane: its tree is a variable of the previous cut with the same label
          let copyOf : Option (Nat × Q) := match t with
            | .var (.n v) => match chosen.findIdx? (·.1 == v) with
              | some kk => if qs.contains (chosen[kk]!).2 then some (kk, (chosen[kk]!).2) else none
              | none => none
            | _ => none
          match copyOf with
          | some (kk, q) =>
            chosen' := chosen' ++ [(id, q)]
            trees := trees ++ [(id, t)]
            calls := calls ++ [s!"h{kk}"]
          | none =>
          -- input-independent quantities label a variable lane only by accident (e.g. a shifted
          -- temporary equal to 0x80000000 on both runs): such a lane would hold a constant tree
          let closedQ (q : Q) : Bool := match q with
            | .W _ r _ | .KW _ r _ | .M1 _ r _ | .M2 _ r _ => r == 1 | .H _ r _ => r == 0 | _ => false
          let qs := if keys.isEmpty then qs else qs.filter (!closedQ ·)
          match qs.find? (fun q => (derive atoms bytes q 40).isSome) with
          | none => pure ()
          | some q =>
            let eqs := (derive atoms bytes q 40).getD []
            chosen' := chosen' ++ [(id, q)]
            trees := trees ++ [(id, t)]
            let eqs := eqs.eraseDups
            -- closed values become parameters (bv_decide then sees only variables)
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
            -- the lane lemma is an instance of a shape lemma over plain words (lanes of one round
            -- and rounds of one kind share it): env terms → x, spec quantities → y, input bytes → z
            let wText := cvals.foldl (fun (acc : String) v => acc.replace s!"({v} : W32)" (pName v)) t.toW
            let hypW := String.join (hyps.map fun (v, _, q1) => s!"\n    (_ : env (.n {v}) = {vq q1})")
            let body := hypW ++ mArgs ++ eqArgs ++ s!" :\n    {wText} = {vq q}"
            let xs := (keys.map fun key => s!"env {key.toLean}").eraseDups
            let ys := ((hyps.map (·.2.2)) ++ (eqs.flatMap (·.vs)) ++ [q]).eraseDups.map vq
            let zs := (mkeys.map fun o => s!"(inp {o.toNat})") ++
              (eqs.flatMap fun e => if e.proof.startsWith "(qR " then
                (match (e.stmt.splitOn "(inp ").drop 1 with
                  | l => l.map fun r => s!"(inp {(r.splitOn ")").head!})") else [])
            let zs := zs.eraseDups
            let canon := replaceAll (replaceAll (replaceAll body xs (s!"x{·}")) ys (s!"y{·}")) zs (s!"z{·}")
            let key := s!"{cvals.length}|{canon}"
            let mut hIdx := shapes.size
            match shapes.get? key with
            | some h => hIdx := h
            | none =>
              shapes := shapes.insert key hIdx
              let ps := (if xs.isEmpty then "" else s!" ({" ".intercalate ((List.range xs.length).map (s!"x{·}"))} : W32)") ++
                (if ys.isEmpty then "" else s!" ({" ".intercalate ((List.range ys.length).map (s!"y{·}"))} : Word)") ++
                (if zs.isEmpty then "" else s!" ({" ".intercalate ((List.range zs.length).map (s!"z{·}"))} : Byte)") ++ kArgs
              let tl := t.terns.eraseDups
              terns := (terns ++ tl).eraseDups
              let tSimp := String.join (tl.map (s!", ternW_{·}"))
              shapeText := shapeText ++ s!"theorem shape{hIdx}{ps}{canon} := by\n" ++
                s!"  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap{tSimp}]\n" ++
                "  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })\n\n"
            let nh := hyps.length + mkeys.length + eqs.length
            let hNames := String.join ((List.range nh).map (s!" h{·}"))
            let hypN := String.join ((hyps.zip (List.range hyps.length)).map fun ((v, _, q1), i) => s!"\n    (h{i} : env (.n {v}) = {vq q1})")
            let mN := String.join ((mkeys.zip (List.range mkeys.length)).map fun (o, i) =>
              s!"\n    (h{hyps.length + i} : env (.m 1 (⟨{o}, [1]⟩ : Lin)) = (inp {o.toNat}).zeroExtend 32)")
            let eN := String.join ((eqs.zip (List.range eqs.length)).map fun (e, i) => s!"\n    (h{hyps.length + mkeys.length + i} : {stmtOf e})")
            let actuals := String.join ((xs ++ ys ++ zs).map (s!" ({·})")) ++ String.join (cvals.map fun v => s!" {pName v}")
            lemmas := lemmas ++ s!"theorem core{c}_{id} (V : Q → Word) (inp : Nat → Byte) (env : Key → W32){kArgs}{hypN}{mN}{eN} :\n" ++
              s!"    E.eval env {tText} = {vq q} :=\n  shape{hIdx}{actuals}{hNames}\n\n"
            let callArgs := String.join (cvals.map fun v => s!" {v}#32") ++
              String.join (hyps.map fun (_, k, _) => s!" h{k}") ++
              String.join (mkeys.map fun o => s!" (hm {o.toNat} (by decide))") ++
              String.join (eqs.map fun e => s!" {e.proof}")
            calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{callArgs}"]
    if first ≤ c ∧ c ≤ last then
      let kName := if c = 0 then "(entryS 24)" else s!"K{c}"
      -- one projection per entry (`obtain` with one big pattern is quadratic: 420 s for 344 entries)
      let pat := String.join ((List.range chosen.length).map fun k => s!"  have h{k} := hI.1; have hI := hI.2\n")
      let tv := calls.foldr (fun cl acc => s!"(And.intro ⟨rfl, {cl}⟩\n      {acc})") "trivial"
      let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L{c}) (hm : HMem {nb} inp env) :\n" ++
        s!"    InvC inp (envAbs env (run prog 4 m0q {orcT} {n} {kName})) L{c + 1} := by\n" ++ pat ++
        s!"  exact invC_of_trees inp env _ T{c} L{c + 1} (slice_trees_mem prog 4 _ _ {n} {kName} K{c + 1} T{c} slice{c} env)\n      {tv}\n\n"
      let hdr := s!"\nopen Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym {kp.ns} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
        s!"set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\nnamespace {gns}\n\n"
      let defs := (if c = 0 then "def L0 : List (Nat × Q) := []\n\n" else "") ++
        s!"def K{c + 1} : State E Lin := {K'.toLean}\n\n" ++
        s!"def L{c + 1} : List (Nat × Q) := {listLean (fun (p : Nat × Q) => s!"({p.1}, {qText p.2})") chosen'}\n\n" ++
        s!"def T{c} : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") trees}\n\n"
      let proofs := s!"theorem slice{c} : sliceCheck prog 4 m0q {orcT} {n} {kName} K{c + 1} T{c} = true := by\n  decide +kernel\n\n" ++
        lemmas ++ step ++ s!"end {gns}\n"
      let base := s!"import Hashtree.Asm.Chain\nimport Hashtree.Asm.SpecQV\nimport {kp.ns}\n"
      -- split: D{c} holds the cut's definitions only; P{c} the proofs, independent of P{c-1}
      if split then IO.FS.writeFile s!"{dir}/D{c}.lean" (base ++ hdr ++ defs ++ s!"end {gns}\n")
      let body := if split then
          base ++ s!"import {gns}.Ro\nimport {gns}.Shapes\nimport {gns}.D{c}\n" ++
            (if c = 0 then "" else s!"import {gns}.D{c - 1}\n") ++ hdr ++ proofs
        else
          base ++ (if c = 0 then s!"import {gns}.Ro\nimport {gns}.Shapes\n" else s!"import {gns}.P{c - 1}\n") ++
            hdr ++ defs ++ proofs
      IO.FS.writeFile s!"{dir}/P{c}.lean" body
      IO.println s!"slice {c}: {n} steps, {labs'.length} labelled, {chosen'.length} proved, {calls.filter (·.startsWith "core") |>.length} lemmas"
    chosen := chosen'
    stepsList := stepsList ++ [n]
    K := K'
    prev := cut
    c := c + 1
  IO.println s!"steps per slice: {stepsList}"
  IO.FS.writeFile s!"{dir}/Shapes.lean" (s!"import Hashtree.Asm.Chain\n\nopen Hashtree.Asm Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    s!"set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\nnamespace {gns}\n\n" ++
    "/-! Shape lemmas: the lane lemmas of the slices are instances (lanes of one round, and rounds of\none kind, share a shape). -/\n\n" ++
    String.join (terns.map fun i => s!"theorem ternW_{i} (a b c : W32) : ternW {i} a b c = {ternText i} := by\n  rfl\n\n") ++
    shapeText ++ s!"end {gns}\n")
  IO.println s!"shapes: {shapes.size}"
  -- Final.lean: chain everything for this call (count 2)
  let C := stepsList.length
  let kn (j : Nat) : String := if j = 0 then "(entryS 24)" else s!"K{j}"
  let finImports := if split then String.join ((List.range C).map (s!"import {gns}.P{·}\n")) else s!"import {gns}.P{C - 1}\n"
  let mut fin := s!"{finImports}\nopen Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym {kp.ns} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    s!"set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {gns}\n\n" ++
    "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) (run prog 4 m0q {(orcs[cc]!).2} {stepsList[cc]!} {kn cc})\n"
  -- invariant chain
  fin := fin ++ s!"\ntheorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem {nb} inp env0) :\n    InvC inp (E{C} env0) L{C} := by\n" ++
    "  have i0 : InvC inp (E0 env0) L0 := True.intro\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have i{cc + 1} : InvC inp (E{cc + 1} env0) L{cc + 1} := step{cc} inp (E{cc} env0) i{cc} hm\n"
  fin := fin ++ s!"  exact i{C}\n\n"
  -- recorded conditions: one lemma per distinct list
  let mut asms : List (List (Cond Lin × Bool)) := []
  let mut asmIdx : List Nat := []
  let mut Kc := entryS 24
  let mut prev2 := 0
  let mut finalK := entryS 24
  for cc in [0:C] do
    let R := run prog 4 m0 (fun pc => (orcs[cc]!).1.contains pc) stepsList[cc]! Kc
    let K' := abstract R
    let A := K'.assume
    match asms.findIdx? (fun x => decide (x = A)) with
    | some j => asmIdx := asmIdx ++ [j]
    | none => asms := asms ++ [A]; asmIdx := asmIdx ++ [asms.length - 1]
    Kc := K'
    finalK := K'
  for j in [0:asms.length] do
    let A := asms[j]!
    let aText := listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") A
    fin := fin ++ s!"def A{j} : List (Cond Lin × Bool) := {aText}\n" ++
      s!"theorem asm{j} (σ : Nat → Int) (hσ : σ 2 = {cnt}) : ∀ p ∈ A{j}, (mapCond σ p.1).decideC = some p.2 := by\n" ++
      s!"  intro p hp\n  simp only [A{j}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
      (if A.isEmpty then "  exact absurd hp id\n\n" else
        s!"  rcases hp with {" | ".intercalate ((List.range A.length).map fun _ => "rfl")} <;>\n" ++
        "    simp [mapCond, Cond.decideC, Lin.eval, dotC, hσ, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]\n\n")
  -- the concrete run
  let sumText : List Nat → String := fun l => l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""
  fin := fin ++ "theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)\n" ++
    s!"    (h0 : Mem0Rel env0 σ (mem0s 4 rodata 24) mem0c) (hσ : σ 2 = {cnt}) :\n" ++
    s!"    run prog 4 mem0c orcC ({sumText stepsList}) (mapState env0 σ (entryS 24)) = mapState (E{C} env0) σ K{C} := by\n" ++
    "  have m0 : Mem0Rel env0 σ m0q mem0c := by rw [m0q_eq]; exact h0\n" ++
    "  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ m0q mem0c := mem0Rel_envAbs _ σ _ mem0c kq m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let sl := s!"(slice_sound {envc} σ m0q mem0c m{cc} prog 4 {(orcs[cc]!).2} orcC {stepsList[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} rfl (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then "mapState env0 σ (entryS 24)" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : run prog 4 mem0c orcC {stepsList[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {sl}\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [run_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  -- outputs
  let mut cases := ""
  for n in [0:cnt] do
    for i in [0:8] do
      for b in [0:4] do
        let o := 32 * n + 4 * i + b
        match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
        | .ok (some (.dat (.var (.n id)) b')) =>
          match chosen.findIdx? (·.1 == id) with
          | some kk =>
            if (chosen[kk]!).2 == .HB n i && b' == b then
              cases := cases ++ s!"  | {n}, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), outCell_sound _ σ K{C} {o} {id} {b'} (by decide),\n" ++
                s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB n i)} from g{kk},\n" ++
                s!"        qHB, byte_bswap _ {b} (by decide), node_byte inp {n} {i} {b} (by decide) (by decide)]; rfl⟩\n"
            else cases := cases ++ s!"  -- output {o}: unexpected label {qText (chosen[kk]!).2} / byte {b'}\n"
          | none => cases := cases ++ s!"  -- output {o}: no label\n"
        | _ => cases := cases ++ s!"  -- output {o}: no stored lane\n"
  fin := fin ++ s!"\n/-- {kp.desc}: every output byte is the SHA-256 byte of its block. -/\n" ++
    "theorem out_final (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)\n" ++
    s!"    (orcC : Nat → Bool) (hw : WfMem 4 rodata 24 mem0c) (he : EnvMem env0 σ mem0c) (hσ : σ 2 = {cnt}) (hm : HMem {nb} inp env0) :\n" ++
    s!"    ∀ n i b, n < {cnt} → i < 8 → b < 4 → ∃ x,\n" ++
    s!"      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)\n        (run prog 4 mem0c orcC ({sumText stepsList}) (mapState env0 σ (entryS 24))).mem = .ok (some (.dat x b)) ∧\n" ++
    "      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by\n" ++
    "  rw [run_final env0 σ mem0c orcC (mem0Rel_of_wf 4 rodata 24 env0 σ mem0c hw he) hσ]\n" ++
    "  have hF := inv_final inp env0 hm\n" ++
    String.join ((List.range chosen.length).map fun k => s!"  have g{k} := hF.1; have hF := hF.2\n") ++
    "  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n" ++ cases ++
    s!"  | _ + {cnt}, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\nend {gns}\n"
  IO.FS.writeFile s!"{dir}/Final.lean" fin
  IO.println "wrote Final.lean"
