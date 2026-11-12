import Hashtree.Asm.Print
import Hashtree.Asm.Slice
import Hashtree.Asm.Chain
import Hashtree.Asm.X86Sym
import Hashtree.Asm.Subst
import Hashtree.Asm.Scan
import Hashtree.Kernels.X86.Shani

/-!
`x86loop <outdir> <segment>`: generate the proof files of one segment of the shani_x2 kernel
for every count.  Segments start at the entry or at the loop-head cut `KH` (pc 4, flags as
fresh symbols 3, 4): `head` (the prologue, `KH`, its instance check), `it` (one 2-block iteration
back to the loop head), `t1` (count 1: the 1-block tail), `t0` (count 0: return).
-/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.Scan
open Hashtree.Kernels.X86.Shani

def m0 := mem0s 4 rodata 24
def cprogs : List Hashtree.Asm.X86Run.Prog := [⟨"hashtree_sha256_shani_x2", prog, 4, rodata.toArray⟩]

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
def cutLabels (t1 t2 : Std.HashMap W32 (List Q)) (K : State E Lin) (s1 s2 : Hashtree.Asm.X86Run.CS) :
    List (Nat × List Q) := Id.run do
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


def ns : String := "Hashtree.Gen.ShaniL"
def opens : String :=
  "open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.Shani Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
  "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"

/-- The concrete state at the loop head of a call with `count` blocks (after the prologue). -/
def headC (m : Addr Int → Cell W32 Int) (count : Nat) : Hashtree.Asm.X86Run.CS :=
  run prog 4 m (fun _ => false) 4 (Hashtree.Asm.X86Run.entry false count 24)

def symHead : State E Lin × State E Lin :=
  let KP := abstract (run prog 4 m0 (fun _ => false) 4 (entryS 24))
  (KP, { KP with flags := some (Lin.sym 3, Lin.sym 4) })

def linLean (l : Lin) : String := l.toLean

/-- Taken branches of a concrete run of `n` steps. -/
def takenOf (m : Addr Int → Cell W32 Int) (n : Nat) (c : Hashtree.Asm.X86Run.CS) : List Nat := Id.run do
  let mut taken : List Nat := []
  let mut cs := c
  for _ in [0:n] do
    let pc0 := cs.pc
    let isBr := match prog[pc0]? with | some (.jcc _ _) | some (.jccTail _ _) => true | _ => false
    cs := run prog 4 m (fun _ => false) 1 cs
    if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
  return taken

/-- Generate one segment from the symbolic cut `K0` (named `k0Name`) over `total` steps; concrete
runs `c1`/`c2` (memories `m1`/`m2`, label tables `t1`/`t2`) choose cuts, branches and labels;
`nb` output blocks; `hsig`: the count hypothesis; returns the final cut. -/
def genSeg (dir seg k0Name : String) (K0 : State E Lin) (c1i c2i : Hashtree.Asm.X86Run.CS)
    (m1 m2 : Addr Int → Cell W32 Int) (t1 t2 : Std.HashMap W32 (List Q)) (total nb : Nat)
    (hsig : String) : IO (State E Lin) := do
  let sns := s!"{ns}.{seg}"
  -- cuts: before and after every sha256rnds2, and at the end
  let mut cuts : List Nat := []
  let mut s := c1i
  for k in [0:total] do
    let isR := match prog[s.pc]? with | some (.sha256rnds2 _ _) => true | _ => false
    s := run prog 4 m1 (fun _ => false) 1 s
    let nextR := match prog[s.pc]? with | some (.sha256rnds2 _ _) => true | _ => false
    if isR || nextR || k + 1 = total then cuts := cuts ++ [k + 1]
  let mut c1 := c1i
  let mut c2 := c2i
  let mut K := K0
  let mut prev := 0
  let mut chosen : List (Nat × Q) := []
  let mut stepsList : List Nat := []
  let mut orcs : List (List Nat × String) := []
  let mut asms : List (List (Cond Lin × Bool)) := []
  let mut asmIdx : List Nat := []
  let mut c := 0
  for cut in cuts do
    let n := cut - prev
    let taken := takenOf m1 n c1
    let orc : Nat → Bool := fun pc => taken.contains pc
    let orcT := s!"(fun pc => decide (pc ∈ ({taken} : List Nat)))"
    orcs := orcs ++ [(taken, orcT)]
    let R := run prog 4 m0 orc n K
    if R.err.isSome then
      IO.println s!"{seg} slice {c}: symbolic run failed: {R.err}"
    let K' := abstract R
    let A := K'.assume
    match asms.findIdx? (fun x => decide (x = A)) with
    | some j => asmIdx := asmIdx ++ [j]
    | none => asms := asms ++ [A]; asmIdx := asmIdx ++ [asms.length - 1]
    c1 := run prog 4 m1 (fun _ => false) n c1
    c2 := run prog 4 m2 (fun _ => false) n c2
    let labs' := cutLabels t1 t2 K' c1 c2
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
            "  simp_all only [E.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]\n  all_goals bv_decide (timeout := 600)\n\n"
          let callArgs := String.join (cvals.map fun v => s!" {v}#32") ++
            String.join (hyps.map fun (_, k, _) => s!" (inv_get hI {k} (by decide))") ++
            String.join (mkeys.map fun o => s!" (hm {o.toNat} (by decide))") ++
            String.join (eqs.map fun e => s!" {e.proof}")
          calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{callArgs}"]
    -- callee-saved registers untouched in this slice: tracked as their own variables
    for id in calleeIds do
      if treeAt R id == some (.var (.n id)) && !(trees.any (·.1 == id)) then
        trees := trees ++ [(id, .var (.n id))]
    let keepAll := calleeIds.all fun id => trees.contains (id, .var (.n id))
    if !keepAll then IO.println s!"{seg} slice {c}: a callee-saved register is not kept"
    let kName := if c = 0 then k0Name else s!"K{c}"
    let cases := String.join ((List.range chosen'.length).map fun k =>
      s!"  | {k}, _ => exact (slice_trees prog 4 _ _ {n} {kName} K{c + 1} T{c} slice{c} env {k} (by decide)).trans ({calls[k]!})\n")
    let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : Inv L{c} inp env) (hm : HMem 128 inp env) :\n" ++
      s!"    Inv L{c + 1} inp (envAbs env (run prog 4 (mem0s 4 rodata 24) {orcT} {n} {kName})) := by\n" ++
      s!"  apply inv_of_get\n  intro k hk\n  match k, hk with\n" ++ cases ++
      s!"  | _ + {chosen'.length}, hk => simp only [L{c + 1}, List.length_cons, List.length_nil] at hk; omega\n\n"
    let imports := "import Hashtree.Asm.Chain\nimport Hashtree.Asm.X86Sym\nimport Hashtree.Kernels.X86.Shani\n" ++
      (if c = 0 then s!"import {ns}.Head\n" else s!"import {sns}.P{c - 1}\n")
    let body := imports ++ "\n" ++ opens ++ s!"namespace {sns}\nopen {ns}\n\n" ++
      (if c = 0 then "def L0 : List (Nat × Q) := []\n\n" else "") ++
      s!"def K{c + 1} : State E Lin := {K'.toLean}\n\n" ++
      s!"def L{c + 1} : List (Nat × Q) := {listLean (fun (p : Nat × Q) => s!"({p.1}, {qText p.2})") chosen'}\n\n" ++
      s!"def T{c} : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") trees}\n\n" ++
      s!"theorem slice{c} : sliceCheck prog 4 (mem0s 4 rodata 24) {orcT} {n} {kName} K{c + 1} T{c} = true := by\n  decide +kernel\n\n" ++
      s!"theorem keep{c} : ∀ id ∈ calleeIds, (id, E.var (.n id)) ∈ T{c} := by decide\n\n" ++
      lemmas ++ step ++ s!"end {sns}\n"
    IO.FS.createDirAll s!"{dir}/{seg}"
    IO.FS.writeFile s!"{dir}/{seg}/P{c}.lean" body
    IO.println s!"{seg} slice {c}: {n} steps, {labs'.length} labelled, {chosen'.length} proved"
    chosen := chosen'
    stepsList := stepsList ++ [n]
    K := K'
    prev := cut
    c := c + 1
  IO.println s!"{seg} steps per slice: {stepsList}"
  -- Final.lean of the segment
  let C := stepsList.length
  let kn (j : Nat) : String := if j = 0 then k0Name else s!"K{j}"
  let sumText : List Nat → String := fun l => l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""
  let N := stepsList.foldl (· + ·) 0
  let mut fin := s!"import {sns}.P{C - 1}\n\n" ++ opens ++ s!"namespace {sns}\nopen {ns}\n\n" ++
    "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) (run prog 4 (mem0s 4 rodata 24) {(orcs[cc]!).2} {stepsList[cc]!} {kn cc})\n"
  fin := fin ++ s!"\n/-- The final cut. -/\ndef KF : State E Lin := K{C}\ndef EF (env0 : Key → W32) : Key → W32 := E{C} env0\n\n"
  fin := fin ++ s!"theorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem 128 inp env0) :\n    Inv L{C} inp (E{C} env0) := by\n" ++
    "  have i0 : Inv L0 inp (E0 env0) := fun p hp => by cases hp\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have i{cc + 1} : Inv L{cc + 1} inp (E{cc + 1} env0) := step{cc} inp (E{cc} env0) i{cc} hm\n"
  fin := fin ++ s!"  exact i{C}\n\n"
  for j in [0:asms.length] do
    let A := asms[j]!
    let aText := listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") A
    fin := fin ++ s!"def A{j} : List (Cond Lin × Bool) := {aText}\n" ++
      s!"theorem asm{j} (σ : Nat → Int) {hsig} : ∀ p ∈ A{j}, (mapCond σ p.1).decideC = some p.2 := by\n" ++
      s!"  intro p hp\n  simp only [A{j}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
      (if A.isEmpty then "  exact absurd hp id\n\n" else
        s!"  rcases hp with {" | ".intercalate ((List.range A.length).map fun _ => "rfl")} <;>\n" ++
        "    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;> omega\n\n")
  fin := fin ++ s!"/-- The steps of the segment. -/\ndef NS : Nat := {sumText stepsList}\n\n"
  -- callee-saved registers keep their values
  fin := fin ++ s!"theorem keep_final (env0 : Key → W32) (id : Nat) (hid : id ∈ calleeIds) : E{C} env0 (.n id) = env0 (.n id) := by\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have k{cc} : E{cc + 1} env0 (.n id) = E{cc} env0 (.n id) := slice_keep _ _ _ _ _ _ _ _ slice{cc} (E{cc} env0) id (keep{cc} id hid)\n"
  fin := fin ++ "  rw [" ++ ", ".intercalate ((List.range C).reverse.map fun cc => s!"k{cc}") ++ "]; rfl\n\n"
  fin := fin ++ "theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)\n" ++
    s!"    (h0 : Mem0Rel env0 σ (mem0s 4 rodata 24) mem0c) {hsig} :\n" ++
    s!"    run prog 4 mem0c orcC NS (mapState env0 σ {k0Name}) = mapState (E{C} env0) σ K{C} := by\n" ++
    "  have m0 : Mem0Rel env0 σ (mem0s 4 rodata 24) mem0c := h0\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ (mem0s 4 rodata 24) mem0c := mem0Rel_envAbs _ σ _ mem0c (mem0s_keyed 4 rodata 24) m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let sl := s!"(slice_sound {envc} σ (mem0s 4 rodata 24) mem0c m{cc} prog 4 {(orcs[cc]!).2} orcC {stepsList[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} rfl (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then s!"mapState env0 σ {k0Name}" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : run prog 4 mem0c orcC {stepsList[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {sl}\n"
  fin := fin ++ "  show run prog 4 mem0c orcC (" ++ sumText stepsList ++ s!") (mapState env0 σ {k0Name}) = _\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [run_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  -- outputs at the final cut
  if nb > 0 then
    let mut cases := ""
    let mut missing := 0
    for n in [0:nb] do
      for i in [0:8] do
        for b in [0:4] do
          let o := 32 * n + 4 * i + b
          let ok := match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) K.mem with
            | .ok (some (.dat (.var (.n id)) b')) =>
              match chosen.findIdx? (·.1 == id) with
              | some kk =>
                if (chosen[kk]!).2 == .HB n i && b' == b then
                  some (s!"  | {n}, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), outCell_sound _ σ K{C} {o} {id} {b'} (by decide),\n" ++
                    s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB n i)} from inv_get (inv_final inp env0 hm) {kk} (by decide),\n" ++
                    s!"        qHB, byte_bswap _ {b} (by decide), node_byte inp {n} {i} {b} (by decide) (by decide)]; rfl⟩\n")
                else none
              | none => none
            | _ => none
          match ok with
          | some t => cases := cases ++ t
          | none => missing := missing + 1; cases := cases ++ s!"  -- output {o}: MISSING\n"
    IO.println s!"{seg}: {missing} output bytes without proof"
    fin := fin ++ s!"\n/-- Every output byte at the final cut is the SHA-256 byte of its block. -/\n" ++
      "theorem out_final (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (hm : HMem 128 inp env0) :\n" ++
      s!"    ∀ n i b, n < {nb} → i < 8 → b < 4 → ∃ x,\n" ++
      s!"      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) (mapState (E{C} env0) σ K{C}).mem = .ok (some (.dat x b)) ∧\n" ++
      "      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by\n" ++
      "  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n" ++ cases ++
      s!"  | _ + {nb}, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n"
  -- the log holds exactly the output bytes of this segment
  fin := fin ++ s!"/-- The log holds output bytes of this segment and bytes of the stack frame below the entry stack. -/\n" ++
    s!"theorem log_final : ∀ p ∈ K{C}.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < {32 * nb}) ∨\n" ++
    "    (p.1.region = rStack ∧ p.1.off.c = [] ∧ -64 ≤ p.1.off.k ∧ p.1.off.k < 24) := by\n  decide\n\n"
  fin := fin ++ s!"end {sns}\n"
  IO.FS.writeFile s!"{dir}/{seg}/Final.lean" fin
  IO.println s!"wrote {seg}/Final.lean ({N} steps)"
  return K

def main (args : List String) : IO Unit := do
  let dir := args.headD "Gen"
  let seg := args.getD 1 "head"
  let (KP, KH) := symHead
  let i1 := randInput 11 128
  let i2 := randInput 22 128
  let m1 := Hashtree.Asm.X86Run.mem0 cprogs i1 24
  let m2 := Hashtree.Asm.X86Run.mem0 cprogs i2 24
  match seg with
  | "head" =>
    let flagsText := match KP.flags with
      | some (a, b) => s!"[Lin.sym 0, Lin.sym 1, Lin.sym 2, {linLean a}, {linLean b}]"
      | none => "[]"
    let body := "import Hashtree.Asm.Chain\nimport Hashtree.Asm.X86Sym\nimport Hashtree.Asm.Subst\nimport Hashtree.Kernels.X86.Shani\n\n" ++ opens ++
      s!"namespace {ns}\n\n" ++
      "/-- The loop-head cut (pc 4): the prologue's cut with the flags as fresh symbols 3, 4. -/\n" ++
      s!"def KH : State E Lin := {KH.toLean}\n\n" ++
      s!"def KP : State E Lin := {KP.toLean}\n\n" ++
      s!"def tauP : List Lin := {flagsText}\n\n" ++
      "def TP : List (Nat × E) := calleeIds.map (fun id => (id, E.var (.n id)))\n\n" ++
      "theorem slicePro : sliceCheck prog 4 (mem0s 4 rodata 24) (fun _ => false) 4 (entryS 24) KP TP = true := by\n  decide +kernel\n\n" ++
      "theorem keepP : ∀ id ∈ calleeIds, (id, E.var (.n id)) ∈ TP := by decide\n\n" ++
      "theorem KP_inst : KP = KH.substL tauP := by decide\n\n" ++
      "theorem KH_err : KH.err = none := rfl\n\n" ++
      s!"end {ns}\n"
    IO.FS.createDirAll dir
    IO.FS.writeFile s!"{dir}/Head.lean" body
    IO.println "wrote Head.lean"
  | "it" =>
    let c1 := headC m1 2
    let c2 := headC m2 2
    -- steps until the loop head again
    let mut s := run prog 4 m1 (fun _ => false) 1 c1
    let mut k := 1
    while s.pc != 4 && k < 10000 do
      s := run prog 4 m1 (fun _ => false) 1 s
      k := k + 1
    let KE ← genSeg dir "It" "KH" KH c1 c2 m1 m2 (table i1 2) (table i2 2) k 2 "(hσ : 2 ≤ σ 2)"
    -- the shape check: the end cut is the loop-head cut under shifted symbols
    let off (g : Nat) : String := match KE.getG g with | .ptr a => linLean a.off | _ => "?"
    let fl := match KE.flags with | some (a, b) => s!"{linLean a}, {linLean b}" | none => "?, ?"
    let tauE := s!"[{off 6}, {off 7}, {off 2}, {fl}]"
    let shape := s!"import {ns}.It.Final\nimport Hashtree.Asm.X86Loop\n\n" ++ opens ++ s!"namespace {ns}.It\nopen {ns}\n\n" ++
      s!"def tauE : List Lin := {tauE}\n\n" ++
      "/-- The end cut's lanes are the loop head's, or constants where the loop head has variables. -/\n" ++
      "theorem KF_vr : vrRel 0 KH.vr KF.vr = true := by decide\n\n" ++
      "theorem KF_shape : { ({ KF with vr := KH.vr } : State E Lin) with mem := [], assume := [] } = KH.substL tauE := by decide\n\n" ++
      s!"end {ns}.It\n"
    IO.FS.writeFile s!"{dir}/It/Shape.lean" shape
    IO.println s!"tauE = {tauE}"
  | "t1" =>
    let c1 := headC m1 1
    let c2 := headC m2 1
    let mut s := c1
    let mut k := 0
    while !s.halted && k < 10000 do
      s := run prog 4 m1 (fun _ => false) 1 s
      k := k + 1
    let _ ← genSeg dir "T1" "KH" KH c1 c2 m1 m2 (table i1 1) (table i2 1) k 1 "(hσ : σ 2 = 1)"
  | "t0" =>
    let c1 := headC m1 0
    let c2 := headC m2 0
    let mut s := c1
    let mut k := 0
    while !s.halted && k < 10000 do
      s := run prog 4 m1 (fun _ => false) 1 s
      k := k + 1
    let _ ← genSeg dir "T0" "KH" KH c1 c2 m1 m2 (table i1 0) (table i2 0) k 0 "(hσ : σ 2 = 0)"
  | _ => IO.println "segments: head it t1 t0"
