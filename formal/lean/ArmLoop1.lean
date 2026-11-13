import Hashtree.Proofs.ArmGen
import Hashtree.Asm.ArmLoop2

/-!
`armloop1 <kernel> <headPc> <blocks> <dir>`: proof files for the loop segments of an AArch64
kernel whose proof restarts at the loop head.

The head cut is the prologue's cut (`KH0`, its stack log removed) renormalized: the output
pointer `x0` is the fresh symbol 5, the end pointer `x2` the fresh symbol 6, and the input pointer
`x1` stays the entry symbol 0 (the input region is addressed from 0, so its offset is the number of
bytes already consumed).  `KH1` is the same cut with the flags as fresh symbols 3, 4.

Segments (all start at a symbolic cut state, all end at a cut, `T0a`/`T0b` exit immediately):

* `It0` — one iteration from `KH0`, cut relation to `KH1`;
* `It`  — one iteration from `KH1`, cut relation to `KH1`;
* `T0a` — the exit (`σ 6 = σ 5`) from `KH0` (used for count 0);
* `T0b` — the exit (`σ 6 = σ 5`) from `KH1`.

Each segment directory gets `P{c}.lean` (kernel-checked slice, per-lane lemmas, step), `Final.lean`
(the chained run, output-byte lemma, final-state facts) and, for the iteration segments, a
`Shape.lean` (`tauE`, the cut relation to `KH1`).  `Head.lean` holds the states and the prologue's
own slice.
-/

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmSym Hashtree.Asm.Scan

structure Sl where
  n : Nat
  taken : List Nat
  /-- the trees of the labelled values at the cut (`treeAt R id`), kept instead of the whole
  symbolic run state so that successive slices do not retain the run states -/
  trs : List (Nat × E)
  K' : State E Lin
  labs : List (Nat × List Q)

instance : Inhabited Sl := ⟨⟨0, [], [], entryS 0, []⟩⟩

def sumText (l : List Nat) : String :=
  l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""

/-- A concrete register value, for the diagnostics. -/
def cval : Val W32 Int → String
  | .ptr a => s!"ptr({a.region}, {a.off})"
  | .num _ _ => "num"

/-- The branches a concrete run takes in `n` steps. -/
def takenOf (prog : Array Instr) (ro : Region) (m : Addr Int → Cell W32 Int) (n : Nat) (c : CS) :
    List Nat := Id.run do
  let mut taken : List Nat := []
  let mut cs := c
  for _ in [0:n] do
    let pc0 := cs.pc
    let isBr := match prog[pc0]? with | some (.bcc _ _) => true | _ => false
    cs := run prog ro m (fun _ => false) 1 cs
    if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
  return taken

/-- Run from `s` until pc `headPc` (stepping at least once). -/
def toHead (prog : Array Instr) (ro : Region) (m : Addr Int → Cell W32 Int) (headPc : Nat)
    (s : CS) : CS × Nat := Id.run do
  let mut s := run prog ro m (fun _ => false) 1 s
  let mut k := 1
  while s.pc != headPc && !s.halted && k < 1000000 do
    s := run prog ro m (fun _ => false) 1 s
    k := k + 1
  return (s, k)

/-- Run until halted. -/
def toHalt (prog : Array Instr) (ro : Region) (m : Addr Int → Cell W32 Int) (s : CS) : Nat := Id.run do
  let mut s := s
  let mut k := 0
  while !s.halted && k < 1000000 do
    s := run prog ro m (fun _ => false) 1 s
    k := k + 1
  return k

/-- The labels a slice actually keeps: carried from `chosen`, or derived from it.  This mirrors
the per-slice label derivation in `genSeg`, so cut selection can avoid cuts whose invariant would
silently lose labels (which collapses the chain for all later slices). -/
def effLabs (cfg : Cfg) (t1 t2 : Std.HashMap W32 (List Q)) (R K' : State E Lin) (a b : CS)
    (chosen : List (Nat × Q)) : List (Nat × List Q × Q) := Id.run do
  let mut res : List (Nat × List Q × Q) := []
  for (id, qs) in cutLabels t1 t2 K' a b do
    match treeAt R id with
    | some (.var (.n v)) =>
      match chosen.findIdx? (·.1 == v) with
      | some j => if qs.contains (chosen[j]!).2 then res := res ++ [(id, qs, (chosen[j]!).2)]
      | none => pure ()
    | none => pure ()
    | some t =>
      let okKey : Key → Bool
        | .n v => chosen.any (·.1 == v)
        | .m 1 l => l.c = [1] && 0 ≤ l.k
        | .m _ _ => false
      let keys := t.keys.eraseDups
      if keys.all okKey then
        let atoms := keys.filterMap fun key => match key with
          | .n v => (chosen.findIdx? (·.1 == v)).map fun k => (chosen[k]!).2
          | .m _ _ => none
        let bytes := keys.any fun k => match k with
          | .m 1 l => l.c = [1] && 0 ≤ l.k
          | _ => false
        match qs.find? (fun q => (derive atoms bytes q 40).isSome) with
        | some q => res := res ++ [(id, qs, q)]
        | none => pure ()
  return res

/-- Cuts chosen adaptively: the longest slice (at most `maxLen` steps) whose cut state is small,
still produces the same output after perturbation, and carries labels. -/
def adaptiveSlices (cfg : Cfg) (m0s : Addr Lin → Cell E Lin) (K0 : State E Lin) (c1i c2i : CS)
    (m1 m2 : Addr Int → Cell W32 Int) (t1 t2 : Std.HashMap W32 (List Q)) (count total : Nat)
    (out : Array Sl) : IO (Except String (Array Sl × State E Lin × CS × CS × Nat)) := do
  let prog := cfg.prog
  let ro := cfg.ro
  let ref := finishOut prog ro m1 count c1i
  let mut K := K0
  let mut c1 := c1i
  let mut c2 := c2i
  let mut out := out
  let mut pos := 0
  let mut unclean := 0
  let mut chosen : List (Nat × Q) := []
  while !c1.halted && pos < total && unclean < 100 do
    let mut cands : Array (State E Lin × CS × CS) := #[]
    let mut R := K
    let mut a := c1
    let mut b := c2
    for _ in [0:cfg.maxLen] do
      if a.halted then break
      let pc0 := a.pc
      let a' := run prog ro m1 (fun _ => false) 1 a
      let tk := match prog[pc0]? with | some (.bcc _ _) => a'.pc != pc0 + 1 || a'.halted | _ => false
      R := run prog ro m0s (fun pc => pc == pc0 && tk) 1 R
      a := a'
      b := run prog ro m2 (fun _ => false) 1 b
      cands := cands.push (R, a, b)
    -- a candidate that reaches the halt ends the run: prefer a clean cut before it, so that
    -- the final slice is a store-only tail whose trees read the labelled digest values
    let jHalt : Option Nat := cands.findIdx? (fun (_, a, _) => a.halted)
    let jMax := match jHalt with | some h => h | none => cands.size
    let mut pick := match jHalt with | some h => h + 1 | none => cands.size
    let mut found := false
    let mut j := jMax
    while j > 0 && !found do
      let (Rj, aj, bj) := cands[j - 1]!
      if stateSize (cfg.maxSize + 1) Rj > cfg.maxSize then
        pure ()
      else
        let Kj := abstract Rj
        let labs := cutLabels t1 t2 Kj aj bj
        let keep (id : Nat) : Bool := labs.any (·.1 == id)
        if finishOut prog ro m1 count (perturb keep Kj aj 7) == ref &&
            finishOut prog ro m1 count (perturb keep Kj aj 99) == ref then
          found := true; pick := j
      j := j - 1
    if !found && jHalt.isSome then found := true
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
    -- nothing clean within the size bound: keep the longest candidate
    if !found then unclean := unclean + 1
    if cands.isEmpty then
      unclean := unclean + 100
    else
      let (Rp, ap, bp) := cands[pick - 1]!
      let n := pick
      if Rp.err.isSome then
        return .error s!"slice {out.size}: symbolic error {Rp.err} at pc {Rp.pc}"
      let K' := abstract Rp
      let labs0 := cutLabels t1 t2 K' ap bp
      if out.size ≤ 2 && (K'.err.isSome) then
        IO.println s!"cut {out.size}: symbolic error {K'.err} at pc {ap.pc}"
      IO.println s!"  slice {out.size}: n {n} pick {pick} cands {cands.size} labs {labs0.length} tree {Rp.pc}"
      let trs := labs0.filterMap fun (id, _) => (treeAt Rp id).map fun t => (id, t)
      out := out.push ⟨n, takenOf prog ro m1 n c1, trs, K', labs0⟩
      K := K'
      c1 := ap
      c2 := bp
      pos := pos + pick
  return .ok (out, K, c1, c2, unclean)

/-- The sliced symbolic run of a segment: cuts from the concrete run `c1`. -/
def segRun (cfg : Cfg) (m0s : Addr Lin → Cell E Lin) (K0 : State E Lin) (c1i c2i : CS)
    (m1 m2 : Addr Int → Cell W32 Int) (t1 t2 : Std.HashMap W32 (List Q)) (total count : Nat) :
    IO (Except String (Array Sl)) := do
  let prog := cfg.prog
  let ro := cfg.ro
  if cfg.adaptive then
    let r ← adaptiveSlices cfg m0s K0 c1i c2i m1 m2 t1 t2 count total #[]
    match r with
    | .error e => return .error e
    | .ok (out, _, _, _, unclean) =>
      IO.println s!"  adaptive: {out.size} slices, {unclean} unclean"
      return .ok out
  let mut c1 := c1i
  let mut c2 := c2i
  let mut K := K0
  let mut prev := 0
  let mut cuts : List Nat := []
  let mut s := c1i
  let mut last := 0
  for k in [0:total] do
    let cur := prog[s.pc]?
    s := run prog ro m1 (fun _ => false) 1 s
    if cfg.cutAt cur prog[s.pc]? || s.halted || k + 1 = total || k + 1 - last ≥ 400 then
      cuts := cuts ++ [k + 1]
      last := k + 1
  let mut out : Array Sl := #[]
  for cut in cuts do
    let n := cut - prev
    let taken := takenOf prog ro m1 n c1
    let R := run prog ro m0s (fun pc => taken.contains pc) n K
    if R.err.isSome then
      return .error s!"slice {out.size}: symbolic error {R.err} at pc {R.pc}"
    let K' := abstract R
    let c1' := run prog ro m1 (fun _ => false) n c1
    let c2' := run prog ro m2 (fun _ => false) n c2
    let labs := cutLabels t1 t2 K' c1' c2'
    out := out.push ⟨n, taken, labs.filterMap fun (id, _) => (treeAt R id).map fun t => (id, t), K', labs⟩
    K := K'
    c1 := c1'
    c2 := c2'
    prev := cut
  return .ok out

/-- Slice a segment with explicit slice lengths (reused from the first-iteration segment: the
loop body is the same, so the same cut positions apply). -/
def segRunCuts (cfg : Cfg) (m0s : Addr Lin → Cell E Lin) (K0 : State E Lin) (c1i c2i : CS)
    (m1 m2 : Addr Int → Cell W32 Int) (t1 t2 : Std.HashMap W32 (List Q)) (ns : List Nat) :
    IO (Except String (Array Sl)) := do
  let prog := cfg.prog
  let ro := cfg.ro
  let mut c1 := c1i
  let mut c2 := c2i
  let mut K := K0
  let mut out : Array Sl := #[]
  for n in ns do
    let taken := takenOf prog ro m1 n c1
    let R := run prog ro m0s (fun pc => taken.contains pc) n K
    if R.err.isSome then
      return .error s!"slice {out.size}: symbolic error {R.err} at pc {R.pc}"
    let K' := abstract R
    let c1' := run prog ro m1 (fun _ => false) n c1
    let c2' := run prog ro m2 (fun _ => false) n c2
    let labs := cutLabels t1 t2 K' c1' c2'
    out := out.push ⟨n, taken, labs.filterMap fun (id, _) => (treeAt R id).map fun t => (id, t), K', labs⟩
    K := K'
    c1 := c1'
    c2 := c2'
  return .ok out

def ok! {α : Type} [Inhabited α] (r : Except String α) : IO α := match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- Generate one segment.  `hsig` is the branch hypothesis (`σ 6 = σ 5` or `σ 6 ≠ σ 5`). -/
def genSeg (cfg : Cfg) (dir ns seg k0Name : String) (k0 : State E Lin) (sls : Array Sl)
    (nb : Nat) (lo : Int) (cOut : String) (hsig : String) : IO (State E Lin) := do
  let prog := cfg.prog
  let ro := cfg.ro
  let roT := s!"{ro}"
  let memT := s!"(Arm.mem0sH {roT} rodata 0 ({lo}))"
  let keyedT := s!"(Arm.mem0sH_keyed {roT} rodata 0 ({lo}))"
  let nsS := s!"{ns}.{seg}"
  let hdr := s!"open Hashtree.Asm Hashtree.Asm.ArmSym Hashtree.Kernels.Arm.{cfg.mod} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n" ++
    s!"namespace {nsS}\n\n"
  let C := sls.size
  if C = 0 then throw (IO.userError s!"{seg}: no slices")
  let finalK : State E Lin := sls[C - 1]!.K'
  let mut chosen : List (Nat × Q) := []
  let mut stepsList : List Nat := []
  let mut orcs : List String := []
  let mut asms : List (List (Cond Lin × Bool)) := []
  let mut asmIdx : List Nat := []
  for c in [0:C] do
    let sl := sls[c]!
    let n := sl.n
    let trs := sl.trs
    let K' := sl.K'
    let orcT := s!"(fun pc => decide (pc ∈ ({sl.taken} : List Nat)))"
    orcs := orcs ++ [orcT]
    let A := K'.assume
    match asms.findIdx? (fun x => decide (x = A)) with
    | some j => asmIdx := asmIdx ++ [j]
    | none => asms := asms ++ [A]; asmIdx := asmIdx ++ [asms.length - 1]
    let mut chosen' : List (Nat × Q) := []
    let mut lemmas := ""
    let mut trees : List (Nat × E) := []
    let mut calls : List String := []
    let mut carryL : List (Nat × Q) := []
    let mut carryT : List (Nat × E) := []
    let mut carryC : List Nat := []
    for (id, qs) in sl.labs do
      let carried : Option (Nat × Q) := match trs.find? (·.1 == id) with
        | some (_, t) => match t with
          | .var (.n v) => match chosen.findIdx? (·.1 == v) with
            | some j => if qs.contains (chosen[j]!).2 then some (j, (chosen[j]!).2) else none
            | none => none
          | _ => none
        | none => none
      match carried with
      | some (j, q0) =>
        carryL := carryL ++ [(id, q0)]
        carryT := carryT ++ [(id, .var (.n (chosen[j]!).1))]
        carryC := carryC ++ [j]
      | none =>
        match trs.find? (·.1 == id) with
        | none => pure ()
        | some (_, t) =>
          let okKey : Key → Bool
            | .n v => chosen.any (·.1 == v)
            | .m 1 l => l.c = [1] && 0 ≤ l.k
            | .m _ _ => false
          let keysOk := t.keys.eraseDups.all okKey
          if !keysOk then
            pure ()
          else do
            let keys := t.keys.eraseDups
            let hyps := keys.filterMap fun key => match key with
              | .n v => (chosen.findIdx? (·.1 == v)).map fun k => (v, k, (chosen[k]!).2)
              | .m _ _ => none
            let atoms := hyps.map (·.2.2)
            let mkeys := keys.filterMap fun key => match key with
              | .m 1 l => if l.c = [1] && 0 ≤ l.k then some l.k else none
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
    let kName := if c = 0 then k0Name else s!"K{c}"
    let cases := String.join ((List.range chosen'.length).map fun k =>
      s!"  | {k}, _ => exact (ArmSlice.slice_trees prog {roT} _ _ {n} {kName} K{c + 1} T{c} slice{c} env {k} (by decide)).trans ({calls[k]!})\n")
    let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : Inv L{c} inp env) (hm : HMem {64 * nb} inp env) :\n" ++
      s!"    Inv L{c + 1} inp (envAbs env (Arm.run prog {roT} {memT} {orcT} {n} {kName})) := by\n" ++
      s!"  have hT := ArmSlice.slice_trees_mem prog {roT} _ _ {n} {kName} K{c + 1} T{c} slice{c} env\n" ++
      s!"  refine inv_append _ _ _ _ ?_ (inv_carry L{c} inp env _ hI T{c}c L{c + 1}c C{c} (fun t ht => hT t (List.mem_append_right _ ht)) (by decide +kernel))\n" ++
      s!"  apply inv_of_get\n  intro k hk\n  match k, hk with\n" ++ cases ++
      s!"  | _ + {chosen'.length}, hk => simp only [L{c + 1}n, List.length_cons, List.length_nil] at hk; omega\n\n"
    let imports := s!"import Hashtree.Asm.ArmLoop2\nimport Hashtree.Asm.Chain\nimport Hashtree.Asm.Carry\nimport Hashtree.Asm.ArmSym\nimport Hashtree.Asm.ArmSlice\nimport Hashtree.Kernels.Arm.{cfg.mod}\nimport {ns}.Head\n" ++
      (if c = 0 then "" else s!"import {nsS}.P{c - 1}\n")
    let body := imports ++ "\n" ++ hdr ++
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
      lemmas ++ step ++ s!"end {nsS}\n"
    IO.FS.writeFile s!"{dir}/P{c}.lean" body
    IO.println s!"  {seg} slice {c}: {n} steps, {sl.labs.length} labelled, {chosen'.length + carryL.length} proved"
    chosen := chosen' ++ carryL
    stepsList := stepsList ++ [n]
  IO.println s!"{seg}: {C} slices, {stepsList.foldl (· + ·) 0} steps"
  let kn (j : Nat) : String := if j = 0 then k0Name else s!"K{j}"
  let sumT := sumText stepsList
  let mut fin := s!"import {nsS}.P{C - 1}\n\n" ++ hdr ++
    "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) (Arm.run prog {roT} {memT} {orcs[cc]!} {stepsList[cc]!} {kn cc})\n"
  fin := fin ++ s!"\ndef KF : State E Lin := K{C}\ndef EF (env0 : Key → W32) : Key → W32 := E{C} env0\ndef NS : Nat := {sumT}\n\n"
  fin := fin ++ s!"theorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem {64 * nb} inp env0) :\n    Inv L{C} inp (E{C} env0) := by\n" ++
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
  fin := fin ++ "theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)\n" ++
    s!"    (h0 : Mem0Rel env0 σ {memT} mem0c) {hsig} :\n" ++
    s!"    Arm.run prog {roT} mem0c orcC NS (mapState env0 σ {k0Name}) = mapState (EF env0) σ KF := by\n" ++
    s!"  have m0 : Mem0Rel env0 σ {memT} mem0c := h0\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ {memT} mem0c := mem0Rel_envAbs _ σ _ mem0c {keyedT} m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let slT := s!"(ArmSlice.slice_sound {envc} σ {memT} mem0c m{cc} prog {roT} {orcs[cc]!} orcC {stepsList[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} rfl (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then s!"mapState env0 σ {k0Name}" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : Arm.run prog {roT} mem0c orcC {stepsList[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {slT}\n"
  fin := fin ++ s!"  show Arm.run prog {roT} mem0c orcC ({sumT}) (mapState env0 σ {k0Name}) = _\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [ArmSlice.run_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  if nb > 0 then
    let mut cases := ""
    let mut bad := 0
    for n in [0:nb] do
      for i in [0:8] do
        for b in [0:4] do
          let o := 32 * n + 4 * i + b
          match lookup ((⟨rOut, Lin.sym 5⟩ : Addr Lin).plusI (o : Int)) finalK.mem with
          | .ok (some (.dat (.var (.n id)) b')) =>
            match chosen.findIdx? (·.1 == id) with
            | some kk =>
              if (chosen[kk]!).2 == .HB n i && b' == b then
                cases := cases ++ s!"  | {n}, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), (by simpa only [Lin.eval_sym, KF, EF] using outCellAt_sound _ σ K{C} (Lin.sym 5) (32 * {n} + 4 * {i} + {b}) {id} {b'} (by decide)),\n" ++
                  s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB n i)} from inv_get (inv_final inp env0 hm) {kk} (by decide),\n" ++
                  s!"        qHB, byte_bswap _ {b} (by decide), node_byte inp {n} {i} {b} (by decide) (by decide)]; rfl⟩\n"
              else cases := cases ++ s!"  -- output {o}: unexpected label {qText (chosen[kk]!).2} / byte {b'}\n"; bad := bad + 1
            | none => cases := cases ++ s!"  -- output {o}: no label\n"; bad := bad + 1
          | _ => cases := cases ++ s!"  -- output {o}: no stored lane\n"; bad := bad + 1
    IO.println s!"{seg}: {bad} output bytes without a proof"
    fin := fin ++ s!"\ntheorem out_final (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)\n" ++
      s!"    (orcC : Nat → Bool) (h0 : Mem0Rel env0 σ {memT} mem0c) {hsig} (hm : HMem {64 * nb} inp env0) :\n" ++
      s!"    ∀ n i b, n < {nb} → i < 8 → b < 4 → ∃ x,\n" ++
      s!"      lookup (⟨rOut, σ 5 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)\n        (Arm.run prog {roT} mem0c orcC NS (mapState env0 σ {k0Name})).mem = .ok (some (.dat x b)) ∧\n" ++
      "      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by\n" ++
      "  rw [run_final env0 σ mem0c orcC h0 hσ]\n  intro n i b hn hi hb\n  match n, i, b, hn, hi, hb with\n" ++ cases ++
      s!"  | _ + {nb}, _, _, hn, _, _ => omega\n  | _, _ + 8, _, _, hi, _ => omega\n  | _, _, _ + 4, _, _, hb => omega\n\n"
  fin := fin ++
    s!"theorem log_final : ∀ p ∈ KF.mem, (p.1.region = rOut ∧ p.1.off.c = {cOut} ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < {32 * nb}) ∨\n" ++
    s!"    (p.1.region = rStack ∧ p.1.off.c = [] ∧ {lo} ≤ p.1.off.k ∧ p.1.off.k < 0) := by\n  decide\n\n" ++
    "theorem KF_onlyOut : KF.mem.all (fun p => decide (p.1.region = rOut)) = true := by decide\n\n" ++
    "theorem KF_halted : KF.halted = " ++ (if finalK.halted then "true" else "false") ++ " := by decide\n" ++
    "theorem KF_err : KF.err = none := by decide\n" ++
    "theorem KF_tail : KF.tail = " ++ (match finalK.tail with | some n => s!"some \"{n}\"" | none => "none") ++ " := by decide\n\n" ++
    s!"end {nsS}\n"
  IO.FS.writeFile s!"{dir}/Final.lean" fin
  return finalK

/-- The cut relation of a segment to the canonical loop head `KH1`. -/
def shapeFile (cfg : Cfg) (ns : String) (sg : String) (KF : State E Lin) (C : Nat) : String :=
  let hdr := s!"open Hashtree.Asm Hashtree.Asm.ArmSym Hashtree.Kernels.Arm.{cfg.mod} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"
  let linOf (g : Nat) : String := match KF.getG g with
    | .ptr a => (Lin.trim a.off).toLean
    | _ => "(Lin.sym 0)"
  let fl := match KF.flags with
    | some (a, b) => s!"{(Lin.trim a).toLean}, {(Lin.trim b).toLean}"
    | none => "Lin.sym 3, Lin.sym 4"
  s!"import {ns}.{sg}.Final\n\n" ++ hdr ++ s!"namespace {ns}.{sg}\n\n" ++
    s!"def tauE : List Lin := [{linOf 1}, Lin.sym 1, Lin.sym 2, {fl}, {linOf 0}, {linOf 2}]\n\n" ++
    "theorem KF_vr : Hashtree.Asm.X86.vrRel 0 KH1.vr KF.vr = true := by decide\n" ++
    s!"theorem KF_shape : \{ (\{ KF with vr := KH1.vr } : State E Lin) with mem := [], assume := [] } = KH1.substL tauE := by decide\n\n" ++
    s!"theorem KF_inst (env0 : Key → W32) (σ : Nat → Int) :\n    mapState (EF env0) σ KF = mapState (EF env0) σ \{ KF with vr := KH1.vr } := by\n" ++
    s!"  have h := Hashtree.Asm.Arm.mapState_vrInst (E{C - 1} env0) σ _ _ _ _ _ _ _ _ slice{C - 1} KH1.vr KF_vr\n" ++
    s!"  simpa only [EF, E{C}, KF] using h\n\n" ++
    s!"end {ns}.{sg}\n"

def main (args : List String) : IO Unit := do
  let kname := args.headD "sha_x1"
  let some cfg := cfgs.lookup kname | throw (IO.userError s!"unknown kernel {kname}")
  let H := (args.getD 1 "11").toNat!
  let nb := (args.getD 2 "1").toNat!
  let dir := args.getD 3 "Hashtree/Gen/ArmShaX1L"
  let ns := "Hashtree.Gen." ++ ((dir.splitOn "/").getLastD dir)
  let cfg := match (args.getD 4 "").toNat? with | some m => { cfg with maxLen := m } | none => cfg
  let cfg := match (args.getD 5 "").toNat? with | some m => { cfg with maxSize := m } | none => cfg
  let prog := cfg.prog
  let ro := cfg.ro
  let ninput := 128 * nb
  let i1 := randInput 11 ninput
  let i2 := randInput 22 ninput
  let m1 := Hashtree.Asm.ArmRun.mem0 progsLinux i1
  let m2 := Hashtree.Asm.ArmRun.mem0 progsLinux i2
  let tab (a : Array Nat) (o : Nat) := table (a.extract o (o + 64 * nb)) nb
  let e2 := Hashtree.Asm.ArmRun.entry (4 * nb) 0
  let (h0c1, NP) := toHead prog ro m1 H e2
  let (h0c2, _) := toHead prog ro m2 H e2
  if h0c1.pc != H then throw (IO.userError s!"prologue run stops at pc {h0c1.pc}, not {H}")
  let RP := run prog ro (mem0s ro cfg.rodata) (fun _ => false) NP (entryS 0)
  let KP := abstract RP
  if KP.err.isSome then throw (IO.userError s!"prologue: {KP.err}")
  unless (match KP.getG 1 with | .ptr a => decide (a.region = rIn) && decide (a.off = Lin.sym 0) | _ => false) do
    throw (IO.userError s!"prologue changed x1: {KP.getG 1 |>.toLean}")
  let r2 := if cfg.countHead then rNum else rOut
  unless (match KP.getG 0, KP.getG 2 with
    | .ptr a, .ptr b => decide (a.region = rOut) && decide (b.region = r2)
    | _, _ => false) do
    throw (IO.userError s!"prologue x0/x2 are not output pointers: {KP.getG 0 |>.toLean} {KP.getG 2 |>.toLean}")
  -- the spill bound: the frame the prologue allocated (the final `sp`) bounds every stack write
  -- of the body, the prologue's own saves are inside it as well
  let spLo : Int := match KP.getG 31 with
    | .ptr a => a.off.asInt.getD 0
    | _ => 0
  let lo : Int := KP.mem.foldl (fun acc p => match p.1.off.asInt with | some o => min acc o | none => acc)
    (min 0 spLo)
  let g0 := ((KP.gpr.set 0 (Val.ptr ⟨rOut, Lin.sym 5⟩)).set 1 (Val.ptr ⟨rIn, Lin.sym 0⟩)).set 2
    (Val.ptr ⟨r2, Lin.sym 6⟩)
  let fl0 : Option (Lin × Lin) :=
    match KP.flags with
    | some _ => some (Lin.sym 3, Lin.sym 4)
    | none => none
  let KH0 : State E Lin := { KP with mem := [], assume := [], gpr := g0, flags := fl0 }
  let KH1 : State E Lin := { KH0 with flags := some (Lin.sym 3, Lin.sym 4) }
  let m0H := mem0sH ro cfg.rodata 0 lo
  let (h1c1, NI) := toHead prog ro m1 H h0c1
  let (h1c2, _) := toHead prog ro m2 H h0c2
  let sls0 ← ok! (← segRun cfg m0H KH0 h0c1 h0c2 m1 m2 (tab i1 0) (tab i2 0) NI (2 * nb))
  let slsIt ← ok! (← segRunCuts cfg m0H KH1 h1c1 h1c2 m1 m2 (tab i1 (64 * nb)) (tab i2 (64 * nb)) (sls0.toList.map (·.n)))
  unless (slsIt.toList.map (·.taken)) == (sls0.toList.map (·.taken)) do
    IO.println "warning: the second head does not repeat the first iteration's branch pattern"
  let e0z := Hashtree.Asm.ArmRun.entry 0 0
  let z1 := (toHead prog ro m1 H e0z).1
  let z2 := (toHead prog ro m2 H e0z).1
  if z1.pc != H then throw (IO.userError s!"count-0 head at pc {z1.pc}")
  let nz := toHalt prog ro m1 z1
  let slsT0a ← ok! (← segRun cfg m0H KH0 z1 z2 m1 m2 (tab i1 0) (tab i2 0) nz 0)
  let e1 := Hashtree.Asm.ArmRun.entry nb 0
  let b1 := (toHead prog ro m1 H (toHead prog ro m1 H e1).1).1
  let b2 := (toHead prog ro m2 H (toHead prog ro m2 H e1).1).1
  let nb1 := toHalt prog ro m1 b1
  let slsT0b ← ok! (← segRun cfg m0H KH1 b1 b2 m1 m2 (tab i1 (64 * nb)) (tab i2 (64 * nb)) nb1 nb)
  IO.println s!"head pc {H}: prologue {NP} steps, lo {lo}, iteration {NI} steps, exit {nz}/{nb1} steps, spill log {KP.mem.length}"
  IO.println s!"  KP x0 {(KP.getG 0).toLean} x1 {(KP.getG 1).toLean} x2 {(KP.getG 2).toLean} flags {KP.flags.map fun (a, b) => a.toLean ++ "/" ++ b.toLean}"
  IO.println s!"  concrete head x0 {cval (h0c1.getG 0)} x1 {cval (h0c1.getG 1)} x2 {cval (h0c1.getG 2)}, sp {cval (h0c1.getG 31)}"
  let offP (g : Nat) : String := match KP.getG g with | .ptr a => (Lin.trim a.off).toLean | _ => "(Lin.sym 0)"
  let flP := match KP.flags with
    | some (a, b) => s!"{(Lin.trim a).toLean}, {(Lin.trim b).toLean}"
    | none => "Lin.sym 3, Lin.sym 4"
  let tauPText := s!"[{offP 1}, Lin.sym 1, Lin.sym 2, {flP}, {offP 0}, {offP 2}]"
  let hdr := s!"open Hashtree.Asm Hashtree.Asm.ArmSym Hashtree.Kernels.Arm.{cfg.mod} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
    "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"
  let headBody := s!"import Hashtree.Asm.Chain\nimport Hashtree.Asm.ArmLoop2\nimport Hashtree.Asm.ArmSym\nimport Hashtree.Asm.ArmSlice\nimport Hashtree.Kernels.Arm.{cfg.mod}\n\n" ++ hdr ++
    s!"namespace {ns}\n\n" ++
    s!"/-- The prologue's run from the entry state ({NP} steps): its log is the spill area. -/\ndef KPrun : State E Lin := {RP.toLean}\n\n" ++
    s!"/-- The prologue's cut at the loop head (pc {H}), {NP} steps. -/\ndef KP : State E Lin := {KP.toLean}\n\n" ++
    "/-- The loop-head cut: the prologue's, without its log; the output pointer `x0` as the fresh\nsymbol 5, the end pointer `x2` as the fresh symbol 6, the input pointer `x1` as the entry symbol 0. -/\n" ++
    s!"def KH0 : State E Lin := {KH0.toLean}\n\n" ++
    "/-- The loop-head cut after an iteration: as `KH0`, with the flags as fresh symbols 3, 4. -/\n" ++
    s!"def KH1 : State E Lin := {KH1.toLean}\n\n" ++
    s!"def tauP : List Lin := {tauPText}\n\ndef NP : Nat := {NP}\ndef lo : Int := ({lo} : Int)\n\n" ++
    s!"theorem slicePro : ArmSlice.sliceCheck prog {ro} (mem0s {ro} rodata) (fun _ => false) {NP} (entryS 0) KP [] = true := by\n  decide +kernel\n\n" ++
    "theorem KP_assume : KP.assume = [] := by decide\n" ++
    "theorem KP_inst : { KP with mem := [], assume := [] } = KH0.substL tauP := by decide\n" ++
    s!"theorem KPrun_run : KPrun = Arm.run prog {ro} (mem0s {ro} rodata) (fun _ => false) {NP} (entryS 0) := by\n  decide\n\n" ++
    "theorem KP_abs : KP = abstract KPrun := by decide\n" ++
    "theorem KP_cutOk : CutOk KPrun := by decide\n" ++
    s!"theorem KP_push : Arm.pushOk KPrun 0 lo = true := by decide\n" ++
    s!"theorem KP_log : ∀ p ∈ KP.mem, p.1.region = rStack ∧ p.1.off.c = [] ∧ lo ≤ p.1.off.k ∧ p.1.off.k < 0 := by decide\n" ++
    "theorem KH0_nOnly : KH0.nOnly = true := by decide\n" ++
    "theorem KH1_nOnly : KH1.nOnly = true := by decide\n\n" ++
    s!"end {ns}\n"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/Head.lean" headBody
  let cOut := "[0, 0, 0, 0, 0, 1]"
  IO.FS.createDirAll s!"{dir}/It0"
  IO.FS.createDirAll s!"{dir}/It"
  IO.FS.createDirAll s!"{dir}/T0a"
  IO.FS.createDirAll s!"{dir}/T0b"
  let hsigIn := if cfg.countHead then "(hσ : ¬ σ 6 < 4)" else "(hσ : σ 6 ≠ σ 5)"
  let hsigOut := if cfg.countHead then "(hσ : σ 6 < 4)" else "(hσ : σ 6 = σ 5)"
  let KF0 ← genSeg cfg s!"{dir}/It0" ns "It0" "KH0" KH0 sls0 nb lo cOut hsigIn
  IO.FS.writeFile s!"{dir}/It0/Shape.lean" (shapeFile cfg ns "It0" KF0 sls0.size)
  let KFIt ← genSeg cfg s!"{dir}/It" ns "It" "KH1" KH1 slsIt nb lo cOut hsigIn
  IO.FS.writeFile s!"{dir}/It/Shape.lean" (shapeFile cfg ns "It" KFIt slsIt.size)
  let _ ← genSeg cfg s!"{dir}/T0a" ns "T0a" "KH0" KH0 slsT0a 0 lo cOut hsigOut
  let _ ← genSeg cfg s!"{dir}/T0b" ns "T0b" "KH1" KH1 slsT0b 0 lo cOut hsigOut
  IO.println "done"
