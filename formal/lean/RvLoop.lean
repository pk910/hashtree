import RvLib

/-!
`rvloop <kernel> <outdir> <segment>`: the segments of the every-count proof of an RV64 kernel
(`x1`, `zbb`, `crypto`).  Segments:

* `head`: the prologue from the entry to the loop-head cut `H` (one slice), the loop-head cut
  `KH`, its facts, the prologue's save slots (`SAVES`, `saveOk`) and the geometry (`H`, `IT`,
  `EX`).  Files: `Base.lean`, `Head.lean`, `T0/Base.lean` (the exit's memory `M0T`).
* `it`: one iteration, from `KH` back to `KH`, with `tauE` and the reopening facts `KF_*`.
  Files: `It/P{c}.lean`, `It/Final.lean`.
* `t0`: the exit for count 0, over `M0T` (the prologue's save slots as memory keys).
  Files: `T0/P{c}.lean`, `T0/Final.lean`.

Slices, labels, core lemmas and the final theorems are those of `RvProof.lean` (the count-2
proof), with the loop head as a segment boundary, the needed locations found backwards from the
final cut's output bytes, and `hsig` the count hypothesis of the segment's branch conditions.
-/

open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym Hashtree.Asm.Scan

abbrev CS := Hashtree.Asm.RiscvRun.CS

/-- The loop head (target of the last backward `jal 0,H`) and the iteration length. -/
def geom (prog : Array Instr) : Nat × Nat := Id.run do
  let mut H : Nat := 0
  let mut L : Nat := 0
  for i in [0:prog.size] do
    match prog[i]? with
    | some (.jal 0 t) =>
      if t < i then
        H := t
        L := i
    | _ => pure ()
  return (H, L - H)

/-- The taken branches of a concrete run of `n` steps. -/
def takenOfR (prog : Array Instr) (m : Addr Int → Cell W32 Int) (n : Nat) (c : CS) : List Nat := Id.run do
  let mut taken : List Nat := []
  let mut cs := c
  for _ in [0:n] do
    let pc0 := cs.pc
    let isBr := match prog[pc0]? with | some (.br _ _ _ _) => true | _ => false
    cs := run prog peR m (fun _ => false) 1 cs
    if isBr && (cs.pc != pc0 + 1 || cs.halted) then taken := taken ++ [pc0]
  return taken

def sumText (l : List Nat) : String :=
  l.foldr (fun n acc => if acc = "" then s!"{n}" else s!"{n} + ({acc})") ""

def hdrOf (kern : Kern) : String :=
  s!"open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym {kern.ns} Hashtree.Asm.SpecQ Hashtree.Spec\n" ++
  "set_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"

/-- The per-kernel segment namespace (`RvX1P` → `RvX1L`). -/
def genL (kern : Kern) : String := (kern.gen.take (kern.gen.length - 1)).toString ++ "L"

/-- The concrete initial state of one of the two labelling runs. -/
def runC (prog : Array Instr) (kern : Kern) (i : Array Nat) (count : Nat) (H : Nat) : CS :=
  let cprogs : List Hashtree.Asm.RiscvRun.Prog :=
    [⟨kern.name, prog, kern.compressed, kern.got, [], kern.rodata.toArray, 10⟩]
  run prog peR (Hashtree.Asm.RiscvRun.mem0 cprogs i {}) (fun _ => false) H
    (Hashtree.Asm.RiscvRun.entry count {})

/-- The exit's step count from the loop head (count 0), and whether the run halted cleanly. -/
def exitSteps (prog : Array Instr) (kern : Kern) (H : Nat) : Nat × Bool := Id.run do
  let cprogs : List Hashtree.Asm.RiscvRun.Prog :=
    [⟨kern.name, prog, kern.compressed, kern.got, [], kern.rodata.toArray, 10⟩]
  let m := Hashtree.Asm.RiscvRun.mem0 cprogs (randInput 11 128) {}
  let mut s := run prog peR m (fun _ => false) H (Hashtree.Asm.RiscvRun.entry 0 {})
  let mut k := 0
  while !s.halted && k < 100000 do
    s := run prog peR m (fun _ => false) 1 s
    k := k + 1
  return (k, s.halted && s.err.isNone)

/-- The prologue's save slots: the stack byte offsets below the entry stack pointer. -/
def saveSlots (KP : State E Lin) : List Int := Id.run do
  let mut saves : List Int := []
  for (a, _) in KP.mem do
    if a.region = rStack then
      match a.off.asInt with
      | some o => if -16 ≤ o ∧ o < 0 then saves := saves ++ [o]
      | none => pure ()
  return saves

/-- `Base.lean` and `Head.lean`: the program environment, the symbolic memory, the loop-head cut
and its facts. -/
def genHead (dir : String) (kern : Kern) (G : String) : IO Unit := do
  let prog := kern.prog
  let (H, IT) := geom prog
  let gotT := gotPtrs kern.got
  let M0 := mem0s 10 11 kern.rodata gotT
  let KP := abstract (run prog peR M0 (fun _ => false) H (entryS 0))
  let KH : State E Lin := { KP with mem := [], assume := [] }
  let (ex, exOk) := exitSteps prog kern H
  if !exOk then IO.println "head: the exit run did not halt cleanly"
  -- the save slots in the prologue's log, with the variable each cell was abstracted to
  let mut slots : List (Int × Nat × String) := []
  for (a, c) in KP.mem do
    if a.region = rStack then
      match a.off.asInt with
      | some o => if -16 ≤ o ∧ o < 0 then
          match c with
          | .dat (.var (.n i)) k => slots := slots ++ [(o, k, s!"e0 (.n {i})")]
          | .dat (.const v) k => slots := slots ++ [(o, k, s!"(BitVec.ofNat 32 {v.toNat})")]
          | _ => slots := slots ++ [(o, 0, "0#32")]
      | none => pure ()
  let saves := slots.map (·.1)
  let saveText : String := "[" ++ ", ".intercalate (saves.map (fun o => s!"({o} : Int)")) ++ "]"
  let rfls : String := " | ".intercalate (saves.map (fun _ => "rfl"))
  let cases : String := String.join (slots.map fun (_, _, w) =>
    s!"  · refine ⟨{w}, ?_⟩\n" ++
    "    simp only [KPLog, List.map_cons, List.map_nil, lookup, AddrEq.same, mapAddr, mapCell,\n" ++
    "      E.eval, Lin.eval, dotC, rIn, rOut, rStack, rNum, rRet]\n    simp\n")
  let aText := listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") KP.assume
  let nA := KP.assume.length
  let rflA : String := " | ".intercalate ((List.range nA).map fun _ => "rfl")
  let mText := listLean (fun (p : Addr Lin × Cell E Lin) => s!"({p.1.toLean}, {p.2.toLean})") KP.mem
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/Base.lean"
    (s!"import Hashtree.Asm.SpecQ1\nimport Hashtree.Asm.RiscvSlice\nimport Hashtree.Asm.RiscvSym\nimport {kern.ns}\n\n" ++
     s!"open Hashtree.Asm Hashtree.Asm.Riscv\n\nnamespace Hashtree.Gen.{G}\n\n" ++
     "/-- The program alone: rodata region 10, GOT 11, code 12. -/\ndef pe : Env := ⟨10, 11, 12, []⟩\n\n" ++
     s!"/-- The GOT entries (pointers). -/\ndef gotT : List (Region × Int) := {gotText gotT}\n\n" ++
     s!"/-- The symbolic initial memory. -/\ndef M0 : Addr Lin → Cell E Lin := RiscvSym.mem0s 10 11 {kern.ns}.rodata gotT\n\n" ++
     s!"end Hashtree.Gen.{G}\n")
  IO.FS.writeFile s!"{dir}/Head.lean"
    (s!"import Hashtree.Gen.{G}.Base\nimport Hashtree.Asm.Chain\nimport Hashtree.Asm.RiscvSlice\nimport Hashtree.Asm.Subst\nimport Hashtree.Asm.RiscvReach\nimport Hashtree.Asm.X86Loop\n\n" ++
     hdrOf kern ++ "open Hashtree.Asm.X86\n\n" ++ s!"namespace Hashtree.Gen.{G}\n\n" ++
     s!"/-- The prologue's step count (entry to the loop head). -/\ndef H : Nat := {H}\n\n" ++
     s!"/-- The iteration's step count. -/\ndef IT : Nat := {IT}\n\n" ++
     s!"/-- The exit's step count (loop head, count 0). -/\ndef EX : Nat := {ex}\n\n" ++
     s!"/-- The stack byte offsets the prologue saves registers in. -/\ndef SAVES : List Int := {saveText}\n\n" ++
     s!"/-- The cut after the prologue. -/\ndef Rhead : State E Lin := run prog pe M0 (fun _ => false) {H} (entryS 0)\n\n" ++
     "/-- The same, abstracted. -/\ndef KP : State E Lin := abstract Rhead\n\n" ++
     "/-- The prologue's recorded assumptions (the count's range: `slli` by 5). -/\n" ++
     s!"def Ahead : List (Cond Lin × Bool) := {aText}\n\n" ++
     "theorem KP_assume : KP.assume = Ahead := by decide +kernel\n\n" ++
     "/-- The prologue's write log. -/\n" ++
     s!"def KPLog : List (Addr Lin × Cell E Lin) := {mText}\n\n" ++
     "theorem KP_mem : KP.mem = KPLog := by decide +kernel\n\n" ++
     "/-- The loop-head cut: the prologue's cut without its memory writes and branches. -/\n" ++
     "def KH : State E Lin := { KP with mem := [], assume := [] }\n\n" ++
     "/-- The prologue's cut denotes the loop-head cut plus its log. -/\n" ++
     "theorem KH_map (e : Key → W32) (σ : Nat → Int) :\n" ++
     "    mapState e σ KP =\n" ++
     "      fr (KP.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) (mapState e σ KH) := by\n" ++
     "  simp only [KH, mapState, fr, List.map_nil, List.nil_append]\n\n" ++
     "/-- The count's range hypotheses discharge the prologue's assumptions. -/\n" ++
     s!"theorem asmHead (σ : Nat → Int) (hσ : 0 ≤ σ 2) (hb : 32 * σ 2 < 2 ^ 63) :\n" ++
     "    ∀ p ∈ Ahead, (mapCond σ p.1).decideC = some p.2 := by\n" ++
     "  intro p hp\n  simp only [Ahead, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
     s!"  rcases hp with {rflA} <;>\n" ++
     "    simp [mapCond, Cond.decideC, hσ, hb, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;>\n" ++
     "    omega\n\n" ++
     "theorem KH_len : KH.gpr.length = 32 := by decide +kernel\n\n" ++
     "theorem KH_vr : KH.vr = [] := by decide +kernel\n\n" ++
     "theorem KH_fl : KH.flags = none := by decide +kernel\n\n" ++
     "theorem KH_mem : KH.mem = [] := by decide +kernel\n\n" ++
     "theorem KH_nOnly : KH.nOnly = true := by decide +kernel\n\n" ++
     "theorem KH_err : KH.err = none := by decide +kernel\n\n" ++
     "theorem KH_tail : KH.tail = none := by decide +kernel\n\n" ++
     "/-- The prologue's slice check: `H` steps from the entry reach `KP`. -/\n" ++
     "theorem slicePro :\n" ++
     "    rvSliceCheck prog pe M0 (fun _ => false) H (entryS 0) KP [] = true := by\n" ++
     "  decide +kernel\n\n" ++
     "/-- The prologue writes the save slots `[-16,0)`. -/\n" ++
     "theorem head_addrs : ∀ p ∈ KP.mem, p.1.region = rStack ∧ p.1.off.c = [] ∧ -16 ≤ p.1.off.k ∧ p.1.off.k < 0 := by\n  decide +kernel\n\n" ++
     "theorem SAVES_lo : ∀ o ∈ SAVES, -16 ≤ o := by decide\n\n" ++
     "/-- The prologue's log holds what it saved. -/\n" ++
     "theorem saveOk (e0 : Key → W32) (σ : Nat → Int) (o : Int) (ho : o ∈ SAVES) :\n" ++
     "    ∃ x, lookup (⟨rStack, o⟩ : Addr Int)\n" ++
     "      (KPLog.map (fun p => (mapAddr σ p.1, mapCell e0 σ p.2))) = .ok (some (.dat x (((o + 16) % 4).toNat))) := by\n" ++
     "  simp only [SAVES, List.mem_cons, List.mem_nil_iff, or_false] at ho\n" ++
     s!"  rcases ho with {rfls}\n" ++ cases ++ "\n" ++
     s!"end Hashtree.Gen.{G}\n")
  IO.FS.createDirAll s!"{dir}/T0"
  IO.FS.writeFile s!"{dir}/T0/Base.lean"
    (s!"import Hashtree.Gen.{G}.Head\n\n" ++
     s!"open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym\n\nnamespace Hashtree.Gen.{G}.T0\n\n" ++
     s!"open Hashtree.Gen.{G}\n\n" ++
     "/-- The exit's symbolic memory: the prologue's save slots are read from the memory keys of\n" ++
     "those addresses, the rest as in `M0`. -/\n" ++
     s!"def M0T : Addr Lin → Cell E Lin := RiscvSym.mem0sT 10 11 {kern.ns}.rodata gotT SAVES\n\n" ++
     s!"end Hashtree.Gen.{G}.T0\n")
  IO.println s!"head: H {H}, IT {IT}, EX {ex}, saves {saves}, KH gprs {KH.gpr.length}, KP.mem {KP.mem.length}"

/-- One segment: the slices from `K0` over `total` steps, the step lemmas and the segment's
`Final`.  `M0Name`/`M0s` are the symbolic initial memory's name and value, `nb` the number of
output blocks the segment produces, `hsig` the count hypothesis, `isIt` whether this is the
iteration (which also emits the reopening facts `KF_*`). -/
def genSeg (dir : String) (kern : Kern) (G seg k0Name M0Name k0Err : String)
    (K0 : State E Lin) (M0s : Addr Lin → Cell E Lin) (total nb : Nat) (hsig : String)
    (isIt : Bool) (c1i c2i : CS) (m1 m2 : Addr Int → Cell W32 Int)
    (t1 t2 : Std.HashMap W32 (List Q)) : IO Unit := do
  let prog := kern.prog
  let sns := s!"Hashtree.Gen.{G}.{seg}"
  -- cuts: after each instruction that first produces an `A n r t` (t ≥ 1), at the segment's end,
  -- and at most 70 steps apart
  let mut cuts : List Nat := []
  let mut s1 := c1i
  let mut s2 := c2i
  let mut seen : List Q := []
  let mut k := 0
  let mut lastCut := 0
  while !s1.halted && k < total do
    s1 := run prog peR m1 (fun _ => false) 1 s1
    s2 := run prog peR m2 (fun _ => false) 1 s2
    k := k + 1
    let mut newA := false
    for (_, qs) in (labelsAt t1 t2 s1 s2).toList do
      for q in qs do
        match q with
        | .A _ _ t => if t ≥ 1 && !seen.contains q then seen := q :: seen; newA := true
        | _ => pure ()
    if newA || s1.halted || k = total || k - lastCut ≥ 70 then cuts := cuts ++ [k]; lastCut := k
  if k != total then IO.println s!"{seg}: concrete run took {k} steps, expected {total}"
  if s1.err.isSome then IO.println s!"{seg}: concrete run failed: {s1.err}"
  -- symbolic slices
  let mut c1 := c1i
  let mut c2 := c2i
  let mut K := K0
  let mut prev := 0
  let mut sls : Array Sl := #[]
  for cut in cuts do
    let n := cut - prev
    let taken := takenOfR prog m1 n c1
    let R := run prog peR M0s (fun pc => taken.contains pc) n K
    if R.err.isSome then IO.println s!"{seg} slice {sls.size}: symbolic error {R.err}"
    let K' := abstract R
    c1 := run prog peR m1 (fun _ => false) n c1
    c2 := run prog peR m2 (fun _ => false) n c2
    sls := sls.push ⟨n, taken, R, K', labelsAt t1 t2 c1 c2⟩
    K := K'
    prev := cut
  let C := sls.size
  if C = 0 then IO.println s!"{seg}: no slices"; return
  let finalK : State E Lin := sls[C - 1]!.K'
  -- the output bytes at the final cut
  let mut outIds : List Nat := []
  let mut badOut := 0
  for o in [0:32 * nb] do
    match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
    | .ok (some (Cell.dat (E.var (Key.n id)) _)) => outIds := outIds ++ [id]
    | _ => badOut := badOut + 1
  if badOut > 0 then IO.println s!"{seg}: {badOut} output bytes are not stored lanes"
  -- needed locations, backwards
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
      | none => IO.println s!"{seg} cut {cc + 1}: needed var {v} has no tree"
    needed := needed.set! cc nd
  if !needed[0]!.isEmpty then IO.println s!"{seg}: entry variables needed: {needed[0]!}"
  -- forward: labels, core lemmas, steps
  let mut labs : List (Nat × L1) := []
  let mut asms : List (List (Cond Lin × Bool)) := []
  let mut asmIdx : List Nat := []
  let mut orcs : List (List Nat × String) := []
  let mut stepsList : List Nat := []
  for c in [0:C] do
    let sl := sls[c]!
    let n := sl.n
    let orcT := s!"(fun pc => decide (pc ∈ ({sl.taken} : List Nat)))"
    orcs := orcs ++ [(sl.taken, orcT)]
    stepsList := stepsList ++ [n]
    let A := sl.K'.assume
    match asms.findIdx? (fun x => decide (x = A)) with
    | some jj => asmIdx := asmIdx ++ [jj]
    | none => asms := asms ++ [A]; asmIdx := asmIdx ++ [asms.length - 1]
    let kName := if c = 0 then k0Name else s!"K{c}"
    let mut labs' : List (Nat × L1) := []
    let mut trees : List (Nat × E) := []
    let mut lemmas := ""
    let mut calls : List String := []
    for id in needed[c + 1]!.mergeSort (· ≤ ·) do
      let some t := treeAt sl.R id | IO.println s!"{seg} slice {c}: no tree {id}"; return
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
      if bad then IO.println s!"{seg} slice {c}: var {id} depends on an unlabelled location"
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
        let link0 : List Eqn := if bytes then atoms.flatMap (fun a => match a with
          | .W _ 0 t => if t < 16 then (derive (atoms.erase a) bytes a 4).getD [] else []
          | .R _ _ => (derive (atoms.erase a) bytes a 4).getD []
          | _ => []) else []
        let linkH : List Eqn := atoms.flatMap (fun a => match a with
          | .H _ r _ => if r ≥ 1 then (derive (atoms.erase a) bytes a 6).getD [] else []
          | _ => [])
        let eqs := ((derive atoms bytes q 40).getD [] ++ link0 ++ linkH).eraseDups
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
      | none =>
        let lab := toL1 (fun w => (labs.find? (·.1 == w)).map (·.2)) t
        let some lab := lab | IO.println s!"{seg} slice {c}: var {id}: no expression label"; return
        lemmas := lemmas ++ s!"theorem core{c}_{id} (V : Q → Word) (inp : Nat → Byte) (env : Key → W32){hypArgs}{mArgs} :\n" ++
          s!"    E.eval env {t.toLean} = QE.eval V inp {lab.toLean} := by\n" ++
          "  simp_all only [E.eval, QE.eval]\n\n"
        calls := calls ++ [s!"core{c}_{id} (qv inp) inp env{hypCall}"]
        labs' := labs' ++ [(id, lab)]
      trees := trees ++ [(id, t)]
    let cases := String.join ((List.range labs'.length).map fun kk =>
      s!"  | {kk}, _ => exact (rvSlice_trees prog pe _ _ {n} {kName} K{c + 1} T{c} slice{c} env {kk} (by decide)).trans ({calls[kk]!})\n")
    let step := s!"theorem step{c} (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L{c} inp env) (hm : HMem 128 inp env) :\n" ++
      s!"    Inv1 L{c + 1} inp (envAbs env (run prog pe {M0Name} {orcT} {n} {kName})) := by\n" ++
      s!"  apply inv1_of_get\n  intro kk hk\n  match kk, hk with\n" ++ cases ++
      s!"  | _ + {labs'.length}, hk => simp only [L{c + 1}, List.length_cons, List.length_nil] at hk; omega\n\n"
    let imports := s!"import Hashtree.Gen.{G}.Base\nimport Hashtree.Asm.Chain\nimport Hashtree.Asm.RiscvSlice\nimport Hashtree.Asm.Subst\nimport Hashtree.Asm.RiscvReach\nimport Std.Tactic.BVDecide\n" ++
      (if c = 0 then (if seg = "It" then s!"import Hashtree.Gen.{G}.Head\n" else s!"import Hashtree.Gen.{G}.T0.Base\n")
       else s!"import {sns}.P{c - 1}\n")
    let body := imports ++ "\n" ++ hdrOf kern ++ s!"namespace {sns}\nopen Hashtree.Gen.{G}\n\n" ++
      (if c = 0 then "def L0 : List (Nat × QE) := []\n\n" else "") ++
      s!"def K{c + 1} : State E Lin := {sl.K'.toLean}\n\n" ++
      s!"def L{c + 1} : List (Nat × QE) := {listLean (fun (p : Nat × L1) => s!"({p.1}, {p.2.toLean})") labs'}\n\n" ++
      s!"def T{c} : List (Nat × E) := {listLean (fun (p : Nat × E) => s!"({p.1}, {p.2.toLean})") trees}\n\n" ++
      s!"theorem slice{c} : rvSliceCheck prog pe {M0Name} {orcT} {n} {kName} K{c + 1} T{c} = true := by\n  decide +kernel\n\n" ++
      lemmas ++ step ++ s!"end {sns}\n"
    IO.FS.createDirAll s!"{dir}/{seg}"
    IO.FS.writeFile s!"{dir}/{seg}/P{c}.lean" body
    IO.println s!"{seg} slice {c}: {n} steps, {sl.labs.size} labelled, {labs'.length} tracked, mem log {sl.K'.mem.length}"
    labs := labs'
  -- Final.lean
  let C := stepsList.length
  let kn (jj : Nat) : String := if jj = 0 then k0Name else s!"K{jj}"
  let runOf (cc : Nat) : String :=
    if isIt && cc + 1 = C then "Rlast"
    else s!"(run prog pe {M0Name} {(orcs[cc]!).2} {stepsList[cc]!} {kn cc})"
  let mut fin := s!"import {sns}.P{C - 1}\n\n" ++ hdrOf kern ++ s!"namespace {sns}\nopen Hashtree.Gen.{G}\n\n"
  if isIt then
    fin := fin ++ s!"/-- The last slice's run, whose log the iteration hands to the next one. -/\n" ++
      s!"def Rlast : State E Lin := run prog pe {M0Name} {(orcs[C - 1]!).2} {stepsList[C - 1]!} {kn (C - 1)}\n\n"
  fin := fin ++ "def E0 (env0 : Key → W32) : Key → W32 := env0\n"
  for cc in [0:C] do
    fin := fin ++ s!"def E{cc + 1} (env0 : Key → W32) : Key → W32 := envAbs (E{cc} env0) {runOf cc}\n"
  fin := fin ++ s!"\n/-- The segment's final cut. -/\ndef KF : State E Lin := K{C}\n\ndef EF (env0 : Key → W32) : Key → W32 := E{C} env0\n\n"
  fin := fin ++ s!"theorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem 128 inp env0) :\n    Inv1 L{C} inp (E{C} env0) := by\n" ++
    "  have i0 : Inv1 L0 inp (E0 env0) := fun p hp => by cases hp\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have i{cc + 1} : Inv1 L{cc + 1} inp (E{cc + 1} env0) := step{cc} inp (E{cc} env0) i{cc} hm\n"
  fin := fin ++ s!"  exact i{C}\n\n"
  for jj in [0:asms.length] do
    let A := asms[jj]!
    let aText := listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") A
    fin := fin ++ s!"def A{jj} : List (Cond Lin × Bool) := {aText}\n" ++
      s!"theorem asm{jj} (σ : Nat → Int) {hsig} : ∀ p ∈ A{jj}, (mapCond σ p.1).decideC = some p.2 := by\n" ++
      s!"  intro p hp\n  simp only [A{jj}, List.mem_cons, List.mem_nil_iff, or_false] at hp\n" ++
      (if A.isEmpty then "  exact absurd hp id\n\n" else
        s!"  rcases hp with {" | ".intercalate ((List.range A.length).map fun _ => "rfl")} <;>\n" ++
        "    simp [mapCond, Cond.decideC, hσ, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;> omega\n\n")
  fin := fin ++ s!"/-- The segment's step count. -/\ndef NS : Nat := {sumText stepsList}\n\n"
  fin := fin ++ s!"theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)\n" ++
    s!"    (orcC : Nat → Bool) (h0 : Mem0Rel env0 σ {M0Name} mem0c) {hsig} :\n" ++
    s!"    run prog pe mem0c orcC NS (mapState env0 σ {k0Name}) = mapState (E{C} env0) σ K{C} := by\n" ++
    s!"  have m0 : Mem0Rel env0 σ {M0Name} mem0c := h0\n"
  for cc in [0:C] do
    fin := fin ++ s!"  have m{cc + 1} : Mem0Rel (E{cc + 1} env0) σ {M0Name} mem0c := mem0Rel_envAbs _ σ _ mem0c {(if isIt then "(RiscvSym.mem0s_keyed 10 11 rodata gotT)" else "(RiscvSym.mem0sT_keyed 10 11 rodata gotT SAVES)")} m{cc} _\n"
  for cc in [0:C] do
    let envc := if cc = 0 then "env0" else s!"(E{cc} env0)"
    let hkn := if cc = 0 then k0Err else "rfl"
    let sl := s!"(rvSlice_sound {envc} σ {M0Name} mem0c m{cc} prog pe {(orcs[cc]!).2} orcC {stepsList[cc]!} {kn cc} K{cc + 1} T{cc} slice{cc} {hkn} (assumeOk_of σ K{cc + 1} A{asmIdx[cc]!} rfl (asm{asmIdx[cc]!} σ hσ))).1"
    let lhsS := if cc = 0 then s!"mapState env0 σ {k0Name}" else s!"mapState (E{cc} env0) σ K{cc}"
    fin := fin ++ s!"  have r{cc} : run prog pe mem0c orcC {stepsList[cc]!} ({lhsS}) = mapState (E{cc + 1} env0) σ K{cc + 1} := {sl}\n"
  fin := fin ++ "  show run prog pe mem0c orcC (" ++ sumText stepsList ++ s!") (mapState env0 σ {k0Name}) = _\n"
  for cc in [0:C] do
    if cc + 1 < C then fin := fin ++ s!"  rw [rvRun_add, r{cc}]\n" else fin := fin ++ s!"  exact r{cc}\n"
  if nb > 0 then
    let mut cases := ""
    let mut missing := 0
    for n in [0:nb] do
      for i in [0:8] do
        for b in [0:4] do
          let o := 32 * n + 4 * i + b
          let ok := match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) finalK.mem with
            | .ok (some (Cell.dat (E.var (Key.n id)) b')) =>
              match labs.findIdx? (·.1 == id) with
              | some kk =>
                if (labs[kk]!).2 == .q (.HB n i) && b' == b then
                  some (s!"  | {n}, {i}, {b}, _, _, _ => exact ⟨E{C} env0 (.n {id}), outCell_sound _ σ K{C} {o} {id} {b'} (by decide),\n" ++
                    s!"      by rw [show E{C} env0 (.n {id}) = qv inp {qText (.HB n i)} from inv1_get (inv_final inp env0 hm) {kk} (by decide),\n" ++
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
  if isIt then
    fin := fin ++ s!"/-- The final cut is the last slice's run, abstracted. -/\ntheorem KF_eq : K{C} = abstract Rlast := by decide +kernel\n\n" ++
      "/-- The last slice's run is a valid cut. -/\n" ++
      "theorem KF_cutok : CutOk Rlast := by decide +kernel\n\n" ++
      "/-- The end-cut substitution: next block's pointers, decremented count. -/\n" ++
      "def tauE : List Lin := [(⟨64, [1]⟩ : Lin), (⟨32, [0, 1]⟩ : Lin), (⟨-1, [0, 0, 1]⟩ : Lin)]\n\n" ++
      "/-- The end cut reopens as the loop head under `tauE`. -/\n" ++
      "theorem KF_live : gprLiveRel Rlast KH tauE = true := by decide +kernel\n\n" ++
      "theorem KF_pc : Rlast.pc = KH.pc := by decide +kernel\n\n" ++
      "theorem KF_halted : Rlast.halted = KH.halted := by decide +kernel\n\n" ++
      "theorem KF_err : Rlast.err = KH.err := by decide +kernel\n\n" ++
      "theorem KF_tail : Rlast.tail = KH.tail := by decide +kernel\n\n" ++
      "theorem KF_vr : Rlast.vr = [] := by decide +kernel\n\n" ++
      "theorem KF_flags : Rlast.flags = none := by decide +kernel\n\n" ++
      "/-- The iteration writes output bytes of its block and stack bytes of the body's frame. -/\n" ++
      "theorem log_final : ∀ p ∈ Rlast.mem,\n" ++
      "    (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 32) ∨\n" ++
      "    (p.1.region = rStack ∧ p.1.off.c = [] ∧ -80 ≤ p.1.off.k ∧ p.1.off.k < -16) := by\n  decide\n\n"
  else
    fin := fin ++ "theorem KF_halted : KF.halted = true := by decide\n\n" ++
      "theorem KF_err : KF.err = none := by decide\n\n" ++
      "theorem KF_tail : KF.tail = none := by decide\n\n" ++
      "theorem KF_mem : KF.mem = [] := by decide\n\n"
  fin := fin ++ s!"end {sns}\n"
  IO.FS.writeFile s!"{dir}/{seg}/Final.lean" fin
  IO.println s!"wrote {seg}/Final.lean ({sumText stepsList} steps, {C} slices)"

def main (args : List String) : IO Unit := do
  let some kern := kerns.lookup (args.headD "x1") | throw (IO.userError "kernel: x1 | zbb | crypto")
  let dir := args.getD 1 "Gen"
  let seg := args.getD 2 "all"
  let G := genL kern
  let prog := kern.prog
  let gotT := gotPtrs kern.got
  let (H, _) := geom prog
  let M0 := mem0s 10 11 kern.rodata gotT
  let KP := abstract (run prog peR M0 (fun _ => false) H (entryS 0))
  let KH : State E Lin := { KP with mem := [], assume := [] }
  let saves := saveSlots KP
  let M0T := mem0sT 10 11 kern.rodata gotT saves
  let i1 := randInput 11 128
  let i2 := randInput 22 128
  let cprogs : List Hashtree.Asm.RiscvRun.Prog :=
    [⟨kern.name, prog, kern.compressed, kern.got, [], kern.rodata.toArray, 10⟩]
  let m1 := Hashtree.Asm.RiscvRun.mem0 cprogs i1 {}
  let m2 := Hashtree.Asm.RiscvRun.mem0 cprogs i2 {}
  if seg = "all" || seg = "head" then genHead dir kern G
  if seg = "all" || seg = "it" then
    let c1 := runC prog kern i1 2 H
    let c2 := runC prog kern i2 2 H
    -- the iteration's step count: until the loop head is reached again
    let mut s := run prog peR m1 (fun _ => false) 1 c1
    let mut k := 1
    while s.pc != H && !s.halted && k < 100000 do
      s := run prog peR m1 (fun _ => false) 1 s
      k := k + 1
    genSeg dir kern G "It" "KH" "M0" "rfl" KH M0 k 1 "(hσ : 1 ≤ σ 2)" true
      c1 c2 m1 m2 (table i1 2) (table i2 2)
  if seg = "all" || seg = "t0" then
    let c1 := runC prog kern i1 0 H
    let c2 := runC prog kern i2 0 H
    let (k, _) := exitSteps prog kern H
    genSeg dir kern G "T0" "KH" "M0T" "rfl" KH M0T k 0 "(hσ : σ 2 = 0)" false
      c1 c2 m1 m2 (table i1 0) (table i2 0)
  IO.println s!"kernel {kern.name}: done"
