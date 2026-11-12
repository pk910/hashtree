import Hashtree.Proofs.ArmGen

/-!
`armproof <kernel> <count> <outdir> <first> <last>`: generate the proof files `P{c}.lean` and
`Final.lean` for one AArch64 kernel (Linux ELF object) called on `count` blocks: per slice the next
cut, the tracked trees, the kernel-checked slice and one lemma per labelled lane of the next cut;
`Final.lean` chains the slices into `out_final` (every output byte is the SHA-256 byte of its block).
Kernels: `sha_x1`, `neon_x1`, `neon_x4`.
-/

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmSym Hashtree.Asm.Scan

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
