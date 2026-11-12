import Hashtree.Asm.ArmRun
import Hashtree.Asm.ArmInsnTests
import Hashtree.Kernels.Arm.ShaX1
import Hashtree.Kernels.Arm.NeonX4
import Hashtree.Kernels.Arm.NeonX1
import Hashtree.Kernels.ArmMac.ShaX1
import Hashtree.Kernels.ArmMac.NeonX4
import Hashtree.Kernels.ArmMac.NeonX1

/-! `armcheck`: run every AArch64 kernel model (Linux ELF and macOS Mach-O objects) on random
inputs for counts 0..34 and SP entry offsets 0, 16, 32, 48, following tail calls, and compare
with `Spec.node`; also check the AAPCS64 observations (callee-saved registers, SP, write
footprint; reads are confined to the input, the rodata and bytes written before, by the poison
memory of `ArmRun.mem0`).

* `armcheck --dump <linux|mac> <kernel> <count> <seed>`: print the output bytes;
* `armcheck --dumpall <linux|mac>`: outputs of every kernel for counts 0..34 (seed count + 7), in
  the format of `tools/arm_kernel_harness.c` (comparison with the real code under qemu,
  `tools/arm_qemu.sh`);
* `armcheck --sym`: one iteration of each kernel loop with a symbolic count (`Lin`);
* `armcheck --insn <file>`: per-instruction differential test against vectors recorded natively
  (`tools/arm_insn_diff.py`). -/

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun

def progsLinux : List Prog := [
  ⟨"hashtree_sha256_sha_x1", Hashtree.Kernels.Arm.ShaX1.prog, 4, Hashtree.Kernels.Arm.ShaX1.rodata.toArray⟩,
  ⟨"hashtree_sha256_neon_x4", Hashtree.Kernels.Arm.NeonX4.prog, 6, Hashtree.Kernels.Arm.NeonX4.rodata.toArray⟩,
  ⟨"hashtree_sha256_neon_x1", Hashtree.Kernels.Arm.NeonX1.prog, 7, Hashtree.Kernels.Arm.NeonX1.rodata.toArray⟩]

def progsMac : List Prog := [
  ⟨"_hashtree_sha256_sha_x1", Hashtree.Kernels.ArmMac.ShaX1.prog, 4, Hashtree.Kernels.ArmMac.ShaX1.rodata.toArray⟩,
  ⟨"_hashtree_sha256_neon_x4", Hashtree.Kernels.ArmMac.NeonX4.prog, 6, Hashtree.Kernels.ArmMac.NeonX4.rodata.toArray⟩,
  ⟨"_hashtree_sha256_neon_x1", Hashtree.Kernels.ArmMac.NeonX1.prog, 7, Hashtree.Kernels.ArmMac.NeonX1.rodata.toArray⟩]

def randInput (seed n : Nat) : Array Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut a : Array Nat := #[]
  for _ in [0:n] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    a := a.push ((x >>> 33) % 256)
  return a

/-- One run; `none` = pass, else a failure description. Also returns the stack depth. -/
def check1 (ps : List Prog) (name : String) (count seed : Nat) (sp0 : Int) : Option String × Int :=
  let input := randInput seed (64 * count)
  let m0 := mem0 ps input
  let (s, path) := runChain ps m0 4000000 8 name (entry count sp0)
  let outOk := outBytes m0 s (32 * count) == some (expected input count)
  let o := abiObs count sp0 s
  let ok := s.err.isNone && s.halted && s.tail.isNone && outOk && o.callerWrites.isEmpty &&
    o.strayWrites.isEmpty && o.outOfRange.isEmpty && o.clobbered.isEmpty && o.spOk
  if ok then (none, o.depth)
  else (some s!"FAIL {name} count={count} sp0={sp0} err={s.err} halted={s.halted} tail={s.tail} path={path} out={outOk} pc={s.pc} abi={repr o}", o.depth)

/-! ## Per-instruction differential test -/

def hexVal (s : String) : Nat :=
  s.foldl (fun n c =>
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
    16 * n + d) 0

def intVal (s : String) : Int := s.toInt!

def mkState (g : List (Val W32 Int)) (vr : List (List W32)) : CS :=
  { gpr := g, vr := vr, flags := none, mem := [], pc := 0, halted := false, tail := none,
    err := none, assume := [] }

/-- Vector line: `idx` then hex words: v0..v7 (32), x2..x5 (8: lo, hi), input buffer (16),
then the native results v0..v7 (32), x2..x5 (8), output buffer (16), and the decimal changes of
x0 and x1. -/
def insnCheck (line : String) : Except String Unit := do
  let toks := (line.splitOn " ").filter (· ≠ "")
  if toks.length ≠ 1 + 56 + 56 + 2 then throw s!"bad line: {toks.length} fields"
  let idx := toks[0]!.toNat!
  let (name, ins) ← match insnTests[idx]? with
    | some t => pure t
    | none => throw s!"no test {idx}"
  let w := (toks.drop 1).take 112 |>.map (fun t => BitVec.ofNat 32 (hexVal t))
  let dx0 := intVal toks[113]!
  let dx1 := intVal toks[114]!
  let inV := (List.range 8).map fun r => (List.range 16).map fun l =>
    if l < 4 then w[4 * r + l]! else (0 : W32)
  let inX := (List.range 4).map fun r => (w[32 + 2 * r]!, w[33 + 2 * r]!)
  let inBuf := (List.range 64).map fun i => ((w[40 + i / 4]!.toNat >>> (8 * (i % 4))) % 256)
  let g := (List.range 32).map junkG
  let g := g.set 0 (.ptr ⟨rOut, 0⟩)
  let g := g.set 1 (.ptr ⟨rIn, 0⟩)
  let g := (List.range 4).foldl (fun g r => g.set (r + 2) (.num inX[r]!.1 inX[r]!.2)) g
  let g := g.set 7 (.ptr ⟨rNum, 64⟩)
  let s0 := mkState g (inV ++ List.replicate 24 (List.replicate 16 0))
  let m0 : Addr Int → Cell W32 Int := fun a =>
    if a.region = rIn then .dat (BitVec.ofNat 32 (inBuf.getD a.off.toNat 0)) 0 else .dat 0 0
  let s := exec 4 m0 (fun _ => false) ins s0
  if let some e := s.err then throw s!"{name}: model error {e}"
  let got := (List.range 8).flatMap (fun r => getQ s r)
  let gotX ← (List.range 4).mapM fun r => match s.getG (r + 2) with
    | .num lo hi => pure [lo, hi]
    | v => throw s!"{name}: x{r + 2} not data: {repr v}"
  let gotX := gotX.flatten
  let gotOut ← (List.range 16).mapM fun k => do
    let bs ← (List.range 4).mapM fun j => match readCell m0 s ⟨rOut, (4 * k + j : Nat)⟩ with
      | .ok (.dat x b) => pure (byteOf x b)
      | _ => throw s!"{name}: output byte not data"
    pure (bs[0]! ||| (bs[1]! <<< 8) ||| (bs[2]! <<< 16) ||| (bs[3]! <<< 24))
  let d0 ← match s.getG 0 with | .ptr ⟨2, o⟩ => pure o | _ => throw s!"{name}: x0"
  let d1 ← match s.getG 1 with | .ptr ⟨1, o⟩ => pure o | _ => throw s!"{name}: x1"
  let want := (w.drop 56)
  let mine := got ++ gotX ++ gotOut
  if mine ≠ want ∨ d0 ≠ dx0 ∨ d1 ≠ dx1 then
    throw s!"{name}: mismatch\n  model  {mine.map (·.toHex)} {d0} {d1}\n  native {want.map (·.toHex)} {dx0} {dx1}"

/-! ## Symbolic smoke run (`Lin` control): one iteration of each kernel's loop with a symbolic
count `s2`, checking that the generic `exec` runs a loop body without errors (aliasing,
alignment, flags, pointer/data confusion).  Data lanes use the constant-propagation domain
`Option W32` (`none` = unknown) instead of `E`: with `E` the core's `Lane.same` (structural
`decide (a = b)` on expression DAGs, used by every `loadLane` of a stored lane) takes time
exponential in the round number (measured: ×5 per round on neon_x1's stack reloads). -/

instance : Lane (Option W32) where
  const := some
  add a b := do pure ((← a) + (← b))
  xor a b := do pure ((← a) ^^^ (← b))
  and a b := match a, b with
    | some 0, _ => some 0 | _, some 0 => some 0
    | some x, some y => some (x &&& y) | _, _ => none
  or a b := do pure ((← a) ||| (← b))
  not a := a.map (~~~ ·)
  shl a n := a.map (fun (x : W32) => x <<< n)
  shr a n := a.map (fun (x : W32) => x >>> n)
  sar a n := a.map (fun x => x.sshiftRight n)
  ror a n := a.map (fun x => x.rotateRight n)
  tern i a b c := do pure (ternW i (← a) (← b) (← c))
  asConst := id
  same _ _ := false

abbrev SS := State (Option W32) Lin

def symMem0 (p : Prog) : Addr Lin → Cell (Option W32) Lin := fun a =>
  match a.off.asInt with
  | some k =>
    if a.region = p.ro then .dat (some (BitVec.ofNat 32 (p.rodata.getD k.toNat 0))) 0
    else .dat none 0
  | none => .dat none 0

def symEntry : SS :=
  let g : List (Val (Option W32) Lin) := (List.range 32).map fun _ => .num none none
  let g := g.set 0 (.ptr ⟨rOut, Lin.ofInt 0⟩)
  let g := g.set 1 (.ptr ⟨rIn, Lin.ofInt 0⟩)
  let g := g.set 2 (.ptr ⟨rNum, Lin.sym 2⟩)
  let g := g.set 30 (.ptr ⟨rRet, Lin.ofInt 0⟩)
  let g := g.set 31 (.ptr ⟨rStack, Lin.ofInt 0⟩)
  let vr := (List.range 32).map fun _ => List.replicate 16 none
  { gpr := g, vr := vr, flags := none, mem := [], pc := 0, halted := false, tail := none,
    err := none, assume := [] }

def loopHead (code : Array Instr) : Nat :=
  code.foldl (fun h i => match i with | .b t => t | _ => h) 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--dump", set, k, c, seed] =>
    let ps := if set = "mac" then progsMac else progsLinux
    let count := c.toNat!
    let input := randInput seed.toNat! (64 * count)
    let m0 := mem0 ps input
    let (s, _) := runChain ps m0 4000000 8 k (entry count 16)
    IO.println s!"{(outBytes m0 s (32 * count)).getD []}"
    return (if s.err.isNone then 0 else 1)
  | ["--dumpall", set] =>
    let ps := if set = "mac" then progsMac else progsLinux
    let mut bad := 0
    for p in ps do
      for count in [0:35] do
        let input := randInput (count + 7) (64 * count)
        let m0 := mem0 ps input
        let (s, _) := runChain ps m0 4000000 8 p.name (entry count 16)
        if s.err.isSome then bad := bad + 1
        let hex := ((outBytes m0 s (32 * count)).getD []).foldl (fun acc b =>
          acc ++ (if b < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 b)) ""
        IO.println s!"{p.name} {count} {hex}"
    return (if bad = 0 then 0 else 1)
  | ["--sym"] =>
    for p in progsLinux ++ progsMac do
      let t0 ← IO.monoMsNow
      let head := loopHead p.code
      let m0 := symMem0 p
      let mut st := symEntry
      let mut arr := 0
      let mut n := 0
      for _ in [0:100000] do
        if st.halted then break
        if st.pc = head then arr := arr + 1
        if arr = 2 then break
        match p.code[st.pc]? with
        | some i => st := exec p.ro m0 (fun _ => false) i st
        | none => st := st.fail "pc out of program"
        n := n + 1
      let t1 ← IO.monoMsNow
      let outCells := (st.mem.filter (·.1.region = rOut)).length
      IO.println s!"{p.name}: loop head {head}, {n} steps, err={st.err}, halted={st.halted}, assumed={repr st.assume}, output bytes {outCells}, {t1 - t0} ms"
    return 0
  | ["--insn", file] =>
    let lines := (← IO.FS.lines file).toList.filter (· ≠ "")
    let mut fails := 0
    let mut names : List String := []
    for ln in lines do
      let idx := ((ln.splitOn " ").head!).toNat!
      let name := (insnTests[idx]?.map (·.1)).getD "?"
      unless names.contains name do names := name :: names
      match insnCheck ln with
      | .ok () => pure ()
      | .error e =>
        fails := fails + 1
        if fails ≤ 20 then IO.println s!"FAIL {e}"
    IO.println s!"instruction tests: {names.length} forms, {lines.length} vectors, failures: {fails}"
    return (if fails = 0 then 0 else 1)
  | _ =>
    -- jobs, run by 8 worker tasks (the machine is shared)
    let mut jobs : Array (String × List Prog × String × Nat × Int) := #[]
    for (set, ps) in [("linux", progsLinux), ("mac", progsMac)] do
      for p in ps do
        for count in [0:35] do
          for sp0 in [0, 16, 32, 48] do
            jobs := jobs.push (set, ps, p.name, count, sp0)
    let nw := 8
    let workers := (List.range nw).map fun k => Task.spawn fun _ =>
      (List.range jobs.size).filterMap fun j =>
        if j % nw = k then
          let (set, ps, name, count, sp0) := jobs[j]!
          some (set, name, check1 ps name count (count + 7) sp0)
        else none
    let results := workers.flatMap (·.get)
    let mut fails := 0
    let mut summary : List ((String × String) × (Nat × Nat × Int)) := []
    for (set, name, (r, depth)) in results do
      if let some msg := r then
        IO.println msg
        fails := fails + 1
      let (n, f, d) := (summary.lookup (set, name)).getD (0, 0, 0)
      let e := (n + 1, f + (if r.isSome then 1 else 0), max d depth)
      summary := ((set, name), e) :: summary.filter (·.1 != (set, name))
    for (k, (n, f, d)) in summary.reverse do
      IO.println s!"{k.1} {k.2}: {n} runs, {f} failures, max stack depth {d} bytes"
    IO.println s!"failures: {fails}"
    return (if fails = 0 then 0 else 1)
