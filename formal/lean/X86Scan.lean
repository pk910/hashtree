import Hashtree.Asm.Scan
import Hashtree.Kernels.X86.Shani
import Hashtree.Kernels.X86.Avx512X16
import Hashtree.Kernels.X86.Avx2X8
import Hashtree.Kernels.X86.AvxX4
import Hashtree.Kernels.X86.AvxX1
import Hashtree.Kernels.X86.SseX1

/-! `x86scan <kernel> <count> [step]`: per step, the round labels found per block (cut finding);
with `step`: every labelled location at that step. -/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Run Hashtree.Asm.Scan

def progs : List Prog := [
  ⟨"hashtree_sha256_shani_x2", Hashtree.Kernels.X86.Shani.prog, 4, Hashtree.Kernels.X86.Shani.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx512_x16", Hashtree.Kernels.X86.Avx512X16.prog, 6, Hashtree.Kernels.X86.Avx512X16.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx2_x8", Hashtree.Kernels.X86.Avx2X8.prog, 7, Hashtree.Kernels.X86.Avx2X8.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx_x4", Hashtree.Kernels.X86.AvxX4.prog, 8, Hashtree.Kernels.X86.AvxX4.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx_x1", Hashtree.Kernels.X86.AvxX1.prog, 9, Hashtree.Kernels.X86.AvxX1.rodata.toArray⟩,
  ⟨"hashtree_sha256_sse_x1", Hashtree.Kernels.X86.SseX1.prog, 10, Hashtree.Kernels.X86.SseX1.rodata.toArray⟩]

def randInput (seed n : Nat) : Array Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut a : Array Nat := #[]
  for _ in [0:n] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    a := a.push ((x >>> 33) % 256)
  return a

/-- One fetch-execute step within the program set (tail calls switch programs). -/
def step1 (m0 : Addr Int → Cell W32 Int) (p : Prog) (s : CS) : Prog × CS :=
  match p.code[s.pc]? with
  | some i =>
    let s' := exec p.ro m0 (fun _ => false) i s
    match s'.tail with
    | some t => match progs.find? (·.name = t) with
      | some q => (q, { s' with pc := 0, halted := false, tail := none })
      | none => (p, s')
    | none => (p, s')
  | none => (p, s.fail "pc")

def roundSummary (labs : List (Loc × List Q)) (count : Nat) : String :=
  String.intercalate " " ((List.range count).map fun n =>
    let ts := labs.flatMap (fun (_, qs) => qs.filterMap fun q => match q with
      | .A n' r t => if n' = n then some (r * 100 + t.toNat) else none
      | _ => none)
    s!"n{n}:{ts.foldl max 0}")

def main (args : List String) : IO Unit := do
  let name := args.getD 0 "hashtree_sha256_shani_x2"
  let count := (args.getD 1 "2").toNat!
  let only := args[2]?.map String.toNat!
  let i1 := randInput 11 (64 * count)
  let i2 := randInput 22 (64 * count)
  let t1 := table i1 count
  let t2 := table i2 count
  let m1 := mem0 progs i1 24
  let m2 := mem0 progs i2 24
  let some p0 := progs.find? (·.name = name) | IO.println "unknown kernel"
  let mut p1 := p0
  let mut p2 := p0
  let mut s1 := entry false count 24
  let mut s2 := entry false count 24
  let mut k := 0
  while !s1.halted && k < 2000000 do
    let labs := labels t1 t2 (lanes m1 s1) (lanes m2 s2)
    match only with
    | some j =>
      if j = k then
        for (loc, qs) in labs do IO.println s!"{loc} {qs}"
        -- unlabelled non-constant lanes
        let l1 := lanes m1 s1
        let l2 := lanes m2 s2
        for (loc, x) in l1 do
          match l2.find? (fun (p : Loc × W32) => p.1 == loc) with
          | some (_, y) => if x != y && !(labs.any (·.1 == loc)) then IO.println s!"{loc} UNLABELLED"
          | none => pure ()
        return
    | none =>
      let l1 := lanes m1 s1
      let l2 := lanes m2 s2
      let unl := (l1.filter fun (loc, x) => match l2.find? (fun (p : Loc × W32) => p.1 == loc) with
        | some (_, y) => x != y && !(labs.any (·.1 == loc))
        | none => false).length
      IO.println s!"{k} {p1.name.drop 16}@{s1.pc} {roundSummary labs count} unl={unl}"
    let (q1, s1') := step1 m1 p1 s1
    let (q2, s2') := step1 m2 p2 s2
    p1 := q1; p2 := q2; s1 := s1'; s2 := s2'
    k := k + 1
  IO.println s!"end step={k} err={s1.err}"
