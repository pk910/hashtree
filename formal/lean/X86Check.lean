import Hashtree.Asm.X86Run
import Hashtree.Kernels.X86.Shani
import Hashtree.Kernels.X86.Avx512X16
import Hashtree.Kernels.X86.Avx2X8
import Hashtree.Kernels.X86.AvxX4
import Hashtree.Kernels.X86.AvxX1
import Hashtree.Kernels.X86.SseX1
import Hashtree.Kernels.X86Win.Shani
import Hashtree.Kernels.X86Win.Avx512X16
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Kernels.X86Win.AvxX1
import Hashtree.Kernels.X86Win.SseX1

/-! `x86check`: run every x86 kernel model on random inputs for many counts and compare with
`Spec.node`; with `--dump <kernel> <count> <seed>` print the output (for the CPU comparison). -/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Run

def progs : List Prog := [
  ⟨"hashtree_sha256_shani_x2", Hashtree.Kernels.X86.Shani.prog, 4, Hashtree.Kernels.X86.Shani.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx512_x16", Hashtree.Kernels.X86.Avx512X16.prog, 6, Hashtree.Kernels.X86.Avx512X16.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx2_x8", Hashtree.Kernels.X86.Avx2X8.prog, 7, Hashtree.Kernels.X86.Avx2X8.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx_x4", Hashtree.Kernels.X86.AvxX4.prog, 8, Hashtree.Kernels.X86.AvxX4.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx_x1", Hashtree.Kernels.X86.AvxX1.prog, 9, Hashtree.Kernels.X86.AvxX1.rodata.toArray⟩,
  ⟨"hashtree_sha256_sse_x1", Hashtree.Kernels.X86.SseX1.prog, 10, Hashtree.Kernels.X86.SseX1.rodata.toArray⟩]

def progsWin : List Prog := [
  ⟨"hashtree_sha256_shani_x2", Hashtree.Kernels.X86Win.Shani.prog, 4, Hashtree.Kernels.X86Win.Shani.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx512_x16", Hashtree.Kernels.X86Win.Avx512X16.prog, 6, Hashtree.Kernels.X86Win.Avx512X16.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx2_x8", Hashtree.Kernels.X86Win.Avx2X8.prog, 7, Hashtree.Kernels.X86Win.Avx2X8.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx_x4", Hashtree.Kernels.X86Win.AvxX4.prog, 8, Hashtree.Kernels.X86Win.AvxX4.rodata.toArray⟩,
  ⟨"hashtree_sha256_avx_x1", Hashtree.Kernels.X86Win.AvxX1.prog, 9, Hashtree.Kernels.X86Win.AvxX1.rodata.toArray⟩,
  ⟨"hashtree_sha256_sse_x1", Hashtree.Kernels.X86Win.SseX1.prog, 10, Hashtree.Kernels.X86Win.SseX1.rodata.toArray⟩]

def randInput (seed n : Nat) : Array Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut a : Array Nat := #[]
  for _ in [0:n] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    a := a.push ((x >>> 33) % 256)
  return a

def check1 (win : Bool) (name : String) (count seed : Nat) (sp0 : Int) : IO Bool := do
  let ps := if win then progsWin else progs
  let input := randInput seed (64 * count)
  let m0 := mem0 ps input sp0
  let (s, path) := runChain ps m0 2000000 8 name (entry win count sp0)
  let ok := s.err.isNone && s.halted && s.tail.isNone && outBytes m0 s (32 * count) == some (expected input count)
  unless ok do
    IO.println s!"FAIL win={win} {name} count={count} sp0={sp0} err={s.err} halted={s.halted} tail={s.tail} path={path}"
  let o := abiObs win count sp0 s
  IO.println s!"ABI win={win} {name} count={count} sp0={sp0} depth={o.depth} callerWrites={o.callerWrites} clobbered={o.clobbered} spOk={o.spOk}"
  return ok

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--dump", k, c, seed] =>
    let count := c.toNat!
    let input := randInput seed.toNat! (64 * count)
    let m0 := mem0 progs input 24
    let (s, _) := runChain progs m0 2000000 8 k (entry false count 24)
    IO.println s!"{(outBytes m0 s (32 * count)).getD []}"
    return 0
  | _ =>
    let mut fails := 0
    for win in [false, true] do
      for p in (if win then progsWin else progs) do
        let mut n := 0
        for count in [0:35] do
          for sp0 in [8, 24, 40, 56] do
            unless (← check1 win p.name count (count + 7) sp0) do fails := fails + 1
            n := n + 1
        IO.println s!"{if win then "win64" else "sysv"} {p.name}: {n} runs"
    IO.println s!"failures: {fails}"
    return (if fails = 0 then 0 else 1)
