import Hashtree.Asm.Print
import Hashtree.Asm.X86Sym
import Hashtree.Asm.X86Run
import Hashtree.Kernels.X86.Shani

/-! `x86slices <outdir> <cut steps…>`: generate the slice files of shani_x2 (pilot). -/

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym
open Hashtree.Kernels.X86.Shani

def m0 := mem0s 4 rodata 24

def main (args : List String) : IO Unit := do
  let dir := args.headD "Gen"
  -- "auto": cut after every executed sha256rnds2 and at the final return
  let cuts : List Nat ← if args.getD 1 "" = "auto" then do
      -- cut positions depend on control flow only: find them on a concrete run (count 2)
      let mut cs : List Nat := []
      let ps : List Hashtree.Asm.X86Run.Prog := [⟨"hashtree_sha256_shani_x2", prog, 4, rodata.toArray⟩]
      let mc := Hashtree.Asm.X86Run.mem0 ps (Array.replicate 128 0) 24
      let mut s := Hashtree.Asm.X86Run.entry false 2 24
      let mut k := 0
      while !s.halted && k < 100000 do
        let isR := match prog[s.pc]? with
          | some (.sha256rnds2 _ _) => true
          | _ => false
        s := run prog 4 mc (fun _ => false) 1 s
        k := k + 1
        if isR || s.halted then cs := cs ++ [k]
      pure cs
    else pure ((args.drop 1).map String.toNat!)
  IO.println s!"{cuts.length} slices: {cuts}"
  let mut K := entryS 24
  let mut prev := 0
  let mut c := 0
  for cut in cuts do
    let n := cut - prev
    let R := run prog 4 m0 (fun _ => false) n K
    if R.err.isSome then
      IO.println s!"slice {c}: error {R.err}"
      return
    let K' := abstract R
    let kName := if c = 0 then "(entryS 24)" else s!"K{c}"
    let body := s!"import Hashtree.Asm.Slice\nimport Hashtree.Asm.X86Sym\nimport Hashtree.Kernels.X86.Shani\n" ++
      (if c = 0 then "" else s!"import Hashtree.Gen.Shani.S{c - 1}\n") ++
      "\nopen Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.Shani\n" ++
      "namespace Hashtree.Gen.Shani\n\n" ++
      s!"set_option maxRecDepth 200000 in\ndef K{c + 1} : State E Lin := {K'.toLean}\n\n" ++
      s!"set_option maxRecDepth 200000 in\ntheorem slice{c} : sliceCheck prog 4 (mem0s 4 rodata 24) (fun _ => false) {n} {kName} K{c + 1} [] = true := by\n  decide +kernel\n\n" ++
      "end Hashtree.Gen.Shani\n"
    IO.FS.writeFile s!"{dir}/S{c}.lean" body
    IO.println s!"slice {c}: steps {prev}→{cut} pc={R.pc} mem={R.mem.length} assume={R.assume.length}"
    K := K'
    prev := cut
    c := c + 1
