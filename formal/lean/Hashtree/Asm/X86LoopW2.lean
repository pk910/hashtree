import Hashtree.Asm.X86Loop2
import Hashtree.Asm.X86SymW

/-! Lookup checks for generated files (a kernel's pushes at the wrapper call state). -/

namespace Hashtree.Asm.X86SymW
open Hashtree.Asm Hashtree.Asm.X86

def lkIsW (a : Addr Lin) (L : List (Addr Lin × Cell E Lin)) (c : Cell E Lin) : Bool :=
  match lookup a L with
  | .ok (some c') => c' == c
  | _ => false

theorem lkIsW_sound (a : Addr Lin) (L : List (Addr Lin × Cell E Lin)) (c : Cell E Lin) (h : lkIsW a L c = true) :
    lookup a L = .ok (some c) := by
  simp only [lkIsW] at h
  split at h
  · rename_i c' hl; simp only [beq_iff_eq] at h; rw [hl, h]
  · cases h

end Hashtree.Asm.X86SymW
