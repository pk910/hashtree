import Hashtree.Asm.Chain

/-!
# Expression labels at cuts

`Inv` (`Chain.lean`) labels each tracked location variable by one spec quantity.  Kernels that keep
partial results live across a cut (e.g. a message-schedule step spread over several rounds) need
labels that are *expressions* over spec quantities and input bytes: `QE`.  `Inv1` is `Inv` with
such labels; a plain quantity is `.q x`.
-/

set_option linter.unusedVariables false

namespace Hashtree.Asm
open Hashtree.Asm.SpecQ Hashtree.Spec

/-- An expression over spec quantities (`q`), input bytes (`m o`: byte `o` of the call's input,
zero-extended) and constants, with the lane operations of `E`. -/
inductive QE where
  | q (x : Q)
  | m (o : Nat)
  | c (v : W32)
  | add (a b : QE)
  | xor (a b : QE)
  | and (a b : QE)
  | or (a b : QE)
  | not (a : QE)
  | shl (a : QE) (n : Nat)
  | shr (a : QE) (n : Nat)
  | sar (a : QE) (n : Nat)
  | ror (a : QE) (n : Nat)
  | tern (imm : Nat) (a b d : QE)
  deriving DecidableEq, Repr, Inhabited

def QE.eval (V : Q → Word) (inp : Nat → Byte) : QE → W32
  | .q x => V x
  | .m o => (inp o).zeroExtend 32
  | .c v => v
  | .add a b => a.eval V inp + b.eval V inp
  | .xor a b => a.eval V inp ^^^ b.eval V inp
  | .and a b => a.eval V inp &&& b.eval V inp
  | .or a b => a.eval V inp ||| b.eval V inp
  | .not a => ~~~ a.eval V inp
  | .shl a n => a.eval V inp <<< n
  | .shr a n => a.eval V inp >>> n
  | .sar a n => (a.eval V inp).sshiftRight n
  | .ror a n => (a.eval V inp).rotateRight n
  | .tern i a b d => ternW i (a.eval V inp) (b.eval V inp) (d.eval V inp)

/-- At a cut: every labelled location variable holds the value of its label. -/
def Inv1 (L : List (Nat × QE)) (inp : Nat → Byte) (env : Key → W32) : Prop :=
  ∀ p ∈ L, env (.n p.1) = p.2.eval (qv inp) inp

theorem inv1_get {L : List (Nat × QE)} {inp : Nat → Byte} {env : Key → W32} (h : Inv1 L inp env) (k : Nat)
    (hk : k < L.length) : env (.n L[k].1) = L[k].2.eval (qv inp) inp := h _ (List.getElem_mem hk)

theorem inv1_of_get (L : List (Nat × QE)) (inp : Nat → Byte) (env : Key → W32)
    (h : ∀ k (hk : k < L.length), env (.n L[k].1) = L[k].2.eval (qv inp) inp) : Inv1 L inp env := by
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  exact h k hk

end Hashtree.Asm
