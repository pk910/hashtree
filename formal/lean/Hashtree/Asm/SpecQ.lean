import Hashtree.SpecLemmas
import Std.Tactic.BVDecide

/-!
# Spec quantities of a call's blocks, and their one-step equations

`qv inp q` is the value of quantity `q` (see `Scan.lean`) for the input bytes `inp` (byte `i` of
the call's input).  The equations below express every quantity through earlier ones, so that a
lane lemma only needs `bv_decide` over a handful of atoms.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace Hashtree.Asm.SpecQ
open Hashtree.Spec

/-- Spec quantities (as in `Scan.Q`, with `Int` round indices for `A`/`E`). -/
inductive Q where
  | A (n r : Nat) (t : Int)
  | E (n r : Nat) (t : Int)
  | W (n r t : Nat)
  | KW (n r t : Nat)
  | R (n t : Nat)
  | H (n r i : Nat)
  | M1 (n r t : Nat)
  | M2 (n r t : Nat)
  | HB (n i : Nat)
  deriving DecidableEq, Repr

variable (inp : Nat → Byte)

/-- Block `n` of the input. -/
def blk (n : Nat) : Fin 64 → Byte := fun i => inp (64 * n + i.val)

/-- Hash value before compression `r` of node `n` (`r = 2`: the digest). -/
def Hr (n : Nat) : Nat → State
  | 0 => H0
  | 1 => compress H0 (inWords (blk inp n))
  | _ => compress (compress H0 (inWords (blk inp n))) padBlock

/-- Message block of compression `r`. -/
def Br (n : Nat) : Nat → List Word
  | 0 => inWords (blk inp n)
  | _ => padBlock

def fld (s : State) : Nat → Word
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d | 4 => s.e | 5 => s.f | 6 => s.g | _ => s.h

def bswap (w : Word) : Word :=
  (w >>> 24 &&& 0xff) ||| ((w >>> 16 &&& 0xff) <<< 8) ||| ((w >>> 8 &&& 0xff) <<< 16) ||| ((w &&& 0xff) <<< 24)

def qv : Q → Word
  | .A n r t => if 0 ≤ t then (rs (Hr inp n r) (Br inp n r) t.toNat).a
      else if t = -1 then (Hr inp n r).b else if t = -2 then (Hr inp n r).c else (Hr inp n r).d
  | .E n r t => if 0 ≤ t then (rs (Hr inp n r) (Br inp n r) t.toNat).e
      else if t = -1 then (Hr inp n r).f else if t = -2 then (Hr inp n r).g else (Hr inp n r).h
  | .W n r t => W (Br inp n r) t
  | .KW n r t => K t + W (Br inp n r) t
  | .R n t => (List.range 4).foldl (fun acc k =>
      acc ||| ((inp (64 * n + 4 * t + k)).zeroExtend 32 <<< (8 * k))) 0
  | .H n r i => fld (Hr inp n r) i
  | .M1 n r t => W (Br inp n r) t + sigma0 (W (Br inp n r) (t + 1))
  | .M2 n r t => W (Br inp n r) t + sigma0 (W (Br inp n r) (t + 1)) + W (Br inp n r) (t + 9)
  | .HB n i => bswap (fld (Hr inp n 2) i)

/-! ## The state after `t` rounds is made of `A`/`E` quantities -/

theorem rs_fields (n r : Nat) : ∀ t : Nat,
    rs (Hr inp n r) (Br inp n r) t =
      ⟨qv inp (.A n r t), qv inp (.A n r (t - 1)), qv inp (.A n r (t - 2)), qv inp (.A n r (t - 3)),
       qv inp (.E n r t), qv inp (.E n r (t - 1)), qv inp (.E n r (t - 2)), qv inp (.E n r (t - 3))⟩
  | 0 => by simp [qv, rs_zero]
  | t + 1 => by
    have ih := rs_fields n r t
    have e1 : ((t + 1 : Nat) : Int) - 1 = (t : Int) := by omega
    have e2 : ((t + 1 : Nat) : Int) - 2 = (t : Int) - 1 := by omega
    have e3 : ((t + 1 : Nat) : Int) - 3 = (t : Int) - 2 := by omega
    have hA : qv inp (.A n r ((t + 1 : Nat) : Int)) = (rs (Hr inp n r) (Br inp n r) (t + 1)).a := by
      simp only [qv]; rw [if_pos (by omega)]; rfl
    have hE : qv inp (.E n r ((t + 1 : Nat) : Int)) = (rs (Hr inp n r) (Br inp n r) (t + 1)).e := by
      simp only [qv]; rw [if_pos (by omega)]; rfl
    have hA0 : qv inp (.A n r (t : Int)) = (rs (Hr inp n r) (Br inp n r) t).a := by
      simp only [qv]; rw [if_pos (by omega)]; rfl
    have hE0 : qv inp (.E n r (t : Int)) = (rs (Hr inp n r) (Br inp n r) t).e := by
      simp only [qv]; rw [if_pos (by omega)]; rfl
    rw [e1, e2, e3, hA, hE, hA0, hE0, rs_succ, ih]
    simp only [State.round]

/-! ## One-step equations -/

theorem qA_succ (n r t : Nat) :
    qv inp (.A n r ((t : Int) + 1)) =
      (qv inp (.E n r ((t : Int) - 3)) + Sigma1 (qv inp (.E n r t)) +
        Ch (qv inp (.E n r t)) (qv inp (.E n r ((t : Int) - 1))) (qv inp (.E n r ((t : Int) - 2))) +
        qv inp (.KW n r t)) +
      (Sigma0 (qv inp (.A n r t)) + Maj (qv inp (.A n r t)) (qv inp (.A n r ((t : Int) - 1)))
        (qv inp (.A n r ((t : Int) - 2)))) := by
  have h : qv inp (.A n r ((t : Int) + 1)) = (rs (Hr inp n r) (Br inp n r) (t + 1)).a := by
    simp only [qv]; rw [if_pos (by omega)]; congr 2
  rw [h, rs_succ, rs_fields inp n r t]
  simp only [State.round, qv, BitVec.add_assoc]

theorem qE_succ (n r t : Nat) :
    qv inp (.E n r ((t : Int) + 1)) =
      qv inp (.A n r ((t : Int) - 3)) +
      (qv inp (.E n r ((t : Int) - 3)) + Sigma1 (qv inp (.E n r t)) +
        Ch (qv inp (.E n r t)) (qv inp (.E n r ((t : Int) - 1))) (qv inp (.E n r ((t : Int) - 2))) +
        qv inp (.KW n r t)) := by
  have h : qv inp (.E n r ((t : Int) + 1)) = (rs (Hr inp n r) (Br inp n r) (t + 1)).e := by
    simp only [qv]; rw [if_pos (by omega)]; congr 2
  rw [h, rs_succ, rs_fields inp n r t]
  simp only [State.round, qv, BitVec.add_assoc]

theorem Br_length (n r : Nat) : (Br inp n r).length = 16 := by
  cases r with
  | zero => simp [Br, inWords]
  | succ r => simp [Br, padBlock]

theorem qW_rec (n r t : Nat) (h1 : 16 ≤ t) (h2 : t < 64) :
    qv inp (.W n r t) = sigma1 (qv inp (.W n r (t - 2))) + qv inp (.W n r (t - 7)) +
      sigma0 (qv inp (.W n r (t - 15))) + qv inp (.W n r (t - 16)) := by
  simp only [qv]; exact W_rec _ (Br_length inp n r) t h1 h2

theorem qKW (n r t : Nat) : qv inp (.KW n r t) = K t + qv inp (.W n r t) := rfl
theorem qM1 (n r t : Nat) : qv inp (.M1 n r t) = qv inp (.W n r t) + sigma0 (qv inp (.W n r (t + 1))) := rfl
theorem qM2 (n r t : Nat) : qv inp (.M2 n r t) = qv inp (.M1 n r t) + qv inp (.W n r (t + 9)) := rfl
theorem qHB (n i : Nat) : qv inp (.HB n i) = bswap (qv inp (.H n 2 i)) := rfl

/-- Message words of the input block are the byte-swapped little-endian loads. -/
theorem qW_R (n t : Nat) (ht : t < 16) : qv inp (.W n 0 t) = bswap (qv inp (.R n t)) := by
  simp only [qv, Br]
  rw [W_lt16 _ (by simp [inWords]) t ht]
  simp only [inWords, List.getD_eq_getElem?_getD, List.getElem?_ofFn, ht, dite_true, Option.getD_some, blk,
    beWord, bswap, List.range, List.range.loop, List.foldl]
  have e : ∀ k, k < 4 → (64 * n + (4 * t + k)) = 64 * n + 4 * t + k := fun k _ => by omega
  simp only [Nat.add_assoc] at *
  generalize inp (64 * n + 4 * t) = b0
  generalize inp (64 * n + (4 * t + 1)) = b1
  generalize inp (64 * n + (4 * t + 2)) = b2
  generalize inp (64 * n + (4 * t + 3)) = b3
  bv_decide

/-- Hash values: the feed-forward of the compressions. -/
theorem qH_succ (n r i : Nat) (hr : r < 2) (hi : i < 8) :
    qv inp (.H n (r + 1) i) = qv inp (.H n r i) +
      qv inp (if i < 4 then .A n r (64 - (i : Int)) else .E n r (64 - ((i - 4 : Nat) : Int))) := by
  have hH : Hr inp n (r + 1) = (Hr inp n r).add (rs (Hr inp n r) (Br inp n r) 64) := by
    cases r with
    | zero => rfl
    | succ r => have : r = 0 := by omega
                subst this; rfl
  simp only [qv, hH, rs_fields inp n r 64]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;> simp [fld, State.add, qv]

/-- The state words before compression `r` are its initial hash value. -/
theorem qA_init (n r : Nat) (j : Nat) (hj : j < 4) :
    qv inp (.A n r (-(j : Int))) = qv inp (.H n r j) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;>
    simp [qv, fld, rs_zero]

theorem qE_init (n r : Nat) (j : Nat) (hj : j < 4) :
    qv inp (.E n r (-(j : Int))) = qv inp (.H n r (j + 4)) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;>
    simp [qv, fld, rs_zero]

/-! ## Closed quantities (constants) -/

theorem qW1 (n t : Nat) : qv inp (.W n 1 t) = W padBlock t := rfl
theorem qKW1 (n t : Nat) : qv inp (.KW n 1 t) = K t + W padBlock t := rfl
theorem qH0 (n i : Nat) : qv inp (.H n 0 i) = fld H0 i := rfl

/-- The raw little-endian input word, as bytes. -/
theorem qR (n t : Nat) : qv inp (.R n t) =
    ((((0 : Word) ||| (inp (64 * n + 4 * t + 0)).zeroExtend 32 <<< 0) |||
      (inp (64 * n + 4 * t + 1)).zeroExtend 32 <<< 8) |||
      (inp (64 * n + 4 * t + 2)).zeroExtend 32 <<< 16) |||
      (inp (64 * n + 4 * t + 3)).zeroExtend 32 <<< 24 := by
  simp [qv, List.range, List.range.loop]

/-- The recurrence through the SHA256MSG1 partial sum. -/
theorem qW_recM (n r t : Nat) (h1 : 16 ≤ t) (h2 : t < 64) :
    qv inp (.W n r t) = sigma1 (qv inp (.W n r (t - 2))) + qv inp (.W n r (t - 7)) +
      qv inp (.M1 n r (t - 16)) := by
  rw [qW_rec inp n r t h1 h2, qM1, show t - 16 + 1 = t - 15 by omega]
  generalize qv inp (.W n r (t - 2)) = a
  generalize qv inp (.W n r (t - 7)) = b
  generalize qv inp (.W n r (t - 15)) = c
  generalize qv inp (.W n r (t - 16)) = d
  bv_decide

/-- The recurrence through the second partial sum. -/
theorem qW_recM2 (n r t : Nat) (h1 : 16 ≤ t) (h2 : t < 64) :
    qv inp (.W n r t) = sigma1 (qv inp (.W n r (t - 2))) + qv inp (.M2 n r (t - 16)) := by
  rw [qW_recM inp n r t h1 h2, qM2, show t - 16 + 9 = t - 7 by omega]
  generalize qv inp (.W n r (t - 2)) = a
  generalize qv inp (.W n r (t - 7)) = b
  generalize qv inp (.M1 n r (t - 16)) = c
  bv_decide

/-! ## Literal-index forms (for generated proofs) -/

theorem qA_succI (n r : Nat) (t : Int) (ht : 0 ≤ t) :
    qv inp (.A n r (t + 1)) =
      (qv inp (.E n r (t - 3)) + Sigma1 (qv inp (.E n r t)) +
        Ch (qv inp (.E n r t)) (qv inp (.E n r (t - 1))) (qv inp (.E n r (t - 2))) +
        qv inp (.KW n r t.toNat)) +
      (Sigma0 (qv inp (.A n r t)) + Maj (qv inp (.A n r t)) (qv inp (.A n r (t - 1)))
        (qv inp (.A n r (t - 2)))) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ht
  exact qA_succ inp n r m

theorem qE_succI (n r : Nat) (t : Int) (ht : 0 ≤ t) :
    qv inp (.E n r (t + 1)) =
      qv inp (.A n r (t - 3)) +
      (qv inp (.E n r (t - 3)) + Sigma1 (qv inp (.E n r t)) +
        Ch (qv inp (.E n r t)) (qv inp (.E n r (t - 1))) (qv inp (.E n r (t - 2))) +
        qv inp (.KW n r t.toNat)) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ht
  exact qE_succ inp n r m

theorem qA_initI (n r j : Nat) (t : Int) (hj : j < 4) (ht : t = -(j : Int)) :
    qv inp (.A n r t) = qv inp (.H n r j) := by subst ht; exact qA_init inp n r j hj

theorem qE_initI (n r j : Nat) (t : Int) (hj : j < 4) (ht : t = -(j : Int)) :
    qv inp (.E n r t) = qv inp (.H n r (j + 4)) := by subst ht; exact qE_init inp n r j hj

theorem qH_succA (n r i : Nat) (t : Int) (hr : r < 2) (hi : i < 4) (ht : t = 64 - (i : Int)) :
    qv inp (.H n (r + 1) i) = qv inp (.H n r i) + qv inp (.A n r t) := by
  rw [qH_succ inp n r i hr (by omega), if_pos hi, ht]

theorem qH_succE (n r i : Nat) (t : Int) (hr : r < 2) (hi : 4 ≤ i ∧ i < 8) (ht : t = 64 - ((i - 4 : Nat) : Int)) :
    qv inp (.H n (r + 1) i) = qv inp (.H n r i) + qv inp (.E n r t) := by
  rw [qH_succ inp n r i hr (by omega), if_neg (by omega), ht]

/-! ## The padding block's schedule as tables (checked once by the kernel) -/

def WpadTab : List Word := [
  0x80000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000200,
  0x80000000, 0x01400000, 0x00205000, 0x00005088, 0x22000800, 0x22550014, 0x05089742, 0xa0000020,
  0x5a880000, 0x005c9400, 0x0016d49d, 0xfa801f00, 0xd33225d0, 0x11675959, 0xf6e6bfda, 0xb30c1549,
  0x08b2b050, 0x9d7c4c27, 0x0ce2a393, 0x88e6e1ea, 0xa52b4335, 0x67a16f49, 0xd732016f, 0x4eeb2e91,
  0x5dbf55e5, 0x8eee2335, 0xe2bc5ec2, 0xa83f4394, 0x45ad78f7, 0x36f3d0cd, 0xd99c05e8, 0xb0511dc7,
  0x69bc7ac4, 0xbd11375b, 0xe3ba71e5, 0x3b209ff2, 0x18feee17, 0xe25ad9e7, 0x13375046, 0x0515089d,
  0x4f0d0f04, 0x2627484e, 0x310128d2, 0xc668b434, 0x420841cc, 0x62d311b8, 0xe59ba771, 0x85a7a484]

def KWpadTab : List Word := [
  0xc28a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf374,
  0x649b69c1, 0xf0fe4786, 0x0fe1edc6, 0x240cf254, 0x4fe9346f, 0x6cc984be, 0x61b9411e, 0x16f988fa,
  0xf2c65152, 0xa88e5a6d, 0xb019fc65, 0xb9d99ec7, 0x9a1231c3, 0xe70eeaa0, 0xfdb1232b, 0xc7353eb0,
  0x3069bad5, 0xcb976d5f, 0x5a0f118f, 0xdc1eeefd, 0x0a35b689, 0xde0b7a04, 0x58f4ca9d, 0xe15d5b16,
  0x007f3e86, 0x37088980, 0xa507ea32, 0x6fab9537, 0x17406110, 0x0d8cd6f1, 0xcdaa3b6d, 0xc0bbbe37,
  0x83613bda, 0xdb48a363, 0x0b02e931, 0x6fd15ca7, 0x521afaca, 0x31338431, 0x6ed41a95, 0x6d437890,
  0xc39c91f2, 0x9eccabbd, 0xb5c9a0e6, 0x532fb63c, 0xd2c741c6, 0x07237ea3, 0xa4954b68, 0x4c191d76]

theorem Wpad_eq : ∀ t, t < 64 → W padBlock t = WpadTab.getD t 0 := by decide +kernel
theorem KWpad_eq : ∀ t, t < 64 → Spec.K t + W padBlock t = KWpadTab.getD t 0 := by decide +kernel

theorem qW1T (n t : Nat) (ht : t < 64) : qv inp (.W n 1 t) = WpadTab.getD t 0 := Wpad_eq t ht
theorem qKW1T (n t : Nat) (ht : t < 64) : qv inp (.KW n 1 t) = KWpadTab.getD t 0 := KWpad_eq t ht

theorem qH_ofA (n r j : Nat) (t : Int) (hj : j < 4) (ht : t = -(j : Int)) :
    qv inp (.H n r j) = qv inp (.A n r t) := (qA_initI inp n r j t hj ht).symm

theorem qH_ofE (n r j : Nat) (t : Int) (hj : j < 4) (ht : t = -(j : Int)) :
    qv inp (.H n r (j + 4)) = qv inp (.E n r t) := (qE_initI inp n r j t hj ht).symm

end Hashtree.Asm.SpecQ
