import Hashtree.GoGeneric
import Hashtree.SpecLemmas
import Std.Tactic.BVDecide

/-!
# The Go fallback computes SHA-256

`pairDigest_eq`: one iteration of the `k` loop of `sha256_1_generic` returns SHA-256 of the
64 bytes `p[2k] ‖ p[2k+1]`, whatever the buffer `w` holds on entry.  `sha256_1_generic_eq`:
the whole function writes `digests[k] = SHA-256(p[2k] ‖ p[2k+1])` for every `k < len(p)/2`
and leaves the other digests unchanged.

Method: a loop invariant over the 64 message rounds — the eight variables equal the
specification's state after `i` rounds (`rs`), and the circular buffer holds the last 16
schedule words, `w[t mod 16] = W_t` — then the padding rounds (`_P[i] = K_i + W'_i`, checked by
the kernel) and the big-endian store.
-/

namespace Hashtree.Go
open Hashtree.Spec

/-! ## Tables and functions -/

theorem Ktab_eq : Go.Ktab = Spec.Ktab := by decide
theorem initTab_eq : initTab = Spec.Htab := by decide
theorem K_eq (t : Nat) : Go.Ktab.getD t 0 = Spec.K t := by rw [Ktab_eq]; rfl

/-- `_P` is `K + W` of the padding block (FIPS schedule of `0x80000000, 0, …, 0, 512`). -/
theorem Ptab_eq : ∀ t, t < 64 → Ptab.getD t 0 = Spec.K t + W padBlock t := by decide +kernel

theorem bigSigma1_eq (e : Word) : bigSigma1 e = Sigma1 e := by
  simp [bigSigma1, Sigma1, rotr, rotateLeft32]; bv_decide
theorem bigSigma0_eq (a : Word) : bigSigma0 a = Sigma0 a := by
  simp [bigSigma0, Sigma0, rotr, rotateLeft32]; bv_decide
theorem s1_eq (x : Word) :
    (rotateLeft32 x (-17) ^^^ rotateLeft32 x (-19) ^^^ (x >>> 10)) = sigma1 x := by
  simp [sigma1, rotr, rotateLeft32]; bv_decide
theorem s0_eq (x : Word) :
    (rotateLeft32 x (-7) ^^^ rotateLeft32 x (-18) ^^^ (x >>> 3)) = sigma0 x := by
  simp [sigma0, rotr, rotateLeft32]; bv_decide

theorem be_eq (b0 b1 b2 b3 : Byte) :
    (b0.zeroExtend 32 <<< 24 ||| b1.zeroExtend 32 <<< 16 ||| b2.zeroExtend 32 <<< 8 ||| b3.zeroExtend 32) =
      beWord b0 b1 b2 b3 := by
  simp only [beWord]; bv_decide

theorem putUint32_eq (x : Word) : putUint32 x = wordBytes x := by
  simp only [putUint32, wordBytes, List.cons.injEq, and_true]; bv_decide

/-! ## Variables vs specification state -/

def Vars.toS (v : Vars) : State := ⟨v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h⟩

theorem roundKW_eq (v : Vars) (k w : Word) : (v.roundKW k w).toS = v.toS.round k w := by
  simp only [Vars.roundKW, Vars.step, Vars.toS, State.round, bigSigma1_eq, bigSigma0_eq, ch, maj, Ch, Maj]

theorem roundP_eq (v : Vars) (k w : Word) : (v.roundP (k + w)).toS = v.toS.round k w := by
  simp only [Vars.roundP, Vars.step, Vars.toS, State.round, bigSigma1_eq, bigSigma0_eq, ch, maj, Ch, Maj,
    BitVec.add_assoc]

theorem initVars_eq : initVars.toS = H0 := by
  simp only [initVars, Vars.toS, initTab_eq]; rfl

theorem add_toS (x y : Vars) : (x.add y).toS = x.toS.add y.toS := rfl

theorem State.add_comm (x y : State) : x.add y = y.add x := by
  cases x; cases y; simp only [State.add, BitVec.add_comm]

/-! ## The 64 message bytes -/

/-- The 64-byte input `p[2k] ‖ p[2k+1]`. -/
def cat (p0 p1 : Fin 32 → Byte) : Fin 64 → Byte := fun i =>
  if h : i.val < 32 then p0 ⟨i.val, h⟩ else p1 ⟨i.val - 32, by omega⟩

theorem inWords_getD (input : Fin 64 → Byte) (j : Nat) (hj : j < 16) :
    (inWords input).getD j 0 =
      beWord (input ⟨4 * j, by omega⟩) (input ⟨4 * j + 1, by omega⟩)
        (input ⟨4 * j + 2, by omega⟩) (input ⟨4 * j + 3, by omega⟩) := by
  simp only [inWords, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem inWords_length (input : Fin 64 → Byte) : (inWords input).length = 16 := by
  simp [inWords]

theorem load_lo (p0 p1 : Fin 32 → Byte) (i : Nat) (hi : i < 8) :
    load p0 (i * 4) = W (inWords (cat p0 p1)) i := by
  rw [W_lt16 _ (inWords_length _) i (by omega), inWords_getD _ i (by omega), load, be_eq]
  simp only [cat]
  have h0 : 4 * i < 32 := by omega
  have h1 : 4 * i + 1 < 32 := by omega
  have h2 : 4 * i + 2 < 32 := by omega
  have h3 : 4 * i + 3 < 32 := by omega
  simp only [h0, h1, h2, h3, dite_true]
  congr 1 <;> (congr 1; apply Fin.ext; simp only []; omega)

theorem load_hi (p0 p1 : Fin 32 → Byte) (i : Nat) (hi1 : 8 ≤ i) (hi2 : i < 16) :
    load p1 ((i - 8) * 4) = W (inWords (cat p0 p1)) i := by
  rw [W_lt16 _ (inWords_length _) i hi2, inWords_getD _ i hi2, load, be_eq]
  simp only [cat]
  have h0 : ¬ 4 * i < 32 := by omega
  have h1 : ¬ 4 * i + 1 < 32 := by omega
  have h2 : ¬ 4 * i + 2 < 32 := by omega
  have h3 : ¬ 4 * i + 3 < 32 := by omega
  simp only [h0, h1, h2, h3, dite_false]
  congr 1 <;> (congr 1; apply Fin.ext; simp only []; omega)

/-! ## The message loops -/

/-- After `i` rounds: the variables are the specification's state, and the buffer holds the
schedule words of the last 16 rounds. -/
def Inv (M : List Word) (i : Nat) (s : MsgSt) : Prop :=
  s.v.toS = rs H0 M i ∧ ∀ t, t < i → i ≤ t + 16 → s.w (t % 16) = W M t

theorem foldl_range'_inv {β : Type} (f : β → Nat → β) (P : Nat → β → Prop) (lo n : Nat) (s : β)
    (h0 : P lo s) (hs : ∀ i s, lo ≤ i → i < lo + n → P i s → P (i + 1) (f s i)) :
    P (lo + n) ((List.range' lo n).foldl f s) := by
  induction n generalizing lo s with
  | zero => simpa using h0
  | succ n ih =>
    show P (lo + (n + 1)) ((List.range' (lo + 1) n).foldl f (f s lo))
    have := ih (lo + 1) (f s lo) (hs lo s (Nat.le_refl _) (by omega) h0)
      (fun i s h1 h2 h => hs i s (by omega) (by omega) h)
    rwa [show lo + 1 + n = lo + (n + 1) by omega] at this

theorem setW_same (w : Nat → Word) (j : Nat) (x : Word) : setW w j x j = x := by simp [setW]
theorem setW_other (w : Nat → Word) (j i : Nat) (x : Word) (h : i ≠ j) : setW w j x i = w i := by
  simp [setW, h]

theorem loop1_step (p0 p1 : Fin 32 → Byte) (i : Nat) (s : MsgSt) (hi : i < 8)
    (h : Inv (inWords (cat p0 p1)) i s) : Inv (inWords (cat p0 p1)) (i + 1) (loop1 p0 s i) := by
  obtain ⟨hv, hw⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [loop1, roundKW_eq, hv, rs_succ, K_eq, setW_same, load_lo p0 p1 i hi]
  · intro t ht1 ht2
    simp only [loop1]
    rcases Nat.lt_or_ge t i with h | h
    · rw [setW_other _ _ _ _ (by omega)]; exact hw t h (by omega)
    · have : t = i := by omega
      subst this
      rw [Nat.mod_eq_of_lt (by omega), setW_same, load_lo p0 p1 t hi]

theorem loop2_step (p0 p1 : Fin 32 → Byte) (i : Nat) (s : MsgSt) (hi1 : 8 ≤ i) (hi2 : i < 16)
    (h : Inv (inWords (cat p0 p1)) i s) : Inv (inWords (cat p0 p1)) (i + 1) (loop2 p1 s i) := by
  obtain ⟨hv, hw⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [loop2, roundKW_eq, hv, rs_succ, K_eq, setW_same, load_hi p0 p1 i hi1 hi2]
  · intro t ht1 ht2
    simp only [loop2]
    rcases Nat.lt_or_ge t i with h | h
    · rw [Nat.mod_eq_of_lt (by omega), setW_other _ _ _ _ (by omega)]
      have := hw t h (by omega); rwa [Nat.mod_eq_of_lt (by omega)] at this
    · have : t = i := by omega
      subst this
      rw [Nat.mod_eq_of_lt (by omega), setW_same, load_hi p0 p1 t hi1 hi2]

theorem sched_step (a s1 b s0 : Word) : a + (s1 + b + s0) = s1 + b + s0 + a := by bv_decide

theorem loop3_step (M : List Word) (hM : M.length = 16) (i : Nat) (s : MsgSt) (hi1 : 16 ≤ i) (hi2 : i < 64)
    (h : Inv M i s) : Inv M (i + 1) (loop3 s i) := by
  obtain ⟨hv, hw⟩ := h
  have hnew : s.w (i % 16) + ((rotateLeft32 (s.w ((i - 2) % 16)) (-17) ^^^ rotateLeft32 (s.w ((i - 2) % 16)) (-19) ^^^
      (s.w ((i - 2) % 16) >>> 10)) + s.w ((i - 7) % 16) +
      (rotateLeft32 (s.w ((i - 15) % 16)) (-7) ^^^ rotateLeft32 (s.w ((i - 15) % 16)) (-18) ^^^
      (s.w ((i - 15) % 16) >>> 3))) = W M i := by
    rw [s1_eq, s0_eq, hw (i - 2) (by omega) (by omega), hw (i - 7) (by omega) (by omega),
      hw (i - 15) (by omega) (by omega), W_rec M hM i hi1 hi2, sched_step]
    have : i % 16 = (i - 16) % 16 := by omega
    rw [this, hw (i - 16) (by omega) (by omega)]
  refine ⟨?_, ?_⟩
  · simp only [loop3, roundKW_eq, hv, rs_succ, K_eq, setW_same]
    rw [hnew]
  · intro t ht1 ht2
    simp only [loop3]
    rcases Nat.lt_or_ge t i with h | h
    · rw [setW_other _ _ _ _ (by omega)]; exact hw t h (by omega)
    · have : t = i := by omega
      subst this
      rw [setW_same, hnew]

/-- The three message loops: the state after 64 rounds. -/
theorem msg_loops (p0 p1 : Fin 32 → Byte) (w0 : Nat → Word) :
    let s : MsgSt := ⟨initVars, w0⟩
    let s := (List.range' 0 8).foldl (loop1 p0) s
    let s := (List.range' 8 8).foldl (loop2 p1) s
    let s := (List.range' 16 48).foldl loop3 s
    s.v.toS = rs H0 (inWords (cat p0 p1)) 64 := by
  intro s1 s2 s3 s4
  have h1 : Inv (inWords (cat p0 p1)) (0 + 8) s2 :=
    foldl_range'_inv (loop1 p0) (Inv (inWords (cat p0 p1))) 0 8 s1
      ⟨initVars_eq, fun t ht _ => absurd ht (Nat.not_lt_zero _)⟩
      (fun i s _ h2 h => loop1_step p0 p1 i s (by omega) h)
  have h2 : Inv (inWords (cat p0 p1)) (8 + 8) s3 :=
    foldl_range'_inv (loop2 p1) (Inv (inWords (cat p0 p1))) 8 8 s2 h1
      (fun i s h1 h2 h => loop2_step p0 p1 i s h1 (by omega) h)
  have h3 : Inv (inWords (cat p0 p1)) (16 + 48) s4 :=
    foldl_range'_inv loop3 (Inv (inWords (cat p0 p1))) 16 48 s3 h2
      (fun i s h1 h2 h => loop3_step _ (inWords_length _) i s h1 (by omega) h)
  exact h3.1

/-! ## Padding rounds and output -/

theorem pad_rounds (hv : Vars) :
    ((List.range' 0 64).foldl (fun v i => v.roundP (Ptab.getD i 0)) hv).toS = rs hv.toS padBlock 64 := by
  have := foldl_range'_inv (fun v i => v.roundP (Ptab.getD i 0)) (fun i v => v.toS = rs hv.toS padBlock i)
    0 64 hv rfl (fun i v _ h2 h => by
      rw [Ptab_eq i (by omega), roundP_eq, h, rs_succ])
  simpa using this

/-- One iteration of the Go `k` loop computes SHA-256 of `p[2k] ‖ p[2k+1]`. -/
theorem pairDigest_eq (p0 p1 : Fin 32 → Byte) (w0 : Nat → Word) :
    (pairDigest p0 p1 w0).1 = node (cat p0 p1) := by
  rw [node_eq, compress_eq, compress_eq]
  simp only [pairDigest]
  have hm := msg_loops p0 p1 w0
  simp only at hm
  generalize hs : (List.range' 16 48).foldl loop3 ((List.range' 8 8).foldl (loop2 p1)
    ((List.range' 0 8).foldl (loop1 p0) ⟨initVars, w0⟩)) = s at hm ⊢
  have hhv : (s.v.add initVars).toS = H0.add (rs H0 (inWords (cat p0 p1)) 64) := by
    rw [add_toS, hm, initVars_eq, State.add_comm]
  have hr := pad_rounds (s.v.add initVars)
  rw [hhv] at hr
  have hout : ((s.v.add initVars).add ((List.range' 0 64).foldl (fun v i => v.roundP (Ptab.getD i 0))
      (s.v.add initVars))).toS = (H0.add (rs H0 (inWords (cat p0 p1)) 64)).add
      (rs (H0.add (rs H0 (inWords (cat p0 p1)) 64)) padBlock 64) := by
    rw [add_toS, hhv, hr]
  rw [← hout]
  simp only [Vars.toS, State.toList, List.flatMap_cons, List.flatMap_nil, putUint32_eq]

/-! ## The `k` loop -/

/-- The digest the Go function must write for pair `k`. -/
def pairNode (p : List (Fin 32 → Byte)) (k : Nat) : List Byte :=
  node (cat (p.getD (2 * k) (fun _ => 0)) (p.getD (2 * k + 1) (fun _ => 0)))

theorem hashLoop_spec (p : List (Fin 32 → Byte)) (n : Nat) (hn : n ≤ p.length / 2) (w : Nat → Word)
    (ds : List (List Byte)) (hds : p.length / 2 ≤ ds.length) :
    let r := hashLoop p n w ds
    r.length = ds.length ∧
      (∀ k, p.length / 2 - n ≤ k → k < p.length / 2 → r.getD k [] = pairNode p k) ∧
      (∀ k, (k < p.length / 2 - n ∨ p.length / 2 ≤ k) → r.getD k [] = ds.getD k []) := by
  induction n generalizing w ds with
  | zero =>
    refine ⟨rfl, fun k h1 h2 => absurd h2 (by omega), fun k _ => rfl⟩
  | succ n ih =>
    simp only [hashLoop]
    generalize hk : p.length / 2 - (n + 1) = k
    have hkl : k < ds.length := by omega
    obtain ⟨l, hin, hout⟩ := ih (by omega) (pairDigest (p.getD (2 * k) fun _ => 0)
      (p.getD (2 * k + 1) fun _ => 0) w).2
      (ds.set k (pairDigest (p.getD (2 * k) fun _ => 0) (p.getD (2 * k + 1) fun _ => 0) w).1)
      (by rw [List.length_set]; omega)
    refine ⟨by rw [l, List.length_set], ?_, ?_⟩
    · intro j h1 h2
      rcases Nat.lt_or_ge j (p.length / 2 - n) with hj | hj
      · have : j = k := by omega
        subst this
        rw [hout j (Or.inl hj)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hkl, Option.getD_some, pairNode]
        rw [pairDigest_eq]
      · exact hin j hj h2
    · intro j hj
      rw [hout j (by omega)]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_set_ne (by omega)]

/-- `sha256_1_generic(digests, p)` writes `digests[k] = SHA-256(p[2k] ‖ p[2k+1])` for every
`k < len(p)/2` and leaves every other digest unchanged (callers guarantee
`len(digests) ≥ len(p)/2`; `Hash`/`HashByteSlice` check it). -/
theorem sha256_1_generic_eq (digests : List (List Byte)) (p : List (Fin 32 → Byte))
    (h : p.length / 2 ≤ digests.length) :
    let r := sha256_1_generic digests p
    r.length = digests.length ∧
      (∀ k, k < p.length / 2 → r.getD k [] = pairNode p k) ∧
      (∀ k, p.length / 2 ≤ k → r.getD k [] = digests.getD k []) := by
  obtain ⟨l, hin, hout⟩ := hashLoop_spec p (p.length / 2) (Nat.le_refl _) (fun _ => 0) digests h
  exact ⟨l, fun k hk => hin k (by omega) hk, fun k hk => hout k (Or.inr hk)⟩

end Hashtree.Go
