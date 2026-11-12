import Hashtree.GoProof

/-!
# The Go API: `Hash`, `HashByteSlice`, `hashChunked` (bindings.go)

Memory is byte-addressed (`Mem := Nat → Byte`), so that a caller hashing a layer in place
(`digests` and `chunks` the same buffer) is covered.  A `[][32]byte` slice is a base address
and a length; `HashByteSlice`'s `unsafe.Slice` casts keep the base and divide the length by 32.

The assembly call `hashtreeHash(output, input, count)` is a parameter `call`, constrained only
by its contract `callSpec` (what the kernel proofs establish): it writes SHA-256 of `count`
64-byte blocks, read from the memory as it was before the call, whenever the output does not
start inside the input (`out ≤ inp`, which includes hashing in place, or the output entirely
after the input).  In-place layer hashing needs `out ≤ inp` in general, not only `out = inp`:
`hashChunked`'s later calls have their output 32 KiB·k behind their input.  The theorems show that every call the
glue makes satisfies those conditions and has `1 ≤ count ≤ maxAsmChunks/2`.
-/

set_option linter.deprecated false

namespace Hashtree.Glue
open Hashtree.Spec Hashtree.Go

abbrev Mem := Nat → Byte

/-- The 64 bytes at address `a`. -/
def blockAt (m : Mem) (a : Nat) : Fin 64 → Byte := fun i => m (a + i.val)

/-- What `hashtreeHash(out, inp, count)` must do: SHA-256 of each input block, read before the call. -/
def callSpec (m : Mem) (out inp count : Nat) : Mem := fun a =>
  if out ≤ a ∧ a < out + 32 * count then (node (blockAt m (inp + 64 * ((a - out) / 32)))).getD ((a - out) % 32) 0
  else m a

/-- The aliasing the kernels must support: the output starts at or before the input (in place
included), or lies entirely after it. -/
def aliasOk (out inp count : Nat) : Prop := out ≤ inp ∨ inp + 64 * count ≤ out

def chunksPerAsmIter : Nat := 32
def maxAsmIters : Nat := 64
def maxAsmChunks : Nat := chunksPerAsmIter * maxAsmIters

/-- A call as the glue may issue it: contract-conforming for admissible arguments. -/
def CallOk (call : Mem → Nat → Nat → Nat → Mem) : Prop :=
  ∀ m out inp count, 1 ≤ count → count ≤ maxAsmChunks / 2 → aliasOk out inp count →
    call m out inp count = callSpec m out inp count

/-- `hashChunked(digests, chunks)` (`fuel` bounds the loop; `fuel ≥ len(chunks)` suffices). -/
def hashChunked (call : Mem → Nat → Nat → Nat → Mem) : Nat → Mem → Nat → Nat → Nat → Mem
  | 0, m, _, _, _ => m
  | fuel + 1, m, d, c, cLen =>
    if cLen > maxAsmChunks then
      -- hashtreeHash(&digests[0][0], &chunks[0][0], maxAsmChunks/2)
      hashChunked call fuel (call m d c (maxAsmChunks / 2)) (d + 32 * (maxAsmChunks / 2))
        (c + 32 * maxAsmChunks) (cLen - maxAsmChunks)
    else if cLen > 1 then call m d c (cLen / 2)
    else m

/-- The effect the API promises for `n` pairs: `digests[i] = SHA-256(chunks[2i] ‖ chunks[2i+1])`. -/
def hashed (m : Mem) (d c n : Nat) : Mem := fun a =>
  if d ≤ a ∧ a < d + 32 * n then (node (blockAt m (c + 64 * ((a - d) / 32)))).getD ((a - d) % 32) 0
  else m a

theorem callSpec_eq_hashed (m : Mem) (d c n : Nat) : callSpec m d c n = hashed m d c n := rfl

/-- Caller-side aliasing: `digests` starts at or before `chunks` (in place included), or lies
entirely after it. -/
def sliceAlias (d c cLen : Nat) : Prop := d ≤ c ∨ c + 32 * cLen ≤ d

theorem hashed_zero (m : Mem) (d c : Nat) : hashed m d c 0 = m := by
  funext a; unfold hashed; rw [if_neg (by omega)]

/-- Hashing `n1` pairs, then the next `n2`, is hashing `n1 + n2` pairs, provided the second
part's input is not inside the first part's output. -/
theorem hashed_split (m : Mem) (d c n1 n2 : Nat)
    (hsep : ∀ x, c + 64 * n1 ≤ x → x < c + 64 * (n1 + n2) → ¬ (d ≤ x ∧ x < d + 32 * n1)) :
    hashed (hashed m d c n1) (d + 32 * n1) (c + 64 * n1) n2 = hashed m d c (n1 + n2) := by
  funext a
  unfold hashed
  by_cases h2 : d + 32 * n1 ≤ a ∧ a < d + 32 * n1 + 32 * n2
  · rw [if_pos h2, if_pos (by omega)]
    have e1 : (a - (d + 32 * n1)) / 32 = (a - d) / 32 - n1 := by omega
    have e2 : (a - (d + 32 * n1)) % 32 = (a - d) % 32 := by omega
    rw [e1, e2]
    congr 2
    funext i
    simp only [blockAt]
    have hx := hsep (c + 64 * n1 + 64 * ((a - d) / 32 - n1) + i.val) (by omega) (by have := i.isLt; omega)
    rw [if_neg hx]
    congr 1
    have := i.isLt
    omega
  · rw [if_neg h2]
    by_cases h1 : d ≤ a ∧ a < d + 32 * n1
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem hashChunked_spec (call : Mem → Nat → Nat → Nat → Mem) (hcall : CallOk call) :
    ∀ fuel m d c cLen, cLen ≤ fuel * 2048 + 1 → cLen % 2 = 0 → sliceAlias d c cLen →
      hashChunked call fuel m d c cLen = hashed m d c (cLen / 2) := by
  have hM : maxAsmChunks = 2048 := by decide
  intro fuel
  induction fuel with
  | zero =>
    intro m d c cLen h1 h2 _
    have : cLen = 0 := by omega
    subst this
    exact (hashed_zero m d c).symm
  | succ fuel ih =>
    intro m d c cLen h1 h2 ha
    simp only [hashChunked, hM]
    by_cases hbig : cLen > 2048
    · rw [if_pos hbig]
      rw [hcall m d c (2048 / 2) (by decide) (by rw [hM]; exact Nat.le_refl _) (by unfold aliasOk sliceAlias at *; omega)]
      rw [ih _ _ _ _ (by rw [Nat.add_mul] at h1; omega) (by omega) (by unfold sliceAlias at *; omega)]
      rw [callSpec_eq_hashed]
      have := hashed_split m d c 1024 ((cLen - 2048) / 2) (by unfold sliceAlias at ha; omega)
      rw [show 32 * 2048 = 64 * 1024 from rfl, show 2048 / 2 = 1024 from rfl, this]
      congr 1; omega
    · rw [if_neg hbig]
      by_cases hsmall : cLen > 1
      · rw [if_pos hsmall, hcall m d c (cLen / 2) (by omega) (by rw [hM]; omega)
          (by unfold aliasOk sliceAlias at *; omega)]
        rfl
      · rw [if_neg hsmall]
        have : cLen = 0 := by omega
        subst this
        exact (hashed_zero m d c).symm

/-! ## `sha256_1_generic` on memory -/

/-- `digests[k] = dig`: store 32 bytes. -/
def store (m : Mem) (a : Nat) (dig : List Byte) : Mem := fun x =>
  if a ≤ x ∧ x < a + 32 then dig.getD (x - a) 0 else m x

/-- The `k` loop of `sha256_1_generic` on memory: iteration `k` reads `p[2k]`, `p[2k+1]` (all its
loads happen before its single store of `digests[k]`), threads the buffer `w`. -/
def genericLoop (d c : Nat) : Nat → Nat → (Nat → Word) → Mem → Mem
  | _, 0, _, m => m
  | k, r + 1, w, m =>
    let p0 : Fin 32 → Byte := fun j => m (c + 64 * k + j.val)
    let p1 : Fin 32 → Byte := fun j => m (c + 64 * k + 32 + j.val)
    let res := pairDigest p0 p1 w
    genericLoop d c (k + 1) r res.2 (store m (d + 32 * k) res.1)

def genericMem (m : Mem) (d c n : Nat) : Mem := genericLoop d c 0 n (fun _ => 0) m

theorem cat_blockAt (m : Mem) (a : Nat) :
    cat (fun j : Fin 32 => m (a + j.val)) (fun j : Fin 32 => m (a + 32 + j.val)) = blockAt m a := by
  funext i
  simp only [cat, blockAt]
  split
  · rfl
  · congr 1; omega

theorem node_length (input : Fin 64 → Byte) : (node input).length = 32 := by
  rw [node_eq]; simp [State.toList, wordBytes]

theorem genericLoop_spec (m0 : Mem) (d c n : Nat) (ha : d ≤ c ∨ c + 64 * n ≤ d) :
    ∀ r k w, k + r = n → genericLoop d c k r w (hashed m0 d c k) = hashed m0 d c n := by
  intro r
  induction r with
  | zero => intro k w h; simp only [genericLoop]; rw [show k = n by omega]
  | succ r ih =>
    intro k w h
    simp only [genericLoop]
    rw [pairDigest_eq]
    -- the pair is read from memory the first k digests have not touched
    have hread : ∀ x, c + 64 * k ≤ x → x < c + 64 * k + 64 → hashed m0 d c k x = m0 x := by
      intro x h1 h2
      unfold hashed; rw [if_neg (by omega)]
    have hp0 : (fun j : Fin 32 => hashed m0 d c k (c + 64 * k + j.val)) = fun j => m0 (c + 64 * k + j.val) := by
      funext j; exact hread _ (by omega) (by have := j.isLt; omega)
    have hp1 : (fun j : Fin 32 => hashed m0 d c k (c + 64 * k + 32 + j.val)) =
        fun j => m0 (c + 64 * k + 32 + j.val) := by
      funext j; exact hread _ (by omega) (by have := j.isLt; omega)
    rw [hp0, hp1, cat_blockAt]
    have hstore : store (hashed m0 d c k) (d + 32 * k) (node (blockAt m0 (c + 64 * k))) = hashed m0 d c (k + 1) := by
      funext x
      unfold store hashed
      by_cases hx : d + 32 * k ≤ x ∧ x < d + 32 * k + 32
      · rw [if_pos hx, if_pos (by omega)]
        have e1 : (x - d) / 32 = k := by omega
        rw [e1, show x - (d + 32 * k) = (x - d) % 32 by omega]
      · rw [if_neg hx]
        by_cases hy : d ≤ x ∧ x < d + 32 * k
        · rw [if_pos hy, if_pos (by omega)]
        · rw [if_neg hy, if_neg (by omega)]
    rw [hstore]
    exact ih (k + 1) _ (by omega)

/-- The memory effect of `sha256_1_generic` is the promised one (in place included). -/
theorem genericMem_spec (m : Mem) (d c n : Nat) (ha : d ≤ c ∨ c + 64 * n ≤ d) :
    genericMem m d c n = hashed m d c n := by
  have := genericLoop_spec m d c n ha n 0 (fun _ => 0) (by omega)
  rwa [hashed_zero] at this

/-! ## `Hash` and `HashByteSlice` -/

inductive Err where
  | oddChunks
  | notEnoughDigests
  | chunksNotMultipleOf64
  | digestsNotMultipleOf32
  deriving DecidableEq, Repr

/-- `Hash(digests, chunks)` on `[][32]byte` slices `(base, len)`; `generic` is the memory
effect of `sha256_1_generic` (see `generic_ok`). -/
def hash (call : Mem → Nat → Nat → Nat → Mem) (generic : Mem → Nat → Nat → Nat → Mem) (supportedCPU : Bool)
    (m : Mem) (d dLen c cLen : Nat) : Except Err Mem :=
  if cLen = 0 then .ok m
  else if cLen % 2 = 1 then .error .oddChunks
  else if dLen < cLen / 2 then .error .notEnoughDigests
  else if supportedCPU then .ok (hashChunked call (cLen + 1) m d c cLen)
  else .ok (generic m d c (cLen / 2))

/-- `HashByteSlice(digests, chunks)` on byte slices `(base, len)`. -/
def hashByteSlice (call : Mem → Nat → Nat → Nat → Mem) (generic : Mem → Nat → Nat → Nat → Mem)
    (supportedCPU : Bool) (m : Mem) (d dLen c cLen : Nat) : Except Err Mem :=
  if cLen = 0 then .ok m
  else if cLen % 64 ≠ 0 then .error .chunksNotMultipleOf64
  else if dLen % 32 ≠ 0 then .error .digestsNotMultipleOf32
  else if dLen < cLen / 2 then .error .notEnoughDigests
  else if supportedCPU then
    -- `Hash(chunkedDigest, chunkedChunks)`; its error result is discarded by the Go code
    match hash call generic supportedCPU m d (dLen >>> 5) c (cLen >>> 5) with
    | .ok m' => .ok m'
    | .error _ => .ok m
  else .ok (generic m d c ((cLen >>> 5) / 2))

/-- `Hash` succeeds exactly when the chunk count is even and there are enough digests, and
then writes `digests[i] = SHA-256(chunks[2i] ‖ chunks[2i+1])` for all `i < len(chunks)/2`
(and nothing else), on both paths. -/
theorem hash_spec (call generic : Mem → Nat → Nat → Nat → Mem) (hcall : CallOk call)
    (hgen : ∀ m d c n, (d ≤ c ∨ c + 64 * n ≤ d) → generic m d c n = hashed m d c n)
    (supportedCPU : Bool) (m : Mem) (d dLen c cLen : Nat) (ha : sliceAlias d c cLen) :
    hash call generic supportedCPU m d dLen c cLen =
      if cLen % 2 = 1 then .error .oddChunks
      else if cLen ≠ 0 ∧ dLen < cLen / 2 then .error .notEnoughDigests
      else .ok (hashed m d c (cLen / 2)) := by
  unfold hash
  by_cases h0 : cLen = 0
  · subst h0; simp [hashed_zero]
  by_cases hodd : cLen % 2 = 1
  · simp [h0, hodd]
  by_cases hd : dLen < cLen / 2
  · simp [h0, hodd, hd]
  simp only [h0, hodd, hd, ite_false, ne_eq, not_false_eq_true, true_and]
  cases supportedCPU
  · simp only [Bool.false_eq_true, ite_false]
    rw [hgen m d c (cLen / 2) (by unfold sliceAlias at ha; omega)]
  · simp only [ite_true]
    rw [hashChunked_spec call hcall (cLen + 1) m d c cLen (by omega) (by omega) ha]

theorem hashByteSlice_spec (call generic : Mem → Nat → Nat → Nat → Mem) (hcall : CallOk call)
    (hgen : ∀ m d c n, (d ≤ c ∨ c + 64 * n ≤ d) → generic m d c n = hashed m d c n)
    (supportedCPU : Bool) (m : Mem) (d dLen c cLen : Nat)
    (ha : d ≤ c ∨ c + cLen ≤ d) :
    hashByteSlice call generic supportedCPU m d dLen c cLen =
      if cLen = 0 then .ok m
      else if cLen % 64 ≠ 0 then .error .chunksNotMultipleOf64
      else if dLen % 32 ≠ 0 then .error .digestsNotMultipleOf32
      else if dLen < cLen / 2 then .error .notEnoughDigests
      else .ok (hashed m d c (cLen / 64)) := by
  unfold hashByteSlice
  by_cases h0 : cLen = 0
  · simp [h0]
  simp only [h0, ite_false]
  by_cases h64 : cLen % 64 ≠ 0
  · simp [h64]
  simp only [h64, ite_false]
  by_cases h32 : dLen % 32 ≠ 0
  · simp [h32]
  simp only [h32, ite_false]
  by_cases hd : dLen < cLen / 2
  · simp [hd]
  simp only [hd, ite_false]
  have hs5 : cLen >>> 5 = cLen / 32 := Nat.shiftRight_eq_div_pow cLen 5
  have hd5 : dLen >>> 5 = dLen / 32 := Nat.shiftRight_eq_div_pow dLen 5
  cases supportedCPU
  · simp only [Bool.false_eq_true, ite_false, hs5]
    rw [hgen m d c (cLen / 32 / 2) (by omega), show cLen / 32 / 2 = cLen / 64 by omega]
  · simp only [ite_true]
    rw [hash_spec call generic hcall hgen true m d (dLen >>> 5) c (cLen >>> 5)
      (by unfold sliceAlias; rw [hs5]; omega)]
    simp only [hs5, hd5]
    have ho : ¬ (cLen / 32) % 2 = 1 := by omega
    have hn : ¬ ((cLen / 32) ≠ 0 ∧ dLen / 32 < (cLen / 32) / 2) := by
      intro ⟨_, hlt⟩
      have : ¬ dLen < cLen / 2 := hd
      omega
    rw [if_neg ho, if_neg hn, show cLen / 32 / 2 = cLen / 64 by omega]

/-- The bindings' `Hash` with the actual fallback: for any contract-conforming assembly call. -/
theorem Hash_spec (call : Mem → Nat → Nat → Nat → Mem) (hcall : CallOk call) (supportedCPU : Bool)
    (m : Mem) (d dLen c cLen : Nat) (ha : sliceAlias d c cLen) :
    hash call genericMem supportedCPU m d dLen c cLen =
      if cLen % 2 = 1 then .error .oddChunks
      else if cLen ≠ 0 ∧ dLen < cLen / 2 then .error .notEnoughDigests
      else .ok (hashed m d c (cLen / 2)) :=
  hash_spec call genericMem hcall genericMem_spec supportedCPU m d dLen c cLen ha

theorem HashByteSlice_spec (call : Mem → Nat → Nat → Nat → Mem) (hcall : CallOk call) (supportedCPU : Bool)
    (m : Mem) (d dLen c cLen : Nat) (ha : d ≤ c ∨ c + cLen ≤ d) :
    hashByteSlice call genericMem supportedCPU m d dLen c cLen =
      if cLen = 0 then .ok m
      else if cLen % 64 ≠ 0 then .error .chunksNotMultipleOf64
      else if dLen % 32 ≠ 0 then .error .digestsNotMultipleOf32
      else if dLen < cLen / 2 then .error .notEnoughDigests
      else .ok (hashed m d c (cLen / 64)) :=
  hashByteSlice_spec call genericMem hcall genericMem_spec supportedCPU m d dLen c cLen ha

end Hashtree.Glue
