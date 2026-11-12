/-!
# SHA-256 (FIPS 180-4)

An independent specification of SHA-256 over byte lists, written from FIPS 180-4
(§4.1.2 functions, §4.2.2 constants, §5.1.1 padding, §5.2.1 parsing, §5.3.3 initial
hash value, §6.2.2 hash computation).  The constants are *derived* as the standard
defines them (first 32 bits of the fractional parts of the cube roots, resp. square
roots, of the first primes) and tied to the literal tables by `decide`.

Every implementation in hashtree hashes one 64-byte input: `node` below.  Its
two-block form (`node_eq`: the message block, then the constant padding block) is a
theorem, not a definition.
-/

namespace Hashtree.Spec

abbrev Word := BitVec 32
abbrev Byte := BitVec 8

/-! ## Functions (§4.1.2) -/

def rotr (x : Word) (n : Nat) : Word := x.rotateRight n
def Ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def Sigma0 (x : Word) : Word := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def Sigma1 (x : Word) : Word := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def sigma0 (x : Word) : Word := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def sigma1 (x : Word) : Word := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-! ## Constants (§4.2.2, §5.3.3) -/

/-- Literal table K (FIPS 180-4 §4.2.2). -/
def Ktab : List Word := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Literal initial hash value H(0) (FIPS 180-4 §5.3.3). -/
def Htab : List Word := [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range (n - 2)).all (fun d => n % (d + 2) != 0)

/-- The first 64 primes (the 64th is 311). -/
def primes : List Nat := (List.range 312).filter isPrime

/-- `⌊n^(1/k)⌋` by bisection on `[lo, hi)` (fuel-bounded, structural). -/
def rootSearch (k n : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let m := (lo + hi) / 2
      if m ^ k ≤ n then rootSearch k n fuel m hi else rootSearch k n fuel lo m

def iroot (k n : Nat) : Nat := rootSearch k n 64 0 (2 ^ 40)

/-- First 32 bits of the fractional part of `p^(1/k)`: `⌊p^(1/k) · 2^32⌋ mod 2^32 =
⌊(p · 2^(32k))^(1/k)⌋ mod 2^32`. -/
def fracBits (k p : Nat) : Word := BitVec.ofNat 32 (iroot k (p * 2 ^ (32 * k)))

theorem Ktab_derived : Ktab = (primes.take 64).map (fracBits 3) := by decide +kernel
theorem Htab_derived : Htab = (primes.take 8).map (fracBits 2) := by decide +kernel
theorem Ktab_length : Ktab.length = 64 := by decide

def K (t : Nat) : Word := Ktab.getD t 0

/-! ## Hash computation (§6.2.2) -/

structure State where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
  deriving DecidableEq, Repr

def H0 : State := ⟨Htab[0]!, Htab[1]!, Htab[2]!, Htab[3]!, Htab[4]!, Htab[5]!, Htab[6]!, Htab[7]!⟩

/-- One round (§6.2.2 step 3) with round constant `k` and schedule word `w`. -/
def State.round (s : State) (k w : Word) : State :=
  let T1 := s.h + Sigma1 s.e + Ch s.e s.f s.g + k + w
  let T2 := Sigma0 s.a + Maj s.a s.b s.c
  ⟨T1 + T2, s.a, s.b, s.c, s.d + T1, s.e, s.f, s.g⟩

/-- Intermediate hash update (§6.2.2 step 4). -/
def State.add (x y : State) : State :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e, x.f + y.f, x.g + y.g, x.h + y.h⟩

/-- Message schedule (§6.2.2 step 1) of a block of 16 words: the 64 words `W_0 … W_63`. -/
def schedule (M : List Word) : List Word :=
  (List.range 48).foldl (fun (W : List Word) i =>
    let t := i + 16
    W ++ [sigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 + sigma0 (W.getD (t - 15) 0) + W.getD (t - 16) 0]) M

/-- The 64 rounds over a schedule, from state `s`. -/
def rounds (s : State) (W : List Word) : State :=
  (List.range 64).foldl (fun s t => s.round (K t) (W.getD t 0)) s

/-- Process one 16-word block (§6.2.2). -/
def compress (H : State) (M : List Word) : State := H.add (rounds H (schedule M))

/-! ## Padding and parsing (§5.1.1, §5.2.1) -/

/-- Big-endian word of four bytes. -/
def beWord (b0 b1 b2 b3 : Byte) : Word := b0 ++ b1 ++ b2 ++ b3

/-- Big-endian bytes of a word. -/
def wordBytes (w : Word) : List Byte :=
  [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]

/-- `ℓ` (the message length in bits) as 8 big-endian bytes. -/
def lenBytes (n : Nat) : List Byte := (List.range 8).reverse.map (fun i => BitVec.ofNat 8 (n / 2 ^ (8 * i)))

/-- Padding of a byte message: `0x80`, then zero bytes up to 56 mod 64, then the bit length. -/
def pad (msg : List Byte) : List Byte :=
  msg ++ [0x80] ++ List.replicate ((119 - msg.length % 64) % 64) 0 ++ lenBytes (8 * msg.length)

/-- Words of a byte list (length a multiple of 4), big-endian. -/
def words : List Byte → List Word
  | b0 :: b1 :: b2 :: b3 :: rest => beWord b0 b1 b2 b3 :: words rest
  | _ => []

/-- 16-word blocks of a word list. -/
def blocks (ws : List Word) : List (List Word) :=
  (List.range (ws.length / 16)).map (fun i => (ws.drop (16 * i)).take 16)

def State.toList (s : State) : List Word := [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

/-- SHA-256 of a byte message: 32 bytes. -/
def sha256 (msg : List Byte) : List Byte :=
  ((blocks (words (pad msg))).foldl compress H0).toList.flatMap wordBytes

/-! ## The hashtree node: SHA-256 of 64 bytes -/

/-- What every hashtree implementation computes for one input block. -/
def node (input : Fin 64 → Byte) : List Byte := sha256 (List.ofFn input)

/-- The 16 big-endian message words of a 64-byte input. -/
def inWords (input : Fin 64 → Byte) : List Word :=
  List.ofFn fun (j : Fin 16) =>
    beWord (input ⟨4 * j.val, by omega⟩) (input ⟨4 * j.val + 1, by omega⟩)
      (input ⟨4 * j.val + 2, by omega⟩) (input ⟨4 * j.val + 3, by omega⟩)

/-- The padding block of a 64-byte message: `0x80000000, 0, …, 0, 512`. -/
def padBlock : List Word := 0x80000000 :: List.replicate 14 0 ++ [512]

end Hashtree.Spec

namespace Hashtree.Spec

theorem pad64 (input : Fin 64 → Byte) :
    pad (List.ofFn input) = List.ofFn input ++ [0x80] ++ List.replicate 55 0 ++ lenBytes 512 := by
  simp [pad]

theorem lenBytes512 : lenBytes 512 = [0, 0, 0, 0, 0, 0, 2, 0] := by decide

theorem blocks64 (input : Fin 64 → Byte) :
    blocks (words (pad (List.ofFn input))) = [inWords input, padBlock] := by
  rw [pad64]
  simp only [List.ofFn_succ, List.ofFn_zero, inWords]
  simp [words, blocks, lenBytes512, padBlock, beWord, List.replicate, List.range_succ]
  repeat' apply And.intro
  all_goals rfl

/-- A 64-byte message is two blocks: its 16 words, then the constant padding block. -/
theorem node_eq (input : Fin 64 → Byte) :
    node input = (compress (compress H0 (inWords input)) padBlock).toList.flatMap wordBytes := by
  simp only [node, sha256, blocks64, List.foldl]

end Hashtree.Spec
