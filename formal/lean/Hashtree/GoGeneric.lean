import Hashtree.Spec

/-!
# Model of the Go fallback `sha256_1_generic` (sha256_1_generic.go)

A line-by-line transliteration of the Go function: the three message loops (words 0–7 from
`p[2k]`, 8–15 from `p[2k+1]`, then 48 rounds that extend the schedule in place in the
16-word circular buffer `w[i%16]`), the feed-forward with `init0…init7`, the 64 padding rounds
driven by the precomputed table `_P`, and the big-endian store.  The tables below are copied
verbatim from the Go source; `check_go_tables.py` re-extracts them and compares.

`uint32` arithmetic is `BitVec 32`; `bits.RotateLeft32(x, k)` rotates left by `k mod 32`.
The buffer `w` is declared outside the `k` loop in Go and carried across iterations; the model
threads it too (`hashLoop`), and `node_w_indep` shows its initial content does not matter.
-/

namespace Hashtree.Go
open Hashtree.Spec

/-- `_P` (sha256_1_generic.go). -/
def Ptab : List Word := [
  0xc28a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf374,
  0x649b69c1, 0xf0fe4786, 0x0fe1edc6, 0x240cf254, 0x4fe9346f, 0x6cc984be, 0x61b9411e, 0x16f988fa,
  0xf2c65152, 0xa88e5a6d, 0xb019fc65, 0xb9d99ec7, 0x9a1231c3, 0xe70eeaa0, 0xfdb1232b, 0xc7353eb0,
  0x3069bad5, 0xcb976d5f, 0x5a0f118f, 0xdc1eeefd, 0x0a35b689, 0xde0b7a04, 0x58f4ca9d, 0xe15d5b16,
  0x007f3e86, 0x37088980, 0xa507ea32, 0x6fab9537, 0x17406110, 0x0d8cd6f1, 0xcdaa3b6d, 0xc0bbbe37,
  0x83613bda, 0xdb48a363, 0x0b02e931, 0x6fd15ca7, 0x521afaca, 0x31338431, 0x6ed41a95, 0x6d437890,
  0xc39c91f2, 0x9eccabbd, 0xb5c9a0e6, 0x532fb63c, 0xd2c741c6, 0x07237ea3, 0xa4954b68, 0x4c191d76]

/-- `_K` (sha256_1_generic.go). -/
def Ktab : List Word := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- `init0 … init7`. -/
def initTab : List Word := [
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- `bits.RotateLeft32(x, k)`: rotate left by `k mod 32`. -/
def rotateLeft32 (x : Word) (k : Int) : Word := x.rotateLeft (k % 32).toNat

/-- `uint32(b[j])<<24 | uint32(b[j+1])<<16 | uint32(b[j+2])<<8 | uint32(b[j+3])`. -/
def load (b : Fin 32 → Byte) (j : Nat) : Word :=
  (b ⟨j % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 32 <<< 24 |||
  (b ⟨(j + 1) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 32 <<< 16 |||
  (b ⟨(j + 2) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 32 <<< 8 |||
  (b ⟨(j + 3) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 32

/-- The Go loop variables. -/
structure Vars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word

/-- The common round body (`t1`, `t2`, then the eight assignments), with the summand `kw`
that the Go code adds last to `t1` split as written: `… + _K[i] + w[i]` or `… + _P[i]`. -/
def bigSigma1 (e : Word) : Word := rotateLeft32 e (-6) ^^^ rotateLeft32 e (-11) ^^^ rotateLeft32 e (-25)
def bigSigma0 (a : Word) : Word := rotateLeft32 a (-2) ^^^ rotateLeft32 a (-13) ^^^ rotateLeft32 a (-22)
def ch (e f g : Word) : Word := (e &&& f) ^^^ (~~~e &&& g)
def maj (a b c : Word) : Word := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

def Vars.step (v : Vars) (t1 : Word) : Vars :=
  let t2 := bigSigma0 v.a + maj v.a v.b v.c
  ⟨t1 + t2, v.a, v.b, v.c, v.d + t1, v.e, v.f, v.g⟩

/-- `t1 := h + Σ1(e) + Ch(e,f,g) + _K[i] + w[i]`. -/
def Vars.roundKW (v : Vars) (k w : Word) : Vars :=
  v.step (v.h + bigSigma1 v.e + ch v.e v.f v.g + k + w)

/-- `t1 := h + Σ1(e) + Ch(e,f,g) + _P[i]`. -/
def Vars.roundP (v : Vars) (p : Word) : Vars :=
  v.step (v.h + bigSigma1 v.e + ch v.e v.f v.g + p)

/-- `w[j] = x` on the 16-word buffer. -/
def setW (w : Nat → Word) (j : Nat) (x : Word) : Nat → Word := fun i => if i = j then x else w i

/-- State of the message loops: the variables and the buffer `w`. -/
structure MsgSt where
  v : Vars
  w : Nat → Word

/-- `for i := 0; i < 8`: `w[i]` from `p[2k]` at byte `4i`. -/
def loop1 (p0 : Fin 32 → Byte) (s : MsgSt) (i : Nat) : MsgSt :=
  let w := setW s.w i (load p0 (i * 4))
  ⟨s.v.roundKW (Ktab.getD i 0) (w i), w⟩

/-- `for i := 8; i < 16`: `w[i]` from `p[2k+1]` at byte `4(i-8)`. -/
def loop2 (p1 : Fin 32 → Byte) (s : MsgSt) (i : Nat) : MsgSt :=
  let w := setW s.w i (load p1 ((i - 8) * 4))
  ⟨s.v.roundKW (Ktab.getD i 0) (w i), w⟩

/-- `for i := 16; i < 64`: extend the schedule in place, then the round. -/
def loop3 (s : MsgSt) (i : Nat) : MsgSt :=
  let v1 := s.w ((i - 2) % 16)
  let t1 := rotateLeft32 v1 (-17) ^^^ rotateLeft32 v1 (-19) ^^^ (v1 >>> 10)
  let v2 := s.w ((i - 15) % 16)
  let t2 := rotateLeft32 v2 (-7) ^^^ rotateLeft32 v2 (-18) ^^^ (v2 >>> 3)
  let w := setW s.w (i % 16) (s.w (i % 16) + (t1 + s.w ((i - 7) % 16) + t2))
  ⟨s.v.roundKW (Ktab.getD i 0) (w (i % 16)), w⟩

def initVars : Vars :=
  ⟨initTab.getD 0 0, initTab.getD 1 0, initTab.getD 2 0, initTab.getD 3 0,
   initTab.getD 4 0, initTab.getD 5 0, initTab.getD 6 0, initTab.getD 7 0⟩

def Vars.add (x y : Vars) : Vars :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e, x.f + y.f, x.g + y.g, x.h + y.h⟩

/-- `binary.BigEndian.PutUint32`. -/
def putUint32 (x : Word) : List Byte :=
  [(x >>> 24).truncate 8, (x >>> 16).truncate 8, (x >>> 8).truncate 8, x.truncate 8]

/-- One iteration of the `k` loop: the digest of the pair `(p[2k], p[2k+1])`, and the buffer
`w` left for the next iteration. -/
def pairDigest (p0 p1 : Fin 32 → Byte) (w0 : Nat → Word) : List Byte × (Nat → Word) :=
  let s : MsgSt := ⟨initVars, w0⟩
  let s := (List.range' 0 8).foldl (loop1 p0) s
  let s := (List.range' 8 8).foldl (loop2 p1) s
  let s := (List.range' 16 48).foldl loop3 s
  -- Add original digest
  let hv := s.v.add initVars
  -- Rounds with padding
  let r := (List.range' 0 64).foldl (fun v i => v.roundP (Ptab.getD i 0)) hv
  let out := hv.add r
  ([out.a, out.b, out.c, out.d, out.e, out.f, out.g, out.h].flatMap putUint32, s.w)

/-- `sha256_1_generic(digests, p)`: `digests[k]` for `k < len(p)/2`, the other digests unchanged. -/
def hashLoop (p : List (Fin 32 → Byte)) : Nat → (Nat → Word) → List (List Byte) → List (List Byte)
  | 0, _, ds => ds
  | n + 1, w, ds =>
    let k := p.length / 2 - (n + 1)
    let (dig, w') := pairDigest (p.getD (2 * k) (fun _ => 0)) (p.getD (2 * k + 1) (fun _ => 0)) w
    hashLoop p n w' (ds.set k dig)

def sha256_1_generic (digests : List (List Byte)) (p : List (Fin 32 → Byte)) : List (List Byte) :=
  hashLoop p (p.length / 2) (fun _ => 0) digests

end Hashtree.Go
