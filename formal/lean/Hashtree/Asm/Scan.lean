import Hashtree.Asm.X86Run
import Hashtree.SpecLemmas
import Std.Data.HashMap

/-!
# Spec-quantity matcher for cut finding (tool, not part of any proof)

For a concrete run, every data lane (general-register halves, vector lanes, stored lanes) is
compared with the SHA-256 quantities of every block of the call: `A r t` / `E r t` (the `a` / `e`
word after `t` rounds of compression `r`, `t ≥ -3`, so `b,c,d` / `f,g,h` are earlier `A` / `E`),
`W r t`, `KW r t` (= `K_t + W_t`), `R t` (raw little-endian input word), `H r i` (hash value
before compression `r`, `r = 2`: the digest).  Labels found in two runs on different inputs are
kept only if they agree, so accidental equalities drop out.
-/

namespace Hashtree.Asm.Scan
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Run Hashtree.Spec

/-- A spec quantity of node (block) `n`. -/
inductive Q where
  | A (n r : Nat) (t : Int)
  | E (n r : Nat) (t : Int)
  | W (n r t : Nat)
  | KW (n r t : Nat)
  | R (n t : Nat)
  | H (n r i : Nat)
  /-- `W_t + σ0(W_{t+1})` (SHA256MSG1 / sigma0 step) -/
  | M1 (n r t : Nat)
  /-- `W_t + σ0(W_{t+1}) + W_{t+9}` (before the σ1 step) -/
  | M2 (n r t : Nat)
  /-- a digest word byte-swapped (as stored, read little-endian) -/
  | HB (n i : Nat)
  deriving DecidableEq, Repr, Hashable, BEq, Inhabited

def Q.toString : Q → String
  | .A n r t => s!"A{n}.{r}.{t}" | .E n r t => s!"E{n}.{r}.{t}" | .W n r t => s!"W{n}.{r}.{t}"
  | .KW n r t => s!"KW{n}.{r}.{t}" | .R n t => s!"R{n}.{t}" | .H n r i => s!"H{n}.{r}.{i}"
  | .M1 n r t => s!"MA{n}.{r}.{t}" | .M2 n r t => s!"MB{n}.{r}.{t}" | .HB n i => s!"HB{n}.{i}"

instance : ToString Q := ⟨Q.toString⟩

def stWord (s : Spec.State) : Nat → Word
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d | 4 => s.e | 5 => s.f | 6 => s.g | _ => s.h

/-- All quantities of node `n` with block `blk`, with their values. -/
def quantities (n : Nat) (blk : Fin 64 → Byte) : List (Q × W32) := Id.run do
  let M := inWords blk
  let H1 := compress H0 M
  let H2 := compress H1 padBlock
  let mut out : List (Q × W32) := []
  for r in [0, 1] do
    let (H, B) := if r = 0 then (H0, M) else (H1, padBlock)
    for t in [0:65] do
      let st := rs H B t
      out := (.A n r t, st.a) :: (.E n r t, st.e) :: out
    out := (.A n r (-1), H.b) :: (.A n r (-2), H.c) :: (.A n r (-3), H.d) ::
      (.E n r (-1), H.f) :: (.E n r (-2), H.g) :: (.E n r (-3), H.h) :: out
    for t in [0:64] do
      out := (.W n r t, W B t) :: (.KW n r t, K t + W B t) :: out
      let m1 := W B t + sigma0 (W B (t + 1))
      out := (.M1 n r t, m1) :: (.M2 n r t, m1 + W B (t + 9)) :: out
  for t in [0:16] do
    let w := (List.range 4).foldl (fun acc k => acc ||| ((blk ⟨(4 * t + k) % 64, Nat.mod_lt _ (by decide)⟩).zeroExtend 32 <<< (8 * k))) 0
    out := (.R n t, w) :: out
  for (r, H) in [(0, H0), (1, H1), (2, H2)] do
    for i in [0:8] do
      out := (.H n r i, stWord H i) :: out
  for i in [0:8] do
    let w := stWord H2 i
    let bs := (w >>> 24 &&& 0xff) ||| ((w >>> 16 &&& 0xff) <<< 8) ||| ((w >>> 8 &&& 0xff) <<< 16) ||| ((w &&& 0xff) <<< 24)
    out := (.HB n i, bs) :: out
  return out

/-- Value → quantities. -/
def table (input : Array Nat) (count : Nat) : Std.HashMap W32 (List Q) := Id.run do
  let mut m : Std.HashMap W32 (List Q) := {}
  for n in [0:count] do
    let blk : Fin 64 → Byte := fun i => BitVec.ofNat 8 (input.getD (64 * n + i.val) 0)
    for (q, v) in quantities n blk do
      m := m.insert v (q :: (m.getD v []))
  return m

/-- A data location of the machine. -/
inductive Loc where
  | g (i : Nat) (hi : Bool)
  | v (i l : Nat)
  | m (region : Nat) (off : Int)
  deriving DecidableEq, Repr, Hashable, BEq, Inhabited

def Loc.toString : Loc → String
  | .g i hi => s!"g{i}{if hi then "h" else "l"}" | .v i l => s!"v{i}.{l}" | .m r o => s!"m{r}@{o}"

instance : ToString Loc := ⟨Loc.toString⟩

/-- The data lanes of a concrete state (stored lanes: newest write per address, whole lanes). -/
def lanes (m0 : Addr Int → Cell W32 Int) (s : CS) : List (Loc × W32) := Id.run do
  let mut out : List (Loc × W32) := []
  for i in [0:16] do
    match s.getG i with
    | .num lo hi => out := (.g i false, lo) :: (.g i true, hi) :: out
    | .ptr _ => pure ()
  for i in [0:32] do
    for l in [0:16] do
      out := (.v i l, (s.getV i).getD l 0) :: out
  -- stored lanes: addresses of logged cells holding byte 0 of a lane
  let mut seen : List (Nat × Int) := []
  for (a, c) in s.mem do
    match c with
    | .dat _ 0 =>
      if !(seen.contains (a.region, a.off)) then
        seen := (a.region, a.off) :: seen
        match loadLane m0 s a with
        | .ok x => out := (.m a.region a.off, x) :: out
        | .error _ => pure ()
    | _ => pure ()
  return out

/-- Labels of each location at a state, agreeing between two runs. -/
def labels (t1 t2 : Std.HashMap W32 (List Q)) (l1 l2 : List (Loc × W32)) : List (Loc × List Q) :=
  l1.filterMap fun (loc, x) =>
    match l2.find? (·.1 == loc) with
    | some (_, y) =>
      let q1 := t1.getD x []
      let q2 := t2.getD y []
      let common := q1.filter (q2.contains ·)
      if common.isEmpty then none else some (loc, common)
    | none => none

end Hashtree.Asm.Scan
