import Hashtree.GoGeneric
import Hashtree.SpecVectors

/-! The Go model agrees with the specification on sample inputs (executable check). -/

namespace Hashtree.GoVectors
open Hashtree.Spec Hashtree.Go Hashtree.SpecVectors

def half (s : String) (k : Nat) : Fin 32 → Byte := fun i => (unhex s).getD (32 * k + i.val) 0

def seq := "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
#guard (pairDigest (half seq 0) (half seq 1) (fun _ => 0)).1 = node (fun i => (unhex seq).getD i.val 0)
#guard (pairDigest (half seq 0) (half seq 1) (fun i => BitVec.ofNat 32 (i * 77))).1 = node (fun i => (unhex seq).getD i.val 0)
-- two pairs through the k loop (the buffer w is carried over)
#guard sha256_1_generic [[], []] [half seq 0, half seq 1, half seq 1, half seq 0] =
  [node (fun i => (unhex seq).getD i.val 0),
   node (fun i => (unhex seq).getD ((i.val + 32) % 64) 0)]

end Hashtree.GoVectors
