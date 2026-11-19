import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D28
import Hashtree.Gen.WinAvxX4P.D27

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice28 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K28 K29 T28 = true := by
  decide +kernel

theorem core28_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 215) = V (.A 3 0 (17)))
    (h1 : env (.n 151) = V (.E 3 0 (17)))
    (h2 : env (.n 119) = V (.E 3 0 (19)))
    (h3 : env (.n 135) = V (.E 3 0 (18)))
    (h4 : env (.n 103) = V (.E 3 0 (20)))
    (h5 : env (.n 327) = V (.W 3 0 20))
    (h6 : V (.E 3 0 (21)) = V (.A 3 0 (17)) + (V (.E 3 0 (17)) + Sigma1 (V (.E 3 0 (20))) + Ch (V (.E 3 0 (20))) (V (.E 3 0 (19))) (V (.E 3 0 (18))) + V (.KW 3 0 20)))
    (h7 : V (.KW 3 0 20) = 770255983#32 + V (.W 3 0 20)) :
    E.eval env (.add (.var (.n 215)) (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.var (.n 327)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7))))) = V (.E 3 0 (21)) :=
  shape42 (env (.n 215)) (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.n 327)) (V (.A 3 0 (17))) (V (.E 3 0 (17))) (V (.E 3 0 (19))) (V (.E 3 0 (18))) (V (.E 3 0 (20))) (V (.W 3 0 20)) (V (.E 3 0 (21))) (V (.KW 3 0 20)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core28_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.A 2 0 (17)))
    (h1 : env (.n 150) = V (.E 2 0 (17)))
    (h2 : env (.n 118) = V (.E 2 0 (19)))
    (h3 : env (.n 134) = V (.E 2 0 (18)))
    (h4 : env (.n 102) = V (.E 2 0 (20)))
    (h5 : env (.n 326) = V (.W 2 0 20))
    (h6 : V (.E 2 0 (21)) = V (.A 2 0 (17)) + (V (.E 2 0 (17)) + Sigma1 (V (.E 2 0 (20))) + Ch (V (.E 2 0 (20))) (V (.E 2 0 (19))) (V (.E 2 0 (18))) + V (.KW 2 0 20)))
    (h7 : V (.KW 2 0 20) = 770255983#32 + V (.W 2 0 20)) :
    E.eval env (.add (.var (.n 214)) (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.var (.n 326)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7))))) = V (.E 2 0 (21)) :=
  shape42 (env (.n 214)) (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.n 326)) (V (.A 2 0 (17))) (V (.E 2 0 (17))) (V (.E 2 0 (19))) (V (.E 2 0 (18))) (V (.E 2 0 (20))) (V (.W 2 0 20)) (V (.E 2 0 (21))) (V (.KW 2 0 20)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core28_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 213) = V (.A 1 0 (17)))
    (h1 : env (.n 149) = V (.E 1 0 (17)))
    (h2 : env (.n 117) = V (.E 1 0 (19)))
    (h3 : env (.n 133) = V (.E 1 0 (18)))
    (h4 : env (.n 101) = V (.E 1 0 (20)))
    (h5 : env (.n 325) = V (.W 1 0 20))
    (h6 : V (.E 1 0 (21)) = V (.A 1 0 (17)) + (V (.E 1 0 (17)) + Sigma1 (V (.E 1 0 (20))) + Ch (V (.E 1 0 (20))) (V (.E 1 0 (19))) (V (.E 1 0 (18))) + V (.KW 1 0 20)))
    (h7 : V (.KW 1 0 20) = 770255983#32 + V (.W 1 0 20)) :
    E.eval env (.add (.var (.n 213)) (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.var (.n 325)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7))))) = V (.E 1 0 (21)) :=
  shape42 (env (.n 213)) (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.n 325)) (V (.A 1 0 (17))) (V (.E 1 0 (17))) (V (.E 1 0 (19))) (V (.E 1 0 (18))) (V (.E 1 0 (20))) (V (.W 1 0 20)) (V (.E 1 0 (21))) (V (.KW 1 0 20)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core28_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.A 0 0 (17)))
    (h1 : env (.n 148) = V (.E 0 0 (17)))
    (h2 : env (.n 116) = V (.E 0 0 (19)))
    (h3 : env (.n 132) = V (.E 0 0 (18)))
    (h4 : env (.n 100) = V (.E 0 0 (20)))
    (h5 : env (.n 324) = V (.W 0 0 20))
    (h6 : V (.E 0 0 (21)) = V (.A 0 0 (17)) + (V (.E 0 0 (17)) + Sigma1 (V (.E 0 0 (20))) + Ch (V (.E 0 0 (20))) (V (.E 0 0 (19))) (V (.E 0 0 (18))) + V (.KW 0 0 20)))
    (h7 : V (.KW 0 0 20) = 770255983#32 + V (.W 0 0 20)) :
    E.eval env (.add (.var (.n 212)) (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.var (.n 324)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7))))) = V (.E 0 0 (21)) :=
  shape42 (env (.n 212)) (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.n 324)) (V (.A 0 0 (17))) (V (.E 0 0 (17))) (V (.E 0 0 (19))) (V (.E 0 0 (18))) (V (.E 0 0 (20))) (V (.W 0 0 20)) (V (.E 0 0 (21))) (V (.KW 0 0 20)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core28_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (17)))
    (h1 : env (.n 119) = V (.E 3 0 (19)))
    (h2 : env (.n 135) = V (.E 3 0 (18)))
    (h3 : env (.n 103) = V (.E 3 0 (20)))
    (h4 : env (.n 327) = V (.W 3 0 20))
    (h5 : env (.n 167) = V (.A 3 0 (20)))
    (h6 : env (.n 199) = V (.A 3 0 (18)))
    (h7 : env (.n 183) = V (.A 3 0 (19)))
    (h8 : V (.A 3 0 (21)) = (V (.E 3 0 (17)) + Sigma1 (V (.E 3 0 (20))) + Ch (V (.E 3 0 (20))) (V (.E 3 0 (19))) (V (.E 3 0 (18))) + V (.KW 3 0 20)) + (Sigma0 (V (.A 3 0 (20))) + Maj (V (.A 3 0 (20))) (V (.A 3 0 (19))) (V (.A 3 0 (18)))))
    (h9 : V (.KW 3 0 20) = 770255983#32 + V (.W 3 0 20)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.var (.n 327)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7)))) (.or (.and (.var (.n 167)) (.var (.n 199))) (.and (.xor (.var (.n 167)) (.var (.n 199))) (.var (.n 183))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 2) (.shl (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 30)) (.or (.shr (.var (.n 167)) 22) (.shl (.var (.n 167)) 10)))) = V (.A 3 0 (21)) :=
  shape43 (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.n 327)) (env (.n 167)) (env (.n 199)) (env (.n 183)) (V (.E 3 0 (17))) (V (.E 3 0 (19))) (V (.E 3 0 (18))) (V (.E 3 0 (20))) (V (.W 3 0 20)) (V (.A 3 0 (20))) (V (.A 3 0 (18))) (V (.A 3 0 (19))) (V (.A 3 0 (21))) (V (.KW 3 0 20)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core28_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (17)))
    (h1 : env (.n 118) = V (.E 2 0 (19)))
    (h2 : env (.n 134) = V (.E 2 0 (18)))
    (h3 : env (.n 102) = V (.E 2 0 (20)))
    (h4 : env (.n 326) = V (.W 2 0 20))
    (h5 : env (.n 166) = V (.A 2 0 (20)))
    (h6 : env (.n 198) = V (.A 2 0 (18)))
    (h7 : env (.n 182) = V (.A 2 0 (19)))
    (h8 : V (.A 2 0 (21)) = (V (.E 2 0 (17)) + Sigma1 (V (.E 2 0 (20))) + Ch (V (.E 2 0 (20))) (V (.E 2 0 (19))) (V (.E 2 0 (18))) + V (.KW 2 0 20)) + (Sigma0 (V (.A 2 0 (20))) + Maj (V (.A 2 0 (20))) (V (.A 2 0 (19))) (V (.A 2 0 (18)))))
    (h9 : V (.KW 2 0 20) = 770255983#32 + V (.W 2 0 20)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.var (.n 326)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7)))) (.or (.and (.var (.n 166)) (.var (.n 198))) (.and (.xor (.var (.n 166)) (.var (.n 198))) (.var (.n 182))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 2) (.shl (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 30)) (.or (.shr (.var (.n 166)) 22) (.shl (.var (.n 166)) 10)))) = V (.A 2 0 (21)) :=
  shape43 (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.n 326)) (env (.n 166)) (env (.n 198)) (env (.n 182)) (V (.E 2 0 (17))) (V (.E 2 0 (19))) (V (.E 2 0 (18))) (V (.E 2 0 (20))) (V (.W 2 0 20)) (V (.A 2 0 (20))) (V (.A 2 0 (18))) (V (.A 2 0 (19))) (V (.A 2 0 (21))) (V (.KW 2 0 20)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core28_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (17)))
    (h1 : env (.n 117) = V (.E 1 0 (19)))
    (h2 : env (.n 133) = V (.E 1 0 (18)))
    (h3 : env (.n 101) = V (.E 1 0 (20)))
    (h4 : env (.n 325) = V (.W 1 0 20))
    (h5 : env (.n 165) = V (.A 1 0 (20)))
    (h6 : env (.n 197) = V (.A 1 0 (18)))
    (h7 : env (.n 181) = V (.A 1 0 (19)))
    (h8 : V (.A 1 0 (21)) = (V (.E 1 0 (17)) + Sigma1 (V (.E 1 0 (20))) + Ch (V (.E 1 0 (20))) (V (.E 1 0 (19))) (V (.E 1 0 (18))) + V (.KW 1 0 20)) + (Sigma0 (V (.A 1 0 (20))) + Maj (V (.A 1 0 (20))) (V (.A 1 0 (19))) (V (.A 1 0 (18)))))
    (h9 : V (.KW 1 0 20) = 770255983#32 + V (.W 1 0 20)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.var (.n 325)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7)))) (.or (.and (.var (.n 165)) (.var (.n 197))) (.and (.xor (.var (.n 165)) (.var (.n 197))) (.var (.n 181))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 2) (.shl (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 30)) (.or (.shr (.var (.n 165)) 22) (.shl (.var (.n 165)) 10)))) = V (.A 1 0 (21)) :=
  shape43 (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.n 325)) (env (.n 165)) (env (.n 197)) (env (.n 181)) (V (.E 1 0 (17))) (V (.E 1 0 (19))) (V (.E 1 0 (18))) (V (.E 1 0 (20))) (V (.W 1 0 20)) (V (.A 1 0 (20))) (V (.A 1 0 (18))) (V (.A 1 0 (19))) (V (.A 1 0 (21))) (V (.KW 1 0 20)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core28_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (17)))
    (h1 : env (.n 116) = V (.E 0 0 (19)))
    (h2 : env (.n 132) = V (.E 0 0 (18)))
    (h3 : env (.n 100) = V (.E 0 0 (20)))
    (h4 : env (.n 324) = V (.W 0 0 20))
    (h5 : env (.n 164) = V (.A 0 0 (20)))
    (h6 : env (.n 196) = V (.A 0 0 (18)))
    (h7 : env (.n 180) = V (.A 0 0 (19)))
    (h8 : V (.A 0 0 (21)) = (V (.E 0 0 (17)) + Sigma1 (V (.E 0 0 (20))) + Ch (V (.E 0 0 (20))) (V (.E 0 0 (19))) (V (.E 0 0 (18))) + V (.KW 0 0 20)) + (Sigma0 (V (.A 0 0 (20))) + Maj (V (.A 0 0 (20))) (V (.A 0 0 (19))) (V (.A 0 0 (18)))))
    (h9 : V (.KW 0 0 20) = 770255983#32 + V (.W 0 0 20)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.var (.n 324)) (.const 770255983))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7)))) (.or (.and (.var (.n 164)) (.var (.n 196))) (.and (.xor (.var (.n 164)) (.var (.n 196))) (.var (.n 180))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 2) (.shl (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 30)) (.or (.shr (.var (.n 164)) 22) (.shl (.var (.n 164)) 10)))) = V (.A 0 0 (21)) :=
  shape43 (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.n 324)) (env (.n 164)) (env (.n 196)) (env (.n 180)) (V (.E 0 0 (17))) (V (.E 0 0 (19))) (V (.E 0 0 (18))) (V (.E 0 0 (20))) (V (.W 0 0 20)) (V (.A 0 0 (20))) (V (.A 0 0 (18))) (V (.A 0 0 (19))) (V (.A 0 0 (21))) (V (.KW 0 0 20)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem step28 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L28) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K28)) L29 := by
  have h0 := hI.1; have hI := hI.2
  have h1 := hI.1; have hI := hI.2
  have h2 := hI.1; have hI := hI.2
  have h3 := hI.1; have hI := hI.2
  have h4 := hI.1; have hI := hI.2
  have h5 := hI.1; have hI := hI.2
  have h6 := hI.1; have hI := hI.2
  have h7 := hI.1; have hI := hI.2
  have h8 := hI.1; have hI := hI.2
  have h9 := hI.1; have hI := hI.2
  have h10 := hI.1; have hI := hI.2
  have h11 := hI.1; have hI := hI.2
  have h12 := hI.1; have hI := hI.2
  have h13 := hI.1; have hI := hI.2
  have h14 := hI.1; have hI := hI.2
  have h15 := hI.1; have hI := hI.2
  have h16 := hI.1; have hI := hI.2
  have h17 := hI.1; have hI := hI.2
  have h18 := hI.1; have hI := hI.2
  have h19 := hI.1; have hI := hI.2
  have h20 := hI.1; have hI := hI.2
  have h21 := hI.1; have hI := hI.2
  have h22 := hI.1; have hI := hI.2
  have h23 := hI.1; have hI := hI.2
  have h24 := hI.1; have hI := hI.2
  have h25 := hI.1; have hI := hI.2
  have h26 := hI.1; have hI := hI.2
  have h27 := hI.1; have hI := hI.2
  have h28 := hI.1; have hI := hI.2
  have h29 := hI.1; have hI := hI.2
  have h30 := hI.1; have hI := hI.2
  have h31 := hI.1; have hI := hI.2
  have h32 := hI.1; have hI := hI.2
  have h33 := hI.1; have hI := hI.2
  have h34 := hI.1; have hI := hI.2
  have h35 := hI.1; have hI := hI.2
  have h36 := hI.1; have hI := hI.2
  have h37 := hI.1; have hI := hI.2
  have h38 := hI.1; have hI := hI.2
  have h39 := hI.1; have hI := hI.2
  have h40 := hI.1; have hI := hI.2
  have h41 := hI.1; have hI := hI.2
  have h42 := hI.1; have hI := hI.2
  have h43 := hI.1; have hI := hI.2
  have h44 := hI.1; have hI := hI.2
  have h45 := hI.1; have hI := hI.2
  have h46 := hI.1; have hI := hI.2
  have h47 := hI.1; have hI := hI.2
  have h48 := hI.1; have hI := hI.2
  have h49 := hI.1; have hI := hI.2
  have h50 := hI.1; have hI := hI.2
  have h51 := hI.1; have hI := hI.2
  have h52 := hI.1; have hI := hI.2
  have h53 := hI.1; have hI := hI.2
  have h54 := hI.1; have hI := hI.2
  have h55 := hI.1; have hI := hI.2
  have h56 := hI.1; have hI := hI.2
  have h57 := hI.1; have hI := hI.2
  have h58 := hI.1; have hI := hI.2
  have h59 := hI.1; have hI := hI.2
  have h60 := hI.1; have hI := hI.2
  have h61 := hI.1; have hI := hI.2
  have h62 := hI.1; have hI := hI.2
  have h63 := hI.1; have hI := hI.2
  have h64 := hI.1; have hI := hI.2
  have h65 := hI.1; have hI := hI.2
  have h66 := hI.1; have hI := hI.2
  have h67 := hI.1; have hI := hI.2
  have h68 := hI.1; have hI := hI.2
  have h69 := hI.1; have hI := hI.2
  have h70 := hI.1; have hI := hI.2
  have h71 := hI.1; have hI := hI.2
  have h72 := hI.1; have hI := hI.2
  have h73 := hI.1; have hI := hI.2
  have h74 := hI.1; have hI := hI.2
  have h75 := hI.1; have hI := hI.2
  have h76 := hI.1; have hI := hI.2
  have h77 := hI.1; have hI := hI.2
  have h78 := hI.1; have hI := hI.2
  have h79 := hI.1; have hI := hI.2
  have h80 := hI.1; have hI := hI.2
  have h81 := hI.1; have hI := hI.2
  have h82 := hI.1; have hI := hI.2
  have h83 := hI.1; have hI := hI.2
  have h84 := hI.1; have hI := hI.2
  have h85 := hI.1; have hI := hI.2
  have h86 := hI.1; have hI := hI.2
  have h87 := hI.1; have hI := hI.2
  have h88 := hI.1; have hI := hI.2
  have h89 := hI.1; have hI := hI.2
  have h90 := hI.1; have hI := hI.2
  have h91 := hI.1; have hI := hI.2
  have h92 := hI.1; have hI := hI.2
  have h93 := hI.1; have hI := hI.2
  have h94 := hI.1; have hI := hI.2
  have h95 := hI.1; have hI := hI.2
  have h96 := hI.1; have hI := hI.2
  have h97 := hI.1; have hI := hI.2
  have h98 := hI.1; have hI := hI.2
  have h99 := hI.1; have hI := hI.2
  have h100 := hI.1; have hI := hI.2
  have h101 := hI.1; have hI := hI.2
  have h102 := hI.1; have hI := hI.2
  have h103 := hI.1; have hI := hI.2
  have h104 := hI.1; have hI := hI.2
  have h105 := hI.1; have hI := hI.2
  have h106 := hI.1; have hI := hI.2
  have h107 := hI.1; have hI := hI.2
  have h108 := hI.1; have hI := hI.2
  have h109 := hI.1; have hI := hI.2
  have h110 := hI.1; have hI := hI.2
  have h111 := hI.1; have hI := hI.2
  have h112 := hI.1; have hI := hI.2
  have h113 := hI.1; have hI := hI.2
  have h114 := hI.1; have hI := hI.2
  have h115 := hI.1; have hI := hI.2
  have h116 := hI.1; have hI := hI.2
  have h117 := hI.1; have hI := hI.2
  have h118 := hI.1; have hI := hI.2
  have h119 := hI.1; have hI := hI.2
  have h120 := hI.1; have hI := hI.2
  have h121 := hI.1; have hI := hI.2
  have h122 := hI.1; have hI := hI.2
  have h123 := hI.1; have hI := hI.2
  have h124 := hI.1; have hI := hI.2
  have h125 := hI.1; have hI := hI.2
  have h126 := hI.1; have hI := hI.2
  have h127 := hI.1; have hI := hI.2
  have h128 := hI.1; have hI := hI.2
  have h129 := hI.1; have hI := hI.2
  have h130 := hI.1; have hI := hI.2
  have h131 := hI.1; have hI := hI.2
  have h132 := hI.1; have hI := hI.2
  have h133 := hI.1; have hI := hI.2
  have h134 := hI.1; have hI := hI.2
  have h135 := hI.1; have hI := hI.2
  have h136 := hI.1; have hI := hI.2
  have h137 := hI.1; have hI := hI.2
  have h138 := hI.1; have hI := hI.2
  have h139 := hI.1; have hI := hI.2
  have h140 := hI.1; have hI := hI.2
  have h141 := hI.1; have hI := hI.2
  have h142 := hI.1; have hI := hI.2
  have h143 := hI.1; have hI := hI.2
  have h144 := hI.1; have hI := hI.2
  have h145 := hI.1; have hI := hI.2
  have h146 := hI.1; have hI := hI.2
  have h147 := hI.1; have hI := hI.2
  have h148 := hI.1; have hI := hI.2
  have h149 := hI.1; have hI := hI.2
  have h150 := hI.1; have hI := hI.2
  have h151 := hI.1; have hI := hI.2
  have h152 := hI.1; have hI := hI.2
  have h153 := hI.1; have hI := hI.2
  have h154 := hI.1; have hI := hI.2
  have h155 := hI.1; have hI := hI.2
  have h156 := hI.1; have hI := hI.2
  have h157 := hI.1; have hI := hI.2
  have h158 := hI.1; have hI := hI.2
  have h159 := hI.1; have hI := hI.2
  have h160 := hI.1; have hI := hI.2
  have h161 := hI.1; have hI := hI.2
  have h162 := hI.1; have hI := hI.2
  have h163 := hI.1; have hI := hI.2
  have h164 := hI.1; have hI := hI.2
  have h165 := hI.1; have hI := hI.2
  have h166 := hI.1; have hI := hI.2
  have h167 := hI.1; have hI := hI.2
  have h168 := hI.1; have hI := hI.2
  have h169 := hI.1; have hI := hI.2
  have h170 := hI.1; have hI := hI.2
  have h171 := hI.1; have hI := hI.2
  have h172 := hI.1; have hI := hI.2
  have h173 := hI.1; have hI := hI.2
  have h174 := hI.1; have hI := hI.2
  have h175 := hI.1; have hI := hI.2
  have h176 := hI.1; have hI := hI.2
  have h177 := hI.1; have hI := hI.2
  have h178 := hI.1; have hI := hI.2
  have h179 := hI.1; have hI := hI.2
  have h180 := hI.1; have hI := hI.2
  have h181 := hI.1; have hI := hI.2
  have h182 := hI.1; have hI := hI.2
  have h183 := hI.1; have hI := hI.2
  have h184 := hI.1; have hI := hI.2
  have h185 := hI.1; have hI := hI.2
  have h186 := hI.1; have hI := hI.2
  have h187 := hI.1; have hI := hI.2
  have h188 := hI.1; have hI := hI.2
  have h189 := hI.1; have hI := hI.2
  have h190 := hI.1; have hI := hI.2
  have h191 := hI.1; have hI := hI.2
  have h192 := hI.1; have hI := hI.2
  have h193 := hI.1; have hI := hI.2
  have h194 := hI.1; have hI := hI.2
  have h195 := hI.1; have hI := hI.2
  have h196 := hI.1; have hI := hI.2
  have h197 := hI.1; have hI := hI.2
  have h198 := hI.1; have hI := hI.2
  have h199 := hI.1; have hI := hI.2
  have h200 := hI.1; have hI := hI.2
  have h201 := hI.1; have hI := hI.2
  have h202 := hI.1; have hI := hI.2
  have h203 := hI.1; have hI := hI.2
  have h204 := hI.1; have hI := hI.2
  have h205 := hI.1; have hI := hI.2
  have h206 := hI.1; have hI := hI.2
  have h207 := hI.1; have hI := hI.2
  have h208 := hI.1; have hI := hI.2
  have h209 := hI.1; have hI := hI.2
  have h210 := hI.1; have hI := hI.2
  have h211 := hI.1; have hI := hI.2
  have h212 := hI.1; have hI := hI.2
  have h213 := hI.1; have hI := hI.2
  have h214 := hI.1; have hI := hI.2
  have h215 := hI.1; have hI := hI.2
  have h216 := hI.1; have hI := hI.2
  have h217 := hI.1; have hI := hI.2
  have h218 := hI.1; have hI := hI.2
  have h219 := hI.1; have hI := hI.2
  have h220 := hI.1; have hI := hI.2
  have h221 := hI.1; have hI := hI.2
  have h222 := hI.1; have hI := hI.2
  have h223 := hI.1; have hI := hI.2
  have h224 := hI.1; have hI := hI.2
  have h225 := hI.1; have hI := hI.2
  have h226 := hI.1; have hI := hI.2
  have h227 := hI.1; have hI := hI.2
  have h228 := hI.1; have hI := hI.2
  have h229 := hI.1; have hI := hI.2
  have h230 := hI.1; have hI := hI.2
  have h231 := hI.1; have hI := hI.2
  have h232 := hI.1; have hI := hI.2
  have h233 := hI.1; have hI := hI.2
  have h234 := hI.1; have hI := hI.2
  have h235 := hI.1; have hI := hI.2
  have h236 := hI.1; have hI := hI.2
  have h237 := hI.1; have hI := hI.2
  have h238 := hI.1; have hI := hI.2
  have h239 := hI.1; have hI := hI.2
  have h240 := hI.1; have hI := hI.2
  have h241 := hI.1; have hI := hI.2
  have h242 := hI.1; have hI := hI.2
  have h243 := hI.1; have hI := hI.2
  have h244 := hI.1; have hI := hI.2
  have h245 := hI.1; have hI := hI.2
  have h246 := hI.1; have hI := hI.2
  have h247 := hI.1; have hI := hI.2
  have h248 := hI.1; have hI := hI.2
  have h249 := hI.1; have hI := hI.2
  have h250 := hI.1; have hI := hI.2
  have h251 := hI.1; have hI := hI.2
  have h252 := hI.1; have hI := hI.2
  have h253 := hI.1; have hI := hI.2
  have h254 := hI.1; have hI := hI.2
  have h255 := hI.1; have hI := hI.2
  have h256 := hI.1; have hI := hI.2
  have h257 := hI.1; have hI := hI.2
  have h258 := hI.1; have hI := hI.2
  have h259 := hI.1; have hI := hI.2
  have h260 := hI.1; have hI := hI.2
  have h261 := hI.1; have hI := hI.2
  have h262 := hI.1; have hI := hI.2
  have h263 := hI.1; have hI := hI.2
  have h264 := hI.1; have hI := hI.2
  have h265 := hI.1; have hI := hI.2
  have h266 := hI.1; have hI := hI.2
  have h267 := hI.1; have hI := hI.2
  have h268 := hI.1; have hI := hI.2
  have h269 := hI.1; have hI := hI.2
  have h270 := hI.1; have hI := hI.2
  have h271 := hI.1; have hI := hI.2
  have h272 := hI.1; have hI := hI.2
  have h273 := hI.1; have hI := hI.2
  have h274 := hI.1; have hI := hI.2
  have h275 := hI.1; have hI := hI.2
  have h276 := hI.1; have hI := hI.2
  have h277 := hI.1; have hI := hI.2
  have h278 := hI.1; have hI := hI.2
  have h279 := hI.1; have hI := hI.2
  have h280 := hI.1; have hI := hI.2
  have h281 := hI.1; have hI := hI.2
  have h282 := hI.1; have hI := hI.2
  have h283 := hI.1; have hI := hI.2
  have h284 := hI.1; have hI := hI.2
  have h285 := hI.1; have hI := hI.2
  have h286 := hI.1; have hI := hI.2
  have h287 := hI.1; have hI := hI.2
  have h288 := hI.1; have hI := hI.2
  have h289 := hI.1; have hI := hI.2
  have h290 := hI.1; have hI := hI.2
  have h291 := hI.1; have hI := hI.2
  exact invC_of_trees inp env _ T28 L29 (slice_trees_mem prog 4 _ _ 38 K28 K29 T28 slice28 env)
      (And.intro ⟨rfl, h16⟩
      (And.intro ⟨rfl, h17⟩
      (And.intro ⟨rfl, h18⟩
      (And.intro ⟨rfl, h19⟩
      (And.intro ⟨rfl, h20⟩
      (And.intro ⟨rfl, h21⟩
      (And.intro ⟨rfl, h22⟩
      (And.intro ⟨rfl, h23⟩
      (And.intro ⟨rfl, h24⟩
      (And.intro ⟨rfl, h25⟩
      (And.intro ⟨rfl, h26⟩
      (And.intro ⟨rfl, h27⟩
      (And.intro ⟨rfl, h28⟩
      (And.intro ⟨rfl, h29⟩
      (And.intro ⟨rfl, h30⟩
      (And.intro ⟨rfl, h31⟩
      (And.intro ⟨rfl, h32⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, h36⟩
      (And.intro ⟨rfl, h37⟩
      (And.intro ⟨rfl, h38⟩
      (And.intro ⟨rfl, h39⟩
      (And.intro ⟨rfl, h40⟩
      (And.intro ⟨rfl, h41⟩
      (And.intro ⟨rfl, h42⟩
      (And.intro ⟨rfl, h43⟩
      (And.intro ⟨rfl, h44⟩
      (And.intro ⟨rfl, h45⟩
      (And.intro ⟨rfl, h46⟩
      (And.intro ⟨rfl, h47⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h52⟩
      (And.intro ⟨rfl, h53⟩
      (And.intro ⟨rfl, h54⟩
      (And.intro ⟨rfl, h55⟩
      (And.intro ⟨rfl, h56⟩
      (And.intro ⟨rfl, h57⟩
      (And.intro ⟨rfl, h58⟩
      (And.intro ⟨rfl, h59⟩
      (And.intro ⟨rfl, h60⟩
      (And.intro ⟨rfl, h61⟩
      (And.intro ⟨rfl, h62⟩
      (And.intro ⟨rfl, h63⟩
      (And.intro ⟨rfl, h64⟩
      (And.intro ⟨rfl, h65⟩
      (And.intro ⟨rfl, h66⟩
      (And.intro ⟨rfl, h67⟩
      (And.intro ⟨rfl, h68⟩
      (And.intro ⟨rfl, h69⟩
      (And.intro ⟨rfl, h70⟩
      (And.intro ⟨rfl, h71⟩
      (And.intro ⟨rfl, h72⟩
      (And.intro ⟨rfl, h73⟩
      (And.intro ⟨rfl, h74⟩
      (And.intro ⟨rfl, h75⟩
      (And.intro ⟨rfl, h76⟩
      (And.intro ⟨rfl, h77⟩
      (And.intro ⟨rfl, h78⟩
      (And.intro ⟨rfl, h79⟩
      (And.intro ⟨rfl, h80⟩
      (And.intro ⟨rfl, h81⟩
      (And.intro ⟨rfl, h82⟩
      (And.intro ⟨rfl, h83⟩
      (And.intro ⟨rfl, h84⟩
      (And.intro ⟨rfl, h85⟩
      (And.intro ⟨rfl, h86⟩
      (And.intro ⟨rfl, h87⟩
      (And.intro ⟨rfl, h88⟩
      (And.intro ⟨rfl, h89⟩
      (And.intro ⟨rfl, h90⟩
      (And.intro ⟨rfl, h91⟩
      (And.intro ⟨rfl, h92⟩
      (And.intro ⟨rfl, h93⟩
      (And.intro ⟨rfl, h94⟩
      (And.intro ⟨rfl, h95⟩
      (And.intro ⟨rfl, h96⟩
      (And.intro ⟨rfl, h97⟩
      (And.intro ⟨rfl, h98⟩
      (And.intro ⟨rfl, h99⟩
      (And.intro ⟨rfl, h100⟩
      (And.intro ⟨rfl, h101⟩
      (And.intro ⟨rfl, h102⟩
      (And.intro ⟨rfl, h103⟩
      (And.intro ⟨rfl, h104⟩
      (And.intro ⟨rfl, h105⟩
      (And.intro ⟨rfl, h106⟩
      (And.intro ⟨rfl, h107⟩
      (And.intro ⟨rfl, h108⟩
      (And.intro ⟨rfl, h109⟩
      (And.intro ⟨rfl, h110⟩
      (And.intro ⟨rfl, h111⟩
      (And.intro ⟨rfl, h112⟩
      (And.intro ⟨rfl, h113⟩
      (And.intro ⟨rfl, h114⟩
      (And.intro ⟨rfl, h115⟩
      (And.intro ⟨rfl, h116⟩
      (And.intro ⟨rfl, h117⟩
      (And.intro ⟨rfl, h118⟩
      (And.intro ⟨rfl, h119⟩
      (And.intro ⟨rfl, h120⟩
      (And.intro ⟨rfl, h121⟩
      (And.intro ⟨rfl, h122⟩
      (And.intro ⟨rfl, h123⟩
      (And.intro ⟨rfl, h124⟩
      (And.intro ⟨rfl, h125⟩
      (And.intro ⟨rfl, h126⟩
      (And.intro ⟨rfl, h127⟩
      (And.intro ⟨rfl, h128⟩
      (And.intro ⟨rfl, h129⟩
      (And.intro ⟨rfl, h130⟩
      (And.intro ⟨rfl, h131⟩
      (And.intro ⟨rfl, h132⟩
      (And.intro ⟨rfl, h133⟩
      (And.intro ⟨rfl, h134⟩
      (And.intro ⟨rfl, h135⟩
      (And.intro ⟨rfl, h136⟩
      (And.intro ⟨rfl, h137⟩
      (And.intro ⟨rfl, h138⟩
      (And.intro ⟨rfl, h139⟩
      (And.intro ⟨rfl, h140⟩
      (And.intro ⟨rfl, h141⟩
      (And.intro ⟨rfl, h142⟩
      (And.intro ⟨rfl, h143⟩
      (And.intro ⟨rfl, h144⟩
      (And.intro ⟨rfl, h145⟩
      (And.intro ⟨rfl, h146⟩
      (And.intro ⟨rfl, h147⟩
      (And.intro ⟨rfl, h148⟩
      (And.intro ⟨rfl, h149⟩
      (And.intro ⟨rfl, h150⟩
      (And.intro ⟨rfl, h151⟩
      (And.intro ⟨rfl, h152⟩
      (And.intro ⟨rfl, h153⟩
      (And.intro ⟨rfl, h154⟩
      (And.intro ⟨rfl, h155⟩
      (And.intro ⟨rfl, h156⟩
      (And.intro ⟨rfl, h157⟩
      (And.intro ⟨rfl, h158⟩
      (And.intro ⟨rfl, h159⟩
      (And.intro ⟨rfl, h160⟩
      (And.intro ⟨rfl, h161⟩
      (And.intro ⟨rfl, h162⟩
      (And.intro ⟨rfl, h163⟩
      (And.intro ⟨rfl, h164⟩
      (And.intro ⟨rfl, h165⟩
      (And.intro ⟨rfl, h166⟩
      (And.intro ⟨rfl, h167⟩
      (And.intro ⟨rfl, h168⟩
      (And.intro ⟨rfl, h169⟩
      (And.intro ⟨rfl, h170⟩
      (And.intro ⟨rfl, h171⟩
      (And.intro ⟨rfl, h172⟩
      (And.intro ⟨rfl, h173⟩
      (And.intro ⟨rfl, h174⟩
      (And.intro ⟨rfl, h175⟩
      (And.intro ⟨rfl, h176⟩
      (And.intro ⟨rfl, h177⟩
      (And.intro ⟨rfl, h178⟩
      (And.intro ⟨rfl, h179⟩
      (And.intro ⟨rfl, h180⟩
      (And.intro ⟨rfl, h181⟩
      (And.intro ⟨rfl, h182⟩
      (And.intro ⟨rfl, h183⟩
      (And.intro ⟨rfl, h184⟩
      (And.intro ⟨rfl, h185⟩
      (And.intro ⟨rfl, h186⟩
      (And.intro ⟨rfl, h187⟩
      (And.intro ⟨rfl, h188⟩
      (And.intro ⟨rfl, h189⟩
      (And.intro ⟨rfl, h190⟩
      (And.intro ⟨rfl, h191⟩
      (And.intro ⟨rfl, h192⟩
      (And.intro ⟨rfl, h193⟩
      (And.intro ⟨rfl, h194⟩
      (And.intro ⟨rfl, h195⟩
      (And.intro ⟨rfl, h196⟩
      (And.intro ⟨rfl, h197⟩
      (And.intro ⟨rfl, h198⟩
      (And.intro ⟨rfl, h199⟩
      (And.intro ⟨rfl, h200⟩
      (And.intro ⟨rfl, h201⟩
      (And.intro ⟨rfl, h202⟩
      (And.intro ⟨rfl, h203⟩
      (And.intro ⟨rfl, h204⟩
      (And.intro ⟨rfl, h205⟩
      (And.intro ⟨rfl, h206⟩
      (And.intro ⟨rfl, h207⟩
      (And.intro ⟨rfl, h208⟩
      (And.intro ⟨rfl, h209⟩
      (And.intro ⟨rfl, h210⟩
      (And.intro ⟨rfl, h211⟩
      (And.intro ⟨rfl, h212⟩
      (And.intro ⟨rfl, h213⟩
      (And.intro ⟨rfl, h214⟩
      (And.intro ⟨rfl, h215⟩
      (And.intro ⟨rfl, h216⟩
      (And.intro ⟨rfl, h217⟩
      (And.intro ⟨rfl, h218⟩
      (And.intro ⟨rfl, h219⟩
      (And.intro ⟨rfl, h220⟩
      (And.intro ⟨rfl, h221⟩
      (And.intro ⟨rfl, h222⟩
      (And.intro ⟨rfl, h223⟩
      (And.intro ⟨rfl, h224⟩
      (And.intro ⟨rfl, h225⟩
      (And.intro ⟨rfl, h226⟩
      (And.intro ⟨rfl, h227⟩
      (And.intro ⟨rfl, h228⟩
      (And.intro ⟨rfl, h229⟩
      (And.intro ⟨rfl, h230⟩
      (And.intro ⟨rfl, h231⟩
      (And.intro ⟨rfl, h232⟩
      (And.intro ⟨rfl, h233⟩
      (And.intro ⟨rfl, h234⟩
      (And.intro ⟨rfl, h235⟩
      (And.intro ⟨rfl, h236⟩
      (And.intro ⟨rfl, h237⟩
      (And.intro ⟨rfl, h238⟩
      (And.intro ⟨rfl, h239⟩
      (And.intro ⟨rfl, h240⟩
      (And.intro ⟨rfl, h241⟩
      (And.intro ⟨rfl, h242⟩
      (And.intro ⟨rfl, h243⟩
      (And.intro ⟨rfl, h244⟩
      (And.intro ⟨rfl, h245⟩
      (And.intro ⟨rfl, h246⟩
      (And.intro ⟨rfl, h247⟩
      (And.intro ⟨rfl, h248⟩
      (And.intro ⟨rfl, h249⟩
      (And.intro ⟨rfl, h250⟩
      (And.intro ⟨rfl, h251⟩
      (And.intro ⟨rfl, h252⟩
      (And.intro ⟨rfl, h253⟩
      (And.intro ⟨rfl, h254⟩
      (And.intro ⟨rfl, h255⟩
      (And.intro ⟨rfl, h259⟩
      (And.intro ⟨rfl, h259⟩
      (And.intro ⟨rfl, h259⟩
      (And.intro ⟨rfl, h259⟩
      (And.intro ⟨rfl, h258⟩
      (And.intro ⟨rfl, h258⟩
      (And.intro ⟨rfl, h258⟩
      (And.intro ⟨rfl, h258⟩
      (And.intro ⟨rfl, h257⟩
      (And.intro ⟨rfl, h257⟩
      (And.intro ⟨rfl, h257⟩
      (And.intro ⟨rfl, h257⟩
      (And.intro ⟨rfl, h256⟩
      (And.intro ⟨rfl, h256⟩
      (And.intro ⟨rfl, h256⟩
      (And.intro ⟨rfl, h256⟩
      (And.intro ⟨rfl, core28_215 (qv inp) inp env h260 h276 h284 h280 h288 h256 (qE_succI inp 3 0 (20) (by decide)) ((qKW inp 3 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, core28_214 (qv inp) inp env h261 h277 h285 h281 h289 h257 (qE_succI inp 2 0 (20) (by decide)) ((qKW inp 2 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, core28_213 (qv inp) inp env h262 h278 h286 h282 h290 h258 (qE_succI inp 1 0 (20) (by decide)) ((qKW inp 1 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, core28_212 (qv inp) inp env h263 h279 h287 h283 h291 h259 (qE_succI inp 0 0 (20) (by decide)) ((qKW inp 0 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, h264⟩
      (And.intro ⟨rfl, h265⟩
      (And.intro ⟨rfl, h266⟩
      (And.intro ⟨rfl, h267⟩
      (And.intro ⟨rfl, h268⟩
      (And.intro ⟨rfl, h269⟩
      (And.intro ⟨rfl, h270⟩
      (And.intro ⟨rfl, h271⟩
      (And.intro ⟨rfl, h272⟩
      (And.intro ⟨rfl, h273⟩
      (And.intro ⟨rfl, h274⟩
      (And.intro ⟨rfl, h275⟩
      (And.intro ⟨rfl, core28_151 (qv inp) inp env h276 h284 h280 h288 h256 h272 h264 h268 (qA_succI inp 3 0 (20) (by decide)) ((qKW inp 3 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, core28_150 (qv inp) inp env h277 h285 h281 h289 h257 h273 h265 h269 (qA_succI inp 2 0 (20) (by decide)) ((qKW inp 2 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, core28_149 (qv inp) inp env h278 h286 h282 h290 h258 h274 h266 h270 (qA_succI inp 1 0 (20) (by decide)) ((qKW inp 1 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, core28_148 (qv inp) inp env h279 h287 h283 h291 h259 h275 h267 h271 (qA_succI inp 0 0 (20) (by decide)) ((qKW inp 0 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide]))⟩
      (And.intro ⟨rfl, h280⟩
      (And.intro ⟨rfl, h281⟩
      (And.intro ⟨rfl, h282⟩
      (And.intro ⟨rfl, h283⟩
      (And.intro ⟨rfl, h284⟩
      (And.intro ⟨rfl, h285⟩
      (And.intro ⟨rfl, h286⟩
      (And.intro ⟨rfl, h287⟩
      (And.intro ⟨rfl, h288⟩
      (And.intro ⟨rfl, h289⟩
      (And.intro ⟨rfl, h290⟩
      (And.intro ⟨rfl, h291⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
