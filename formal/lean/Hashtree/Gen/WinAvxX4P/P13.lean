import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D13
import Hashtree.Gen.WinAvxX4P.D12

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice13 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K13 K14 T13 = true := by
  decide +kernel

theorem core13_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 183) = V (.E 3 0 (7)))
    (h1 : env (.n 151) = V (.E 3 0 (9)))
    (h2 : env (.n 167) = V (.E 3 0 (8)))
    (h3 : env (.n 135) = V (.E 3 0 (10)))
    (h4 : env (.n 295) = V (.W 3 0 10))
    (h5 : env (.n 199) = V (.A 3 0 (10)))
    (h6 : env (.n 103) = V (.A 3 0 (8)))
    (h7 : env (.n 215) = V (.A 3 0 (9)))
    (h8 : V (.A 3 0 (11)) = (V (.E 3 0 (7)) + Sigma1 (V (.E 3 0 (10))) + Ch (V (.E 3 0 (10))) (V (.E 3 0 (9))) (V (.E 3 0 (8))) + V (.KW 3 0 10)) + (Sigma0 (V (.A 3 0 (10))) + Maj (V (.A 3 0 (10))) (V (.A 3 0 (9))) (V (.A 3 0 (8)))))
    (h9 : V (.KW 3 0 10) = 607225278#32 + V (.W 3 0 10)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 183)) (.xor (.and (.xor (.var (.n 151)) (.var (.n 167))) (.var (.n 135))) (.var (.n 167)))) (.add (.var (.n 295)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 6) (.shl (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 26)) (.or (.shr (.var (.n 135)) 25) (.shl (.var (.n 135)) 7)))) (.or (.and (.var (.n 199)) (.var (.n 103))) (.and (.xor (.var (.n 199)) (.var (.n 103))) (.var (.n 215))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 199)) 11) (.shl (.var (.n 199)) 21)) (.var (.n 199))) 2) (.shl (.xor (.or (.shr (.var (.n 199)) 11) (.shl (.var (.n 199)) 21)) (.var (.n 199))) 30)) (.or (.shr (.var (.n 199)) 22) (.shl (.var (.n 199)) 10)))) = V (.A 3 0 (11)) :=
  shape21 (env (.n 183)) (env (.n 151)) (env (.n 167)) (env (.n 135)) (env (.n 295)) (env (.n 199)) (env (.n 103)) (env (.n 215)) (V (.E 3 0 (7))) (V (.E 3 0 (9))) (V (.E 3 0 (8))) (V (.E 3 0 (10))) (V (.W 3 0 10)) (V (.A 3 0 (10))) (V (.A 3 0 (8))) (V (.A 3 0 (9))) (V (.A 3 0 (11))) (V (.KW 3 0 10)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core13_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 182) = V (.E 2 0 (7)))
    (h1 : env (.n 150) = V (.E 2 0 (9)))
    (h2 : env (.n 166) = V (.E 2 0 (8)))
    (h3 : env (.n 134) = V (.E 2 0 (10)))
    (h4 : env (.n 294) = V (.W 2 0 10))
    (h5 : env (.n 198) = V (.A 2 0 (10)))
    (h6 : env (.n 102) = V (.A 2 0 (8)))
    (h7 : env (.n 214) = V (.A 2 0 (9)))
    (h8 : V (.A 2 0 (11)) = (V (.E 2 0 (7)) + Sigma1 (V (.E 2 0 (10))) + Ch (V (.E 2 0 (10))) (V (.E 2 0 (9))) (V (.E 2 0 (8))) + V (.KW 2 0 10)) + (Sigma0 (V (.A 2 0 (10))) + Maj (V (.A 2 0 (10))) (V (.A 2 0 (9))) (V (.A 2 0 (8)))))
    (h9 : V (.KW 2 0 10) = 607225278#32 + V (.W 2 0 10)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 182)) (.xor (.and (.xor (.var (.n 150)) (.var (.n 166))) (.var (.n 134))) (.var (.n 166)))) (.add (.var (.n 294)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 6) (.shl (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 26)) (.or (.shr (.var (.n 134)) 25) (.shl (.var (.n 134)) 7)))) (.or (.and (.var (.n 198)) (.var (.n 102))) (.and (.xor (.var (.n 198)) (.var (.n 102))) (.var (.n 214))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 198)) 11) (.shl (.var (.n 198)) 21)) (.var (.n 198))) 2) (.shl (.xor (.or (.shr (.var (.n 198)) 11) (.shl (.var (.n 198)) 21)) (.var (.n 198))) 30)) (.or (.shr (.var (.n 198)) 22) (.shl (.var (.n 198)) 10)))) = V (.A 2 0 (11)) :=
  shape21 (env (.n 182)) (env (.n 150)) (env (.n 166)) (env (.n 134)) (env (.n 294)) (env (.n 198)) (env (.n 102)) (env (.n 214)) (V (.E 2 0 (7))) (V (.E 2 0 (9))) (V (.E 2 0 (8))) (V (.E 2 0 (10))) (V (.W 2 0 10)) (V (.A 2 0 (10))) (V (.A 2 0 (8))) (V (.A 2 0 (9))) (V (.A 2 0 (11))) (V (.KW 2 0 10)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core13_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 181) = V (.E 1 0 (7)))
    (h1 : env (.n 149) = V (.E 1 0 (9)))
    (h2 : env (.n 165) = V (.E 1 0 (8)))
    (h3 : env (.n 133) = V (.E 1 0 (10)))
    (h4 : env (.n 293) = V (.W 1 0 10))
    (h5 : env (.n 197) = V (.A 1 0 (10)))
    (h6 : env (.n 101) = V (.A 1 0 (8)))
    (h7 : env (.n 213) = V (.A 1 0 (9)))
    (h8 : V (.A 1 0 (11)) = (V (.E 1 0 (7)) + Sigma1 (V (.E 1 0 (10))) + Ch (V (.E 1 0 (10))) (V (.E 1 0 (9))) (V (.E 1 0 (8))) + V (.KW 1 0 10)) + (Sigma0 (V (.A 1 0 (10))) + Maj (V (.A 1 0 (10))) (V (.A 1 0 (9))) (V (.A 1 0 (8)))))
    (h9 : V (.KW 1 0 10) = 607225278#32 + V (.W 1 0 10)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 181)) (.xor (.and (.xor (.var (.n 149)) (.var (.n 165))) (.var (.n 133))) (.var (.n 165)))) (.add (.var (.n 293)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 6) (.shl (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 26)) (.or (.shr (.var (.n 133)) 25) (.shl (.var (.n 133)) 7)))) (.or (.and (.var (.n 197)) (.var (.n 101))) (.and (.xor (.var (.n 197)) (.var (.n 101))) (.var (.n 213))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 197)) 11) (.shl (.var (.n 197)) 21)) (.var (.n 197))) 2) (.shl (.xor (.or (.shr (.var (.n 197)) 11) (.shl (.var (.n 197)) 21)) (.var (.n 197))) 30)) (.or (.shr (.var (.n 197)) 22) (.shl (.var (.n 197)) 10)))) = V (.A 1 0 (11)) :=
  shape21 (env (.n 181)) (env (.n 149)) (env (.n 165)) (env (.n 133)) (env (.n 293)) (env (.n 197)) (env (.n 101)) (env (.n 213)) (V (.E 1 0 (7))) (V (.E 1 0 (9))) (V (.E 1 0 (8))) (V (.E 1 0 (10))) (V (.W 1 0 10)) (V (.A 1 0 (10))) (V (.A 1 0 (8))) (V (.A 1 0 (9))) (V (.A 1 0 (11))) (V (.KW 1 0 10)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core13_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 180) = V (.E 0 0 (7)))
    (h1 : env (.n 148) = V (.E 0 0 (9)))
    (h2 : env (.n 164) = V (.E 0 0 (8)))
    (h3 : env (.n 132) = V (.E 0 0 (10)))
    (h4 : env (.n 292) = V (.W 0 0 10))
    (h5 : env (.n 196) = V (.A 0 0 (10)))
    (h6 : env (.n 100) = V (.A 0 0 (8)))
    (h7 : env (.n 212) = V (.A 0 0 (9)))
    (h8 : V (.A 0 0 (11)) = (V (.E 0 0 (7)) + Sigma1 (V (.E 0 0 (10))) + Ch (V (.E 0 0 (10))) (V (.E 0 0 (9))) (V (.E 0 0 (8))) + V (.KW 0 0 10)) + (Sigma0 (V (.A 0 0 (10))) + Maj (V (.A 0 0 (10))) (V (.A 0 0 (9))) (V (.A 0 0 (8)))))
    (h9 : V (.KW 0 0 10) = 607225278#32 + V (.W 0 0 10)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 180)) (.xor (.and (.xor (.var (.n 148)) (.var (.n 164))) (.var (.n 132))) (.var (.n 164)))) (.add (.var (.n 292)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 6) (.shl (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 26)) (.or (.shr (.var (.n 132)) 25) (.shl (.var (.n 132)) 7)))) (.or (.and (.var (.n 196)) (.var (.n 100))) (.and (.xor (.var (.n 196)) (.var (.n 100))) (.var (.n 212))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 196)) 11) (.shl (.var (.n 196)) 21)) (.var (.n 196))) 2) (.shl (.xor (.or (.shr (.var (.n 196)) 11) (.shl (.var (.n 196)) 21)) (.var (.n 196))) 30)) (.or (.shr (.var (.n 196)) 22) (.shl (.var (.n 196)) 10)))) = V (.A 0 0 (11)) :=
  shape21 (env (.n 180)) (env (.n 148)) (env (.n 164)) (env (.n 132)) (env (.n 292)) (env (.n 196)) (env (.n 100)) (env (.n 212)) (V (.E 0 0 (7))) (V (.E 0 0 (9))) (V (.E 0 0 (8))) (V (.E 0 0 (10))) (V (.W 0 0 10)) (V (.A 0 0 (10))) (V (.A 0 0 (8))) (V (.A 0 0 (9))) (V (.A 0 0 (11))) (V (.KW 0 0 10)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core13_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 119) = V (.A 3 0 (7)))
    (h1 : env (.n 183) = V (.E 3 0 (7)))
    (h2 : env (.n 151) = V (.E 3 0 (9)))
    (h3 : env (.n 167) = V (.E 3 0 (8)))
    (h4 : env (.n 135) = V (.E 3 0 (10)))
    (h5 : env (.n 295) = V (.W 3 0 10))
    (h6 : V (.E 3 0 (11)) = V (.A 3 0 (7)) + (V (.E 3 0 (7)) + Sigma1 (V (.E 3 0 (10))) + Ch (V (.E 3 0 (10))) (V (.E 3 0 (9))) (V (.E 3 0 (8))) + V (.KW 3 0 10)))
    (h7 : V (.KW 3 0 10) = 607225278#32 + V (.W 3 0 10)) :
    E.eval env (.add (.var (.n 119)) (.add (.add (.add (.var (.n 183)) (.xor (.and (.xor (.var (.n 151)) (.var (.n 167))) (.var (.n 135))) (.var (.n 167)))) (.add (.var (.n 295)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 6) (.shl (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 26)) (.or (.shr (.var (.n 135)) 25) (.shl (.var (.n 135)) 7))))) = V (.E 3 0 (11)) :=
  shape22 (env (.n 119)) (env (.n 183)) (env (.n 151)) (env (.n 167)) (env (.n 135)) (env (.n 295)) (V (.A 3 0 (7))) (V (.E 3 0 (7))) (V (.E 3 0 (9))) (V (.E 3 0 (8))) (V (.E 3 0 (10))) (V (.W 3 0 10)) (V (.E 3 0 (11))) (V (.KW 3 0 10)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core13_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 118) = V (.A 2 0 (7)))
    (h1 : env (.n 182) = V (.E 2 0 (7)))
    (h2 : env (.n 150) = V (.E 2 0 (9)))
    (h3 : env (.n 166) = V (.E 2 0 (8)))
    (h4 : env (.n 134) = V (.E 2 0 (10)))
    (h5 : env (.n 294) = V (.W 2 0 10))
    (h6 : V (.E 2 0 (11)) = V (.A 2 0 (7)) + (V (.E 2 0 (7)) + Sigma1 (V (.E 2 0 (10))) + Ch (V (.E 2 0 (10))) (V (.E 2 0 (9))) (V (.E 2 0 (8))) + V (.KW 2 0 10)))
    (h7 : V (.KW 2 0 10) = 607225278#32 + V (.W 2 0 10)) :
    E.eval env (.add (.var (.n 118)) (.add (.add (.add (.var (.n 182)) (.xor (.and (.xor (.var (.n 150)) (.var (.n 166))) (.var (.n 134))) (.var (.n 166)))) (.add (.var (.n 294)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 6) (.shl (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 26)) (.or (.shr (.var (.n 134)) 25) (.shl (.var (.n 134)) 7))))) = V (.E 2 0 (11)) :=
  shape22 (env (.n 118)) (env (.n 182)) (env (.n 150)) (env (.n 166)) (env (.n 134)) (env (.n 294)) (V (.A 2 0 (7))) (V (.E 2 0 (7))) (V (.E 2 0 (9))) (V (.E 2 0 (8))) (V (.E 2 0 (10))) (V (.W 2 0 10)) (V (.E 2 0 (11))) (V (.KW 2 0 10)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core13_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 117) = V (.A 1 0 (7)))
    (h1 : env (.n 181) = V (.E 1 0 (7)))
    (h2 : env (.n 149) = V (.E 1 0 (9)))
    (h3 : env (.n 165) = V (.E 1 0 (8)))
    (h4 : env (.n 133) = V (.E 1 0 (10)))
    (h5 : env (.n 293) = V (.W 1 0 10))
    (h6 : V (.E 1 0 (11)) = V (.A 1 0 (7)) + (V (.E 1 0 (7)) + Sigma1 (V (.E 1 0 (10))) + Ch (V (.E 1 0 (10))) (V (.E 1 0 (9))) (V (.E 1 0 (8))) + V (.KW 1 0 10)))
    (h7 : V (.KW 1 0 10) = 607225278#32 + V (.W 1 0 10)) :
    E.eval env (.add (.var (.n 117)) (.add (.add (.add (.var (.n 181)) (.xor (.and (.xor (.var (.n 149)) (.var (.n 165))) (.var (.n 133))) (.var (.n 165)))) (.add (.var (.n 293)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 6) (.shl (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 26)) (.or (.shr (.var (.n 133)) 25) (.shl (.var (.n 133)) 7))))) = V (.E 1 0 (11)) :=
  shape22 (env (.n 117)) (env (.n 181)) (env (.n 149)) (env (.n 165)) (env (.n 133)) (env (.n 293)) (V (.A 1 0 (7))) (V (.E 1 0 (7))) (V (.E 1 0 (9))) (V (.E 1 0 (8))) (V (.E 1 0 (10))) (V (.W 1 0 10)) (V (.E 1 0 (11))) (V (.KW 1 0 10)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core13_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 116) = V (.A 0 0 (7)))
    (h1 : env (.n 180) = V (.E 0 0 (7)))
    (h2 : env (.n 148) = V (.E 0 0 (9)))
    (h3 : env (.n 164) = V (.E 0 0 (8)))
    (h4 : env (.n 132) = V (.E 0 0 (10)))
    (h5 : env (.n 292) = V (.W 0 0 10))
    (h6 : V (.E 0 0 (11)) = V (.A 0 0 (7)) + (V (.E 0 0 (7)) + Sigma1 (V (.E 0 0 (10))) + Ch (V (.E 0 0 (10))) (V (.E 0 0 (9))) (V (.E 0 0 (8))) + V (.KW 0 0 10)))
    (h7 : V (.KW 0 0 10) = 607225278#32 + V (.W 0 0 10)) :
    E.eval env (.add (.var (.n 116)) (.add (.add (.add (.var (.n 180)) (.xor (.and (.xor (.var (.n 148)) (.var (.n 164))) (.var (.n 132))) (.var (.n 164)))) (.add (.var (.n 292)) (.const 607225278))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 6) (.shl (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 26)) (.or (.shr (.var (.n 132)) 25) (.shl (.var (.n 132)) 7))))) = V (.E 0 0 (11)) :=
  shape22 (env (.n 116)) (env (.n 180)) (env (.n 148)) (env (.n 164)) (env (.n 132)) (env (.n 292)) (V (.A 0 0 (7))) (V (.E 0 0 (7))) (V (.E 0 0 (9))) (V (.E 0 0 (8))) (V (.E 0 0 (10))) (V (.W 0 0 10)) (V (.E 0 0 (11))) (V (.KW 0 0 10)) h0 h1 h2 h3 h4 h5 h6 h7

theorem step13 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L13) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K13)) L14 := by
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
  exact invC_of_trees inp env _ T13 L14 (slice_trees_mem prog 4 _ _ 38 K13 K14 T13 slice13 env)
      (And.intro ⟨rfl, h0⟩
      (And.intro ⟨rfl, h1⟩
      (And.intro ⟨rfl, h2⟩
      (And.intro ⟨rfl, h3⟩
      (And.intro ⟨rfl, h4⟩
      (And.intro ⟨rfl, h5⟩
      (And.intro ⟨rfl, h6⟩
      (And.intro ⟨rfl, h7⟩
      (And.intro ⟨rfl, h8⟩
      (And.intro ⟨rfl, h9⟩
      (And.intro ⟨rfl, h10⟩
      (And.intro ⟨rfl, h11⟩
      (And.intro ⟨rfl, h12⟩
      (And.intro ⟨rfl, h13⟩
      (And.intro ⟨rfl, h14⟩
      (And.intro ⟨rfl, h15⟩
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
      (And.intro ⟨rfl, h163⟩
      (And.intro ⟨rfl, h163⟩
      (And.intro ⟨rfl, h163⟩
      (And.intro ⟨rfl, h163⟩
      (And.intro ⟨rfl, h162⟩
      (And.intro ⟨rfl, h162⟩
      (And.intro ⟨rfl, h162⟩
      (And.intro ⟨rfl, h162⟩
      (And.intro ⟨rfl, h161⟩
      (And.intro ⟨rfl, h161⟩
      (And.intro ⟨rfl, h161⟩
      (And.intro ⟨rfl, h161⟩
      (And.intro ⟨rfl, h160⟩
      (And.intro ⟨rfl, h160⟩
      (And.intro ⟨rfl, h160⟩
      (And.intro ⟨rfl, h160⟩
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
      (And.intro ⟨rfl, core13_183 (qv inp) inp env h176 h184 h180 h188 h160 h172 h196 h168 (qA_succI inp 3 0 (10) (by decide)) ((qKW inp 3 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, core13_182 (qv inp) inp env h177 h185 h181 h189 h161 h173 h197 h169 (qA_succI inp 2 0 (10) (by decide)) ((qKW inp 2 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, core13_181 (qv inp) inp env h178 h186 h182 h190 h162 h174 h198 h170 (qA_succI inp 1 0 (10) (by decide)) ((qKW inp 1 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, core13_180 (qv inp) inp env h179 h187 h183 h191 h163 h175 h199 h171 (qA_succI inp 0 0 (10) (by decide)) ((qKW inp 0 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
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
      (And.intro ⟨rfl, core13_119 (qv inp) inp env h192 h176 h184 h180 h188 h160 (qE_succI inp 3 0 (10) (by decide)) ((qKW inp 3 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, core13_118 (qv inp) inp env h193 h177 h185 h181 h189 h161 (qE_succI inp 2 0 (10) (by decide)) ((qKW inp 2 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, core13_117 (qv inp) inp env h194 h178 h186 h182 h190 h162 (qE_succI inp 1 0 (10) (by decide)) ((qKW inp 1 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, core13_116 (qv inp) inp env h195 h179 h187 h183 h191 h163 (qE_succI inp 0 0 (10) (by decide)) ((qKW inp 0 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide]))⟩
      (And.intro ⟨rfl, h196⟩
      (And.intro ⟨rfl, h197⟩
      (And.intro ⟨rfl, h198⟩
      (And.intro ⟨rfl, h199⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
