import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D5
import Hashtree.Gen.WinAvxX4P.D4

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice5 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K5 K6 T5 = true := by
  decide +kernel

theorem core5_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 135) = V (.E 3 0 (2)))
    (h2 : env (.n 295) = V (.W 3 0 2))
    (h3 : env (.n 199) = V (.A 3 0 (2)))
    (h4 : env (.n 215) = V (.A 3 0 (1)))
    (h5 : V (.A 3 0 (3)) = (V (.E 3 0 (-1)) + Sigma1 (V (.E 3 0 (2))) + Ch (V (.E 3 0 (2))) (V (.E 3 0 (1))) (V (.E 3 0 (0))) + V (.KW 3 0 2)) + (Sigma0 (V (.A 3 0 (2))) + Maj (V (.A 3 0 (2))) (V (.A 3 0 (1))) (V (.A 3 0 (0)))))
    (h6 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h7 : V (.H 3 0 5) = 2600822924#32)
    (h8 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h9 : V (.H 3 0 4) = 1359893119#32)
    (h10 : V (.KW 3 0 2) = 3049323471#32 + V (.W 3 0 2))
    (h11 : V (.A 3 0 (0)) = V (.H 3 0 0))
    (h12 : V (.H 3 0 0) = 1779033703#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 151)) (.const 1359893119)) (.var (.n 135))) (.const 1359893119))) (.add (.var (.n 295)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 6) (.shl (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 26)) (.or (.shr (.var (.n 135)) 25) (.shl (.var (.n 135)) 7)))) (.or (.and (.var (.n 199)) (.const 1779033703)) (.and (.xor (.var (.n 199)) (.const 1779033703)) (.var (.n 215))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 199)) 11) (.shl (.var (.n 199)) 21)) (.var (.n 199))) 2) (.shl (.xor (.or (.shr (.var (.n 199)) 11) (.shl (.var (.n 199)) 21)) (.var (.n 199))) 30)) (.or (.shr (.var (.n 199)) 22) (.shl (.var (.n 199)) 10)))) = V (.A 3 0 (3)) :=
  shape5 (env (.n 151)) (env (.n 135)) (env (.n 295)) (env (.n 199)) (env (.n 215)) (V (.E 3 0 (1))) (V (.E 3 0 (2))) (V (.W 3 0 2)) (V (.A 3 0 (2))) (V (.A 3 0 (1))) (V (.A 3 0 (3))) (V (.E 3 0 (-1))) (V (.E 3 0 (0))) (V (.KW 3 0 2)) (V (.A 3 0 (0))) (V (.H 3 0 5)) (V (.H 3 0 4)) (V (.H 3 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core5_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 134) = V (.E 2 0 (2)))
    (h2 : env (.n 294) = V (.W 2 0 2))
    (h3 : env (.n 198) = V (.A 2 0 (2)))
    (h4 : env (.n 214) = V (.A 2 0 (1)))
    (h5 : V (.A 2 0 (3)) = (V (.E 2 0 (-1)) + Sigma1 (V (.E 2 0 (2))) + Ch (V (.E 2 0 (2))) (V (.E 2 0 (1))) (V (.E 2 0 (0))) + V (.KW 2 0 2)) + (Sigma0 (V (.A 2 0 (2))) + Maj (V (.A 2 0 (2))) (V (.A 2 0 (1))) (V (.A 2 0 (0)))))
    (h6 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h7 : V (.H 2 0 5) = 2600822924#32)
    (h8 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h9 : V (.H 2 0 4) = 1359893119#32)
    (h10 : V (.KW 2 0 2) = 3049323471#32 + V (.W 2 0 2))
    (h11 : V (.A 2 0 (0)) = V (.H 2 0 0))
    (h12 : V (.H 2 0 0) = 1779033703#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 150)) (.const 1359893119)) (.var (.n 134))) (.const 1359893119))) (.add (.var (.n 294)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 6) (.shl (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 26)) (.or (.shr (.var (.n 134)) 25) (.shl (.var (.n 134)) 7)))) (.or (.and (.var (.n 198)) (.const 1779033703)) (.and (.xor (.var (.n 198)) (.const 1779033703)) (.var (.n 214))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 198)) 11) (.shl (.var (.n 198)) 21)) (.var (.n 198))) 2) (.shl (.xor (.or (.shr (.var (.n 198)) 11) (.shl (.var (.n 198)) 21)) (.var (.n 198))) 30)) (.or (.shr (.var (.n 198)) 22) (.shl (.var (.n 198)) 10)))) = V (.A 2 0 (3)) :=
  shape5 (env (.n 150)) (env (.n 134)) (env (.n 294)) (env (.n 198)) (env (.n 214)) (V (.E 2 0 (1))) (V (.E 2 0 (2))) (V (.W 2 0 2)) (V (.A 2 0 (2))) (V (.A 2 0 (1))) (V (.A 2 0 (3))) (V (.E 2 0 (-1))) (V (.E 2 0 (0))) (V (.KW 2 0 2)) (V (.A 2 0 (0))) (V (.H 2 0 5)) (V (.H 2 0 4)) (V (.H 2 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core5_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 133) = V (.E 1 0 (2)))
    (h2 : env (.n 293) = V (.W 1 0 2))
    (h3 : env (.n 197) = V (.A 1 0 (2)))
    (h4 : env (.n 213) = V (.A 1 0 (1)))
    (h5 : V (.A 1 0 (3)) = (V (.E 1 0 (-1)) + Sigma1 (V (.E 1 0 (2))) + Ch (V (.E 1 0 (2))) (V (.E 1 0 (1))) (V (.E 1 0 (0))) + V (.KW 1 0 2)) + (Sigma0 (V (.A 1 0 (2))) + Maj (V (.A 1 0 (2))) (V (.A 1 0 (1))) (V (.A 1 0 (0)))))
    (h6 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h7 : V (.H 1 0 5) = 2600822924#32)
    (h8 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h9 : V (.H 1 0 4) = 1359893119#32)
    (h10 : V (.KW 1 0 2) = 3049323471#32 + V (.W 1 0 2))
    (h11 : V (.A 1 0 (0)) = V (.H 1 0 0))
    (h12 : V (.H 1 0 0) = 1779033703#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 149)) (.const 1359893119)) (.var (.n 133))) (.const 1359893119))) (.add (.var (.n 293)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 6) (.shl (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 26)) (.or (.shr (.var (.n 133)) 25) (.shl (.var (.n 133)) 7)))) (.or (.and (.var (.n 197)) (.const 1779033703)) (.and (.xor (.var (.n 197)) (.const 1779033703)) (.var (.n 213))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 197)) 11) (.shl (.var (.n 197)) 21)) (.var (.n 197))) 2) (.shl (.xor (.or (.shr (.var (.n 197)) 11) (.shl (.var (.n 197)) 21)) (.var (.n 197))) 30)) (.or (.shr (.var (.n 197)) 22) (.shl (.var (.n 197)) 10)))) = V (.A 1 0 (3)) :=
  shape5 (env (.n 149)) (env (.n 133)) (env (.n 293)) (env (.n 197)) (env (.n 213)) (V (.E 1 0 (1))) (V (.E 1 0 (2))) (V (.W 1 0 2)) (V (.A 1 0 (2))) (V (.A 1 0 (1))) (V (.A 1 0 (3))) (V (.E 1 0 (-1))) (V (.E 1 0 (0))) (V (.KW 1 0 2)) (V (.A 1 0 (0))) (V (.H 1 0 5)) (V (.H 1 0 4)) (V (.H 1 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core5_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 132) = V (.E 0 0 (2)))
    (h2 : env (.n 292) = V (.W 0 0 2))
    (h3 : env (.n 196) = V (.A 0 0 (2)))
    (h4 : env (.n 212) = V (.A 0 0 (1)))
    (h5 : V (.A 0 0 (3)) = (V (.E 0 0 (-1)) + Sigma1 (V (.E 0 0 (2))) + Ch (V (.E 0 0 (2))) (V (.E 0 0 (1))) (V (.E 0 0 (0))) + V (.KW 0 0 2)) + (Sigma0 (V (.A 0 0 (2))) + Maj (V (.A 0 0 (2))) (V (.A 0 0 (1))) (V (.A 0 0 (0)))))
    (h6 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h7 : V (.H 0 0 5) = 2600822924#32)
    (h8 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h9 : V (.H 0 0 4) = 1359893119#32)
    (h10 : V (.KW 0 0 2) = 3049323471#32 + V (.W 0 0 2))
    (h11 : V (.A 0 0 (0)) = V (.H 0 0 0))
    (h12 : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 148)) (.const 1359893119)) (.var (.n 132))) (.const 1359893119))) (.add (.var (.n 292)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 6) (.shl (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 26)) (.or (.shr (.var (.n 132)) 25) (.shl (.var (.n 132)) 7)))) (.or (.and (.var (.n 196)) (.const 1779033703)) (.and (.xor (.var (.n 196)) (.const 1779033703)) (.var (.n 212))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 196)) 11) (.shl (.var (.n 196)) 21)) (.var (.n 196))) 2) (.shl (.xor (.or (.shr (.var (.n 196)) 11) (.shl (.var (.n 196)) 21)) (.var (.n 196))) 30)) (.or (.shr (.var (.n 196)) 22) (.shl (.var (.n 196)) 10)))) = V (.A 0 0 (3)) :=
  shape5 (env (.n 148)) (env (.n 132)) (env (.n 292)) (env (.n 196)) (env (.n 212)) (V (.E 0 0 (1))) (V (.E 0 0 (2))) (V (.W 0 0 2)) (V (.A 0 0 (2))) (V (.A 0 0 (1))) (V (.A 0 0 (3))) (V (.E 0 0 (-1))) (V (.E 0 0 (0))) (V (.KW 0 0 2)) (V (.A 0 0 (0))) (V (.H 0 0 5)) (V (.H 0 0 4)) (V (.H 0 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core5_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 135) = V (.E 3 0 (2)))
    (h2 : env (.n 295) = V (.W 3 0 2))
    (h3 : V (.E 3 0 (3)) = V (.A 3 0 (-1)) + (V (.E 3 0 (-1)) + Sigma1 (V (.E 3 0 (2))) + Ch (V (.E 3 0 (2))) (V (.E 3 0 (1))) (V (.E 3 0 (0))) + V (.KW 3 0 2)))
    (h4 : V (.A 3 0 (-1)) = V (.H 3 0 1))
    (h5 : V (.H 3 0 1) = 3144134277#32)
    (h6 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h7 : V (.H 3 0 5) = 2600822924#32)
    (h8 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h9 : V (.H 3 0 4) = 1359893119#32)
    (h10 : V (.KW 3 0 2) = 3049323471#32 + V (.W 3 0 2)) :
    E.eval env (.add (.const 3144134277) (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 151)) (.const 1359893119)) (.var (.n 135))) (.const 1359893119))) (.add (.var (.n 295)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 6) (.shl (.xor (.or (.shr (.var (.n 135)) 5) (.shl (.var (.n 135)) 27)) (.var (.n 135))) 26)) (.or (.shr (.var (.n 135)) 25) (.shl (.var (.n 135)) 7))))) = V (.E 3 0 (3)) :=
  shape6 (env (.n 151)) (env (.n 135)) (env (.n 295)) (V (.E 3 0 (1))) (V (.E 3 0 (2))) (V (.W 3 0 2)) (V (.E 3 0 (3))) (V (.A 3 0 (-1))) (V (.E 3 0 (-1))) (V (.E 3 0 (0))) (V (.KW 3 0 2)) (V (.H 3 0 1)) (V (.H 3 0 5)) (V (.H 3 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core5_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 134) = V (.E 2 0 (2)))
    (h2 : env (.n 294) = V (.W 2 0 2))
    (h3 : V (.E 2 0 (3)) = V (.A 2 0 (-1)) + (V (.E 2 0 (-1)) + Sigma1 (V (.E 2 0 (2))) + Ch (V (.E 2 0 (2))) (V (.E 2 0 (1))) (V (.E 2 0 (0))) + V (.KW 2 0 2)))
    (h4 : V (.A 2 0 (-1)) = V (.H 2 0 1))
    (h5 : V (.H 2 0 1) = 3144134277#32)
    (h6 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h7 : V (.H 2 0 5) = 2600822924#32)
    (h8 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h9 : V (.H 2 0 4) = 1359893119#32)
    (h10 : V (.KW 2 0 2) = 3049323471#32 + V (.W 2 0 2)) :
    E.eval env (.add (.const 3144134277) (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 150)) (.const 1359893119)) (.var (.n 134))) (.const 1359893119))) (.add (.var (.n 294)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 6) (.shl (.xor (.or (.shr (.var (.n 134)) 5) (.shl (.var (.n 134)) 27)) (.var (.n 134))) 26)) (.or (.shr (.var (.n 134)) 25) (.shl (.var (.n 134)) 7))))) = V (.E 2 0 (3)) :=
  shape6 (env (.n 150)) (env (.n 134)) (env (.n 294)) (V (.E 2 0 (1))) (V (.E 2 0 (2))) (V (.W 2 0 2)) (V (.E 2 0 (3))) (V (.A 2 0 (-1))) (V (.E 2 0 (-1))) (V (.E 2 0 (0))) (V (.KW 2 0 2)) (V (.H 2 0 1)) (V (.H 2 0 5)) (V (.H 2 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core5_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 133) = V (.E 1 0 (2)))
    (h2 : env (.n 293) = V (.W 1 0 2))
    (h3 : V (.E 1 0 (3)) = V (.A 1 0 (-1)) + (V (.E 1 0 (-1)) + Sigma1 (V (.E 1 0 (2))) + Ch (V (.E 1 0 (2))) (V (.E 1 0 (1))) (V (.E 1 0 (0))) + V (.KW 1 0 2)))
    (h4 : V (.A 1 0 (-1)) = V (.H 1 0 1))
    (h5 : V (.H 1 0 1) = 3144134277#32)
    (h6 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h7 : V (.H 1 0 5) = 2600822924#32)
    (h8 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h9 : V (.H 1 0 4) = 1359893119#32)
    (h10 : V (.KW 1 0 2) = 3049323471#32 + V (.W 1 0 2)) :
    E.eval env (.add (.const 3144134277) (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 149)) (.const 1359893119)) (.var (.n 133))) (.const 1359893119))) (.add (.var (.n 293)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 6) (.shl (.xor (.or (.shr (.var (.n 133)) 5) (.shl (.var (.n 133)) 27)) (.var (.n 133))) 26)) (.or (.shr (.var (.n 133)) 25) (.shl (.var (.n 133)) 7))))) = V (.E 1 0 (3)) :=
  shape6 (env (.n 149)) (env (.n 133)) (env (.n 293)) (V (.E 1 0 (1))) (V (.E 1 0 (2))) (V (.W 1 0 2)) (V (.E 1 0 (3))) (V (.A 1 0 (-1))) (V (.E 1 0 (-1))) (V (.E 1 0 (0))) (V (.KW 1 0 2)) (V (.H 1 0 1)) (V (.H 1 0 5)) (V (.H 1 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core5_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 132) = V (.E 0 0 (2)))
    (h2 : env (.n 292) = V (.W 0 0 2))
    (h3 : V (.E 0 0 (3)) = V (.A 0 0 (-1)) + (V (.E 0 0 (-1)) + Sigma1 (V (.E 0 0 (2))) + Ch (V (.E 0 0 (2))) (V (.E 0 0 (1))) (V (.E 0 0 (0))) + V (.KW 0 0 2)))
    (h4 : V (.A 0 0 (-1)) = V (.H 0 0 1))
    (h5 : V (.H 0 0 1) = 3144134277#32)
    (h6 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h7 : V (.H 0 0 5) = 2600822924#32)
    (h8 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h9 : V (.H 0 0 4) = 1359893119#32)
    (h10 : V (.KW 0 0 2) = 3049323471#32 + V (.W 0 0 2)) :
    E.eval env (.add (.const 3144134277) (.add (.add (.add (.const 2600822924) (.xor (.and (.xor (.var (.n 148)) (.const 1359893119)) (.var (.n 132))) (.const 1359893119))) (.add (.var (.n 292)) (.const 3049323471))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 6) (.shl (.xor (.or (.shr (.var (.n 132)) 5) (.shl (.var (.n 132)) 27)) (.var (.n 132))) 26)) (.or (.shr (.var (.n 132)) 25) (.shl (.var (.n 132)) 7))))) = V (.E 0 0 (3)) :=
  shape6 (env (.n 148)) (env (.n 132)) (env (.n 292)) (V (.E 0 0 (1))) (V (.E 0 0 (2))) (V (.W 0 0 2)) (V (.E 0 0 (3))) (V (.A 0 0 (-1))) (V (.E 0 0 (-1))) (V (.E 0 0 (0))) (V (.KW 0 0 2)) (V (.H 0 0 1)) (V (.H 0 0 5)) (V (.H 0 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem step5 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L5) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K5)) L6 := by
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
  exact invC_of_trees inp env _ T5 L6 (slice_trees_mem prog 4 _ _ 38 K5 K6 T5 slice5 env)
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
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h32⟩
      (And.intro ⟨rfl, h32⟩
      (And.intro ⟨rfl, h32⟩
      (And.intro ⟨rfl, h32⟩
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
      (And.intro ⟨rfl, core5_183 (qv inp) inp env h48 h52 h32 h44 h40 (qA_succI inp 3 0 (2) (by decide)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 3 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide])) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32))⟩
      (And.intro ⟨rfl, core5_182 (qv inp) inp env h49 h53 h33 h45 h41 (qA_succI inp 2 0 (2) (by decide)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 2 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide])) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32))⟩
      (And.intro ⟨rfl, core5_181 (qv inp) inp env h50 h54 h34 h46 h42 (qA_succI inp 1 0 (2) (by decide)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 1 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide])) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32))⟩
      (And.intro ⟨rfl, core5_180 (qv inp) inp env h51 h55 h35 h47 h43 (qA_succI inp 0 0 (2) (by decide)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 0 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide])) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32))⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h52⟩
      (And.intro ⟨rfl, h53⟩
      (And.intro ⟨rfl, h54⟩
      (And.intro ⟨rfl, h55⟩
      (And.intro ⟨rfl, core5_119 (qv inp) inp env h48 h52 h32 (qE_succI inp 3 0 (2) (by decide)) (qA_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 1).trans (by decide : fld H0 1 = 3144134277#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 3 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide]))⟩
      (And.intro ⟨rfl, core5_118 (qv inp) inp env h49 h53 h33 (qE_succI inp 2 0 (2) (by decide)) (qA_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 1).trans (by decide : fld H0 1 = 3144134277#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 2 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide]))⟩
      (And.intro ⟨rfl, core5_117 (qv inp) inp env h50 h54 h34 (qE_succI inp 1 0 (2) (by decide)) (qA_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 1).trans (by decide : fld H0 1 = 3144134277#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 1 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide]))⟩
      (And.intro ⟨rfl, core5_116 (qv inp) inp env h51 h55 h35 (qE_succI inp 0 0 (2) (by decide)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 0 0 2).trans (by rw [show Spec.K 2 = 3049323471#32 from by decide]))⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
