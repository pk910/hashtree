import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D4
import Hashtree.Gen.WinAvxX4P.D3

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice4 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K4 K5 T4 = true := by
  decide +kernel

theorem core4_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 311) = V (.W 3 0 1))
    (h2 : env (.n 215) = V (.A 3 0 (1)))
    (h3 : V (.A 3 0 (2)) = (V (.E 3 0 (-2)) + Sigma1 (V (.E 3 0 (1))) + Ch (V (.E 3 0 (1))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) + V (.KW 3 0 1)) + (Sigma0 (V (.A 3 0 (1))) + Maj (V (.A 3 0 (1))) (V (.A 3 0 (0))) (V (.A 3 0 (-1)))))
    (h4 : V (.E 3 0 (-2)) = V (.H 3 0 6))
    (h5 : V (.H 3 0 6) = 528734635#32)
    (h6 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h7 : V (.H 3 0 4) = 1359893119#32)
    (h8 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h9 : V (.H 3 0 5) = 2600822924#32)
    (h10 : V (.KW 3 0 1) = 1899447441#32 + V (.W 3 0 1))
    (h11 : V (.A 3 0 (0)) = V (.H 3 0 0))
    (h12 : V (.H 3 0 0) = 1779033703#32)
    (h13 : V (.A 3 0 (-1)) = V (.H 3 0 1))
    (h14 : V (.H 3 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 151))) (.const 2600822924))) (.add (.var (.n 311)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 6) (.shl (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 26)) (.or (.shr (.var (.n 151)) 25) (.shl (.var (.n 151)) 7)))) (.or (.and (.var (.n 215)) (.const 3144134277)) (.and (.xor (.var (.n 215)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 215)) 11) (.shl (.var (.n 215)) 21)) (.var (.n 215))) 2) (.shl (.xor (.or (.shr (.var (.n 215)) 11) (.shl (.var (.n 215)) 21)) (.var (.n 215))) 30)) (.or (.shr (.var (.n 215)) 22) (.shl (.var (.n 215)) 10)))) = V (.A 3 0 (2)) :=
  shape3 (env (.n 151)) (env (.n 311)) (env (.n 215)) (V (.E 3 0 (1))) (V (.W 3 0 1)) (V (.A 3 0 (1))) (V (.A 3 0 (2))) (V (.E 3 0 (-2))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.KW 3 0 1)) (V (.A 3 0 (0))) (V (.A 3 0 (-1))) (V (.H 3 0 6)) (V (.H 3 0 4)) (V (.H 3 0 5)) (V (.H 3 0 0)) (V (.H 3 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core4_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 310) = V (.W 2 0 1))
    (h2 : env (.n 214) = V (.A 2 0 (1)))
    (h3 : V (.A 2 0 (2)) = (V (.E 2 0 (-2)) + Sigma1 (V (.E 2 0 (1))) + Ch (V (.E 2 0 (1))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) + V (.KW 2 0 1)) + (Sigma0 (V (.A 2 0 (1))) + Maj (V (.A 2 0 (1))) (V (.A 2 0 (0))) (V (.A 2 0 (-1)))))
    (h4 : V (.E 2 0 (-2)) = V (.H 2 0 6))
    (h5 : V (.H 2 0 6) = 528734635#32)
    (h6 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h7 : V (.H 2 0 4) = 1359893119#32)
    (h8 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h9 : V (.H 2 0 5) = 2600822924#32)
    (h10 : V (.KW 2 0 1) = 1899447441#32 + V (.W 2 0 1))
    (h11 : V (.A 2 0 (0)) = V (.H 2 0 0))
    (h12 : V (.H 2 0 0) = 1779033703#32)
    (h13 : V (.A 2 0 (-1)) = V (.H 2 0 1))
    (h14 : V (.H 2 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 150))) (.const 2600822924))) (.add (.var (.n 310)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 6) (.shl (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 26)) (.or (.shr (.var (.n 150)) 25) (.shl (.var (.n 150)) 7)))) (.or (.and (.var (.n 214)) (.const 3144134277)) (.and (.xor (.var (.n 214)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 214)) 11) (.shl (.var (.n 214)) 21)) (.var (.n 214))) 2) (.shl (.xor (.or (.shr (.var (.n 214)) 11) (.shl (.var (.n 214)) 21)) (.var (.n 214))) 30)) (.or (.shr (.var (.n 214)) 22) (.shl (.var (.n 214)) 10)))) = V (.A 2 0 (2)) :=
  shape3 (env (.n 150)) (env (.n 310)) (env (.n 214)) (V (.E 2 0 (1))) (V (.W 2 0 1)) (V (.A 2 0 (1))) (V (.A 2 0 (2))) (V (.E 2 0 (-2))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.KW 2 0 1)) (V (.A 2 0 (0))) (V (.A 2 0 (-1))) (V (.H 2 0 6)) (V (.H 2 0 4)) (V (.H 2 0 5)) (V (.H 2 0 0)) (V (.H 2 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core4_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 309) = V (.W 1 0 1))
    (h2 : env (.n 213) = V (.A 1 0 (1)))
    (h3 : V (.A 1 0 (2)) = (V (.E 1 0 (-2)) + Sigma1 (V (.E 1 0 (1))) + Ch (V (.E 1 0 (1))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) + V (.KW 1 0 1)) + (Sigma0 (V (.A 1 0 (1))) + Maj (V (.A 1 0 (1))) (V (.A 1 0 (0))) (V (.A 1 0 (-1)))))
    (h4 : V (.E 1 0 (-2)) = V (.H 1 0 6))
    (h5 : V (.H 1 0 6) = 528734635#32)
    (h6 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h7 : V (.H 1 0 4) = 1359893119#32)
    (h8 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h9 : V (.H 1 0 5) = 2600822924#32)
    (h10 : V (.KW 1 0 1) = 1899447441#32 + V (.W 1 0 1))
    (h11 : V (.A 1 0 (0)) = V (.H 1 0 0))
    (h12 : V (.H 1 0 0) = 1779033703#32)
    (h13 : V (.A 1 0 (-1)) = V (.H 1 0 1))
    (h14 : V (.H 1 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 149))) (.const 2600822924))) (.add (.var (.n 309)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 6) (.shl (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 26)) (.or (.shr (.var (.n 149)) 25) (.shl (.var (.n 149)) 7)))) (.or (.and (.var (.n 213)) (.const 3144134277)) (.and (.xor (.var (.n 213)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 213)) 11) (.shl (.var (.n 213)) 21)) (.var (.n 213))) 2) (.shl (.xor (.or (.shr (.var (.n 213)) 11) (.shl (.var (.n 213)) 21)) (.var (.n 213))) 30)) (.or (.shr (.var (.n 213)) 22) (.shl (.var (.n 213)) 10)))) = V (.A 1 0 (2)) :=
  shape3 (env (.n 149)) (env (.n 309)) (env (.n 213)) (V (.E 1 0 (1))) (V (.W 1 0 1)) (V (.A 1 0 (1))) (V (.A 1 0 (2))) (V (.E 1 0 (-2))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.KW 1 0 1)) (V (.A 1 0 (0))) (V (.A 1 0 (-1))) (V (.H 1 0 6)) (V (.H 1 0 4)) (V (.H 1 0 5)) (V (.H 1 0 0)) (V (.H 1 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core4_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 308) = V (.W 0 0 1))
    (h2 : env (.n 212) = V (.A 0 0 (1)))
    (h3 : V (.A 0 0 (2)) = (V (.E 0 0 (-2)) + Sigma1 (V (.E 0 0 (1))) + Ch (V (.E 0 0 (1))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) + V (.KW 0 0 1)) + (Sigma0 (V (.A 0 0 (1))) + Maj (V (.A 0 0 (1))) (V (.A 0 0 (0))) (V (.A 0 0 (-1)))))
    (h4 : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (h5 : V (.H 0 0 6) = 528734635#32)
    (h6 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h7 : V (.H 0 0 4) = 1359893119#32)
    (h8 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h9 : V (.H 0 0 5) = 2600822924#32)
    (h10 : V (.KW 0 0 1) = 1899447441#32 + V (.W 0 0 1))
    (h11 : V (.A 0 0 (0)) = V (.H 0 0 0))
    (h12 : V (.H 0 0 0) = 1779033703#32)
    (h13 : V (.A 0 0 (-1)) = V (.H 0 0 1))
    (h14 : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 148))) (.const 2600822924))) (.add (.var (.n 308)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 6) (.shl (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 26)) (.or (.shr (.var (.n 148)) 25) (.shl (.var (.n 148)) 7)))) (.or (.and (.var (.n 212)) (.const 3144134277)) (.and (.xor (.var (.n 212)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 212)) 11) (.shl (.var (.n 212)) 21)) (.var (.n 212))) 2) (.shl (.xor (.or (.shr (.var (.n 212)) 11) (.shl (.var (.n 212)) 21)) (.var (.n 212))) 30)) (.or (.shr (.var (.n 212)) 22) (.shl (.var (.n 212)) 10)))) = V (.A 0 0 (2)) :=
  shape3 (env (.n 148)) (env (.n 308)) (env (.n 212)) (V (.E 0 0 (1))) (V (.W 0 0 1)) (V (.A 0 0 (1))) (V (.A 0 0 (2))) (V (.E 0 0 (-2))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.KW 0 0 1)) (V (.A 0 0 (0))) (V (.A 0 0 (-1))) (V (.H 0 0 6)) (V (.H 0 0 4)) (V (.H 0 0 5)) (V (.H 0 0 0)) (V (.H 0 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core4_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 311) = V (.W 3 0 1))
    (h2 : V (.E 3 0 (2)) = V (.A 3 0 (-2)) + (V (.E 3 0 (-2)) + Sigma1 (V (.E 3 0 (1))) + Ch (V (.E 3 0 (1))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) + V (.KW 3 0 1)))
    (h3 : V (.A 3 0 (-2)) = V (.H 3 0 2))
    (h4 : V (.H 3 0 2) = 1013904242#32)
    (h5 : V (.E 3 0 (-2)) = V (.H 3 0 6))
    (h6 : V (.H 3 0 6) = 528734635#32)
    (h7 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h8 : V (.H 3 0 4) = 1359893119#32)
    (h9 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h10 : V (.H 3 0 5) = 2600822924#32)
    (h11 : V (.KW 3 0 1) = 1899447441#32 + V (.W 3 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 151))) (.const 2600822924))) (.add (.var (.n 311)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 6) (.shl (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 26)) (.or (.shr (.var (.n 151)) 25) (.shl (.var (.n 151)) 7))))) = V (.E 3 0 (2)) :=
  shape4 (env (.n 151)) (env (.n 311)) (V (.E 3 0 (1))) (V (.W 3 0 1)) (V (.E 3 0 (2))) (V (.A 3 0 (-2))) (V (.E 3 0 (-2))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.KW 3 0 1)) (V (.H 3 0 2)) (V (.H 3 0 6)) (V (.H 3 0 4)) (V (.H 3 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core4_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 310) = V (.W 2 0 1))
    (h2 : V (.E 2 0 (2)) = V (.A 2 0 (-2)) + (V (.E 2 0 (-2)) + Sigma1 (V (.E 2 0 (1))) + Ch (V (.E 2 0 (1))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) + V (.KW 2 0 1)))
    (h3 : V (.A 2 0 (-2)) = V (.H 2 0 2))
    (h4 : V (.H 2 0 2) = 1013904242#32)
    (h5 : V (.E 2 0 (-2)) = V (.H 2 0 6))
    (h6 : V (.H 2 0 6) = 528734635#32)
    (h7 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h8 : V (.H 2 0 4) = 1359893119#32)
    (h9 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h10 : V (.H 2 0 5) = 2600822924#32)
    (h11 : V (.KW 2 0 1) = 1899447441#32 + V (.W 2 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 150))) (.const 2600822924))) (.add (.var (.n 310)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 6) (.shl (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 26)) (.or (.shr (.var (.n 150)) 25) (.shl (.var (.n 150)) 7))))) = V (.E 2 0 (2)) :=
  shape4 (env (.n 150)) (env (.n 310)) (V (.E 2 0 (1))) (V (.W 2 0 1)) (V (.E 2 0 (2))) (V (.A 2 0 (-2))) (V (.E 2 0 (-2))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.KW 2 0 1)) (V (.H 2 0 2)) (V (.H 2 0 6)) (V (.H 2 0 4)) (V (.H 2 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core4_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 309) = V (.W 1 0 1))
    (h2 : V (.E 1 0 (2)) = V (.A 1 0 (-2)) + (V (.E 1 0 (-2)) + Sigma1 (V (.E 1 0 (1))) + Ch (V (.E 1 0 (1))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) + V (.KW 1 0 1)))
    (h3 : V (.A 1 0 (-2)) = V (.H 1 0 2))
    (h4 : V (.H 1 0 2) = 1013904242#32)
    (h5 : V (.E 1 0 (-2)) = V (.H 1 0 6))
    (h6 : V (.H 1 0 6) = 528734635#32)
    (h7 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h8 : V (.H 1 0 4) = 1359893119#32)
    (h9 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h10 : V (.H 1 0 5) = 2600822924#32)
    (h11 : V (.KW 1 0 1) = 1899447441#32 + V (.W 1 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 149))) (.const 2600822924))) (.add (.var (.n 309)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 6) (.shl (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 26)) (.or (.shr (.var (.n 149)) 25) (.shl (.var (.n 149)) 7))))) = V (.E 1 0 (2)) :=
  shape4 (env (.n 149)) (env (.n 309)) (V (.E 1 0 (1))) (V (.W 1 0 1)) (V (.E 1 0 (2))) (V (.A 1 0 (-2))) (V (.E 1 0 (-2))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.KW 1 0 1)) (V (.H 1 0 2)) (V (.H 1 0 6)) (V (.H 1 0 4)) (V (.H 1 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core4_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 308) = V (.W 0 0 1))
    (h2 : V (.E 0 0 (2)) = V (.A 0 0 (-2)) + (V (.E 0 0 (-2)) + Sigma1 (V (.E 0 0 (1))) + Ch (V (.E 0 0 (1))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) + V (.KW 0 0 1)))
    (h3 : V (.A 0 0 (-2)) = V (.H 0 0 2))
    (h4 : V (.H 0 0 2) = 1013904242#32)
    (h5 : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (h6 : V (.H 0 0 6) = 528734635#32)
    (h7 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h8 : V (.H 0 0 4) = 1359893119#32)
    (h9 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h10 : V (.H 0 0 5) = 2600822924#32)
    (h11 : V (.KW 0 0 1) = 1899447441#32 + V (.W 0 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 148))) (.const 2600822924))) (.add (.var (.n 308)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 6) (.shl (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 26)) (.or (.shr (.var (.n 148)) 25) (.shl (.var (.n 148)) 7))))) = V (.E 0 0 (2)) :=
  shape4 (env (.n 148)) (env (.n 308)) (V (.E 0 0 (1))) (V (.W 0 0 1)) (V (.E 0 0 (2))) (V (.A 0 0 (-2))) (V (.E 0 0 (-2))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.KW 0 0 1)) (V (.H 0 0 2)) (V (.H 0 0 6)) (V (.H 0 0 4)) (V (.H 0 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem step4 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L4) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K4)) L5 := by
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
  exact invC_of_trees inp env _ T4 L5 (slice_trees_mem prog 4 _ _ 38 K4 K5 T4 slice4 env)
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
      (And.intro ⟨rfl, h19⟩
      (And.intro ⟨rfl, h19⟩
      (And.intro ⟨rfl, h19⟩
      (And.intro ⟨rfl, h19⟩
      (And.intro ⟨rfl, h18⟩
      (And.intro ⟨rfl, h18⟩
      (And.intro ⟨rfl, h18⟩
      (And.intro ⟨rfl, h18⟩
      (And.intro ⟨rfl, h17⟩
      (And.intro ⟨rfl, h17⟩
      (And.intro ⟨rfl, h17⟩
      (And.intro ⟨rfl, h17⟩
      (And.intro ⟨rfl, h16⟩
      (And.intro ⟨rfl, h16⟩
      (And.intro ⟨rfl, h16⟩
      (And.intro ⟨rfl, h16⟩
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
      (And.intro ⟨rfl, core4_199 (qv inp) inp env h32 h16 h28 (qA_succI inp 3 0 (1) (by decide)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 3 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core4_198 (qv inp) inp env h33 h17 h29 (qA_succI inp 2 0 (1) (by decide)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 2 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core4_197 (qv inp) inp env h34 h18 h30 (qA_succI inp 1 0 (1) (by decide)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 1 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core4_196 (qv inp) inp env h35 h19 h31 (qA_succI inp 0 0 (1) (by decide)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 0 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, h32⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, core4_135 (qv inp) inp env h32 h16 (qE_succI inp 3 0 (1) (by decide)) (qA_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 3 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core4_134 (qv inp) inp env h33 h17 (qE_succI inp 2 0 (1) (by decide)) (qA_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 2 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core4_133 (qv inp) inp env h34 h18 (qE_succI inp 1 0 (1) (by decide)) (qA_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 1 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core4_132 (qv inp) inp env h35 h19 (qE_succI inp 0 0 (1) (by decide)) (qA_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 0 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
