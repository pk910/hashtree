import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D6
import Hashtree.Gen.WinAvxX4P.D5

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice6 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K6 K7 T6 = true := by
  decide +kernel

theorem core6_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 135) = V (.E 3 0 (2)))
    (h1 : env (.n 151) = V (.E 3 0 (1)))
    (h2 : env (.n 119) = V (.E 3 0 (3)))
    (h3 : env (.n 279) = V (.W 3 0 3))
    (h4 : env (.n 183) = V (.A 3 0 (3)))
    (h5 : env (.n 215) = V (.A 3 0 (1)))
    (h6 : env (.n 199) = V (.A 3 0 (2)))
    (h7 : V (.A 3 0 (4)) = (V (.E 3 0 (0)) + Sigma1 (V (.E 3 0 (3))) + Ch (V (.E 3 0 (3))) (V (.E 3 0 (2))) (V (.E 3 0 (1))) + V (.KW 3 0 3)) + (Sigma0 (V (.A 3 0 (3))) + Maj (V (.A 3 0 (3))) (V (.A 3 0 (2))) (V (.A 3 0 (1)))))
    (h8 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h9 : V (.H 3 0 4) = 1359893119#32)
    (h10 : V (.KW 3 0 3) = 3921009573#32 + V (.W 3 0 3)) :
    E.eval env (.add (.add (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 135)) (.var (.n 151))) (.var (.n 119))) (.var (.n 151)))) (.add (.var (.n 279)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 6) (.shl (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 26)) (.or (.shr (.var (.n 119)) 25) (.shl (.var (.n 119)) 7)))) (.or (.and (.var (.n 183)) (.var (.n 215))) (.and (.xor (.var (.n 183)) (.var (.n 215))) (.var (.n 199))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 183)) 11) (.shl (.var (.n 183)) 21)) (.var (.n 183))) 2) (.shl (.xor (.or (.shr (.var (.n 183)) 11) (.shl (.var (.n 183)) 21)) (.var (.n 183))) 30)) (.or (.shr (.var (.n 183)) 22) (.shl (.var (.n 183)) 10)))) = V (.A 3 0 (4)) :=
  shape7 (env (.n 135)) (env (.n 151)) (env (.n 119)) (env (.n 279)) (env (.n 183)) (env (.n 215)) (env (.n 199)) (V (.E 3 0 (2))) (V (.E 3 0 (1))) (V (.E 3 0 (3))) (V (.W 3 0 3)) (V (.A 3 0 (3))) (V (.A 3 0 (1))) (V (.A 3 0 (2))) (V (.A 3 0 (4))) (V (.E 3 0 (0))) (V (.KW 3 0 3)) (V (.H 3 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core6_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 134) = V (.E 2 0 (2)))
    (h1 : env (.n 150) = V (.E 2 0 (1)))
    (h2 : env (.n 118) = V (.E 2 0 (3)))
    (h3 : env (.n 278) = V (.W 2 0 3))
    (h4 : env (.n 182) = V (.A 2 0 (3)))
    (h5 : env (.n 214) = V (.A 2 0 (1)))
    (h6 : env (.n 198) = V (.A 2 0 (2)))
    (h7 : V (.A 2 0 (4)) = (V (.E 2 0 (0)) + Sigma1 (V (.E 2 0 (3))) + Ch (V (.E 2 0 (3))) (V (.E 2 0 (2))) (V (.E 2 0 (1))) + V (.KW 2 0 3)) + (Sigma0 (V (.A 2 0 (3))) + Maj (V (.A 2 0 (3))) (V (.A 2 0 (2))) (V (.A 2 0 (1)))))
    (h8 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h9 : V (.H 2 0 4) = 1359893119#32)
    (h10 : V (.KW 2 0 3) = 3921009573#32 + V (.W 2 0 3)) :
    E.eval env (.add (.add (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 134)) (.var (.n 150))) (.var (.n 118))) (.var (.n 150)))) (.add (.var (.n 278)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 6) (.shl (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 26)) (.or (.shr (.var (.n 118)) 25) (.shl (.var (.n 118)) 7)))) (.or (.and (.var (.n 182)) (.var (.n 214))) (.and (.xor (.var (.n 182)) (.var (.n 214))) (.var (.n 198))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 182)) 11) (.shl (.var (.n 182)) 21)) (.var (.n 182))) 2) (.shl (.xor (.or (.shr (.var (.n 182)) 11) (.shl (.var (.n 182)) 21)) (.var (.n 182))) 30)) (.or (.shr (.var (.n 182)) 22) (.shl (.var (.n 182)) 10)))) = V (.A 2 0 (4)) :=
  shape7 (env (.n 134)) (env (.n 150)) (env (.n 118)) (env (.n 278)) (env (.n 182)) (env (.n 214)) (env (.n 198)) (V (.E 2 0 (2))) (V (.E 2 0 (1))) (V (.E 2 0 (3))) (V (.W 2 0 3)) (V (.A 2 0 (3))) (V (.A 2 0 (1))) (V (.A 2 0 (2))) (V (.A 2 0 (4))) (V (.E 2 0 (0))) (V (.KW 2 0 3)) (V (.H 2 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core6_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 133) = V (.E 1 0 (2)))
    (h1 : env (.n 149) = V (.E 1 0 (1)))
    (h2 : env (.n 117) = V (.E 1 0 (3)))
    (h3 : env (.n 277) = V (.W 1 0 3))
    (h4 : env (.n 181) = V (.A 1 0 (3)))
    (h5 : env (.n 213) = V (.A 1 0 (1)))
    (h6 : env (.n 197) = V (.A 1 0 (2)))
    (h7 : V (.A 1 0 (4)) = (V (.E 1 0 (0)) + Sigma1 (V (.E 1 0 (3))) + Ch (V (.E 1 0 (3))) (V (.E 1 0 (2))) (V (.E 1 0 (1))) + V (.KW 1 0 3)) + (Sigma0 (V (.A 1 0 (3))) + Maj (V (.A 1 0 (3))) (V (.A 1 0 (2))) (V (.A 1 0 (1)))))
    (h8 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h9 : V (.H 1 0 4) = 1359893119#32)
    (h10 : V (.KW 1 0 3) = 3921009573#32 + V (.W 1 0 3)) :
    E.eval env (.add (.add (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 133)) (.var (.n 149))) (.var (.n 117))) (.var (.n 149)))) (.add (.var (.n 277)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 6) (.shl (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 26)) (.or (.shr (.var (.n 117)) 25) (.shl (.var (.n 117)) 7)))) (.or (.and (.var (.n 181)) (.var (.n 213))) (.and (.xor (.var (.n 181)) (.var (.n 213))) (.var (.n 197))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 181)) 11) (.shl (.var (.n 181)) 21)) (.var (.n 181))) 2) (.shl (.xor (.or (.shr (.var (.n 181)) 11) (.shl (.var (.n 181)) 21)) (.var (.n 181))) 30)) (.or (.shr (.var (.n 181)) 22) (.shl (.var (.n 181)) 10)))) = V (.A 1 0 (4)) :=
  shape7 (env (.n 133)) (env (.n 149)) (env (.n 117)) (env (.n 277)) (env (.n 181)) (env (.n 213)) (env (.n 197)) (V (.E 1 0 (2))) (V (.E 1 0 (1))) (V (.E 1 0 (3))) (V (.W 1 0 3)) (V (.A 1 0 (3))) (V (.A 1 0 (1))) (V (.A 1 0 (2))) (V (.A 1 0 (4))) (V (.E 1 0 (0))) (V (.KW 1 0 3)) (V (.H 1 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core6_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 132) = V (.E 0 0 (2)))
    (h1 : env (.n 148) = V (.E 0 0 (1)))
    (h2 : env (.n 116) = V (.E 0 0 (3)))
    (h3 : env (.n 276) = V (.W 0 0 3))
    (h4 : env (.n 180) = V (.A 0 0 (3)))
    (h5 : env (.n 212) = V (.A 0 0 (1)))
    (h6 : env (.n 196) = V (.A 0 0 (2)))
    (h7 : V (.A 0 0 (4)) = (V (.E 0 0 (0)) + Sigma1 (V (.E 0 0 (3))) + Ch (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (1))) + V (.KW 0 0 3)) + (Sigma0 (V (.A 0 0 (3))) + Maj (V (.A 0 0 (3))) (V (.A 0 0 (2))) (V (.A 0 0 (1)))))
    (h8 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h9 : V (.H 0 0 4) = 1359893119#32)
    (h10 : V (.KW 0 0 3) = 3921009573#32 + V (.W 0 0 3)) :
    E.eval env (.add (.add (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 132)) (.var (.n 148))) (.var (.n 116))) (.var (.n 148)))) (.add (.var (.n 276)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 6) (.shl (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 26)) (.or (.shr (.var (.n 116)) 25) (.shl (.var (.n 116)) 7)))) (.or (.and (.var (.n 180)) (.var (.n 212))) (.and (.xor (.var (.n 180)) (.var (.n 212))) (.var (.n 196))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 180)) 11) (.shl (.var (.n 180)) 21)) (.var (.n 180))) 2) (.shl (.xor (.or (.shr (.var (.n 180)) 11) (.shl (.var (.n 180)) 21)) (.var (.n 180))) 30)) (.or (.shr (.var (.n 180)) 22) (.shl (.var (.n 180)) 10)))) = V (.A 0 0 (4)) :=
  shape7 (env (.n 132)) (env (.n 148)) (env (.n 116)) (env (.n 276)) (env (.n 180)) (env (.n 212)) (env (.n 196)) (V (.E 0 0 (2))) (V (.E 0 0 (1))) (V (.E 0 0 (3))) (V (.W 0 0 3)) (V (.A 0 0 (3))) (V (.A 0 0 (1))) (V (.A 0 0 (2))) (V (.A 0 0 (4))) (V (.E 0 0 (0))) (V (.KW 0 0 3)) (V (.H 0 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem core6_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 135) = V (.E 3 0 (2)))
    (h1 : env (.n 151) = V (.E 3 0 (1)))
    (h2 : env (.n 119) = V (.E 3 0 (3)))
    (h3 : env (.n 279) = V (.W 3 0 3))
    (h4 : V (.E 3 0 (4)) = V (.A 3 0 (0)) + (V (.E 3 0 (0)) + Sigma1 (V (.E 3 0 (3))) + Ch (V (.E 3 0 (3))) (V (.E 3 0 (2))) (V (.E 3 0 (1))) + V (.KW 3 0 3)))
    (h5 : V (.A 3 0 (0)) = V (.H 3 0 0))
    (h6 : V (.H 3 0 0) = 1779033703#32)
    (h7 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h8 : V (.H 3 0 4) = 1359893119#32)
    (h9 : V (.KW 3 0 3) = 3921009573#32 + V (.W 3 0 3)) :
    E.eval env (.add (.const 1779033703) (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 135)) (.var (.n 151))) (.var (.n 119))) (.var (.n 151)))) (.add (.var (.n 279)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 6) (.shl (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 26)) (.or (.shr (.var (.n 119)) 25) (.shl (.var (.n 119)) 7))))) = V (.E 3 0 (4)) :=
  shape8 (env (.n 135)) (env (.n 151)) (env (.n 119)) (env (.n 279)) (V (.E 3 0 (2))) (V (.E 3 0 (1))) (V (.E 3 0 (3))) (V (.W 3 0 3)) (V (.E 3 0 (4))) (V (.A 3 0 (0))) (V (.E 3 0 (0))) (V (.KW 3 0 3)) (V (.H 3 0 0)) (V (.H 3 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core6_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 134) = V (.E 2 0 (2)))
    (h1 : env (.n 150) = V (.E 2 0 (1)))
    (h2 : env (.n 118) = V (.E 2 0 (3)))
    (h3 : env (.n 278) = V (.W 2 0 3))
    (h4 : V (.E 2 0 (4)) = V (.A 2 0 (0)) + (V (.E 2 0 (0)) + Sigma1 (V (.E 2 0 (3))) + Ch (V (.E 2 0 (3))) (V (.E 2 0 (2))) (V (.E 2 0 (1))) + V (.KW 2 0 3)))
    (h5 : V (.A 2 0 (0)) = V (.H 2 0 0))
    (h6 : V (.H 2 0 0) = 1779033703#32)
    (h7 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h8 : V (.H 2 0 4) = 1359893119#32)
    (h9 : V (.KW 2 0 3) = 3921009573#32 + V (.W 2 0 3)) :
    E.eval env (.add (.const 1779033703) (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 134)) (.var (.n 150))) (.var (.n 118))) (.var (.n 150)))) (.add (.var (.n 278)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 6) (.shl (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 26)) (.or (.shr (.var (.n 118)) 25) (.shl (.var (.n 118)) 7))))) = V (.E 2 0 (4)) :=
  shape8 (env (.n 134)) (env (.n 150)) (env (.n 118)) (env (.n 278)) (V (.E 2 0 (2))) (V (.E 2 0 (1))) (V (.E 2 0 (3))) (V (.W 2 0 3)) (V (.E 2 0 (4))) (V (.A 2 0 (0))) (V (.E 2 0 (0))) (V (.KW 2 0 3)) (V (.H 2 0 0)) (V (.H 2 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core6_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 133) = V (.E 1 0 (2)))
    (h1 : env (.n 149) = V (.E 1 0 (1)))
    (h2 : env (.n 117) = V (.E 1 0 (3)))
    (h3 : env (.n 277) = V (.W 1 0 3))
    (h4 : V (.E 1 0 (4)) = V (.A 1 0 (0)) + (V (.E 1 0 (0)) + Sigma1 (V (.E 1 0 (3))) + Ch (V (.E 1 0 (3))) (V (.E 1 0 (2))) (V (.E 1 0 (1))) + V (.KW 1 0 3)))
    (h5 : V (.A 1 0 (0)) = V (.H 1 0 0))
    (h6 : V (.H 1 0 0) = 1779033703#32)
    (h7 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h8 : V (.H 1 0 4) = 1359893119#32)
    (h9 : V (.KW 1 0 3) = 3921009573#32 + V (.W 1 0 3)) :
    E.eval env (.add (.const 1779033703) (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 133)) (.var (.n 149))) (.var (.n 117))) (.var (.n 149)))) (.add (.var (.n 277)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 6) (.shl (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 26)) (.or (.shr (.var (.n 117)) 25) (.shl (.var (.n 117)) 7))))) = V (.E 1 0 (4)) :=
  shape8 (env (.n 133)) (env (.n 149)) (env (.n 117)) (env (.n 277)) (V (.E 1 0 (2))) (V (.E 1 0 (1))) (V (.E 1 0 (3))) (V (.W 1 0 3)) (V (.E 1 0 (4))) (V (.A 1 0 (0))) (V (.E 1 0 (0))) (V (.KW 1 0 3)) (V (.H 1 0 0)) (V (.H 1 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core6_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 132) = V (.E 0 0 (2)))
    (h1 : env (.n 148) = V (.E 0 0 (1)))
    (h2 : env (.n 116) = V (.E 0 0 (3)))
    (h3 : env (.n 276) = V (.W 0 0 3))
    (h4 : V (.E 0 0 (4)) = V (.A 0 0 (0)) + (V (.E 0 0 (0)) + Sigma1 (V (.E 0 0 (3))) + Ch (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (1))) + V (.KW 0 0 3)))
    (h5 : V (.A 0 0 (0)) = V (.H 0 0 0))
    (h6 : V (.H 0 0 0) = 1779033703#32)
    (h7 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h8 : V (.H 0 0 4) = 1359893119#32)
    (h9 : V (.KW 0 0 3) = 3921009573#32 + V (.W 0 0 3)) :
    E.eval env (.add (.const 1779033703) (.add (.add (.add (.const 1359893119) (.xor (.and (.xor (.var (.n 132)) (.var (.n 148))) (.var (.n 116))) (.var (.n 148)))) (.add (.var (.n 276)) (.const 3921009573))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 6) (.shl (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 26)) (.or (.shr (.var (.n 116)) 25) (.shl (.var (.n 116)) 7))))) = V (.E 0 0 (4)) :=
  shape8 (env (.n 132)) (env (.n 148)) (env (.n 116)) (env (.n 276)) (V (.E 0 0 (2))) (V (.E 0 0 (1))) (V (.E 0 0 (3))) (V (.W 0 0 3)) (V (.E 0 0 (4))) (V (.A 0 0 (0))) (V (.E 0 0 (0))) (V (.KW 0 0 3)) (V (.H 0 0 0)) (V (.H 0 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem step6 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L6) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K6)) L7 := by
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
  exact invC_of_trees inp env _ T6 L7 (slice_trees_mem prog 4 _ _ 38 K6 K7 T6 slice6 env)
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
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h48⟩
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
      (And.intro ⟨rfl, core6_167 (qv inp) inp env h68 h64 h72 h48 h60 h52 h56 (qA_succI inp 3 0 (3) (by decide)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 3 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      (And.intro ⟨rfl, core6_166 (qv inp) inp env h69 h65 h73 h49 h61 h53 h57 (qA_succI inp 2 0 (3) (by decide)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 2 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      (And.intro ⟨rfl, core6_165 (qv inp) inp env h70 h66 h74 h50 h62 h54 h58 (qA_succI inp 1 0 (3) (by decide)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 1 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      (And.intro ⟨rfl, core6_164 (qv inp) inp env h71 h67 h75 h51 h63 h55 h59 (qA_succI inp 0 0 (3) (by decide)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 0 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
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
      (And.intro ⟨rfl, core6_103 (qv inp) inp env h68 h64 h72 h48 (qE_succI inp 3 0 (3) (by decide)) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 3 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      (And.intro ⟨rfl, core6_102 (qv inp) inp env h69 h65 h73 h49 (qE_succI inp 2 0 (3) (by decide)) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 2 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      (And.intro ⟨rfl, core6_101 (qv inp) inp env h70 h66 h74 h50 (qE_succI inp 1 0 (3) (by decide)) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 1 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      (And.intro ⟨rfl, core6_100 (qv inp) inp env h71 h67 h75 h51 (qE_succI inp 0 0 (3) (by decide)) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) ((qKW inp 0 0 3).trans (by rw [show Spec.K 3 = 3921009573#32 from by decide]))⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
