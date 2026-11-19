import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D8
import Hashtree.Gen.WinAvx2X8P.D7

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice8 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K8 K9 T8 = true := by
  decide +kernel

theorem core8_235 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1131) = V (.W 7 0 4))
    (h1 : env (.n 1130) = V (.W 7 0 4))
    (h2 : env (.n 1129) = V (.W 7 0 4))
    (h3 : env (.n 1128) = V (.W 7 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1131)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1130)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1129)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1128)) 24) (.const 255)) 24))) = V (.W 7 0 4) :=
  shape4 (env (.n 1131)) (env (.n 1130)) (env (.n 1129)) (env (.n 1128)) (V (.W 7 0 4)) h0 h1 h2 h3

theorem core8_234 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1135) = V (.W 6 0 4))
    (h1 : env (.n 1134) = V (.W 6 0 4))
    (h2 : env (.n 1133) = V (.W 6 0 4))
    (h3 : env (.n 1132) = V (.W 6 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1135)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1134)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1133)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1132)) 24) (.const 255)) 24))) = V (.W 6 0 4) :=
  shape4 (env (.n 1135)) (env (.n 1134)) (env (.n 1133)) (env (.n 1132)) (V (.W 6 0 4)) h0 h1 h2 h3

theorem core8_233 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1139) = V (.W 5 0 4))
    (h1 : env (.n 1138) = V (.W 5 0 4))
    (h2 : env (.n 1137) = V (.W 5 0 4))
    (h3 : env (.n 1136) = V (.W 5 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1139)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1138)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1137)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1136)) 24) (.const 255)) 24))) = V (.W 5 0 4) :=
  shape4 (env (.n 1139)) (env (.n 1138)) (env (.n 1137)) (env (.n 1136)) (V (.W 5 0 4)) h0 h1 h2 h3

theorem core8_232 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1143) = V (.W 4 0 4))
    (h1 : env (.n 1142) = V (.W 4 0 4))
    (h2 : env (.n 1141) = V (.W 4 0 4))
    (h3 : env (.n 1140) = V (.W 4 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1143)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1142)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1141)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1140)) 24) (.const 255)) 24))) = V (.W 4 0 4) :=
  shape4 (env (.n 1143)) (env (.n 1142)) (env (.n 1141)) (env (.n 1140)) (V (.W 4 0 4)) h0 h1 h2 h3

theorem core8_231 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1147) = V (.W 3 0 4))
    (h1 : env (.n 1146) = V (.W 3 0 4))
    (h2 : env (.n 1145) = V (.W 3 0 4))
    (h3 : env (.n 1144) = V (.W 3 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1147)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1146)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1145)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1144)) 24) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape4 (env (.n 1147)) (env (.n 1146)) (env (.n 1145)) (env (.n 1144)) (V (.W 3 0 4)) h0 h1 h2 h3

theorem core8_230 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1151) = V (.W 2 0 4))
    (h1 : env (.n 1150) = V (.W 2 0 4))
    (h2 : env (.n 1149) = V (.W 2 0 4))
    (h3 : env (.n 1148) = V (.W 2 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1151)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1150)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1149)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1148)) 24) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape4 (env (.n 1151)) (env (.n 1150)) (env (.n 1149)) (env (.n 1148)) (V (.W 2 0 4)) h0 h1 h2 h3

theorem core8_229 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1155) = V (.W 1 0 4))
    (h1 : env (.n 1154) = V (.W 1 0 4))
    (h2 : env (.n 1153) = V (.W 1 0 4))
    (h3 : env (.n 1152) = V (.W 1 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1155)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1154)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1153)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1152)) 24) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape4 (env (.n 1155)) (env (.n 1154)) (env (.n 1153)) (env (.n 1152)) (V (.W 1 0 4)) h0 h1 h2 h3

theorem core8_228 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1159) = V (.W 0 0 4))
    (h1 : env (.n 1158) = V (.W 0 0 4))
    (h2 : env (.n 1157) = V (.W 0 0 4))
    (h3 : env (.n 1156) = V (.W 0 0 4)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1159)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1158)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1157)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1156)) 24) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape4 (env (.n 1159)) (env (.n 1158)) (env (.n 1157)) (env (.n 1156)) (V (.W 0 0 4)) h0 h1 h2 h3

theorem core8_203 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 155) = V (.E 7 0 (1)))
    (h1 : env (.n 251) = V (.W 7 0 1))
    (h2 : env (.n 219) = V (.A 7 0 (1)))
    (h3 : V (.A 7 0 (2)) = (V (.E 7 0 (-2)) + Sigma1 (V (.E 7 0 (1))) + Ch (V (.E 7 0 (1))) (V (.E 7 0 (0))) (V (.E 7 0 (-1))) + V (.KW 7 0 1)) + (Sigma0 (V (.A 7 0 (1))) + Maj (V (.A 7 0 (1))) (V (.A 7 0 (0))) (V (.A 7 0 (-1)))))
    (h4 : V (.E 7 0 (-2)) = V (.H 7 0 6))
    (h5 : V (.H 7 0 6) = 528734635#32)
    (h6 : V (.E 7 0 (0)) = V (.H 7 0 4))
    (h7 : V (.H 7 0 4) = 1359893119#32)
    (h8 : V (.E 7 0 (-1)) = V (.H 7 0 5))
    (h9 : V (.H 7 0 5) = 2600822924#32)
    (h10 : V (.KW 7 0 1) = 1899447441#32 + V (.W 7 0 1))
    (h11 : V (.A 7 0 (0)) = V (.H 7 0 0))
    (h12 : V (.H 7 0 0) = 1779033703#32)
    (h13 : V (.A 7 0 (-1)) = V (.H 7 0 1))
    (h14 : V (.H 7 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 155))) (.const 2600822924))) (.add (.var (.n 251)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 155)) 5) (.shl (.var (.n 155)) 27)) (.var (.n 155))) 6) (.shl (.xor (.or (.shr (.var (.n 155)) 5) (.shl (.var (.n 155)) 27)) (.var (.n 155))) 26)) (.or (.shr (.var (.n 155)) 25) (.shl (.var (.n 155)) 7)))) (.or (.and (.var (.n 219)) (.const 3144134277)) (.and (.xor (.var (.n 219)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 219)) 11) (.shl (.var (.n 219)) 21)) (.var (.n 219))) 2) (.shl (.xor (.or (.shr (.var (.n 219)) 11) (.shl (.var (.n 219)) 21)) (.var (.n 219))) 30)) (.or (.shr (.var (.n 219)) 22) (.shl (.var (.n 219)) 10)))) = V (.A 7 0 (2)) :=
  shape5 (env (.n 155)) (env (.n 251)) (env (.n 219)) (V (.E 7 0 (1))) (V (.W 7 0 1)) (V (.A 7 0 (1))) (V (.A 7 0 (2))) (V (.E 7 0 (-2))) (V (.E 7 0 (0))) (V (.E 7 0 (-1))) (V (.KW 7 0 1)) (V (.A 7 0 (0))) (V (.A 7 0 (-1))) (V (.H 7 0 6)) (V (.H 7 0 4)) (V (.H 7 0 5)) (V (.H 7 0 0)) (V (.H 7 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_202 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 154) = V (.E 6 0 (1)))
    (h1 : env (.n 250) = V (.W 6 0 1))
    (h2 : env (.n 218) = V (.A 6 0 (1)))
    (h3 : V (.A 6 0 (2)) = (V (.E 6 0 (-2)) + Sigma1 (V (.E 6 0 (1))) + Ch (V (.E 6 0 (1))) (V (.E 6 0 (0))) (V (.E 6 0 (-1))) + V (.KW 6 0 1)) + (Sigma0 (V (.A 6 0 (1))) + Maj (V (.A 6 0 (1))) (V (.A 6 0 (0))) (V (.A 6 0 (-1)))))
    (h4 : V (.E 6 0 (-2)) = V (.H 6 0 6))
    (h5 : V (.H 6 0 6) = 528734635#32)
    (h6 : V (.E 6 0 (0)) = V (.H 6 0 4))
    (h7 : V (.H 6 0 4) = 1359893119#32)
    (h8 : V (.E 6 0 (-1)) = V (.H 6 0 5))
    (h9 : V (.H 6 0 5) = 2600822924#32)
    (h10 : V (.KW 6 0 1) = 1899447441#32 + V (.W 6 0 1))
    (h11 : V (.A 6 0 (0)) = V (.H 6 0 0))
    (h12 : V (.H 6 0 0) = 1779033703#32)
    (h13 : V (.A 6 0 (-1)) = V (.H 6 0 1))
    (h14 : V (.H 6 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 154))) (.const 2600822924))) (.add (.var (.n 250)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 154)) 5) (.shl (.var (.n 154)) 27)) (.var (.n 154))) 6) (.shl (.xor (.or (.shr (.var (.n 154)) 5) (.shl (.var (.n 154)) 27)) (.var (.n 154))) 26)) (.or (.shr (.var (.n 154)) 25) (.shl (.var (.n 154)) 7)))) (.or (.and (.var (.n 218)) (.const 3144134277)) (.and (.xor (.var (.n 218)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 218)) 11) (.shl (.var (.n 218)) 21)) (.var (.n 218))) 2) (.shl (.xor (.or (.shr (.var (.n 218)) 11) (.shl (.var (.n 218)) 21)) (.var (.n 218))) 30)) (.or (.shr (.var (.n 218)) 22) (.shl (.var (.n 218)) 10)))) = V (.A 6 0 (2)) :=
  shape5 (env (.n 154)) (env (.n 250)) (env (.n 218)) (V (.E 6 0 (1))) (V (.W 6 0 1)) (V (.A 6 0 (1))) (V (.A 6 0 (2))) (V (.E 6 0 (-2))) (V (.E 6 0 (0))) (V (.E 6 0 (-1))) (V (.KW 6 0 1)) (V (.A 6 0 (0))) (V (.A 6 0 (-1))) (V (.H 6 0 6)) (V (.H 6 0 4)) (V (.H 6 0 5)) (V (.H 6 0 0)) (V (.H 6 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_201 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 153) = V (.E 5 0 (1)))
    (h1 : env (.n 249) = V (.W 5 0 1))
    (h2 : env (.n 217) = V (.A 5 0 (1)))
    (h3 : V (.A 5 0 (2)) = (V (.E 5 0 (-2)) + Sigma1 (V (.E 5 0 (1))) + Ch (V (.E 5 0 (1))) (V (.E 5 0 (0))) (V (.E 5 0 (-1))) + V (.KW 5 0 1)) + (Sigma0 (V (.A 5 0 (1))) + Maj (V (.A 5 0 (1))) (V (.A 5 0 (0))) (V (.A 5 0 (-1)))))
    (h4 : V (.E 5 0 (-2)) = V (.H 5 0 6))
    (h5 : V (.H 5 0 6) = 528734635#32)
    (h6 : V (.E 5 0 (0)) = V (.H 5 0 4))
    (h7 : V (.H 5 0 4) = 1359893119#32)
    (h8 : V (.E 5 0 (-1)) = V (.H 5 0 5))
    (h9 : V (.H 5 0 5) = 2600822924#32)
    (h10 : V (.KW 5 0 1) = 1899447441#32 + V (.W 5 0 1))
    (h11 : V (.A 5 0 (0)) = V (.H 5 0 0))
    (h12 : V (.H 5 0 0) = 1779033703#32)
    (h13 : V (.A 5 0 (-1)) = V (.H 5 0 1))
    (h14 : V (.H 5 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 153))) (.const 2600822924))) (.add (.var (.n 249)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 153)) 5) (.shl (.var (.n 153)) 27)) (.var (.n 153))) 6) (.shl (.xor (.or (.shr (.var (.n 153)) 5) (.shl (.var (.n 153)) 27)) (.var (.n 153))) 26)) (.or (.shr (.var (.n 153)) 25) (.shl (.var (.n 153)) 7)))) (.or (.and (.var (.n 217)) (.const 3144134277)) (.and (.xor (.var (.n 217)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 217)) 11) (.shl (.var (.n 217)) 21)) (.var (.n 217))) 2) (.shl (.xor (.or (.shr (.var (.n 217)) 11) (.shl (.var (.n 217)) 21)) (.var (.n 217))) 30)) (.or (.shr (.var (.n 217)) 22) (.shl (.var (.n 217)) 10)))) = V (.A 5 0 (2)) :=
  shape5 (env (.n 153)) (env (.n 249)) (env (.n 217)) (V (.E 5 0 (1))) (V (.W 5 0 1)) (V (.A 5 0 (1))) (V (.A 5 0 (2))) (V (.E 5 0 (-2))) (V (.E 5 0 (0))) (V (.E 5 0 (-1))) (V (.KW 5 0 1)) (V (.A 5 0 (0))) (V (.A 5 0 (-1))) (V (.H 5 0 6)) (V (.H 5 0 4)) (V (.H 5 0 5)) (V (.H 5 0 0)) (V (.H 5 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_200 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 152) = V (.E 4 0 (1)))
    (h1 : env (.n 248) = V (.W 4 0 1))
    (h2 : env (.n 216) = V (.A 4 0 (1)))
    (h3 : V (.A 4 0 (2)) = (V (.E 4 0 (-2)) + Sigma1 (V (.E 4 0 (1))) + Ch (V (.E 4 0 (1))) (V (.E 4 0 (0))) (V (.E 4 0 (-1))) + V (.KW 4 0 1)) + (Sigma0 (V (.A 4 0 (1))) + Maj (V (.A 4 0 (1))) (V (.A 4 0 (0))) (V (.A 4 0 (-1)))))
    (h4 : V (.E 4 0 (-2)) = V (.H 4 0 6))
    (h5 : V (.H 4 0 6) = 528734635#32)
    (h6 : V (.E 4 0 (0)) = V (.H 4 0 4))
    (h7 : V (.H 4 0 4) = 1359893119#32)
    (h8 : V (.E 4 0 (-1)) = V (.H 4 0 5))
    (h9 : V (.H 4 0 5) = 2600822924#32)
    (h10 : V (.KW 4 0 1) = 1899447441#32 + V (.W 4 0 1))
    (h11 : V (.A 4 0 (0)) = V (.H 4 0 0))
    (h12 : V (.H 4 0 0) = 1779033703#32)
    (h13 : V (.A 4 0 (-1)) = V (.H 4 0 1))
    (h14 : V (.H 4 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 152))) (.const 2600822924))) (.add (.var (.n 248)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 152)) 5) (.shl (.var (.n 152)) 27)) (.var (.n 152))) 6) (.shl (.xor (.or (.shr (.var (.n 152)) 5) (.shl (.var (.n 152)) 27)) (.var (.n 152))) 26)) (.or (.shr (.var (.n 152)) 25) (.shl (.var (.n 152)) 7)))) (.or (.and (.var (.n 216)) (.const 3144134277)) (.and (.xor (.var (.n 216)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 216)) 11) (.shl (.var (.n 216)) 21)) (.var (.n 216))) 2) (.shl (.xor (.or (.shr (.var (.n 216)) 11) (.shl (.var (.n 216)) 21)) (.var (.n 216))) 30)) (.or (.shr (.var (.n 216)) 22) (.shl (.var (.n 216)) 10)))) = V (.A 4 0 (2)) :=
  shape5 (env (.n 152)) (env (.n 248)) (env (.n 216)) (V (.E 4 0 (1))) (V (.W 4 0 1)) (V (.A 4 0 (1))) (V (.A 4 0 (2))) (V (.E 4 0 (-2))) (V (.E 4 0 (0))) (V (.E 4 0 (-1))) (V (.KW 4 0 1)) (V (.A 4 0 (0))) (V (.A 4 0 (-1))) (V (.H 4 0 6)) (V (.H 4 0 4)) (V (.H 4 0 5)) (V (.H 4 0 0)) (V (.H 4 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 247) = V (.W 3 0 1))
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
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 151))) (.const 2600822924))) (.add (.var (.n 247)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 6) (.shl (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 26)) (.or (.shr (.var (.n 151)) 25) (.shl (.var (.n 151)) 7)))) (.or (.and (.var (.n 215)) (.const 3144134277)) (.and (.xor (.var (.n 215)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 215)) 11) (.shl (.var (.n 215)) 21)) (.var (.n 215))) 2) (.shl (.xor (.or (.shr (.var (.n 215)) 11) (.shl (.var (.n 215)) 21)) (.var (.n 215))) 30)) (.or (.shr (.var (.n 215)) 22) (.shl (.var (.n 215)) 10)))) = V (.A 3 0 (2)) :=
  shape5 (env (.n 151)) (env (.n 247)) (env (.n 215)) (V (.E 3 0 (1))) (V (.W 3 0 1)) (V (.A 3 0 (1))) (V (.A 3 0 (2))) (V (.E 3 0 (-2))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.KW 3 0 1)) (V (.A 3 0 (0))) (V (.A 3 0 (-1))) (V (.H 3 0 6)) (V (.H 3 0 4)) (V (.H 3 0 5)) (V (.H 3 0 0)) (V (.H 3 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 246) = V (.W 2 0 1))
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
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 150))) (.const 2600822924))) (.add (.var (.n 246)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 6) (.shl (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 26)) (.or (.shr (.var (.n 150)) 25) (.shl (.var (.n 150)) 7)))) (.or (.and (.var (.n 214)) (.const 3144134277)) (.and (.xor (.var (.n 214)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 214)) 11) (.shl (.var (.n 214)) 21)) (.var (.n 214))) 2) (.shl (.xor (.or (.shr (.var (.n 214)) 11) (.shl (.var (.n 214)) 21)) (.var (.n 214))) 30)) (.or (.shr (.var (.n 214)) 22) (.shl (.var (.n 214)) 10)))) = V (.A 2 0 (2)) :=
  shape5 (env (.n 150)) (env (.n 246)) (env (.n 214)) (V (.E 2 0 (1))) (V (.W 2 0 1)) (V (.A 2 0 (1))) (V (.A 2 0 (2))) (V (.E 2 0 (-2))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.KW 2 0 1)) (V (.A 2 0 (0))) (V (.A 2 0 (-1))) (V (.H 2 0 6)) (V (.H 2 0 4)) (V (.H 2 0 5)) (V (.H 2 0 0)) (V (.H 2 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 245) = V (.W 1 0 1))
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
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 149))) (.const 2600822924))) (.add (.var (.n 245)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 6) (.shl (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 26)) (.or (.shr (.var (.n 149)) 25) (.shl (.var (.n 149)) 7)))) (.or (.and (.var (.n 213)) (.const 3144134277)) (.and (.xor (.var (.n 213)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 213)) 11) (.shl (.var (.n 213)) 21)) (.var (.n 213))) 2) (.shl (.xor (.or (.shr (.var (.n 213)) 11) (.shl (.var (.n 213)) 21)) (.var (.n 213))) 30)) (.or (.shr (.var (.n 213)) 22) (.shl (.var (.n 213)) 10)))) = V (.A 1 0 (2)) :=
  shape5 (env (.n 149)) (env (.n 245)) (env (.n 213)) (V (.E 1 0 (1))) (V (.W 1 0 1)) (V (.A 1 0 (1))) (V (.A 1 0 (2))) (V (.E 1 0 (-2))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.KW 1 0 1)) (V (.A 1 0 (0))) (V (.A 1 0 (-1))) (V (.H 1 0 6)) (V (.H 1 0 4)) (V (.H 1 0 5)) (V (.H 1 0 0)) (V (.H 1 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 244) = V (.W 0 0 1))
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
    E.eval env (.add (.add (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 148))) (.const 2600822924))) (.add (.var (.n 244)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 6) (.shl (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 26)) (.or (.shr (.var (.n 148)) 25) (.shl (.var (.n 148)) 7)))) (.or (.and (.var (.n 212)) (.const 3144134277)) (.and (.xor (.var (.n 212)) (.const 3144134277)) (.const 1779033703)))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 212)) 11) (.shl (.var (.n 212)) 21)) (.var (.n 212))) 2) (.shl (.xor (.or (.shr (.var (.n 212)) 11) (.shl (.var (.n 212)) 21)) (.var (.n 212))) 30)) (.or (.shr (.var (.n 212)) 22) (.shl (.var (.n 212)) 10)))) = V (.A 0 0 (2)) :=
  shape5 (env (.n 148)) (env (.n 244)) (env (.n 212)) (V (.E 0 0 (1))) (V (.W 0 0 1)) (V (.A 0 0 (1))) (V (.A 0 0 (2))) (V (.E 0 0 (-2))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.KW 0 0 1)) (V (.A 0 0 (0))) (V (.A 0 0 (-1))) (V (.H 0 0 6)) (V (.H 0 0 4)) (V (.H 0 0 5)) (V (.H 0 0 0)) (V (.H 0 0 1)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core8_139 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 155) = V (.E 7 0 (1)))
    (h1 : env (.n 251) = V (.W 7 0 1))
    (h2 : V (.E 7 0 (2)) = V (.A 7 0 (-2)) + (V (.E 7 0 (-2)) + Sigma1 (V (.E 7 0 (1))) + Ch (V (.E 7 0 (1))) (V (.E 7 0 (0))) (V (.E 7 0 (-1))) + V (.KW 7 0 1)))
    (h3 : V (.A 7 0 (-2)) = V (.H 7 0 2))
    (h4 : V (.H 7 0 2) = 1013904242#32)
    (h5 : V (.E 7 0 (-2)) = V (.H 7 0 6))
    (h6 : V (.H 7 0 6) = 528734635#32)
    (h7 : V (.E 7 0 (0)) = V (.H 7 0 4))
    (h8 : V (.H 7 0 4) = 1359893119#32)
    (h9 : V (.E 7 0 (-1)) = V (.H 7 0 5))
    (h10 : V (.H 7 0 5) = 2600822924#32)
    (h11 : V (.KW 7 0 1) = 1899447441#32 + V (.W 7 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 155))) (.const 2600822924))) (.add (.var (.n 251)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 155)) 5) (.shl (.var (.n 155)) 27)) (.var (.n 155))) 6) (.shl (.xor (.or (.shr (.var (.n 155)) 5) (.shl (.var (.n 155)) 27)) (.var (.n 155))) 26)) (.or (.shr (.var (.n 155)) 25) (.shl (.var (.n 155)) 7))))) = V (.E 7 0 (2)) :=
  shape6 (env (.n 155)) (env (.n 251)) (V (.E 7 0 (1))) (V (.W 7 0 1)) (V (.E 7 0 (2))) (V (.A 7 0 (-2))) (V (.E 7 0 (-2))) (V (.E 7 0 (0))) (V (.E 7 0 (-1))) (V (.KW 7 0 1)) (V (.H 7 0 2)) (V (.H 7 0 6)) (V (.H 7 0 4)) (V (.H 7 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_138 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 154) = V (.E 6 0 (1)))
    (h1 : env (.n 250) = V (.W 6 0 1))
    (h2 : V (.E 6 0 (2)) = V (.A 6 0 (-2)) + (V (.E 6 0 (-2)) + Sigma1 (V (.E 6 0 (1))) + Ch (V (.E 6 0 (1))) (V (.E 6 0 (0))) (V (.E 6 0 (-1))) + V (.KW 6 0 1)))
    (h3 : V (.A 6 0 (-2)) = V (.H 6 0 2))
    (h4 : V (.H 6 0 2) = 1013904242#32)
    (h5 : V (.E 6 0 (-2)) = V (.H 6 0 6))
    (h6 : V (.H 6 0 6) = 528734635#32)
    (h7 : V (.E 6 0 (0)) = V (.H 6 0 4))
    (h8 : V (.H 6 0 4) = 1359893119#32)
    (h9 : V (.E 6 0 (-1)) = V (.H 6 0 5))
    (h10 : V (.H 6 0 5) = 2600822924#32)
    (h11 : V (.KW 6 0 1) = 1899447441#32 + V (.W 6 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 154))) (.const 2600822924))) (.add (.var (.n 250)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 154)) 5) (.shl (.var (.n 154)) 27)) (.var (.n 154))) 6) (.shl (.xor (.or (.shr (.var (.n 154)) 5) (.shl (.var (.n 154)) 27)) (.var (.n 154))) 26)) (.or (.shr (.var (.n 154)) 25) (.shl (.var (.n 154)) 7))))) = V (.E 6 0 (2)) :=
  shape6 (env (.n 154)) (env (.n 250)) (V (.E 6 0 (1))) (V (.W 6 0 1)) (V (.E 6 0 (2))) (V (.A 6 0 (-2))) (V (.E 6 0 (-2))) (V (.E 6 0 (0))) (V (.E 6 0 (-1))) (V (.KW 6 0 1)) (V (.H 6 0 2)) (V (.H 6 0 6)) (V (.H 6 0 4)) (V (.H 6 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_137 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 153) = V (.E 5 0 (1)))
    (h1 : env (.n 249) = V (.W 5 0 1))
    (h2 : V (.E 5 0 (2)) = V (.A 5 0 (-2)) + (V (.E 5 0 (-2)) + Sigma1 (V (.E 5 0 (1))) + Ch (V (.E 5 0 (1))) (V (.E 5 0 (0))) (V (.E 5 0 (-1))) + V (.KW 5 0 1)))
    (h3 : V (.A 5 0 (-2)) = V (.H 5 0 2))
    (h4 : V (.H 5 0 2) = 1013904242#32)
    (h5 : V (.E 5 0 (-2)) = V (.H 5 0 6))
    (h6 : V (.H 5 0 6) = 528734635#32)
    (h7 : V (.E 5 0 (0)) = V (.H 5 0 4))
    (h8 : V (.H 5 0 4) = 1359893119#32)
    (h9 : V (.E 5 0 (-1)) = V (.H 5 0 5))
    (h10 : V (.H 5 0 5) = 2600822924#32)
    (h11 : V (.KW 5 0 1) = 1899447441#32 + V (.W 5 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 153))) (.const 2600822924))) (.add (.var (.n 249)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 153)) 5) (.shl (.var (.n 153)) 27)) (.var (.n 153))) 6) (.shl (.xor (.or (.shr (.var (.n 153)) 5) (.shl (.var (.n 153)) 27)) (.var (.n 153))) 26)) (.or (.shr (.var (.n 153)) 25) (.shl (.var (.n 153)) 7))))) = V (.E 5 0 (2)) :=
  shape6 (env (.n 153)) (env (.n 249)) (V (.E 5 0 (1))) (V (.W 5 0 1)) (V (.E 5 0 (2))) (V (.A 5 0 (-2))) (V (.E 5 0 (-2))) (V (.E 5 0 (0))) (V (.E 5 0 (-1))) (V (.KW 5 0 1)) (V (.H 5 0 2)) (V (.H 5 0 6)) (V (.H 5 0 4)) (V (.H 5 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_136 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 152) = V (.E 4 0 (1)))
    (h1 : env (.n 248) = V (.W 4 0 1))
    (h2 : V (.E 4 0 (2)) = V (.A 4 0 (-2)) + (V (.E 4 0 (-2)) + Sigma1 (V (.E 4 0 (1))) + Ch (V (.E 4 0 (1))) (V (.E 4 0 (0))) (V (.E 4 0 (-1))) + V (.KW 4 0 1)))
    (h3 : V (.A 4 0 (-2)) = V (.H 4 0 2))
    (h4 : V (.H 4 0 2) = 1013904242#32)
    (h5 : V (.E 4 0 (-2)) = V (.H 4 0 6))
    (h6 : V (.H 4 0 6) = 528734635#32)
    (h7 : V (.E 4 0 (0)) = V (.H 4 0 4))
    (h8 : V (.H 4 0 4) = 1359893119#32)
    (h9 : V (.E 4 0 (-1)) = V (.H 4 0 5))
    (h10 : V (.H 4 0 5) = 2600822924#32)
    (h11 : V (.KW 4 0 1) = 1899447441#32 + V (.W 4 0 1)) :
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 152))) (.const 2600822924))) (.add (.var (.n 248)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 152)) 5) (.shl (.var (.n 152)) 27)) (.var (.n 152))) 6) (.shl (.xor (.or (.shr (.var (.n 152)) 5) (.shl (.var (.n 152)) 27)) (.var (.n 152))) 26)) (.or (.shr (.var (.n 152)) 25) (.shl (.var (.n 152)) 7))))) = V (.E 4 0 (2)) :=
  shape6 (env (.n 152)) (env (.n 248)) (V (.E 4 0 (1))) (V (.W 4 0 1)) (V (.E 4 0 (2))) (V (.A 4 0 (-2))) (V (.E 4 0 (-2))) (V (.E 4 0 (0))) (V (.E 4 0 (-1))) (V (.KW 4 0 1)) (V (.H 4 0 2)) (V (.H 4 0 6)) (V (.H 4 0 4)) (V (.H 4 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 247) = V (.W 3 0 1))
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
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 151))) (.const 2600822924))) (.add (.var (.n 247)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 6) (.shl (.xor (.or (.shr (.var (.n 151)) 5) (.shl (.var (.n 151)) 27)) (.var (.n 151))) 26)) (.or (.shr (.var (.n 151)) 25) (.shl (.var (.n 151)) 7))))) = V (.E 3 0 (2)) :=
  shape6 (env (.n 151)) (env (.n 247)) (V (.E 3 0 (1))) (V (.W 3 0 1)) (V (.E 3 0 (2))) (V (.A 3 0 (-2))) (V (.E 3 0 (-2))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.KW 3 0 1)) (V (.H 3 0 2)) (V (.H 3 0 6)) (V (.H 3 0 4)) (V (.H 3 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 246) = V (.W 2 0 1))
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
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 150))) (.const 2600822924))) (.add (.var (.n 246)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 6) (.shl (.xor (.or (.shr (.var (.n 150)) 5) (.shl (.var (.n 150)) 27)) (.var (.n 150))) 26)) (.or (.shr (.var (.n 150)) 25) (.shl (.var (.n 150)) 7))))) = V (.E 2 0 (2)) :=
  shape6 (env (.n 150)) (env (.n 246)) (V (.E 2 0 (1))) (V (.W 2 0 1)) (V (.E 2 0 (2))) (V (.A 2 0 (-2))) (V (.E 2 0 (-2))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.KW 2 0 1)) (V (.H 2 0 2)) (V (.H 2 0 6)) (V (.H 2 0 4)) (V (.H 2 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 245) = V (.W 1 0 1))
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
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 149))) (.const 2600822924))) (.add (.var (.n 245)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 6) (.shl (.xor (.or (.shr (.var (.n 149)) 5) (.shl (.var (.n 149)) 27)) (.var (.n 149))) 26)) (.or (.shr (.var (.n 149)) 25) (.shl (.var (.n 149)) 7))))) = V (.E 1 0 (2)) :=
  shape6 (env (.n 149)) (env (.n 245)) (V (.E 1 0 (1))) (V (.W 1 0 1)) (V (.E 1 0 (2))) (V (.A 1 0 (-2))) (V (.E 1 0 (-2))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.KW 1 0 1)) (V (.H 1 0 2)) (V (.H 1 0 6)) (V (.H 1 0 4)) (V (.H 1 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem core8_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 244) = V (.W 0 0 1))
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
    E.eval env (.add (.const 1013904242) (.add (.add (.add (.const 528734635) (.xor (.and (.const 3389733619) (.var (.n 148))) (.const 2600822924))) (.add (.var (.n 244)) (.const 1899447441))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 6) (.shl (.xor (.or (.shr (.var (.n 148)) 5) (.shl (.var (.n 148)) 27)) (.var (.n 148))) 26)) (.or (.shr (.var (.n 148)) 25) (.shl (.var (.n 148)) 7))))) = V (.E 0 0 (2)) :=
  shape6 (env (.n 148)) (env (.n 244)) (V (.E 0 0 (1))) (V (.W 0 0 1)) (V (.E 0 0 (2))) (V (.A 0 0 (-2))) (V (.E 0 0 (-2))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.KW 0 0 1)) (V (.H 0 0 2)) (V (.H 0 0 6)) (V (.H 0 0 4)) (V (.H 0 0 5)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem step8 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L8) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K8)) L9 := by
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
  exact invC_of_trees inp env _ T8 L9 (slice_trees_mem prog 4 _ _ 38 K8 K9 T8 slice8 env)
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
      (And.intro ⟨rfl, h183⟩
      (And.intro ⟨rfl, h183⟩
      (And.intro ⟨rfl, h183⟩
      (And.intro ⟨rfl, h183⟩
      (And.intro ⟨rfl, h182⟩
      (And.intro ⟨rfl, h182⟩
      (And.intro ⟨rfl, h182⟩
      (And.intro ⟨rfl, h182⟩
      (And.intro ⟨rfl, h181⟩
      (And.intro ⟨rfl, h181⟩
      (And.intro ⟨rfl, h181⟩
      (And.intro ⟨rfl, h181⟩
      (And.intro ⟨rfl, h180⟩
      (And.intro ⟨rfl, h180⟩
      (And.intro ⟨rfl, h180⟩
      (And.intro ⟨rfl, h180⟩
      (And.intro ⟨rfl, h179⟩
      (And.intro ⟨rfl, h179⟩
      (And.intro ⟨rfl, h179⟩
      (And.intro ⟨rfl, h179⟩
      (And.intro ⟨rfl, h178⟩
      (And.intro ⟨rfl, h178⟩
      (And.intro ⟨rfl, h178⟩
      (And.intro ⟨rfl, h178⟩
      (And.intro ⟨rfl, h177⟩
      (And.intro ⟨rfl, h177⟩
      (And.intro ⟨rfl, h177⟩
      (And.intro ⟨rfl, h177⟩
      (And.intro ⟨rfl, h176⟩
      (And.intro ⟨rfl, h176⟩
      (And.intro ⟨rfl, h176⟩
      (And.intro ⟨rfl, h176⟩
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
      (And.intro ⟨rfl, core8_235 (qv inp) inp env h28 h29 h30 h31⟩
      (And.intro ⟨rfl, core8_234 (qv inp) inp env h24 h25 h26 h27⟩
      (And.intro ⟨rfl, core8_233 (qv inp) inp env h20 h21 h22 h23⟩
      (And.intro ⟨rfl, core8_232 (qv inp) inp env h16 h17 h18 h19⟩
      (And.intro ⟨rfl, core8_231 (qv inp) inp env h12 h13 h14 h15⟩
      (And.intro ⟨rfl, core8_230 (qv inp) inp env h8 h9 h10 h11⟩
      (And.intro ⟨rfl, core8_229 (qv inp) inp env h4 h5 h6 h7⟩
      (And.intro ⟨rfl, core8_228 (qv inp) inp env h0 h1 h2 h3⟩
      (And.intro ⟨rfl, h184⟩
      (And.intro ⟨rfl, h185⟩
      (And.intro ⟨rfl, h186⟩
      (And.intro ⟨rfl, h187⟩
      (And.intro ⟨rfl, h188⟩
      (And.intro ⟨rfl, h189⟩
      (And.intro ⟨rfl, h190⟩
      (And.intro ⟨rfl, h191⟩
      (And.intro ⟨rfl, core8_203 (qv inp) inp env h192 h176 h184 (qA_succI inp 7 0 (1) (by decide)) (qE_initI inp 7 0 2 (-2) (by decide) (by decide)) ((qH0 inp 7 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 7 0 0 (0) (by decide) (by decide)) ((qH0 inp 7 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 7 0 1 (-1) (by decide) (by decide)) ((qH0 inp 7 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 7 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 7 0 0 (0) (by decide) (by decide)) ((qH0 inp 7 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 7 0 1 (-1) (by decide) (by decide)) ((qH0 inp 7 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_202 (qv inp) inp env h193 h177 h185 (qA_succI inp 6 0 (1) (by decide)) (qE_initI inp 6 0 2 (-2) (by decide) (by decide)) ((qH0 inp 6 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 6 0 0 (0) (by decide) (by decide)) ((qH0 inp 6 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 6 0 1 (-1) (by decide) (by decide)) ((qH0 inp 6 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 6 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 6 0 0 (0) (by decide) (by decide)) ((qH0 inp 6 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 6 0 1 (-1) (by decide) (by decide)) ((qH0 inp 6 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_201 (qv inp) inp env h194 h178 h186 (qA_succI inp 5 0 (1) (by decide)) (qE_initI inp 5 0 2 (-2) (by decide) (by decide)) ((qH0 inp 5 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 5 0 0 (0) (by decide) (by decide)) ((qH0 inp 5 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 5 0 1 (-1) (by decide) (by decide)) ((qH0 inp 5 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 5 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 5 0 0 (0) (by decide) (by decide)) ((qH0 inp 5 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 5 0 1 (-1) (by decide) (by decide)) ((qH0 inp 5 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_200 (qv inp) inp env h195 h179 h187 (qA_succI inp 4 0 (1) (by decide)) (qE_initI inp 4 0 2 (-2) (by decide) (by decide)) ((qH0 inp 4 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 4 0 0 (0) (by decide) (by decide)) ((qH0 inp 4 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 4 0 1 (-1) (by decide) (by decide)) ((qH0 inp 4 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 4 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 4 0 0 (0) (by decide) (by decide)) ((qH0 inp 4 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 4 0 1 (-1) (by decide) (by decide)) ((qH0 inp 4 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_199 (qv inp) inp env h196 h180 h188 (qA_succI inp 3 0 (1) (by decide)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 3 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_198 (qv inp) inp env h197 h181 h189 (qA_succI inp 2 0 (1) (by decide)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 2 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_197 (qv inp) inp env h198 h182 h190 (qA_succI inp 1 0 (1) (by decide)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 1 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, core8_196 (qv inp) inp env h199 h183 h191 (qA_succI inp 0 0 (1) (by decide)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 0 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide])) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32))⟩
      (And.intro ⟨rfl, h192⟩
      (And.intro ⟨rfl, h193⟩
      (And.intro ⟨rfl, h194⟩
      (And.intro ⟨rfl, h195⟩
      (And.intro ⟨rfl, h196⟩
      (And.intro ⟨rfl, h197⟩
      (And.intro ⟨rfl, h198⟩
      (And.intro ⟨rfl, h199⟩
      (And.intro ⟨rfl, core8_139 (qv inp) inp env h192 h176 (qE_succI inp 7 0 (1) (by decide)) (qA_initI inp 7 0 2 (-2) (by decide) (by decide)) ((qH0 inp 7 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 7 0 2 (-2) (by decide) (by decide)) ((qH0 inp 7 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 7 0 0 (0) (by decide) (by decide)) ((qH0 inp 7 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 7 0 1 (-1) (by decide) (by decide)) ((qH0 inp 7 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 7 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_138 (qv inp) inp env h193 h177 (qE_succI inp 6 0 (1) (by decide)) (qA_initI inp 6 0 2 (-2) (by decide) (by decide)) ((qH0 inp 6 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 6 0 2 (-2) (by decide) (by decide)) ((qH0 inp 6 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 6 0 0 (0) (by decide) (by decide)) ((qH0 inp 6 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 6 0 1 (-1) (by decide) (by decide)) ((qH0 inp 6 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 6 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_137 (qv inp) inp env h194 h178 (qE_succI inp 5 0 (1) (by decide)) (qA_initI inp 5 0 2 (-2) (by decide) (by decide)) ((qH0 inp 5 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 5 0 2 (-2) (by decide) (by decide)) ((qH0 inp 5 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 5 0 0 (0) (by decide) (by decide)) ((qH0 inp 5 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 5 0 1 (-1) (by decide) (by decide)) ((qH0 inp 5 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 5 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_136 (qv inp) inp env h195 h179 (qE_succI inp 4 0 (1) (by decide)) (qA_initI inp 4 0 2 (-2) (by decide) (by decide)) ((qH0 inp 4 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 4 0 2 (-2) (by decide) (by decide)) ((qH0 inp 4 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 4 0 0 (0) (by decide) (by decide)) ((qH0 inp 4 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 4 0 1 (-1) (by decide) (by decide)) ((qH0 inp 4 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 4 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_135 (qv inp) inp env h196 h180 (qE_succI inp 3 0 (1) (by decide)) (qA_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 3 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_134 (qv inp) inp env h197 h181 (qE_succI inp 2 0 (1) (by decide)) (qA_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 2 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_133 (qv inp) inp env h198 h182 (qE_succI inp 1 0 (1) (by decide)) (qA_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 1 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      (And.intro ⟨rfl, core8_132 (qv inp) inp env h199 h183 (qE_succI inp 0 0 (1) (by decide)) (qA_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) ((qKW inp 0 0 1).trans (by rw [show Spec.K 1 = 1899447441#32 from by decide]))⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
