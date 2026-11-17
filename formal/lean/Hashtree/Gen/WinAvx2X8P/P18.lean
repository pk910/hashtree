import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D18
import Hashtree.Gen.WinAvx2X8P.D17

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice18 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K18 K19 T18 = true := by
  decide +kernel

theorem core18_267 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1131) = V (.W 7 0 14))
    (h1 : env (.n 1130) = V (.W 7 0 14))
    (h2 : env (.n 1129) = V (.W 7 0 14))
    (h3 : env (.n 1128) = V (.W 7 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1131)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1130)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1129)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1128)) 24) (.const 255)) 24))) = V (.W 7 0 14) :=
  shape4 (env (.n 1131)) (env (.n 1130)) (env (.n 1129)) (env (.n 1128)) (V (.W 7 0 14)) h0 h1 h2 h3

theorem core18_266 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1135) = V (.W 6 0 14))
    (h1 : env (.n 1134) = V (.W 6 0 14))
    (h2 : env (.n 1133) = V (.W 6 0 14))
    (h3 : env (.n 1132) = V (.W 6 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1135)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1134)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1133)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1132)) 24) (.const 255)) 24))) = V (.W 6 0 14) :=
  shape4 (env (.n 1135)) (env (.n 1134)) (env (.n 1133)) (env (.n 1132)) (V (.W 6 0 14)) h0 h1 h2 h3

theorem core18_265 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1139) = V (.W 5 0 14))
    (h1 : env (.n 1138) = V (.W 5 0 14))
    (h2 : env (.n 1137) = V (.W 5 0 14))
    (h3 : env (.n 1136) = V (.W 5 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1139)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1138)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1137)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1136)) 24) (.const 255)) 24))) = V (.W 5 0 14) :=
  shape4 (env (.n 1139)) (env (.n 1138)) (env (.n 1137)) (env (.n 1136)) (V (.W 5 0 14)) h0 h1 h2 h3

theorem core18_264 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1143) = V (.W 4 0 14))
    (h1 : env (.n 1142) = V (.W 4 0 14))
    (h2 : env (.n 1141) = V (.W 4 0 14))
    (h3 : env (.n 1140) = V (.W 4 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1143)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1142)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1141)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1140)) 24) (.const 255)) 24))) = V (.W 4 0 14) :=
  shape4 (env (.n 1143)) (env (.n 1142)) (env (.n 1141)) (env (.n 1140)) (V (.W 4 0 14)) h0 h1 h2 h3

theorem core18_263 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1147) = V (.W 3 0 14))
    (h1 : env (.n 1146) = V (.W 3 0 14))
    (h2 : env (.n 1145) = V (.W 3 0 14))
    (h3 : env (.n 1144) = V (.W 3 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1147)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1146)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1145)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1144)) 24) (.const 255)) 24))) = V (.W 3 0 14) :=
  shape4 (env (.n 1147)) (env (.n 1146)) (env (.n 1145)) (env (.n 1144)) (V (.W 3 0 14)) h0 h1 h2 h3

theorem core18_262 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1151) = V (.W 2 0 14))
    (h1 : env (.n 1150) = V (.W 2 0 14))
    (h2 : env (.n 1149) = V (.W 2 0 14))
    (h3 : env (.n 1148) = V (.W 2 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1151)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1150)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1149)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1148)) 24) (.const 255)) 24))) = V (.W 2 0 14) :=
  shape4 (env (.n 1151)) (env (.n 1150)) (env (.n 1149)) (env (.n 1148)) (V (.W 2 0 14)) h0 h1 h2 h3

theorem core18_261 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1155) = V (.W 1 0 14))
    (h1 : env (.n 1154) = V (.W 1 0 14))
    (h2 : env (.n 1153) = V (.W 1 0 14))
    (h3 : env (.n 1152) = V (.W 1 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1155)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1154)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1153)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1152)) 24) (.const 255)) 24))) = V (.W 1 0 14) :=
  shape4 (env (.n 1155)) (env (.n 1154)) (env (.n 1153)) (env (.n 1152)) (V (.W 1 0 14)) h0 h1 h2 h3

theorem core18_260 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1159) = V (.W 0 0 14))
    (h1 : env (.n 1158) = V (.W 0 0 14))
    (h2 : env (.n 1157) = V (.W 0 0 14))
    (h3 : env (.n 1156) = V (.W 0 0 14)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1159)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1158)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1157)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1156)) 24) (.const 255)) 24))) = V (.W 0 0 14) :=
  shape4 (env (.n 1159)) (env (.n 1158)) (env (.n 1157)) (env (.n 1156)) (V (.W 0 0 14)) h0 h1 h2 h3

theorem core18_171 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 171) = V (.E 7 0 (8)))
    (h1 : env (.n 139) = V (.E 7 0 (10)))
    (h2 : env (.n 155) = V (.E 7 0 (9)))
    (h3 : env (.n 123) = V (.E 7 0 (11)))
    (h4 : env (.n 283) = V (.W 7 0 11))
    (h5 : env (.n 187) = V (.A 7 0 (11)))
    (h6 : env (.n 219) = V (.A 7 0 (9)))
    (h7 : env (.n 203) = V (.A 7 0 (10)))
    (h8 : V (.A 7 0 (12)) = (V (.E 7 0 (8)) + Sigma1 (V (.E 7 0 (11))) + Ch (V (.E 7 0 (11))) (V (.E 7 0 (10))) (V (.E 7 0 (9))) + V (.KW 7 0 11)) + (Sigma0 (V (.A 7 0 (11))) + Maj (V (.A 7 0 (11))) (V (.A 7 0 (10))) (V (.A 7 0 (9)))))
    (h9 : V (.KW 7 0 11) = 1426881987#32 + V (.W 7 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 171)) (.xor (.and (.xor (.var (.n 139)) (.var (.n 155))) (.var (.n 123))) (.var (.n 155)))) (.add (.var (.n 283)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 123)) 5) (.shl (.var (.n 123)) 27)) (.var (.n 123))) 6) (.shl (.xor (.or (.shr (.var (.n 123)) 5) (.shl (.var (.n 123)) 27)) (.var (.n 123))) 26)) (.or (.shr (.var (.n 123)) 25) (.shl (.var (.n 123)) 7)))) (.or (.and (.var (.n 187)) (.var (.n 219))) (.and (.xor (.var (.n 187)) (.var (.n 219))) (.var (.n 203))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 187)) 11) (.shl (.var (.n 187)) 21)) (.var (.n 187))) 2) (.shl (.xor (.or (.shr (.var (.n 187)) 11) (.shl (.var (.n 187)) 21)) (.var (.n 187))) 30)) (.or (.shr (.var (.n 187)) 22) (.shl (.var (.n 187)) 10)))) = V (.A 7 0 (12)) :=
  shape26 (env (.n 171)) (env (.n 139)) (env (.n 155)) (env (.n 123)) (env (.n 283)) (env (.n 187)) (env (.n 219)) (env (.n 203)) (V (.E 7 0 (8))) (V (.E 7 0 (10))) (V (.E 7 0 (9))) (V (.E 7 0 (11))) (V (.W 7 0 11)) (V (.A 7 0 (11))) (V (.A 7 0 (9))) (V (.A 7 0 (10))) (V (.A 7 0 (12))) (V (.KW 7 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_170 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 170) = V (.E 6 0 (8)))
    (h1 : env (.n 138) = V (.E 6 0 (10)))
    (h2 : env (.n 154) = V (.E 6 0 (9)))
    (h3 : env (.n 122) = V (.E 6 0 (11)))
    (h4 : env (.n 282) = V (.W 6 0 11))
    (h5 : env (.n 186) = V (.A 6 0 (11)))
    (h6 : env (.n 218) = V (.A 6 0 (9)))
    (h7 : env (.n 202) = V (.A 6 0 (10)))
    (h8 : V (.A 6 0 (12)) = (V (.E 6 0 (8)) + Sigma1 (V (.E 6 0 (11))) + Ch (V (.E 6 0 (11))) (V (.E 6 0 (10))) (V (.E 6 0 (9))) + V (.KW 6 0 11)) + (Sigma0 (V (.A 6 0 (11))) + Maj (V (.A 6 0 (11))) (V (.A 6 0 (10))) (V (.A 6 0 (9)))))
    (h9 : V (.KW 6 0 11) = 1426881987#32 + V (.W 6 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 170)) (.xor (.and (.xor (.var (.n 138)) (.var (.n 154))) (.var (.n 122))) (.var (.n 154)))) (.add (.var (.n 282)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 122)) 5) (.shl (.var (.n 122)) 27)) (.var (.n 122))) 6) (.shl (.xor (.or (.shr (.var (.n 122)) 5) (.shl (.var (.n 122)) 27)) (.var (.n 122))) 26)) (.or (.shr (.var (.n 122)) 25) (.shl (.var (.n 122)) 7)))) (.or (.and (.var (.n 186)) (.var (.n 218))) (.and (.xor (.var (.n 186)) (.var (.n 218))) (.var (.n 202))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 186)) 11) (.shl (.var (.n 186)) 21)) (.var (.n 186))) 2) (.shl (.xor (.or (.shr (.var (.n 186)) 11) (.shl (.var (.n 186)) 21)) (.var (.n 186))) 30)) (.or (.shr (.var (.n 186)) 22) (.shl (.var (.n 186)) 10)))) = V (.A 6 0 (12)) :=
  shape26 (env (.n 170)) (env (.n 138)) (env (.n 154)) (env (.n 122)) (env (.n 282)) (env (.n 186)) (env (.n 218)) (env (.n 202)) (V (.E 6 0 (8))) (V (.E 6 0 (10))) (V (.E 6 0 (9))) (V (.E 6 0 (11))) (V (.W 6 0 11)) (V (.A 6 0 (11))) (V (.A 6 0 (9))) (V (.A 6 0 (10))) (V (.A 6 0 (12))) (V (.KW 6 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_169 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 169) = V (.E 5 0 (8)))
    (h1 : env (.n 137) = V (.E 5 0 (10)))
    (h2 : env (.n 153) = V (.E 5 0 (9)))
    (h3 : env (.n 121) = V (.E 5 0 (11)))
    (h4 : env (.n 281) = V (.W 5 0 11))
    (h5 : env (.n 185) = V (.A 5 0 (11)))
    (h6 : env (.n 217) = V (.A 5 0 (9)))
    (h7 : env (.n 201) = V (.A 5 0 (10)))
    (h8 : V (.A 5 0 (12)) = (V (.E 5 0 (8)) + Sigma1 (V (.E 5 0 (11))) + Ch (V (.E 5 0 (11))) (V (.E 5 0 (10))) (V (.E 5 0 (9))) + V (.KW 5 0 11)) + (Sigma0 (V (.A 5 0 (11))) + Maj (V (.A 5 0 (11))) (V (.A 5 0 (10))) (V (.A 5 0 (9)))))
    (h9 : V (.KW 5 0 11) = 1426881987#32 + V (.W 5 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 169)) (.xor (.and (.xor (.var (.n 137)) (.var (.n 153))) (.var (.n 121))) (.var (.n 153)))) (.add (.var (.n 281)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 121)) 5) (.shl (.var (.n 121)) 27)) (.var (.n 121))) 6) (.shl (.xor (.or (.shr (.var (.n 121)) 5) (.shl (.var (.n 121)) 27)) (.var (.n 121))) 26)) (.or (.shr (.var (.n 121)) 25) (.shl (.var (.n 121)) 7)))) (.or (.and (.var (.n 185)) (.var (.n 217))) (.and (.xor (.var (.n 185)) (.var (.n 217))) (.var (.n 201))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 185)) 11) (.shl (.var (.n 185)) 21)) (.var (.n 185))) 2) (.shl (.xor (.or (.shr (.var (.n 185)) 11) (.shl (.var (.n 185)) 21)) (.var (.n 185))) 30)) (.or (.shr (.var (.n 185)) 22) (.shl (.var (.n 185)) 10)))) = V (.A 5 0 (12)) :=
  shape26 (env (.n 169)) (env (.n 137)) (env (.n 153)) (env (.n 121)) (env (.n 281)) (env (.n 185)) (env (.n 217)) (env (.n 201)) (V (.E 5 0 (8))) (V (.E 5 0 (10))) (V (.E 5 0 (9))) (V (.E 5 0 (11))) (V (.W 5 0 11)) (V (.A 5 0 (11))) (V (.A 5 0 (9))) (V (.A 5 0 (10))) (V (.A 5 0 (12))) (V (.KW 5 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_168 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 168) = V (.E 4 0 (8)))
    (h1 : env (.n 136) = V (.E 4 0 (10)))
    (h2 : env (.n 152) = V (.E 4 0 (9)))
    (h3 : env (.n 120) = V (.E 4 0 (11)))
    (h4 : env (.n 280) = V (.W 4 0 11))
    (h5 : env (.n 184) = V (.A 4 0 (11)))
    (h6 : env (.n 216) = V (.A 4 0 (9)))
    (h7 : env (.n 200) = V (.A 4 0 (10)))
    (h8 : V (.A 4 0 (12)) = (V (.E 4 0 (8)) + Sigma1 (V (.E 4 0 (11))) + Ch (V (.E 4 0 (11))) (V (.E 4 0 (10))) (V (.E 4 0 (9))) + V (.KW 4 0 11)) + (Sigma0 (V (.A 4 0 (11))) + Maj (V (.A 4 0 (11))) (V (.A 4 0 (10))) (V (.A 4 0 (9)))))
    (h9 : V (.KW 4 0 11) = 1426881987#32 + V (.W 4 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 168)) (.xor (.and (.xor (.var (.n 136)) (.var (.n 152))) (.var (.n 120))) (.var (.n 152)))) (.add (.var (.n 280)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 120)) 5) (.shl (.var (.n 120)) 27)) (.var (.n 120))) 6) (.shl (.xor (.or (.shr (.var (.n 120)) 5) (.shl (.var (.n 120)) 27)) (.var (.n 120))) 26)) (.or (.shr (.var (.n 120)) 25) (.shl (.var (.n 120)) 7)))) (.or (.and (.var (.n 184)) (.var (.n 216))) (.and (.xor (.var (.n 184)) (.var (.n 216))) (.var (.n 200))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 184)) 11) (.shl (.var (.n 184)) 21)) (.var (.n 184))) 2) (.shl (.xor (.or (.shr (.var (.n 184)) 11) (.shl (.var (.n 184)) 21)) (.var (.n 184))) 30)) (.or (.shr (.var (.n 184)) 22) (.shl (.var (.n 184)) 10)))) = V (.A 4 0 (12)) :=
  shape26 (env (.n 168)) (env (.n 136)) (env (.n 152)) (env (.n 120)) (env (.n 280)) (env (.n 184)) (env (.n 216)) (env (.n 200)) (V (.E 4 0 (8))) (V (.E 4 0 (10))) (V (.E 4 0 (9))) (V (.E 4 0 (11))) (V (.W 4 0 11)) (V (.A 4 0 (11))) (V (.A 4 0 (9))) (V (.A 4 0 (10))) (V (.A 4 0 (12))) (V (.KW 4 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 167) = V (.E 3 0 (8)))
    (h1 : env (.n 135) = V (.E 3 0 (10)))
    (h2 : env (.n 151) = V (.E 3 0 (9)))
    (h3 : env (.n 119) = V (.E 3 0 (11)))
    (h4 : env (.n 279) = V (.W 3 0 11))
    (h5 : env (.n 183) = V (.A 3 0 (11)))
    (h6 : env (.n 215) = V (.A 3 0 (9)))
    (h7 : env (.n 199) = V (.A 3 0 (10)))
    (h8 : V (.A 3 0 (12)) = (V (.E 3 0 (8)) + Sigma1 (V (.E 3 0 (11))) + Ch (V (.E 3 0 (11))) (V (.E 3 0 (10))) (V (.E 3 0 (9))) + V (.KW 3 0 11)) + (Sigma0 (V (.A 3 0 (11))) + Maj (V (.A 3 0 (11))) (V (.A 3 0 (10))) (V (.A 3 0 (9)))))
    (h9 : V (.KW 3 0 11) = 1426881987#32 + V (.W 3 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 167)) (.xor (.and (.xor (.var (.n 135)) (.var (.n 151))) (.var (.n 119))) (.var (.n 151)))) (.add (.var (.n 279)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 6) (.shl (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 26)) (.or (.shr (.var (.n 119)) 25) (.shl (.var (.n 119)) 7)))) (.or (.and (.var (.n 183)) (.var (.n 215))) (.and (.xor (.var (.n 183)) (.var (.n 215))) (.var (.n 199))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 183)) 11) (.shl (.var (.n 183)) 21)) (.var (.n 183))) 2) (.shl (.xor (.or (.shr (.var (.n 183)) 11) (.shl (.var (.n 183)) 21)) (.var (.n 183))) 30)) (.or (.shr (.var (.n 183)) 22) (.shl (.var (.n 183)) 10)))) = V (.A 3 0 (12)) :=
  shape26 (env (.n 167)) (env (.n 135)) (env (.n 151)) (env (.n 119)) (env (.n 279)) (env (.n 183)) (env (.n 215)) (env (.n 199)) (V (.E 3 0 (8))) (V (.E 3 0 (10))) (V (.E 3 0 (9))) (V (.E 3 0 (11))) (V (.W 3 0 11)) (V (.A 3 0 (11))) (V (.A 3 0 (9))) (V (.A 3 0 (10))) (V (.A 3 0 (12))) (V (.KW 3 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 166) = V (.E 2 0 (8)))
    (h1 : env (.n 134) = V (.E 2 0 (10)))
    (h2 : env (.n 150) = V (.E 2 0 (9)))
    (h3 : env (.n 118) = V (.E 2 0 (11)))
    (h4 : env (.n 278) = V (.W 2 0 11))
    (h5 : env (.n 182) = V (.A 2 0 (11)))
    (h6 : env (.n 214) = V (.A 2 0 (9)))
    (h7 : env (.n 198) = V (.A 2 0 (10)))
    (h8 : V (.A 2 0 (12)) = (V (.E 2 0 (8)) + Sigma1 (V (.E 2 0 (11))) + Ch (V (.E 2 0 (11))) (V (.E 2 0 (10))) (V (.E 2 0 (9))) + V (.KW 2 0 11)) + (Sigma0 (V (.A 2 0 (11))) + Maj (V (.A 2 0 (11))) (V (.A 2 0 (10))) (V (.A 2 0 (9)))))
    (h9 : V (.KW 2 0 11) = 1426881987#32 + V (.W 2 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 166)) (.xor (.and (.xor (.var (.n 134)) (.var (.n 150))) (.var (.n 118))) (.var (.n 150)))) (.add (.var (.n 278)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 6) (.shl (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 26)) (.or (.shr (.var (.n 118)) 25) (.shl (.var (.n 118)) 7)))) (.or (.and (.var (.n 182)) (.var (.n 214))) (.and (.xor (.var (.n 182)) (.var (.n 214))) (.var (.n 198))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 182)) 11) (.shl (.var (.n 182)) 21)) (.var (.n 182))) 2) (.shl (.xor (.or (.shr (.var (.n 182)) 11) (.shl (.var (.n 182)) 21)) (.var (.n 182))) 30)) (.or (.shr (.var (.n 182)) 22) (.shl (.var (.n 182)) 10)))) = V (.A 2 0 (12)) :=
  shape26 (env (.n 166)) (env (.n 134)) (env (.n 150)) (env (.n 118)) (env (.n 278)) (env (.n 182)) (env (.n 214)) (env (.n 198)) (V (.E 2 0 (8))) (V (.E 2 0 (10))) (V (.E 2 0 (9))) (V (.E 2 0 (11))) (V (.W 2 0 11)) (V (.A 2 0 (11))) (V (.A 2 0 (9))) (V (.A 2 0 (10))) (V (.A 2 0 (12))) (V (.KW 2 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 165) = V (.E 1 0 (8)))
    (h1 : env (.n 133) = V (.E 1 0 (10)))
    (h2 : env (.n 149) = V (.E 1 0 (9)))
    (h3 : env (.n 117) = V (.E 1 0 (11)))
    (h4 : env (.n 277) = V (.W 1 0 11))
    (h5 : env (.n 181) = V (.A 1 0 (11)))
    (h6 : env (.n 213) = V (.A 1 0 (9)))
    (h7 : env (.n 197) = V (.A 1 0 (10)))
    (h8 : V (.A 1 0 (12)) = (V (.E 1 0 (8)) + Sigma1 (V (.E 1 0 (11))) + Ch (V (.E 1 0 (11))) (V (.E 1 0 (10))) (V (.E 1 0 (9))) + V (.KW 1 0 11)) + (Sigma0 (V (.A 1 0 (11))) + Maj (V (.A 1 0 (11))) (V (.A 1 0 (10))) (V (.A 1 0 (9)))))
    (h9 : V (.KW 1 0 11) = 1426881987#32 + V (.W 1 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 165)) (.xor (.and (.xor (.var (.n 133)) (.var (.n 149))) (.var (.n 117))) (.var (.n 149)))) (.add (.var (.n 277)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 6) (.shl (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 26)) (.or (.shr (.var (.n 117)) 25) (.shl (.var (.n 117)) 7)))) (.or (.and (.var (.n 181)) (.var (.n 213))) (.and (.xor (.var (.n 181)) (.var (.n 213))) (.var (.n 197))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 181)) 11) (.shl (.var (.n 181)) 21)) (.var (.n 181))) 2) (.shl (.xor (.or (.shr (.var (.n 181)) 11) (.shl (.var (.n 181)) 21)) (.var (.n 181))) 30)) (.or (.shr (.var (.n 181)) 22) (.shl (.var (.n 181)) 10)))) = V (.A 1 0 (12)) :=
  shape26 (env (.n 165)) (env (.n 133)) (env (.n 149)) (env (.n 117)) (env (.n 277)) (env (.n 181)) (env (.n 213)) (env (.n 197)) (V (.E 1 0 (8))) (V (.E 1 0 (10))) (V (.E 1 0 (9))) (V (.E 1 0 (11))) (V (.W 1 0 11)) (V (.A 1 0 (11))) (V (.A 1 0 (9))) (V (.A 1 0 (10))) (V (.A 1 0 (12))) (V (.KW 1 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 164) = V (.E 0 0 (8)))
    (h1 : env (.n 132) = V (.E 0 0 (10)))
    (h2 : env (.n 148) = V (.E 0 0 (9)))
    (h3 : env (.n 116) = V (.E 0 0 (11)))
    (h4 : env (.n 276) = V (.W 0 0 11))
    (h5 : env (.n 180) = V (.A 0 0 (11)))
    (h6 : env (.n 212) = V (.A 0 0 (9)))
    (h7 : env (.n 196) = V (.A 0 0 (10)))
    (h8 : V (.A 0 0 (12)) = (V (.E 0 0 (8)) + Sigma1 (V (.E 0 0 (11))) + Ch (V (.E 0 0 (11))) (V (.E 0 0 (10))) (V (.E 0 0 (9))) + V (.KW 0 0 11)) + (Sigma0 (V (.A 0 0 (11))) + Maj (V (.A 0 0 (11))) (V (.A 0 0 (10))) (V (.A 0 0 (9)))))
    (h9 : V (.KW 0 0 11) = 1426881987#32 + V (.W 0 0 11)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 164)) (.xor (.and (.xor (.var (.n 132)) (.var (.n 148))) (.var (.n 116))) (.var (.n 148)))) (.add (.var (.n 276)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 6) (.shl (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 26)) (.or (.shr (.var (.n 116)) 25) (.shl (.var (.n 116)) 7)))) (.or (.and (.var (.n 180)) (.var (.n 212))) (.and (.xor (.var (.n 180)) (.var (.n 212))) (.var (.n 196))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 180)) 11) (.shl (.var (.n 180)) 21)) (.var (.n 180))) 2) (.shl (.xor (.or (.shr (.var (.n 180)) 11) (.shl (.var (.n 180)) 21)) (.var (.n 180))) 30)) (.or (.shr (.var (.n 180)) 22) (.shl (.var (.n 180)) 10)))) = V (.A 0 0 (12)) :=
  shape26 (env (.n 164)) (env (.n 132)) (env (.n 148)) (env (.n 116)) (env (.n 276)) (env (.n 180)) (env (.n 212)) (env (.n 196)) (V (.E 0 0 (8))) (V (.E 0 0 (10))) (V (.E 0 0 (9))) (V (.E 0 0 (11))) (V (.W 0 0 11)) (V (.A 0 0 (11))) (V (.A 0 0 (9))) (V (.A 0 0 (10))) (V (.A 0 0 (12))) (V (.KW 0 0 11)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core18_107 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 107) = V (.A 7 0 (8)))
    (h1 : env (.n 171) = V (.E 7 0 (8)))
    (h2 : env (.n 139) = V (.E 7 0 (10)))
    (h3 : env (.n 155) = V (.E 7 0 (9)))
    (h4 : env (.n 123) = V (.E 7 0 (11)))
    (h5 : env (.n 283) = V (.W 7 0 11))
    (h6 : V (.E 7 0 (12)) = V (.A 7 0 (8)) + (V (.E 7 0 (8)) + Sigma1 (V (.E 7 0 (11))) + Ch (V (.E 7 0 (11))) (V (.E 7 0 (10))) (V (.E 7 0 (9))) + V (.KW 7 0 11)))
    (h7 : V (.KW 7 0 11) = 1426881987#32 + V (.W 7 0 11)) :
    E.eval env (.add (.var (.n 107)) (.add (.add (.add (.var (.n 171)) (.xor (.and (.xor (.var (.n 139)) (.var (.n 155))) (.var (.n 123))) (.var (.n 155)))) (.add (.var (.n 283)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 123)) 5) (.shl (.var (.n 123)) 27)) (.var (.n 123))) 6) (.shl (.xor (.or (.shr (.var (.n 123)) 5) (.shl (.var (.n 123)) 27)) (.var (.n 123))) 26)) (.or (.shr (.var (.n 123)) 25) (.shl (.var (.n 123)) 7))))) = V (.E 7 0 (12)) :=
  shape27 (env (.n 107)) (env (.n 171)) (env (.n 139)) (env (.n 155)) (env (.n 123)) (env (.n 283)) (V (.A 7 0 (8))) (V (.E 7 0 (8))) (V (.E 7 0 (10))) (V (.E 7 0 (9))) (V (.E 7 0 (11))) (V (.W 7 0 11)) (V (.E 7 0 (12))) (V (.KW 7 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_106 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 106) = V (.A 6 0 (8)))
    (h1 : env (.n 170) = V (.E 6 0 (8)))
    (h2 : env (.n 138) = V (.E 6 0 (10)))
    (h3 : env (.n 154) = V (.E 6 0 (9)))
    (h4 : env (.n 122) = V (.E 6 0 (11)))
    (h5 : env (.n 282) = V (.W 6 0 11))
    (h6 : V (.E 6 0 (12)) = V (.A 6 0 (8)) + (V (.E 6 0 (8)) + Sigma1 (V (.E 6 0 (11))) + Ch (V (.E 6 0 (11))) (V (.E 6 0 (10))) (V (.E 6 0 (9))) + V (.KW 6 0 11)))
    (h7 : V (.KW 6 0 11) = 1426881987#32 + V (.W 6 0 11)) :
    E.eval env (.add (.var (.n 106)) (.add (.add (.add (.var (.n 170)) (.xor (.and (.xor (.var (.n 138)) (.var (.n 154))) (.var (.n 122))) (.var (.n 154)))) (.add (.var (.n 282)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 122)) 5) (.shl (.var (.n 122)) 27)) (.var (.n 122))) 6) (.shl (.xor (.or (.shr (.var (.n 122)) 5) (.shl (.var (.n 122)) 27)) (.var (.n 122))) 26)) (.or (.shr (.var (.n 122)) 25) (.shl (.var (.n 122)) 7))))) = V (.E 6 0 (12)) :=
  shape27 (env (.n 106)) (env (.n 170)) (env (.n 138)) (env (.n 154)) (env (.n 122)) (env (.n 282)) (V (.A 6 0 (8))) (V (.E 6 0 (8))) (V (.E 6 0 (10))) (V (.E 6 0 (9))) (V (.E 6 0 (11))) (V (.W 6 0 11)) (V (.E 6 0 (12))) (V (.KW 6 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_105 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 105) = V (.A 5 0 (8)))
    (h1 : env (.n 169) = V (.E 5 0 (8)))
    (h2 : env (.n 137) = V (.E 5 0 (10)))
    (h3 : env (.n 153) = V (.E 5 0 (9)))
    (h4 : env (.n 121) = V (.E 5 0 (11)))
    (h5 : env (.n 281) = V (.W 5 0 11))
    (h6 : V (.E 5 0 (12)) = V (.A 5 0 (8)) + (V (.E 5 0 (8)) + Sigma1 (V (.E 5 0 (11))) + Ch (V (.E 5 0 (11))) (V (.E 5 0 (10))) (V (.E 5 0 (9))) + V (.KW 5 0 11)))
    (h7 : V (.KW 5 0 11) = 1426881987#32 + V (.W 5 0 11)) :
    E.eval env (.add (.var (.n 105)) (.add (.add (.add (.var (.n 169)) (.xor (.and (.xor (.var (.n 137)) (.var (.n 153))) (.var (.n 121))) (.var (.n 153)))) (.add (.var (.n 281)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 121)) 5) (.shl (.var (.n 121)) 27)) (.var (.n 121))) 6) (.shl (.xor (.or (.shr (.var (.n 121)) 5) (.shl (.var (.n 121)) 27)) (.var (.n 121))) 26)) (.or (.shr (.var (.n 121)) 25) (.shl (.var (.n 121)) 7))))) = V (.E 5 0 (12)) :=
  shape27 (env (.n 105)) (env (.n 169)) (env (.n 137)) (env (.n 153)) (env (.n 121)) (env (.n 281)) (V (.A 5 0 (8))) (V (.E 5 0 (8))) (V (.E 5 0 (10))) (V (.E 5 0 (9))) (V (.E 5 0 (11))) (V (.W 5 0 11)) (V (.E 5 0 (12))) (V (.KW 5 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_104 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 104) = V (.A 4 0 (8)))
    (h1 : env (.n 168) = V (.E 4 0 (8)))
    (h2 : env (.n 136) = V (.E 4 0 (10)))
    (h3 : env (.n 152) = V (.E 4 0 (9)))
    (h4 : env (.n 120) = V (.E 4 0 (11)))
    (h5 : env (.n 280) = V (.W 4 0 11))
    (h6 : V (.E 4 0 (12)) = V (.A 4 0 (8)) + (V (.E 4 0 (8)) + Sigma1 (V (.E 4 0 (11))) + Ch (V (.E 4 0 (11))) (V (.E 4 0 (10))) (V (.E 4 0 (9))) + V (.KW 4 0 11)))
    (h7 : V (.KW 4 0 11) = 1426881987#32 + V (.W 4 0 11)) :
    E.eval env (.add (.var (.n 104)) (.add (.add (.add (.var (.n 168)) (.xor (.and (.xor (.var (.n 136)) (.var (.n 152))) (.var (.n 120))) (.var (.n 152)))) (.add (.var (.n 280)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 120)) 5) (.shl (.var (.n 120)) 27)) (.var (.n 120))) 6) (.shl (.xor (.or (.shr (.var (.n 120)) 5) (.shl (.var (.n 120)) 27)) (.var (.n 120))) 26)) (.or (.shr (.var (.n 120)) 25) (.shl (.var (.n 120)) 7))))) = V (.E 4 0 (12)) :=
  shape27 (env (.n 104)) (env (.n 168)) (env (.n 136)) (env (.n 152)) (env (.n 120)) (env (.n 280)) (V (.A 4 0 (8))) (V (.E 4 0 (8))) (V (.E 4 0 (10))) (V (.E 4 0 (9))) (V (.E 4 0 (11))) (V (.W 4 0 11)) (V (.E 4 0 (12))) (V (.KW 4 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 103) = V (.A 3 0 (8)))
    (h1 : env (.n 167) = V (.E 3 0 (8)))
    (h2 : env (.n 135) = V (.E 3 0 (10)))
    (h3 : env (.n 151) = V (.E 3 0 (9)))
    (h4 : env (.n 119) = V (.E 3 0 (11)))
    (h5 : env (.n 279) = V (.W 3 0 11))
    (h6 : V (.E 3 0 (12)) = V (.A 3 0 (8)) + (V (.E 3 0 (8)) + Sigma1 (V (.E 3 0 (11))) + Ch (V (.E 3 0 (11))) (V (.E 3 0 (10))) (V (.E 3 0 (9))) + V (.KW 3 0 11)))
    (h7 : V (.KW 3 0 11) = 1426881987#32 + V (.W 3 0 11)) :
    E.eval env (.add (.var (.n 103)) (.add (.add (.add (.var (.n 167)) (.xor (.and (.xor (.var (.n 135)) (.var (.n 151))) (.var (.n 119))) (.var (.n 151)))) (.add (.var (.n 279)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 6) (.shl (.xor (.or (.shr (.var (.n 119)) 5) (.shl (.var (.n 119)) 27)) (.var (.n 119))) 26)) (.or (.shr (.var (.n 119)) 25) (.shl (.var (.n 119)) 7))))) = V (.E 3 0 (12)) :=
  shape27 (env (.n 103)) (env (.n 167)) (env (.n 135)) (env (.n 151)) (env (.n 119)) (env (.n 279)) (V (.A 3 0 (8))) (V (.E 3 0 (8))) (V (.E 3 0 (10))) (V (.E 3 0 (9))) (V (.E 3 0 (11))) (V (.W 3 0 11)) (V (.E 3 0 (12))) (V (.KW 3 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 102) = V (.A 2 0 (8)))
    (h1 : env (.n 166) = V (.E 2 0 (8)))
    (h2 : env (.n 134) = V (.E 2 0 (10)))
    (h3 : env (.n 150) = V (.E 2 0 (9)))
    (h4 : env (.n 118) = V (.E 2 0 (11)))
    (h5 : env (.n 278) = V (.W 2 0 11))
    (h6 : V (.E 2 0 (12)) = V (.A 2 0 (8)) + (V (.E 2 0 (8)) + Sigma1 (V (.E 2 0 (11))) + Ch (V (.E 2 0 (11))) (V (.E 2 0 (10))) (V (.E 2 0 (9))) + V (.KW 2 0 11)))
    (h7 : V (.KW 2 0 11) = 1426881987#32 + V (.W 2 0 11)) :
    E.eval env (.add (.var (.n 102)) (.add (.add (.add (.var (.n 166)) (.xor (.and (.xor (.var (.n 134)) (.var (.n 150))) (.var (.n 118))) (.var (.n 150)))) (.add (.var (.n 278)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 6) (.shl (.xor (.or (.shr (.var (.n 118)) 5) (.shl (.var (.n 118)) 27)) (.var (.n 118))) 26)) (.or (.shr (.var (.n 118)) 25) (.shl (.var (.n 118)) 7))))) = V (.E 2 0 (12)) :=
  shape27 (env (.n 102)) (env (.n 166)) (env (.n 134)) (env (.n 150)) (env (.n 118)) (env (.n 278)) (V (.A 2 0 (8))) (V (.E 2 0 (8))) (V (.E 2 0 (10))) (V (.E 2 0 (9))) (V (.E 2 0 (11))) (V (.W 2 0 11)) (V (.E 2 0 (12))) (V (.KW 2 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 101) = V (.A 1 0 (8)))
    (h1 : env (.n 165) = V (.E 1 0 (8)))
    (h2 : env (.n 133) = V (.E 1 0 (10)))
    (h3 : env (.n 149) = V (.E 1 0 (9)))
    (h4 : env (.n 117) = V (.E 1 0 (11)))
    (h5 : env (.n 277) = V (.W 1 0 11))
    (h6 : V (.E 1 0 (12)) = V (.A 1 0 (8)) + (V (.E 1 0 (8)) + Sigma1 (V (.E 1 0 (11))) + Ch (V (.E 1 0 (11))) (V (.E 1 0 (10))) (V (.E 1 0 (9))) + V (.KW 1 0 11)))
    (h7 : V (.KW 1 0 11) = 1426881987#32 + V (.W 1 0 11)) :
    E.eval env (.add (.var (.n 101)) (.add (.add (.add (.var (.n 165)) (.xor (.and (.xor (.var (.n 133)) (.var (.n 149))) (.var (.n 117))) (.var (.n 149)))) (.add (.var (.n 277)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 6) (.shl (.xor (.or (.shr (.var (.n 117)) 5) (.shl (.var (.n 117)) 27)) (.var (.n 117))) 26)) (.or (.shr (.var (.n 117)) 25) (.shl (.var (.n 117)) 7))))) = V (.E 1 0 (12)) :=
  shape27 (env (.n 101)) (env (.n 165)) (env (.n 133)) (env (.n 149)) (env (.n 117)) (env (.n 277)) (V (.A 1 0 (8))) (V (.E 1 0 (8))) (V (.E 1 0 (10))) (V (.E 1 0 (9))) (V (.E 1 0 (11))) (V (.W 1 0 11)) (V (.E 1 0 (12))) (V (.KW 1 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core18_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 100) = V (.A 0 0 (8)))
    (h1 : env (.n 164) = V (.E 0 0 (8)))
    (h2 : env (.n 132) = V (.E 0 0 (10)))
    (h3 : env (.n 148) = V (.E 0 0 (9)))
    (h4 : env (.n 116) = V (.E 0 0 (11)))
    (h5 : env (.n 276) = V (.W 0 0 11))
    (h6 : V (.E 0 0 (12)) = V (.A 0 0 (8)) + (V (.E 0 0 (8)) + Sigma1 (V (.E 0 0 (11))) + Ch (V (.E 0 0 (11))) (V (.E 0 0 (10))) (V (.E 0 0 (9))) + V (.KW 0 0 11)))
    (h7 : V (.KW 0 0 11) = 1426881987#32 + V (.W 0 0 11)) :
    E.eval env (.add (.var (.n 100)) (.add (.add (.add (.var (.n 164)) (.xor (.and (.xor (.var (.n 132)) (.var (.n 148))) (.var (.n 116))) (.var (.n 148)))) (.add (.var (.n 276)) (.const 1426881987))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 6) (.shl (.xor (.or (.shr (.var (.n 116)) 5) (.shl (.var (.n 116)) 27)) (.var (.n 116))) 26)) (.or (.shr (.var (.n 116)) 25) (.shl (.var (.n 116)) 7))))) = V (.E 0 0 (12)) :=
  shape27 (env (.n 100)) (env (.n 164)) (env (.n 132)) (env (.n 148)) (env (.n 116)) (env (.n 276)) (V (.A 0 0 (8))) (V (.E 0 0 (8))) (V (.E 0 0 (10))) (V (.E 0 0 (9))) (V (.E 0 0 (11))) (V (.W 0 0 11)) (V (.E 0 0 (12))) (V (.KW 0 0 11)) h0 h1 h2 h3 h4 h5 h6 h7

theorem step18 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L18) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K18)) L19 := by
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
  have h292 := hI.1; have hI := hI.2
  have h293 := hI.1; have hI := hI.2
  have h294 := hI.1; have hI := hI.2
  have h295 := hI.1; have hI := hI.2
  have h296 := hI.1; have hI := hI.2
  have h297 := hI.1; have hI := hI.2
  have h298 := hI.1; have hI := hI.2
  have h299 := hI.1; have hI := hI.2
  have h300 := hI.1; have hI := hI.2
  have h301 := hI.1; have hI := hI.2
  have h302 := hI.1; have hI := hI.2
  have h303 := hI.1; have hI := hI.2
  have h304 := hI.1; have hI := hI.2
  have h305 := hI.1; have hI := hI.2
  have h306 := hI.1; have hI := hI.2
  have h307 := hI.1; have hI := hI.2
  have h308 := hI.1; have hI := hI.2
  have h309 := hI.1; have hI := hI.2
  have h310 := hI.1; have hI := hI.2
  have h311 := hI.1; have hI := hI.2
  have h312 := hI.1; have hI := hI.2
  have h313 := hI.1; have hI := hI.2
  have h314 := hI.1; have hI := hI.2
  have h315 := hI.1; have hI := hI.2
  have h316 := hI.1; have hI := hI.2
  have h317 := hI.1; have hI := hI.2
  have h318 := hI.1; have hI := hI.2
  have h319 := hI.1; have hI := hI.2
  have h320 := hI.1; have hI := hI.2
  have h321 := hI.1; have hI := hI.2
  have h322 := hI.1; have hI := hI.2
  have h323 := hI.1; have hI := hI.2
  have h324 := hI.1; have hI := hI.2
  have h325 := hI.1; have hI := hI.2
  have h326 := hI.1; have hI := hI.2
  have h327 := hI.1; have hI := hI.2
  have h328 := hI.1; have hI := hI.2
  have h329 := hI.1; have hI := hI.2
  have h330 := hI.1; have hI := hI.2
  have h331 := hI.1; have hI := hI.2
  have h332 := hI.1; have hI := hI.2
  have h333 := hI.1; have hI := hI.2
  have h334 := hI.1; have hI := hI.2
  have h335 := hI.1; have hI := hI.2
  have h336 := hI.1; have hI := hI.2
  have h337 := hI.1; have hI := hI.2
  have h338 := hI.1; have hI := hI.2
  have h339 := hI.1; have hI := hI.2
  have h340 := hI.1; have hI := hI.2
  have h341 := hI.1; have hI := hI.2
  have h342 := hI.1; have hI := hI.2
  have h343 := hI.1; have hI := hI.2
  have h344 := hI.1; have hI := hI.2
  have h345 := hI.1; have hI := hI.2
  have h346 := hI.1; have hI := hI.2
  have h347 := hI.1; have hI := hI.2
  have h348 := hI.1; have hI := hI.2
  have h349 := hI.1; have hI := hI.2
  have h350 := hI.1; have hI := hI.2
  have h351 := hI.1; have hI := hI.2
  have h352 := hI.1; have hI := hI.2
  have h353 := hI.1; have hI := hI.2
  have h354 := hI.1; have hI := hI.2
  have h355 := hI.1; have hI := hI.2
  have h356 := hI.1; have hI := hI.2
  have h357 := hI.1; have hI := hI.2
  have h358 := hI.1; have hI := hI.2
  have h359 := hI.1; have hI := hI.2
  have h360 := hI.1; have hI := hI.2
  have h361 := hI.1; have hI := hI.2
  have h362 := hI.1; have hI := hI.2
  have h363 := hI.1; have hI := hI.2
  have h364 := hI.1; have hI := hI.2
  have h365 := hI.1; have hI := hI.2
  have h366 := hI.1; have hI := hI.2
  have h367 := hI.1; have hI := hI.2
  have h368 := hI.1; have hI := hI.2
  have h369 := hI.1; have hI := hI.2
  have h370 := hI.1; have hI := hI.2
  have h371 := hI.1; have hI := hI.2
  have h372 := hI.1; have hI := hI.2
  have h373 := hI.1; have hI := hI.2
  have h374 := hI.1; have hI := hI.2
  have h375 := hI.1; have hI := hI.2
  have h376 := hI.1; have hI := hI.2
  have h377 := hI.1; have hI := hI.2
  have h378 := hI.1; have hI := hI.2
  have h379 := hI.1; have hI := hI.2
  have h380 := hI.1; have hI := hI.2
  have h381 := hI.1; have hI := hI.2
  have h382 := hI.1; have hI := hI.2
  have h383 := hI.1; have hI := hI.2
  have h384 := hI.1; have hI := hI.2
  have h385 := hI.1; have hI := hI.2
  have h386 := hI.1; have hI := hI.2
  have h387 := hI.1; have hI := hI.2
  have h388 := hI.1; have hI := hI.2
  have h389 := hI.1; have hI := hI.2
  have h390 := hI.1; have hI := hI.2
  have h391 := hI.1; have hI := hI.2
  have h392 := hI.1; have hI := hI.2
  have h393 := hI.1; have hI := hI.2
  have h394 := hI.1; have hI := hI.2
  have h395 := hI.1; have hI := hI.2
  have h396 := hI.1; have hI := hI.2
  have h397 := hI.1; have hI := hI.2
  have h398 := hI.1; have hI := hI.2
  have h399 := hI.1; have hI := hI.2
  have h400 := hI.1; have hI := hI.2
  have h401 := hI.1; have hI := hI.2
  have h402 := hI.1; have hI := hI.2
  have h403 := hI.1; have hI := hI.2
  have h404 := hI.1; have hI := hI.2
  have h405 := hI.1; have hI := hI.2
  have h406 := hI.1; have hI := hI.2
  have h407 := hI.1; have hI := hI.2
  have h408 := hI.1; have hI := hI.2
  have h409 := hI.1; have hI := hI.2
  have h410 := hI.1; have hI := hI.2
  have h411 := hI.1; have hI := hI.2
  have h412 := hI.1; have hI := hI.2
  have h413 := hI.1; have hI := hI.2
  have h414 := hI.1; have hI := hI.2
  have h415 := hI.1; have hI := hI.2
  have h416 := hI.1; have hI := hI.2
  have h417 := hI.1; have hI := hI.2
  have h418 := hI.1; have hI := hI.2
  have h419 := hI.1; have hI := hI.2
  have h420 := hI.1; have hI := hI.2
  have h421 := hI.1; have hI := hI.2
  have h422 := hI.1; have hI := hI.2
  have h423 := hI.1; have hI := hI.2
  have h424 := hI.1; have hI := hI.2
  have h425 := hI.1; have hI := hI.2
  have h426 := hI.1; have hI := hI.2
  have h427 := hI.1; have hI := hI.2
  have h428 := hI.1; have hI := hI.2
  have h429 := hI.1; have hI := hI.2
  have h430 := hI.1; have hI := hI.2
  have h431 := hI.1; have hI := hI.2
  have h432 := hI.1; have hI := hI.2
  have h433 := hI.1; have hI := hI.2
  have h434 := hI.1; have hI := hI.2
  have h435 := hI.1; have hI := hI.2
  have h436 := hI.1; have hI := hI.2
  have h437 := hI.1; have hI := hI.2
  have h438 := hI.1; have hI := hI.2
  have h439 := hI.1; have hI := hI.2
  have h440 := hI.1; have hI := hI.2
  have h441 := hI.1; have hI := hI.2
  have h442 := hI.1; have hI := hI.2
  have h443 := hI.1; have hI := hI.2
  have h444 := hI.1; have hI := hI.2
  have h445 := hI.1; have hI := hI.2
  have h446 := hI.1; have hI := hI.2
  have h447 := hI.1; have hI := hI.2
  have h448 := hI.1; have hI := hI.2
  have h449 := hI.1; have hI := hI.2
  have h450 := hI.1; have hI := hI.2
  have h451 := hI.1; have hI := hI.2
  have h452 := hI.1; have hI := hI.2
  have h453 := hI.1; have hI := hI.2
  have h454 := hI.1; have hI := hI.2
  have h455 := hI.1; have hI := hI.2
  have h456 := hI.1; have hI := hI.2
  have h457 := hI.1; have hI := hI.2
  have h458 := hI.1; have hI := hI.2
  have h459 := hI.1; have hI := hI.2
  have h460 := hI.1; have hI := hI.2
  have h461 := hI.1; have hI := hI.2
  have h462 := hI.1; have hI := hI.2
  have h463 := hI.1; have hI := hI.2
  have h464 := hI.1; have hI := hI.2
  have h465 := hI.1; have hI := hI.2
  have h466 := hI.1; have hI := hI.2
  have h467 := hI.1; have hI := hI.2
  have h468 := hI.1; have hI := hI.2
  have h469 := hI.1; have hI := hI.2
  have h470 := hI.1; have hI := hI.2
  have h471 := hI.1; have hI := hI.2
  have h472 := hI.1; have hI := hI.2
  have h473 := hI.1; have hI := hI.2
  have h474 := hI.1; have hI := hI.2
  have h475 := hI.1; have hI := hI.2
  have h476 := hI.1; have hI := hI.2
  have h477 := hI.1; have hI := hI.2
  have h478 := hI.1; have hI := hI.2
  have h479 := hI.1; have hI := hI.2
  have h480 := hI.1; have hI := hI.2
  have h481 := hI.1; have hI := hI.2
  have h482 := hI.1; have hI := hI.2
  have h483 := hI.1; have hI := hI.2
  have h484 := hI.1; have hI := hI.2
  have h485 := hI.1; have hI := hI.2
  have h486 := hI.1; have hI := hI.2
  have h487 := hI.1; have hI := hI.2
  have h488 := hI.1; have hI := hI.2
  have h489 := hI.1; have hI := hI.2
  have h490 := hI.1; have hI := hI.2
  have h491 := hI.1; have hI := hI.2
  have h492 := hI.1; have hI := hI.2
  have h493 := hI.1; have hI := hI.2
  have h494 := hI.1; have hI := hI.2
  have h495 := hI.1; have hI := hI.2
  have h496 := hI.1; have hI := hI.2
  have h497 := hI.1; have hI := hI.2
  have h498 := hI.1; have hI := hI.2
  have h499 := hI.1; have hI := hI.2
  have h500 := hI.1; have hI := hI.2
  have h501 := hI.1; have hI := hI.2
  have h502 := hI.1; have hI := hI.2
  have h503 := hI.1; have hI := hI.2
  have h504 := hI.1; have hI := hI.2
  have h505 := hI.1; have hI := hI.2
  have h506 := hI.1; have hI := hI.2
  have h507 := hI.1; have hI := hI.2
  have h508 := hI.1; have hI := hI.2
  have h509 := hI.1; have hI := hI.2
  have h510 := hI.1; have hI := hI.2
  have h511 := hI.1; have hI := hI.2
  have h512 := hI.1; have hI := hI.2
  have h513 := hI.1; have hI := hI.2
  have h514 := hI.1; have hI := hI.2
  have h515 := hI.1; have hI := hI.2
  have h516 := hI.1; have hI := hI.2
  have h517 := hI.1; have hI := hI.2
  have h518 := hI.1; have hI := hI.2
  have h519 := hI.1; have hI := hI.2
  have h520 := hI.1; have hI := hI.2
  have h521 := hI.1; have hI := hI.2
  have h522 := hI.1; have hI := hI.2
  have h523 := hI.1; have hI := hI.2
  have h524 := hI.1; have hI := hI.2
  have h525 := hI.1; have hI := hI.2
  have h526 := hI.1; have hI := hI.2
  have h527 := hI.1; have hI := hI.2
  have h528 := hI.1; have hI := hI.2
  have h529 := hI.1; have hI := hI.2
  have h530 := hI.1; have hI := hI.2
  have h531 := hI.1; have hI := hI.2
  have h532 := hI.1; have hI := hI.2
  have h533 := hI.1; have hI := hI.2
  have h534 := hI.1; have hI := hI.2
  have h535 := hI.1; have hI := hI.2
  have h536 := hI.1; have hI := hI.2
  have h537 := hI.1; have hI := hI.2
  have h538 := hI.1; have hI := hI.2
  have h539 := hI.1; have hI := hI.2
  have h540 := hI.1; have hI := hI.2
  have h541 := hI.1; have hI := hI.2
  have h542 := hI.1; have hI := hI.2
  have h543 := hI.1; have hI := hI.2
  have h544 := hI.1; have hI := hI.2
  have h545 := hI.1; have hI := hI.2
  have h546 := hI.1; have hI := hI.2
  have h547 := hI.1; have hI := hI.2
  have h548 := hI.1; have hI := hI.2
  have h549 := hI.1; have hI := hI.2
  have h550 := hI.1; have hI := hI.2
  have h551 := hI.1; have hI := hI.2
  have h552 := hI.1; have hI := hI.2
  have h553 := hI.1; have hI := hI.2
  have h554 := hI.1; have hI := hI.2
  have h555 := hI.1; have hI := hI.2
  have h556 := hI.1; have hI := hI.2
  have h557 := hI.1; have hI := hI.2
  have h558 := hI.1; have hI := hI.2
  have h559 := hI.1; have hI := hI.2
  have h560 := hI.1; have hI := hI.2
  have h561 := hI.1; have hI := hI.2
  have h562 := hI.1; have hI := hI.2
  have h563 := hI.1; have hI := hI.2
  have h564 := hI.1; have hI := hI.2
  have h565 := hI.1; have hI := hI.2
  have h566 := hI.1; have hI := hI.2
  have h567 := hI.1; have hI := hI.2
  exact invC_of_trees inp env _ T18 L19 (slice_trees_mem prog 4 _ _ 38 K18 K19 T18 slice18 env)
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
      (And.intro ⟨rfl, h256⟩
      (And.intro ⟨rfl, h257⟩
      (And.intro ⟨rfl, h258⟩
      (And.intro ⟨rfl, h259⟩
      (And.intro ⟨rfl, h260⟩
      (And.intro ⟨rfl, h261⟩
      (And.intro ⟨rfl, h262⟩
      (And.intro ⟨rfl, h263⟩
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
      (And.intro ⟨rfl, h276⟩
      (And.intro ⟨rfl, h277⟩
      (And.intro ⟨rfl, h278⟩
      (And.intro ⟨rfl, h279⟩
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
      (And.intro ⟨rfl, h292⟩
      (And.intro ⟨rfl, h293⟩
      (And.intro ⟨rfl, h294⟩
      (And.intro ⟨rfl, h295⟩
      (And.intro ⟨rfl, h296⟩
      (And.intro ⟨rfl, h297⟩
      (And.intro ⟨rfl, h298⟩
      (And.intro ⟨rfl, h299⟩
      (And.intro ⟨rfl, h300⟩
      (And.intro ⟨rfl, h301⟩
      (And.intro ⟨rfl, h302⟩
      (And.intro ⟨rfl, h303⟩
      (And.intro ⟨rfl, h304⟩
      (And.intro ⟨rfl, h305⟩
      (And.intro ⟨rfl, h306⟩
      (And.intro ⟨rfl, h307⟩
      (And.intro ⟨rfl, h308⟩
      (And.intro ⟨rfl, h309⟩
      (And.intro ⟨rfl, h310⟩
      (And.intro ⟨rfl, h311⟩
      (And.intro ⟨rfl, h312⟩
      (And.intro ⟨rfl, h313⟩
      (And.intro ⟨rfl, h314⟩
      (And.intro ⟨rfl, h315⟩
      (And.intro ⟨rfl, h316⟩
      (And.intro ⟨rfl, h317⟩
      (And.intro ⟨rfl, h318⟩
      (And.intro ⟨rfl, h319⟩
      (And.intro ⟨rfl, h320⟩
      (And.intro ⟨rfl, h321⟩
      (And.intro ⟨rfl, h322⟩
      (And.intro ⟨rfl, h323⟩
      (And.intro ⟨rfl, h324⟩
      (And.intro ⟨rfl, h325⟩
      (And.intro ⟨rfl, h326⟩
      (And.intro ⟨rfl, h327⟩
      (And.intro ⟨rfl, h328⟩
      (And.intro ⟨rfl, h329⟩
      (And.intro ⟨rfl, h330⟩
      (And.intro ⟨rfl, h331⟩
      (And.intro ⟨rfl, h332⟩
      (And.intro ⟨rfl, h333⟩
      (And.intro ⟨rfl, h334⟩
      (And.intro ⟨rfl, h335⟩
      (And.intro ⟨rfl, h336⟩
      (And.intro ⟨rfl, h337⟩
      (And.intro ⟨rfl, h338⟩
      (And.intro ⟨rfl, h339⟩
      (And.intro ⟨rfl, h340⟩
      (And.intro ⟨rfl, h341⟩
      (And.intro ⟨rfl, h342⟩
      (And.intro ⟨rfl, h343⟩
      (And.intro ⟨rfl, h344⟩
      (And.intro ⟨rfl, h345⟩
      (And.intro ⟨rfl, h346⟩
      (And.intro ⟨rfl, h347⟩
      (And.intro ⟨rfl, h348⟩
      (And.intro ⟨rfl, h349⟩
      (And.intro ⟨rfl, h350⟩
      (And.intro ⟨rfl, h351⟩
      (And.intro ⟨rfl, h352⟩
      (And.intro ⟨rfl, h353⟩
      (And.intro ⟨rfl, h354⟩
      (And.intro ⟨rfl, h355⟩
      (And.intro ⟨rfl, h356⟩
      (And.intro ⟨rfl, h357⟩
      (And.intro ⟨rfl, h358⟩
      (And.intro ⟨rfl, h359⟩
      (And.intro ⟨rfl, h360⟩
      (And.intro ⟨rfl, h361⟩
      (And.intro ⟨rfl, h362⟩
      (And.intro ⟨rfl, h363⟩
      (And.intro ⟨rfl, h364⟩
      (And.intro ⟨rfl, h365⟩
      (And.intro ⟨rfl, h366⟩
      (And.intro ⟨rfl, h367⟩
      (And.intro ⟨rfl, h368⟩
      (And.intro ⟨rfl, h369⟩
      (And.intro ⟨rfl, h370⟩
      (And.intro ⟨rfl, h371⟩
      (And.intro ⟨rfl, h372⟩
      (And.intro ⟨rfl, h373⟩
      (And.intro ⟨rfl, h374⟩
      (And.intro ⟨rfl, h375⟩
      (And.intro ⟨rfl, h376⟩
      (And.intro ⟨rfl, h377⟩
      (And.intro ⟨rfl, h378⟩
      (And.intro ⟨rfl, h379⟩
      (And.intro ⟨rfl, h380⟩
      (And.intro ⟨rfl, h381⟩
      (And.intro ⟨rfl, h382⟩
      (And.intro ⟨rfl, h383⟩
      (And.intro ⟨rfl, h384⟩
      (And.intro ⟨rfl, h385⟩
      (And.intro ⟨rfl, h386⟩
      (And.intro ⟨rfl, h387⟩
      (And.intro ⟨rfl, h388⟩
      (And.intro ⟨rfl, h389⟩
      (And.intro ⟨rfl, h390⟩
      (And.intro ⟨rfl, h391⟩
      (And.intro ⟨rfl, h392⟩
      (And.intro ⟨rfl, h393⟩
      (And.intro ⟨rfl, h394⟩
      (And.intro ⟨rfl, h395⟩
      (And.intro ⟨rfl, h396⟩
      (And.intro ⟨rfl, h397⟩
      (And.intro ⟨rfl, h398⟩
      (And.intro ⟨rfl, h399⟩
      (And.intro ⟨rfl, h400⟩
      (And.intro ⟨rfl, h401⟩
      (And.intro ⟨rfl, h402⟩
      (And.intro ⟨rfl, h403⟩
      (And.intro ⟨rfl, h404⟩
      (And.intro ⟨rfl, h405⟩
      (And.intro ⟨rfl, h406⟩
      (And.intro ⟨rfl, h407⟩
      (And.intro ⟨rfl, h408⟩
      (And.intro ⟨rfl, h409⟩
      (And.intro ⟨rfl, h410⟩
      (And.intro ⟨rfl, h411⟩
      (And.intro ⟨rfl, h412⟩
      (And.intro ⟨rfl, h413⟩
      (And.intro ⟨rfl, h414⟩
      (And.intro ⟨rfl, h415⟩
      (And.intro ⟨rfl, h416⟩
      (And.intro ⟨rfl, h417⟩
      (And.intro ⟨rfl, h418⟩
      (And.intro ⟨rfl, h419⟩
      (And.intro ⟨rfl, h420⟩
      (And.intro ⟨rfl, h421⟩
      (And.intro ⟨rfl, h422⟩
      (And.intro ⟨rfl, h423⟩
      (And.intro ⟨rfl, h424⟩
      (And.intro ⟨rfl, h425⟩
      (And.intro ⟨rfl, h426⟩
      (And.intro ⟨rfl, h427⟩
      (And.intro ⟨rfl, h428⟩
      (And.intro ⟨rfl, h429⟩
      (And.intro ⟨rfl, h430⟩
      (And.intro ⟨rfl, h431⟩
      (And.intro ⟨rfl, h432⟩
      (And.intro ⟨rfl, h433⟩
      (And.intro ⟨rfl, h434⟩
      (And.intro ⟨rfl, h435⟩
      (And.intro ⟨rfl, h436⟩
      (And.intro ⟨rfl, h437⟩
      (And.intro ⟨rfl, h438⟩
      (And.intro ⟨rfl, h439⟩
      (And.intro ⟨rfl, h440⟩
      (And.intro ⟨rfl, h441⟩
      (And.intro ⟨rfl, h442⟩
      (And.intro ⟨rfl, h443⟩
      (And.intro ⟨rfl, h444⟩
      (And.intro ⟨rfl, h445⟩
      (And.intro ⟨rfl, h446⟩
      (And.intro ⟨rfl, h447⟩
      (And.intro ⟨rfl, h448⟩
      (And.intro ⟨rfl, h449⟩
      (And.intro ⟨rfl, h450⟩
      (And.intro ⟨rfl, h451⟩
      (And.intro ⟨rfl, h452⟩
      (And.intro ⟨rfl, h453⟩
      (And.intro ⟨rfl, h454⟩
      (And.intro ⟨rfl, h455⟩
      (And.intro ⟨rfl, h456⟩
      (And.intro ⟨rfl, h457⟩
      (And.intro ⟨rfl, h458⟩
      (And.intro ⟨rfl, h459⟩
      (And.intro ⟨rfl, h460⟩
      (And.intro ⟨rfl, h461⟩
      (And.intro ⟨rfl, h462⟩
      (And.intro ⟨rfl, h463⟩
      (And.intro ⟨rfl, h464⟩
      (And.intro ⟨rfl, h465⟩
      (And.intro ⟨rfl, h466⟩
      (And.intro ⟨rfl, h467⟩
      (And.intro ⟨rfl, h468⟩
      (And.intro ⟨rfl, h469⟩
      (And.intro ⟨rfl, h470⟩
      (And.intro ⟨rfl, h471⟩
      (And.intro ⟨rfl, h472⟩
      (And.intro ⟨rfl, h473⟩
      (And.intro ⟨rfl, h474⟩
      (And.intro ⟨rfl, h475⟩
      (And.intro ⟨rfl, h476⟩
      (And.intro ⟨rfl, h477⟩
      (And.intro ⟨rfl, h478⟩
      (And.intro ⟨rfl, h479⟩
      (And.intro ⟨rfl, h487⟩
      (And.intro ⟨rfl, h487⟩
      (And.intro ⟨rfl, h487⟩
      (And.intro ⟨rfl, h487⟩
      (And.intro ⟨rfl, h486⟩
      (And.intro ⟨rfl, h486⟩
      (And.intro ⟨rfl, h486⟩
      (And.intro ⟨rfl, h486⟩
      (And.intro ⟨rfl, h485⟩
      (And.intro ⟨rfl, h485⟩
      (And.intro ⟨rfl, h485⟩
      (And.intro ⟨rfl, h485⟩
      (And.intro ⟨rfl, h484⟩
      (And.intro ⟨rfl, h484⟩
      (And.intro ⟨rfl, h484⟩
      (And.intro ⟨rfl, h484⟩
      (And.intro ⟨rfl, h483⟩
      (And.intro ⟨rfl, h483⟩
      (And.intro ⟨rfl, h483⟩
      (And.intro ⟨rfl, h483⟩
      (And.intro ⟨rfl, h482⟩
      (And.intro ⟨rfl, h482⟩
      (And.intro ⟨rfl, h482⟩
      (And.intro ⟨rfl, h482⟩
      (And.intro ⟨rfl, h481⟩
      (And.intro ⟨rfl, h481⟩
      (And.intro ⟨rfl, h481⟩
      (And.intro ⟨rfl, h481⟩
      (And.intro ⟨rfl, h480⟩
      (And.intro ⟨rfl, h480⟩
      (And.intro ⟨rfl, h480⟩
      (And.intro ⟨rfl, h480⟩
      (And.intro ⟨rfl, core18_267 (qv inp) inp env h348 h349 h350 h351⟩
      (And.intro ⟨rfl, core18_266 (qv inp) inp env h344 h345 h346 h347⟩
      (And.intro ⟨rfl, core18_265 (qv inp) inp env h340 h341 h342 h343⟩
      (And.intro ⟨rfl, core18_264 (qv inp) inp env h336 h337 h338 h339⟩
      (And.intro ⟨rfl, core18_263 (qv inp) inp env h332 h333 h334 h335⟩
      (And.intro ⟨rfl, core18_262 (qv inp) inp env h328 h329 h330 h331⟩
      (And.intro ⟨rfl, core18_261 (qv inp) inp env h324 h325 h326 h327⟩
      (And.intro ⟨rfl, core18_260 (qv inp) inp env h320 h321 h322 h323⟩
      (And.intro ⟨rfl, h488⟩
      (And.intro ⟨rfl, h489⟩
      (And.intro ⟨rfl, h490⟩
      (And.intro ⟨rfl, h491⟩
      (And.intro ⟨rfl, h492⟩
      (And.intro ⟨rfl, h493⟩
      (And.intro ⟨rfl, h494⟩
      (And.intro ⟨rfl, h495⟩
      (And.intro ⟨rfl, h496⟩
      (And.intro ⟨rfl, h497⟩
      (And.intro ⟨rfl, h498⟩
      (And.intro ⟨rfl, h499⟩
      (And.intro ⟨rfl, h500⟩
      (And.intro ⟨rfl, h501⟩
      (And.intro ⟨rfl, h502⟩
      (And.intro ⟨rfl, h503⟩
      (And.intro ⟨rfl, h504⟩
      (And.intro ⟨rfl, h505⟩
      (And.intro ⟨rfl, h506⟩
      (And.intro ⟨rfl, h507⟩
      (And.intro ⟨rfl, h508⟩
      (And.intro ⟨rfl, h509⟩
      (And.intro ⟨rfl, h510⟩
      (And.intro ⟨rfl, h511⟩
      (And.intro ⟨rfl, h512⟩
      (And.intro ⟨rfl, h513⟩
      (And.intro ⟨rfl, h514⟩
      (And.intro ⟨rfl, h515⟩
      (And.intro ⟨rfl, h516⟩
      (And.intro ⟨rfl, h517⟩
      (And.intro ⟨rfl, h518⟩
      (And.intro ⟨rfl, h519⟩
      (And.intro ⟨rfl, h520⟩
      (And.intro ⟨rfl, h521⟩
      (And.intro ⟨rfl, h522⟩
      (And.intro ⟨rfl, h523⟩
      (And.intro ⟨rfl, h524⟩
      (And.intro ⟨rfl, h525⟩
      (And.intro ⟨rfl, h526⟩
      (And.intro ⟨rfl, h527⟩
      (And.intro ⟨rfl, core18_171 (qv inp) inp env h528 h544 h536 h552 h480 h520 h504 h512 (qA_succI inp 7 0 (11) (by decide)) ((qKW inp 7 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_170 (qv inp) inp env h529 h545 h537 h553 h481 h521 h505 h513 (qA_succI inp 6 0 (11) (by decide)) ((qKW inp 6 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_169 (qv inp) inp env h530 h546 h538 h554 h482 h522 h506 h514 (qA_succI inp 5 0 (11) (by decide)) ((qKW inp 5 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_168 (qv inp) inp env h531 h547 h539 h555 h483 h523 h507 h515 (qA_succI inp 4 0 (11) (by decide)) ((qKW inp 4 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_167 (qv inp) inp env h532 h548 h540 h556 h484 h524 h508 h516 (qA_succI inp 3 0 (11) (by decide)) ((qKW inp 3 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_166 (qv inp) inp env h533 h549 h541 h557 h485 h525 h509 h517 (qA_succI inp 2 0 (11) (by decide)) ((qKW inp 2 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_165 (qv inp) inp env h534 h550 h542 h558 h486 h526 h510 h518 (qA_succI inp 1 0 (11) (by decide)) ((qKW inp 1 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_164 (qv inp) inp env h535 h551 h543 h559 h487 h527 h511 h519 (qA_succI inp 0 0 (11) (by decide)) ((qKW inp 0 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, h536⟩
      (And.intro ⟨rfl, h537⟩
      (And.intro ⟨rfl, h538⟩
      (And.intro ⟨rfl, h539⟩
      (And.intro ⟨rfl, h540⟩
      (And.intro ⟨rfl, h541⟩
      (And.intro ⟨rfl, h542⟩
      (And.intro ⟨rfl, h543⟩
      (And.intro ⟨rfl, h544⟩
      (And.intro ⟨rfl, h545⟩
      (And.intro ⟨rfl, h546⟩
      (And.intro ⟨rfl, h547⟩
      (And.intro ⟨rfl, h548⟩
      (And.intro ⟨rfl, h549⟩
      (And.intro ⟨rfl, h550⟩
      (And.intro ⟨rfl, h551⟩
      (And.intro ⟨rfl, h552⟩
      (And.intro ⟨rfl, h553⟩
      (And.intro ⟨rfl, h554⟩
      (And.intro ⟨rfl, h555⟩
      (And.intro ⟨rfl, h556⟩
      (And.intro ⟨rfl, h557⟩
      (And.intro ⟨rfl, h558⟩
      (And.intro ⟨rfl, h559⟩
      (And.intro ⟨rfl, core18_107 (qv inp) inp env h560 h528 h544 h536 h552 h480 (qE_succI inp 7 0 (11) (by decide)) ((qKW inp 7 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_106 (qv inp) inp env h561 h529 h545 h537 h553 h481 (qE_succI inp 6 0 (11) (by decide)) ((qKW inp 6 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_105 (qv inp) inp env h562 h530 h546 h538 h554 h482 (qE_succI inp 5 0 (11) (by decide)) ((qKW inp 5 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_104 (qv inp) inp env h563 h531 h547 h539 h555 h483 (qE_succI inp 4 0 (11) (by decide)) ((qKW inp 4 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_103 (qv inp) inp env h564 h532 h548 h540 h556 h484 (qE_succI inp 3 0 (11) (by decide)) ((qKW inp 3 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_102 (qv inp) inp env h565 h533 h549 h541 h557 h485 (qE_succI inp 2 0 (11) (by decide)) ((qKW inp 2 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_101 (qv inp) inp env h566 h534 h550 h542 h558 h486 (qE_succI inp 1 0 (11) (by decide)) ((qKW inp 1 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      (And.intro ⟨rfl, core18_100 (qv inp) inp env h567 h535 h551 h543 h559 h487 (qE_succI inp 0 0 (11) (by decide)) ((qKW inp 0 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide]))⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
