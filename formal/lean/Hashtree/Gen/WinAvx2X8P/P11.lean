import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D11
import Hashtree.Gen.WinAvx2X8P.D10

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice11 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K11 K12 T11 = true := by
  decide +kernel

theorem core11_283 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1131) = V (.W 7 0 7))
    (h1 : env (.n 1130) = V (.W 7 0 7))
    (h2 : env (.n 1129) = V (.W 7 0 7))
    (h3 : env (.n 1128) = V (.W 7 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1131)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1130)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1129)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1128)) 24) (.const 255)) 24))) = V (.W 7 0 7) :=
  shape4 (env (.n 1131)) (env (.n 1130)) (env (.n 1129)) (env (.n 1128)) (V (.W 7 0 7)) h0 h1 h2 h3

theorem core11_282 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1135) = V (.W 6 0 7))
    (h1 : env (.n 1134) = V (.W 6 0 7))
    (h2 : env (.n 1133) = V (.W 6 0 7))
    (h3 : env (.n 1132) = V (.W 6 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1135)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1134)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1133)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1132)) 24) (.const 255)) 24))) = V (.W 6 0 7) :=
  shape4 (env (.n 1135)) (env (.n 1134)) (env (.n 1133)) (env (.n 1132)) (V (.W 6 0 7)) h0 h1 h2 h3

theorem core11_281 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1139) = V (.W 5 0 7))
    (h1 : env (.n 1138) = V (.W 5 0 7))
    (h2 : env (.n 1137) = V (.W 5 0 7))
    (h3 : env (.n 1136) = V (.W 5 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1139)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1138)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1137)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1136)) 24) (.const 255)) 24))) = V (.W 5 0 7) :=
  shape4 (env (.n 1139)) (env (.n 1138)) (env (.n 1137)) (env (.n 1136)) (V (.W 5 0 7)) h0 h1 h2 h3

theorem core11_280 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1143) = V (.W 4 0 7))
    (h1 : env (.n 1142) = V (.W 4 0 7))
    (h2 : env (.n 1141) = V (.W 4 0 7))
    (h3 : env (.n 1140) = V (.W 4 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1143)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1142)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1141)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1140)) 24) (.const 255)) 24))) = V (.W 4 0 7) :=
  shape4 (env (.n 1143)) (env (.n 1142)) (env (.n 1141)) (env (.n 1140)) (V (.W 4 0 7)) h0 h1 h2 h3

theorem core11_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1147) = V (.W 3 0 7))
    (h1 : env (.n 1146) = V (.W 3 0 7))
    (h2 : env (.n 1145) = V (.W 3 0 7))
    (h3 : env (.n 1144) = V (.W 3 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1147)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1146)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1145)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1144)) 24) (.const 255)) 24))) = V (.W 3 0 7) :=
  shape4 (env (.n 1147)) (env (.n 1146)) (env (.n 1145)) (env (.n 1144)) (V (.W 3 0 7)) h0 h1 h2 h3

theorem core11_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1151) = V (.W 2 0 7))
    (h1 : env (.n 1150) = V (.W 2 0 7))
    (h2 : env (.n 1149) = V (.W 2 0 7))
    (h3 : env (.n 1148) = V (.W 2 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1151)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1150)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1149)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1148)) 24) (.const 255)) 24))) = V (.W 2 0 7) :=
  shape4 (env (.n 1151)) (env (.n 1150)) (env (.n 1149)) (env (.n 1148)) (V (.W 2 0 7)) h0 h1 h2 h3

theorem core11_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1155) = V (.W 1 0 7))
    (h1 : env (.n 1154) = V (.W 1 0 7))
    (h2 : env (.n 1153) = V (.W 1 0 7))
    (h3 : env (.n 1152) = V (.W 1 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1155)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1154)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1153)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1152)) 24) (.const 255)) 24))) = V (.W 1 0 7) :=
  shape4 (env (.n 1155)) (env (.n 1154)) (env (.n 1153)) (env (.n 1152)) (V (.W 1 0 7)) h0 h1 h2 h3

theorem core11_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1159) = V (.W 0 0 7))
    (h1 : env (.n 1158) = V (.W 0 0 7))
    (h2 : env (.n 1157) = V (.W 0 0 7))
    (h3 : env (.n 1156) = V (.W 0 0 7)) :
    E.eval env (.or (.or (.and (.shr (.var (.n 1159)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1158)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1157)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1156)) 24) (.const 255)) 24))) = V (.W 0 0 7) :=
  shape4 (env (.n 1159)) (env (.n 1158)) (env (.n 1157)) (env (.n 1156)) (V (.W 0 0 7)) h0 h1 h2 h3

theorem core11_219 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 219) = V (.A 7 0 (1)))
    (h1 : env (.n 155) = V (.E 7 0 (1)))
    (h2 : env (.n 123) = V (.E 7 0 (3)))
    (h3 : env (.n 139) = V (.E 7 0 (2)))
    (h4 : env (.n 107) = V (.E 7 0 (4)))
    (h5 : env (.n 235) = V (.W 7 0 4))
    (h6 : V (.E 7 0 (5)) = V (.A 7 0 (1)) + (V (.E 7 0 (1)) + Sigma1 (V (.E 7 0 (4))) + Ch (V (.E 7 0 (4))) (V (.E 7 0 (3))) (V (.E 7 0 (2))) + V (.KW 7 0 4)))
    (h7 : V (.KW 7 0 4) = 961987163#32 + V (.W 7 0 4)) :
    E.eval env (.add (.var (.n 219)) (.add (.add (.add (.var (.n 155)) (.xor (.and (.xor (.var (.n 123)) (.var (.n 139))) (.var (.n 107))) (.var (.n 139)))) (.add (.var (.n 235)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 107)) 5) (.shl (.var (.n 107)) 27)) (.var (.n 107))) 6) (.shl (.xor (.or (.shr (.var (.n 107)) 5) (.shl (.var (.n 107)) 27)) (.var (.n 107))) 26)) (.or (.shr (.var (.n 107)) 25) (.shl (.var (.n 107)) 7))))) = V (.E 7 0 (5)) :=
  shape11 (env (.n 219)) (env (.n 155)) (env (.n 123)) (env (.n 139)) (env (.n 107)) (env (.n 235)) (V (.A 7 0 (1))) (V (.E 7 0 (1))) (V (.E 7 0 (3))) (V (.E 7 0 (2))) (V (.E 7 0 (4))) (V (.W 7 0 4)) (V (.E 7 0 (5))) (V (.KW 7 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_218 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.A 6 0 (1)))
    (h1 : env (.n 154) = V (.E 6 0 (1)))
    (h2 : env (.n 122) = V (.E 6 0 (3)))
    (h3 : env (.n 138) = V (.E 6 0 (2)))
    (h4 : env (.n 106) = V (.E 6 0 (4)))
    (h5 : env (.n 234) = V (.W 6 0 4))
    (h6 : V (.E 6 0 (5)) = V (.A 6 0 (1)) + (V (.E 6 0 (1)) + Sigma1 (V (.E 6 0 (4))) + Ch (V (.E 6 0 (4))) (V (.E 6 0 (3))) (V (.E 6 0 (2))) + V (.KW 6 0 4)))
    (h7 : V (.KW 6 0 4) = 961987163#32 + V (.W 6 0 4)) :
    E.eval env (.add (.var (.n 218)) (.add (.add (.add (.var (.n 154)) (.xor (.and (.xor (.var (.n 122)) (.var (.n 138))) (.var (.n 106))) (.var (.n 138)))) (.add (.var (.n 234)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 106)) 5) (.shl (.var (.n 106)) 27)) (.var (.n 106))) 6) (.shl (.xor (.or (.shr (.var (.n 106)) 5) (.shl (.var (.n 106)) 27)) (.var (.n 106))) 26)) (.or (.shr (.var (.n 106)) 25) (.shl (.var (.n 106)) 7))))) = V (.E 6 0 (5)) :=
  shape11 (env (.n 218)) (env (.n 154)) (env (.n 122)) (env (.n 138)) (env (.n 106)) (env (.n 234)) (V (.A 6 0 (1))) (V (.E 6 0 (1))) (V (.E 6 0 (3))) (V (.E 6 0 (2))) (V (.E 6 0 (4))) (V (.W 6 0 4)) (V (.E 6 0 (5))) (V (.KW 6 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_217 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 217) = V (.A 5 0 (1)))
    (h1 : env (.n 153) = V (.E 5 0 (1)))
    (h2 : env (.n 121) = V (.E 5 0 (3)))
    (h3 : env (.n 137) = V (.E 5 0 (2)))
    (h4 : env (.n 105) = V (.E 5 0 (4)))
    (h5 : env (.n 233) = V (.W 5 0 4))
    (h6 : V (.E 5 0 (5)) = V (.A 5 0 (1)) + (V (.E 5 0 (1)) + Sigma1 (V (.E 5 0 (4))) + Ch (V (.E 5 0 (4))) (V (.E 5 0 (3))) (V (.E 5 0 (2))) + V (.KW 5 0 4)))
    (h7 : V (.KW 5 0 4) = 961987163#32 + V (.W 5 0 4)) :
    E.eval env (.add (.var (.n 217)) (.add (.add (.add (.var (.n 153)) (.xor (.and (.xor (.var (.n 121)) (.var (.n 137))) (.var (.n 105))) (.var (.n 137)))) (.add (.var (.n 233)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 105)) 5) (.shl (.var (.n 105)) 27)) (.var (.n 105))) 6) (.shl (.xor (.or (.shr (.var (.n 105)) 5) (.shl (.var (.n 105)) 27)) (.var (.n 105))) 26)) (.or (.shr (.var (.n 105)) 25) (.shl (.var (.n 105)) 7))))) = V (.E 5 0 (5)) :=
  shape11 (env (.n 217)) (env (.n 153)) (env (.n 121)) (env (.n 137)) (env (.n 105)) (env (.n 233)) (V (.A 5 0 (1))) (V (.E 5 0 (1))) (V (.E 5 0 (3))) (V (.E 5 0 (2))) (V (.E 5 0 (4))) (V (.W 5 0 4)) (V (.E 5 0 (5))) (V (.KW 5 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_216 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.A 4 0 (1)))
    (h1 : env (.n 152) = V (.E 4 0 (1)))
    (h2 : env (.n 120) = V (.E 4 0 (3)))
    (h3 : env (.n 136) = V (.E 4 0 (2)))
    (h4 : env (.n 104) = V (.E 4 0 (4)))
    (h5 : env (.n 232) = V (.W 4 0 4))
    (h6 : V (.E 4 0 (5)) = V (.A 4 0 (1)) + (V (.E 4 0 (1)) + Sigma1 (V (.E 4 0 (4))) + Ch (V (.E 4 0 (4))) (V (.E 4 0 (3))) (V (.E 4 0 (2))) + V (.KW 4 0 4)))
    (h7 : V (.KW 4 0 4) = 961987163#32 + V (.W 4 0 4)) :
    E.eval env (.add (.var (.n 216)) (.add (.add (.add (.var (.n 152)) (.xor (.and (.xor (.var (.n 120)) (.var (.n 136))) (.var (.n 104))) (.var (.n 136)))) (.add (.var (.n 232)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 104)) 5) (.shl (.var (.n 104)) 27)) (.var (.n 104))) 6) (.shl (.xor (.or (.shr (.var (.n 104)) 5) (.shl (.var (.n 104)) 27)) (.var (.n 104))) 26)) (.or (.shr (.var (.n 104)) 25) (.shl (.var (.n 104)) 7))))) = V (.E 4 0 (5)) :=
  shape11 (env (.n 216)) (env (.n 152)) (env (.n 120)) (env (.n 136)) (env (.n 104)) (env (.n 232)) (V (.A 4 0 (1))) (V (.E 4 0 (1))) (V (.E 4 0 (3))) (V (.E 4 0 (2))) (V (.E 4 0 (4))) (V (.W 4 0 4)) (V (.E 4 0 (5))) (V (.KW 4 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 215) = V (.A 3 0 (1)))
    (h1 : env (.n 151) = V (.E 3 0 (1)))
    (h2 : env (.n 119) = V (.E 3 0 (3)))
    (h3 : env (.n 135) = V (.E 3 0 (2)))
    (h4 : env (.n 103) = V (.E 3 0 (4)))
    (h5 : env (.n 231) = V (.W 3 0 4))
    (h6 : V (.E 3 0 (5)) = V (.A 3 0 (1)) + (V (.E 3 0 (1)) + Sigma1 (V (.E 3 0 (4))) + Ch (V (.E 3 0 (4))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) + V (.KW 3 0 4)))
    (h7 : V (.KW 3 0 4) = 961987163#32 + V (.W 3 0 4)) :
    E.eval env (.add (.var (.n 215)) (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.var (.n 231)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7))))) = V (.E 3 0 (5)) :=
  shape11 (env (.n 215)) (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.n 231)) (V (.A 3 0 (1))) (V (.E 3 0 (1))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) (V (.E 3 0 (4))) (V (.W 3 0 4)) (V (.E 3 0 (5))) (V (.KW 3 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.A 2 0 (1)))
    (h1 : env (.n 150) = V (.E 2 0 (1)))
    (h2 : env (.n 118) = V (.E 2 0 (3)))
    (h3 : env (.n 134) = V (.E 2 0 (2)))
    (h4 : env (.n 102) = V (.E 2 0 (4)))
    (h5 : env (.n 230) = V (.W 2 0 4))
    (h6 : V (.E 2 0 (5)) = V (.A 2 0 (1)) + (V (.E 2 0 (1)) + Sigma1 (V (.E 2 0 (4))) + Ch (V (.E 2 0 (4))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) + V (.KW 2 0 4)))
    (h7 : V (.KW 2 0 4) = 961987163#32 + V (.W 2 0 4)) :
    E.eval env (.add (.var (.n 214)) (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.var (.n 230)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7))))) = V (.E 2 0 (5)) :=
  shape11 (env (.n 214)) (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.n 230)) (V (.A 2 0 (1))) (V (.E 2 0 (1))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) (V (.E 2 0 (4))) (V (.W 2 0 4)) (V (.E 2 0 (5))) (V (.KW 2 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 213) = V (.A 1 0 (1)))
    (h1 : env (.n 149) = V (.E 1 0 (1)))
    (h2 : env (.n 117) = V (.E 1 0 (3)))
    (h3 : env (.n 133) = V (.E 1 0 (2)))
    (h4 : env (.n 101) = V (.E 1 0 (4)))
    (h5 : env (.n 229) = V (.W 1 0 4))
    (h6 : V (.E 1 0 (5)) = V (.A 1 0 (1)) + (V (.E 1 0 (1)) + Sigma1 (V (.E 1 0 (4))) + Ch (V (.E 1 0 (4))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) + V (.KW 1 0 4)))
    (h7 : V (.KW 1 0 4) = 961987163#32 + V (.W 1 0 4)) :
    E.eval env (.add (.var (.n 213)) (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.var (.n 229)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7))))) = V (.E 1 0 (5)) :=
  shape11 (env (.n 213)) (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.n 229)) (V (.A 1 0 (1))) (V (.E 1 0 (1))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) (V (.E 1 0 (4))) (V (.W 1 0 4)) (V (.E 1 0 (5))) (V (.KW 1 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.A 0 0 (1)))
    (h1 : env (.n 148) = V (.E 0 0 (1)))
    (h2 : env (.n 116) = V (.E 0 0 (3)))
    (h3 : env (.n 132) = V (.E 0 0 (2)))
    (h4 : env (.n 100) = V (.E 0 0 (4)))
    (h5 : env (.n 228) = V (.W 0 0 4))
    (h6 : V (.E 0 0 (5)) = V (.A 0 0 (1)) + (V (.E 0 0 (1)) + Sigma1 (V (.E 0 0 (4))) + Ch (V (.E 0 0 (4))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) + V (.KW 0 0 4)))
    (h7 : V (.KW 0 0 4) = 961987163#32 + V (.W 0 0 4)) :
    E.eval env (.add (.var (.n 212)) (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.var (.n 228)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7))))) = V (.E 0 0 (5)) :=
  shape11 (env (.n 212)) (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.n 228)) (V (.A 0 0 (1))) (V (.E 0 0 (1))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (4))) (V (.W 0 0 4)) (V (.E 0 0 (5))) (V (.KW 0 0 4)) h0 h1 h2 h3 h4 h5 h6 h7

theorem core11_155 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 155) = V (.E 7 0 (1)))
    (h1 : env (.n 123) = V (.E 7 0 (3)))
    (h2 : env (.n 139) = V (.E 7 0 (2)))
    (h3 : env (.n 107) = V (.E 7 0 (4)))
    (h4 : env (.n 235) = V (.W 7 0 4))
    (h5 : env (.n 171) = V (.A 7 0 (4)))
    (h6 : env (.n 203) = V (.A 7 0 (2)))
    (h7 : env (.n 187) = V (.A 7 0 (3)))
    (h8 : V (.A 7 0 (5)) = (V (.E 7 0 (1)) + Sigma1 (V (.E 7 0 (4))) + Ch (V (.E 7 0 (4))) (V (.E 7 0 (3))) (V (.E 7 0 (2))) + V (.KW 7 0 4)) + (Sigma0 (V (.A 7 0 (4))) + Maj (V (.A 7 0 (4))) (V (.A 7 0 (3))) (V (.A 7 0 (2)))))
    (h9 : V (.KW 7 0 4) = 961987163#32 + V (.W 7 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 155)) (.xor (.and (.xor (.var (.n 123)) (.var (.n 139))) (.var (.n 107))) (.var (.n 139)))) (.add (.var (.n 235)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 107)) 5) (.shl (.var (.n 107)) 27)) (.var (.n 107))) 6) (.shl (.xor (.or (.shr (.var (.n 107)) 5) (.shl (.var (.n 107)) 27)) (.var (.n 107))) 26)) (.or (.shr (.var (.n 107)) 25) (.shl (.var (.n 107)) 7)))) (.or (.and (.var (.n 171)) (.var (.n 203))) (.and (.xor (.var (.n 171)) (.var (.n 203))) (.var (.n 187))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 171)) 11) (.shl (.var (.n 171)) 21)) (.var (.n 171))) 2) (.shl (.xor (.or (.shr (.var (.n 171)) 11) (.shl (.var (.n 171)) 21)) (.var (.n 171))) 30)) (.or (.shr (.var (.n 171)) 22) (.shl (.var (.n 171)) 10)))) = V (.A 7 0 (5)) :=
  shape12 (env (.n 155)) (env (.n 123)) (env (.n 139)) (env (.n 107)) (env (.n 235)) (env (.n 171)) (env (.n 203)) (env (.n 187)) (V (.E 7 0 (1))) (V (.E 7 0 (3))) (V (.E 7 0 (2))) (V (.E 7 0 (4))) (V (.W 7 0 4)) (V (.A 7 0 (4))) (V (.A 7 0 (2))) (V (.A 7 0 (3))) (V (.A 7 0 (5))) (V (.KW 7 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_154 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 154) = V (.E 6 0 (1)))
    (h1 : env (.n 122) = V (.E 6 0 (3)))
    (h2 : env (.n 138) = V (.E 6 0 (2)))
    (h3 : env (.n 106) = V (.E 6 0 (4)))
    (h4 : env (.n 234) = V (.W 6 0 4))
    (h5 : env (.n 170) = V (.A 6 0 (4)))
    (h6 : env (.n 202) = V (.A 6 0 (2)))
    (h7 : env (.n 186) = V (.A 6 0 (3)))
    (h8 : V (.A 6 0 (5)) = (V (.E 6 0 (1)) + Sigma1 (V (.E 6 0 (4))) + Ch (V (.E 6 0 (4))) (V (.E 6 0 (3))) (V (.E 6 0 (2))) + V (.KW 6 0 4)) + (Sigma0 (V (.A 6 0 (4))) + Maj (V (.A 6 0 (4))) (V (.A 6 0 (3))) (V (.A 6 0 (2)))))
    (h9 : V (.KW 6 0 4) = 961987163#32 + V (.W 6 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 154)) (.xor (.and (.xor (.var (.n 122)) (.var (.n 138))) (.var (.n 106))) (.var (.n 138)))) (.add (.var (.n 234)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 106)) 5) (.shl (.var (.n 106)) 27)) (.var (.n 106))) 6) (.shl (.xor (.or (.shr (.var (.n 106)) 5) (.shl (.var (.n 106)) 27)) (.var (.n 106))) 26)) (.or (.shr (.var (.n 106)) 25) (.shl (.var (.n 106)) 7)))) (.or (.and (.var (.n 170)) (.var (.n 202))) (.and (.xor (.var (.n 170)) (.var (.n 202))) (.var (.n 186))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 170)) 11) (.shl (.var (.n 170)) 21)) (.var (.n 170))) 2) (.shl (.xor (.or (.shr (.var (.n 170)) 11) (.shl (.var (.n 170)) 21)) (.var (.n 170))) 30)) (.or (.shr (.var (.n 170)) 22) (.shl (.var (.n 170)) 10)))) = V (.A 6 0 (5)) :=
  shape12 (env (.n 154)) (env (.n 122)) (env (.n 138)) (env (.n 106)) (env (.n 234)) (env (.n 170)) (env (.n 202)) (env (.n 186)) (V (.E 6 0 (1))) (V (.E 6 0 (3))) (V (.E 6 0 (2))) (V (.E 6 0 (4))) (V (.W 6 0 4)) (V (.A 6 0 (4))) (V (.A 6 0 (2))) (V (.A 6 0 (3))) (V (.A 6 0 (5))) (V (.KW 6 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_153 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 153) = V (.E 5 0 (1)))
    (h1 : env (.n 121) = V (.E 5 0 (3)))
    (h2 : env (.n 137) = V (.E 5 0 (2)))
    (h3 : env (.n 105) = V (.E 5 0 (4)))
    (h4 : env (.n 233) = V (.W 5 0 4))
    (h5 : env (.n 169) = V (.A 5 0 (4)))
    (h6 : env (.n 201) = V (.A 5 0 (2)))
    (h7 : env (.n 185) = V (.A 5 0 (3)))
    (h8 : V (.A 5 0 (5)) = (V (.E 5 0 (1)) + Sigma1 (V (.E 5 0 (4))) + Ch (V (.E 5 0 (4))) (V (.E 5 0 (3))) (V (.E 5 0 (2))) + V (.KW 5 0 4)) + (Sigma0 (V (.A 5 0 (4))) + Maj (V (.A 5 0 (4))) (V (.A 5 0 (3))) (V (.A 5 0 (2)))))
    (h9 : V (.KW 5 0 4) = 961987163#32 + V (.W 5 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 153)) (.xor (.and (.xor (.var (.n 121)) (.var (.n 137))) (.var (.n 105))) (.var (.n 137)))) (.add (.var (.n 233)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 105)) 5) (.shl (.var (.n 105)) 27)) (.var (.n 105))) 6) (.shl (.xor (.or (.shr (.var (.n 105)) 5) (.shl (.var (.n 105)) 27)) (.var (.n 105))) 26)) (.or (.shr (.var (.n 105)) 25) (.shl (.var (.n 105)) 7)))) (.or (.and (.var (.n 169)) (.var (.n 201))) (.and (.xor (.var (.n 169)) (.var (.n 201))) (.var (.n 185))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 169)) 11) (.shl (.var (.n 169)) 21)) (.var (.n 169))) 2) (.shl (.xor (.or (.shr (.var (.n 169)) 11) (.shl (.var (.n 169)) 21)) (.var (.n 169))) 30)) (.or (.shr (.var (.n 169)) 22) (.shl (.var (.n 169)) 10)))) = V (.A 5 0 (5)) :=
  shape12 (env (.n 153)) (env (.n 121)) (env (.n 137)) (env (.n 105)) (env (.n 233)) (env (.n 169)) (env (.n 201)) (env (.n 185)) (V (.E 5 0 (1))) (V (.E 5 0 (3))) (V (.E 5 0 (2))) (V (.E 5 0 (4))) (V (.W 5 0 4)) (V (.A 5 0 (4))) (V (.A 5 0 (2))) (V (.A 5 0 (3))) (V (.A 5 0 (5))) (V (.KW 5 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_152 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 152) = V (.E 4 0 (1)))
    (h1 : env (.n 120) = V (.E 4 0 (3)))
    (h2 : env (.n 136) = V (.E 4 0 (2)))
    (h3 : env (.n 104) = V (.E 4 0 (4)))
    (h4 : env (.n 232) = V (.W 4 0 4))
    (h5 : env (.n 168) = V (.A 4 0 (4)))
    (h6 : env (.n 200) = V (.A 4 0 (2)))
    (h7 : env (.n 184) = V (.A 4 0 (3)))
    (h8 : V (.A 4 0 (5)) = (V (.E 4 0 (1)) + Sigma1 (V (.E 4 0 (4))) + Ch (V (.E 4 0 (4))) (V (.E 4 0 (3))) (V (.E 4 0 (2))) + V (.KW 4 0 4)) + (Sigma0 (V (.A 4 0 (4))) + Maj (V (.A 4 0 (4))) (V (.A 4 0 (3))) (V (.A 4 0 (2)))))
    (h9 : V (.KW 4 0 4) = 961987163#32 + V (.W 4 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 152)) (.xor (.and (.xor (.var (.n 120)) (.var (.n 136))) (.var (.n 104))) (.var (.n 136)))) (.add (.var (.n 232)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 104)) 5) (.shl (.var (.n 104)) 27)) (.var (.n 104))) 6) (.shl (.xor (.or (.shr (.var (.n 104)) 5) (.shl (.var (.n 104)) 27)) (.var (.n 104))) 26)) (.or (.shr (.var (.n 104)) 25) (.shl (.var (.n 104)) 7)))) (.or (.and (.var (.n 168)) (.var (.n 200))) (.and (.xor (.var (.n 168)) (.var (.n 200))) (.var (.n 184))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 168)) 11) (.shl (.var (.n 168)) 21)) (.var (.n 168))) 2) (.shl (.xor (.or (.shr (.var (.n 168)) 11) (.shl (.var (.n 168)) 21)) (.var (.n 168))) 30)) (.or (.shr (.var (.n 168)) 22) (.shl (.var (.n 168)) 10)))) = V (.A 4 0 (5)) :=
  shape12 (env (.n 152)) (env (.n 120)) (env (.n 136)) (env (.n 104)) (env (.n 232)) (env (.n 168)) (env (.n 200)) (env (.n 184)) (V (.E 4 0 (1))) (V (.E 4 0 (3))) (V (.E 4 0 (2))) (V (.E 4 0 (4))) (V (.W 4 0 4)) (V (.A 4 0 (4))) (V (.A 4 0 (2))) (V (.A 4 0 (3))) (V (.A 4 0 (5))) (V (.KW 4 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 119) = V (.E 3 0 (3)))
    (h2 : env (.n 135) = V (.E 3 0 (2)))
    (h3 : env (.n 103) = V (.E 3 0 (4)))
    (h4 : env (.n 231) = V (.W 3 0 4))
    (h5 : env (.n 167) = V (.A 3 0 (4)))
    (h6 : env (.n 199) = V (.A 3 0 (2)))
    (h7 : env (.n 183) = V (.A 3 0 (3)))
    (h8 : V (.A 3 0 (5)) = (V (.E 3 0 (1)) + Sigma1 (V (.E 3 0 (4))) + Ch (V (.E 3 0 (4))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) + V (.KW 3 0 4)) + (Sigma0 (V (.A 3 0 (4))) + Maj (V (.A 3 0 (4))) (V (.A 3 0 (3))) (V (.A 3 0 (2)))))
    (h9 : V (.KW 3 0 4) = 961987163#32 + V (.W 3 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.var (.n 231)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7)))) (.or (.and (.var (.n 167)) (.var (.n 199))) (.and (.xor (.var (.n 167)) (.var (.n 199))) (.var (.n 183))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 2) (.shl (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 30)) (.or (.shr (.var (.n 167)) 22) (.shl (.var (.n 167)) 10)))) = V (.A 3 0 (5)) :=
  shape12 (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.n 231)) (env (.n 167)) (env (.n 199)) (env (.n 183)) (V (.E 3 0 (1))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) (V (.E 3 0 (4))) (V (.W 3 0 4)) (V (.A 3 0 (4))) (V (.A 3 0 (2))) (V (.A 3 0 (3))) (V (.A 3 0 (5))) (V (.KW 3 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 118) = V (.E 2 0 (3)))
    (h2 : env (.n 134) = V (.E 2 0 (2)))
    (h3 : env (.n 102) = V (.E 2 0 (4)))
    (h4 : env (.n 230) = V (.W 2 0 4))
    (h5 : env (.n 166) = V (.A 2 0 (4)))
    (h6 : env (.n 198) = V (.A 2 0 (2)))
    (h7 : env (.n 182) = V (.A 2 0 (3)))
    (h8 : V (.A 2 0 (5)) = (V (.E 2 0 (1)) + Sigma1 (V (.E 2 0 (4))) + Ch (V (.E 2 0 (4))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) + V (.KW 2 0 4)) + (Sigma0 (V (.A 2 0 (4))) + Maj (V (.A 2 0 (4))) (V (.A 2 0 (3))) (V (.A 2 0 (2)))))
    (h9 : V (.KW 2 0 4) = 961987163#32 + V (.W 2 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.var (.n 230)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7)))) (.or (.and (.var (.n 166)) (.var (.n 198))) (.and (.xor (.var (.n 166)) (.var (.n 198))) (.var (.n 182))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 2) (.shl (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 30)) (.or (.shr (.var (.n 166)) 22) (.shl (.var (.n 166)) 10)))) = V (.A 2 0 (5)) :=
  shape12 (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.n 230)) (env (.n 166)) (env (.n 198)) (env (.n 182)) (V (.E 2 0 (1))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) (V (.E 2 0 (4))) (V (.W 2 0 4)) (V (.A 2 0 (4))) (V (.A 2 0 (2))) (V (.A 2 0 (3))) (V (.A 2 0 (5))) (V (.KW 2 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 117) = V (.E 1 0 (3)))
    (h2 : env (.n 133) = V (.E 1 0 (2)))
    (h3 : env (.n 101) = V (.E 1 0 (4)))
    (h4 : env (.n 229) = V (.W 1 0 4))
    (h5 : env (.n 165) = V (.A 1 0 (4)))
    (h6 : env (.n 197) = V (.A 1 0 (2)))
    (h7 : env (.n 181) = V (.A 1 0 (3)))
    (h8 : V (.A 1 0 (5)) = (V (.E 1 0 (1)) + Sigma1 (V (.E 1 0 (4))) + Ch (V (.E 1 0 (4))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) + V (.KW 1 0 4)) + (Sigma0 (V (.A 1 0 (4))) + Maj (V (.A 1 0 (4))) (V (.A 1 0 (3))) (V (.A 1 0 (2)))))
    (h9 : V (.KW 1 0 4) = 961987163#32 + V (.W 1 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.var (.n 229)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7)))) (.or (.and (.var (.n 165)) (.var (.n 197))) (.and (.xor (.var (.n 165)) (.var (.n 197))) (.var (.n 181))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 2) (.shl (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 30)) (.or (.shr (.var (.n 165)) 22) (.shl (.var (.n 165)) 10)))) = V (.A 1 0 (5)) :=
  shape12 (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.n 229)) (env (.n 165)) (env (.n 197)) (env (.n 181)) (V (.E 1 0 (1))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) (V (.E 1 0 (4))) (V (.W 1 0 4)) (V (.A 1 0 (4))) (V (.A 1 0 (2))) (V (.A 1 0 (3))) (V (.A 1 0 (5))) (V (.KW 1 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem core11_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 116) = V (.E 0 0 (3)))
    (h2 : env (.n 132) = V (.E 0 0 (2)))
    (h3 : env (.n 100) = V (.E 0 0 (4)))
    (h4 : env (.n 228) = V (.W 0 0 4))
    (h5 : env (.n 164) = V (.A 0 0 (4)))
    (h6 : env (.n 196) = V (.A 0 0 (2)))
    (h7 : env (.n 180) = V (.A 0 0 (3)))
    (h8 : V (.A 0 0 (5)) = (V (.E 0 0 (1)) + Sigma1 (V (.E 0 0 (4))) + Ch (V (.E 0 0 (4))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) + V (.KW 0 0 4)) + (Sigma0 (V (.A 0 0 (4))) + Maj (V (.A 0 0 (4))) (V (.A 0 0 (3))) (V (.A 0 0 (2)))))
    (h9 : V (.KW 0 0 4) = 961987163#32 + V (.W 0 0 4)) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.var (.n 228)) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7)))) (.or (.and (.var (.n 164)) (.var (.n 196))) (.and (.xor (.var (.n 164)) (.var (.n 196))) (.var (.n 180))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 2) (.shl (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 30)) (.or (.shr (.var (.n 164)) 22) (.shl (.var (.n 164)) 10)))) = V (.A 0 0 (5)) :=
  shape12 (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.n 228)) (env (.n 164)) (env (.n 196)) (env (.n 180)) (V (.E 0 0 (1))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (4))) (V (.W 0 0 4)) (V (.A 0 0 (4))) (V (.A 0 0 (2))) (V (.A 0 0 (3))) (V (.A 0 0 (5))) (V (.KW 0 0 4)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem step11 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L11) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 38 K11)) L12 := by
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
  exact invC_of_trees inp env _ T11 L12 (slice_trees_mem prog 4 _ _ 38 K11 K12 T11 slice11 env)
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
      (And.intro ⟨rfl, h279⟩
      (And.intro ⟨rfl, h279⟩
      (And.intro ⟨rfl, h279⟩
      (And.intro ⟨rfl, h279⟩
      (And.intro ⟨rfl, h278⟩
      (And.intro ⟨rfl, h278⟩
      (And.intro ⟨rfl, h278⟩
      (And.intro ⟨rfl, h278⟩
      (And.intro ⟨rfl, h277⟩
      (And.intro ⟨rfl, h277⟩
      (And.intro ⟨rfl, h277⟩
      (And.intro ⟨rfl, h277⟩
      (And.intro ⟨rfl, h276⟩
      (And.intro ⟨rfl, h276⟩
      (And.intro ⟨rfl, h276⟩
      (And.intro ⟨rfl, h276⟩
      (And.intro ⟨rfl, h275⟩
      (And.intro ⟨rfl, h275⟩
      (And.intro ⟨rfl, h275⟩
      (And.intro ⟨rfl, h275⟩
      (And.intro ⟨rfl, h274⟩
      (And.intro ⟨rfl, h274⟩
      (And.intro ⟨rfl, h274⟩
      (And.intro ⟨rfl, h274⟩
      (And.intro ⟨rfl, h273⟩
      (And.intro ⟨rfl, h273⟩
      (And.intro ⟨rfl, h273⟩
      (And.intro ⟨rfl, h273⟩
      (And.intro ⟨rfl, h272⟩
      (And.intro ⟨rfl, h272⟩
      (And.intro ⟨rfl, h272⟩
      (And.intro ⟨rfl, h272⟩
      (And.intro ⟨rfl, core11_283 (qv inp) inp env h124 h125 h126 h127⟩
      (And.intro ⟨rfl, core11_282 (qv inp) inp env h120 h121 h122 h123⟩
      (And.intro ⟨rfl, core11_281 (qv inp) inp env h116 h117 h118 h119⟩
      (And.intro ⟨rfl, core11_280 (qv inp) inp env h112 h113 h114 h115⟩
      (And.intro ⟨rfl, core11_279 (qv inp) inp env h108 h109 h110 h111⟩
      (And.intro ⟨rfl, core11_278 (qv inp) inp env h104 h105 h106 h107⟩
      (And.intro ⟨rfl, core11_277 (qv inp) inp env h100 h101 h102 h103⟩
      (And.intro ⟨rfl, core11_276 (qv inp) inp env h96 h97 h98 h99⟩
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
      (And.intro ⟨rfl, core11_219 (qv inp) inp env h280 h312 h328 h320 h336 h272 (qE_succI inp 7 0 (4) (by decide)) ((qKW inp 7 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_218 (qv inp) inp env h281 h313 h329 h321 h337 h273 (qE_succI inp 6 0 (4) (by decide)) ((qKW inp 6 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_217 (qv inp) inp env h282 h314 h330 h322 h338 h274 (qE_succI inp 5 0 (4) (by decide)) ((qKW inp 5 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_216 (qv inp) inp env h283 h315 h331 h323 h339 h275 (qE_succI inp 4 0 (4) (by decide)) ((qKW inp 4 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_215 (qv inp) inp env h284 h316 h332 h324 h340 h276 (qE_succI inp 3 0 (4) (by decide)) ((qKW inp 3 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_214 (qv inp) inp env h285 h317 h333 h325 h341 h277 (qE_succI inp 2 0 (4) (by decide)) ((qKW inp 2 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_213 (qv inp) inp env h286 h318 h334 h326 h342 h278 (qE_succI inp 1 0 (4) (by decide)) ((qKW inp 1 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_212 (qv inp) inp env h287 h319 h335 h327 h343 h279 (qE_succI inp 0 0 (4) (by decide)) ((qKW inp 0 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
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
      (And.intro ⟨rfl, core11_155 (qv inp) inp env h312 h328 h320 h336 h272 h304 h288 h296 (qA_succI inp 7 0 (4) (by decide)) ((qKW inp 7 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_154 (qv inp) inp env h313 h329 h321 h337 h273 h305 h289 h297 (qA_succI inp 6 0 (4) (by decide)) ((qKW inp 6 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_153 (qv inp) inp env h314 h330 h322 h338 h274 h306 h290 h298 (qA_succI inp 5 0 (4) (by decide)) ((qKW inp 5 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_152 (qv inp) inp env h315 h331 h323 h339 h275 h307 h291 h299 (qA_succI inp 4 0 (4) (by decide)) ((qKW inp 4 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_151 (qv inp) inp env h316 h332 h324 h340 h276 h308 h292 h300 (qA_succI inp 3 0 (4) (by decide)) ((qKW inp 3 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_150 (qv inp) inp env h317 h333 h325 h341 h277 h309 h293 h301 (qA_succI inp 2 0 (4) (by decide)) ((qKW inp 2 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_149 (qv inp) inp env h318 h334 h326 h342 h278 h310 h294 h302 (qA_succI inp 1 0 (4) (by decide)) ((qKW inp 1 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
      (And.intro ⟨rfl, core11_148 (qv inp) inp env h319 h335 h327 h343 h279 h311 h295 h303 (qA_succI inp 0 0 (4) (by decide)) ((qKW inp 0 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide]))⟩
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
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
