import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D7
import Hashtree.Gen.WinAvx2X8P.D6

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice7 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 64 K7 K8 T7 = true := by
  decide +kernel

theorem core7_1159 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 292) = V (.R 0 4))
    (h1 : V (.W 0 0 4) = bswap (V (.R 0 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 292)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 292)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 292)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 292)) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape1 (env (.n 292)) (V (.R 0 4)) (V (.W 0 0 4)) h0 h1

theorem core7_1158 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 292) = V (.R 0 4))
    (h1 : V (.W 0 0 4) = bswap (V (.R 0 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 292)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 292)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 292)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 292)) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape1 (env (.n 292)) (V (.R 0 4)) (V (.W 0 0 4)) h0 h1

theorem core7_1157 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 292) = V (.R 0 4))
    (h1 : V (.W 0 0 4) = bswap (V (.R 0 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 292)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 292)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 292)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 292)) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape1 (env (.n 292)) (V (.R 0 4)) (V (.W 0 0 4)) h0 h1

theorem core7_1156 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 292) = V (.R 0 4))
    (h1 : V (.W 0 0 4) = bswap (V (.R 0 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 292)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 292)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 292)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 292)) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape1 (env (.n 292)) (V (.R 0 4)) (V (.W 0 0 4)) h0 h1

theorem core7_1155 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 308) = V (.R 1 4))
    (h1 : V (.W 1 0 4) = bswap (V (.R 1 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 308)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 308)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 308)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 308)) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape1 (env (.n 308)) (V (.R 1 4)) (V (.W 1 0 4)) h0 h1

theorem core7_1154 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 308) = V (.R 1 4))
    (h1 : V (.W 1 0 4) = bswap (V (.R 1 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 308)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 308)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 308)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 308)) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape1 (env (.n 308)) (V (.R 1 4)) (V (.W 1 0 4)) h0 h1

theorem core7_1153 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 308) = V (.R 1 4))
    (h1 : V (.W 1 0 4) = bswap (V (.R 1 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 308)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 308)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 308)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 308)) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape1 (env (.n 308)) (V (.R 1 4)) (V (.W 1 0 4)) h0 h1

theorem core7_1152 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 308) = V (.R 1 4))
    (h1 : V (.W 1 0 4) = bswap (V (.R 1 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 308)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 308)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 308)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 308)) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape1 (env (.n 308)) (V (.R 1 4)) (V (.W 1 0 4)) h0 h1

theorem core7_1151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 324) = V (.R 2 4))
    (h1 : V (.W 2 0 4) = bswap (V (.R 2 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 324)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 324)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 324)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 324)) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape1 (env (.n 324)) (V (.R 2 4)) (V (.W 2 0 4)) h0 h1

theorem core7_1150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 324) = V (.R 2 4))
    (h1 : V (.W 2 0 4) = bswap (V (.R 2 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 324)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 324)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 324)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 324)) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape1 (env (.n 324)) (V (.R 2 4)) (V (.W 2 0 4)) h0 h1

theorem core7_1149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 324) = V (.R 2 4))
    (h1 : V (.W 2 0 4) = bswap (V (.R 2 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 324)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 324)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 324)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 324)) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape1 (env (.n 324)) (V (.R 2 4)) (V (.W 2 0 4)) h0 h1

theorem core7_1148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 324) = V (.R 2 4))
    (h1 : V (.W 2 0 4) = bswap (V (.R 2 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 324)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 324)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 324)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 324)) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape1 (env (.n 324)) (V (.R 2 4)) (V (.W 2 0 4)) h0 h1

theorem core7_1147 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 340) = V (.R 3 4))
    (h1 : V (.W 3 0 4) = bswap (V (.R 3 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 340)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 340)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 340)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 340)) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape1 (env (.n 340)) (V (.R 3 4)) (V (.W 3 0 4)) h0 h1

theorem core7_1146 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 340) = V (.R 3 4))
    (h1 : V (.W 3 0 4) = bswap (V (.R 3 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 340)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 340)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 340)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 340)) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape1 (env (.n 340)) (V (.R 3 4)) (V (.W 3 0 4)) h0 h1

theorem core7_1145 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 340) = V (.R 3 4))
    (h1 : V (.W 3 0 4) = bswap (V (.R 3 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 340)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 340)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 340)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 340)) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape1 (env (.n 340)) (V (.R 3 4)) (V (.W 3 0 4)) h0 h1

theorem core7_1144 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 340) = V (.R 3 4))
    (h1 : V (.W 3 0 4) = bswap (V (.R 3 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 340)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 340)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 340)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 340)) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape1 (env (.n 340)) (V (.R 3 4)) (V (.W 3 0 4)) h0 h1

theorem core7_1143 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 296) = V (.R 4 4))
    (h1 : V (.W 4 0 4) = bswap (V (.R 4 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 296)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 296)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 296)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 296)) 0) (.const 255)) 24))) = V (.W 4 0 4) :=
  shape1 (env (.n 296)) (V (.R 4 4)) (V (.W 4 0 4)) h0 h1

theorem core7_1142 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 296) = V (.R 4 4))
    (h1 : V (.W 4 0 4) = bswap (V (.R 4 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 296)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 296)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 296)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 296)) 0) (.const 255)) 24))) = V (.W 4 0 4) :=
  shape1 (env (.n 296)) (V (.R 4 4)) (V (.W 4 0 4)) h0 h1

theorem core7_1141 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 296) = V (.R 4 4))
    (h1 : V (.W 4 0 4) = bswap (V (.R 4 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 296)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 296)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 296)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 296)) 0) (.const 255)) 24))) = V (.W 4 0 4) :=
  shape1 (env (.n 296)) (V (.R 4 4)) (V (.W 4 0 4)) h0 h1

theorem core7_1140 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 296) = V (.R 4 4))
    (h1 : V (.W 4 0 4) = bswap (V (.R 4 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 296)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 296)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 296)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 296)) 0) (.const 255)) 24))) = V (.W 4 0 4) :=
  shape1 (env (.n 296)) (V (.R 4 4)) (V (.W 4 0 4)) h0 h1

theorem core7_1139 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 312) = V (.R 5 4))
    (h1 : V (.W 5 0 4) = bswap (V (.R 5 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 312)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 312)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 312)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 312)) 0) (.const 255)) 24))) = V (.W 5 0 4) :=
  shape1 (env (.n 312)) (V (.R 5 4)) (V (.W 5 0 4)) h0 h1

theorem core7_1138 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 312) = V (.R 5 4))
    (h1 : V (.W 5 0 4) = bswap (V (.R 5 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 312)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 312)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 312)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 312)) 0) (.const 255)) 24))) = V (.W 5 0 4) :=
  shape1 (env (.n 312)) (V (.R 5 4)) (V (.W 5 0 4)) h0 h1

theorem core7_1137 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 312) = V (.R 5 4))
    (h1 : V (.W 5 0 4) = bswap (V (.R 5 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 312)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 312)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 312)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 312)) 0) (.const 255)) 24))) = V (.W 5 0 4) :=
  shape1 (env (.n 312)) (V (.R 5 4)) (V (.W 5 0 4)) h0 h1

theorem core7_1136 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 312) = V (.R 5 4))
    (h1 : V (.W 5 0 4) = bswap (V (.R 5 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 312)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 312)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 312)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 312)) 0) (.const 255)) 24))) = V (.W 5 0 4) :=
  shape1 (env (.n 312)) (V (.R 5 4)) (V (.W 5 0 4)) h0 h1

theorem core7_1135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 328) = V (.R 6 4))
    (h1 : V (.W 6 0 4) = bswap (V (.R 6 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 328)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 328)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 328)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 328)) 0) (.const 255)) 24))) = V (.W 6 0 4) :=
  shape1 (env (.n 328)) (V (.R 6 4)) (V (.W 6 0 4)) h0 h1

theorem core7_1134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 328) = V (.R 6 4))
    (h1 : V (.W 6 0 4) = bswap (V (.R 6 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 328)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 328)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 328)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 328)) 0) (.const 255)) 24))) = V (.W 6 0 4) :=
  shape1 (env (.n 328)) (V (.R 6 4)) (V (.W 6 0 4)) h0 h1

theorem core7_1133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 328) = V (.R 6 4))
    (h1 : V (.W 6 0 4) = bswap (V (.R 6 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 328)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 328)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 328)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 328)) 0) (.const 255)) 24))) = V (.W 6 0 4) :=
  shape1 (env (.n 328)) (V (.R 6 4)) (V (.W 6 0 4)) h0 h1

theorem core7_1132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 328) = V (.R 6 4))
    (h1 : V (.W 6 0 4) = bswap (V (.R 6 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 328)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 328)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 328)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 328)) 0) (.const 255)) 24))) = V (.W 6 0 4) :=
  shape1 (env (.n 328)) (V (.R 6 4)) (V (.W 6 0 4)) h0 h1

theorem core7_1131 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 344) = V (.R 7 4))
    (h1 : V (.W 7 0 4) = bswap (V (.R 7 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 344)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 344)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 344)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 344)) 0) (.const 255)) 24))) = V (.W 7 0 4) :=
  shape1 (env (.n 344)) (V (.R 7 4)) (V (.W 7 0 4)) h0 h1

theorem core7_1130 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 344) = V (.R 7 4))
    (h1 : V (.W 7 0 4) = bswap (V (.R 7 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 344)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 344)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 344)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 344)) 0) (.const 255)) 24))) = V (.W 7 0 4) :=
  shape1 (env (.n 344)) (V (.R 7 4)) (V (.W 7 0 4)) h0 h1

theorem core7_1129 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 344) = V (.R 7 4))
    (h1 : V (.W 7 0 4) = bswap (V (.R 7 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 344)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 344)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 344)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 344)) 0) (.const 255)) 24))) = V (.W 7 0 4) :=
  shape1 (env (.n 344)) (V (.R 7 4)) (V (.W 7 0 4)) h0 h1

theorem core7_1128 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 344) = V (.R 7 4))
    (h1 : V (.W 7 0 4) = bswap (V (.R 7 4))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 344)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 344)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 344)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 344)) 0) (.const 255)) 24))) = V (.W 7 0 4) :=
  shape1 (env (.n 344)) (V (.R 7 4)) (V (.W 7 0 4)) h0 h1

theorem core7_1127 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 293) = V (.R 0 5))
    (h1 : V (.W 0 0 5) = bswap (V (.R 0 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 293)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 293)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 293)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 293)) 0) (.const 255)) 24))) = V (.W 0 0 5) :=
  shape1 (env (.n 293)) (V (.R 0 5)) (V (.W 0 0 5)) h0 h1

theorem core7_1126 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 293) = V (.R 0 5))
    (h1 : V (.W 0 0 5) = bswap (V (.R 0 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 293)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 293)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 293)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 293)) 0) (.const 255)) 24))) = V (.W 0 0 5) :=
  shape1 (env (.n 293)) (V (.R 0 5)) (V (.W 0 0 5)) h0 h1

theorem core7_1125 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 293) = V (.R 0 5))
    (h1 : V (.W 0 0 5) = bswap (V (.R 0 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 293)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 293)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 293)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 293)) 0) (.const 255)) 24))) = V (.W 0 0 5) :=
  shape1 (env (.n 293)) (V (.R 0 5)) (V (.W 0 0 5)) h0 h1

theorem core7_1124 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 293) = V (.R 0 5))
    (h1 : V (.W 0 0 5) = bswap (V (.R 0 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 293)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 293)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 293)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 293)) 0) (.const 255)) 24))) = V (.W 0 0 5) :=
  shape1 (env (.n 293)) (V (.R 0 5)) (V (.W 0 0 5)) h0 h1

theorem core7_1123 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 309) = V (.R 1 5))
    (h1 : V (.W 1 0 5) = bswap (V (.R 1 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 309)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 309)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 309)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 309)) 0) (.const 255)) 24))) = V (.W 1 0 5) :=
  shape1 (env (.n 309)) (V (.R 1 5)) (V (.W 1 0 5)) h0 h1

theorem core7_1122 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 309) = V (.R 1 5))
    (h1 : V (.W 1 0 5) = bswap (V (.R 1 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 309)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 309)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 309)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 309)) 0) (.const 255)) 24))) = V (.W 1 0 5) :=
  shape1 (env (.n 309)) (V (.R 1 5)) (V (.W 1 0 5)) h0 h1

theorem core7_1121 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 309) = V (.R 1 5))
    (h1 : V (.W 1 0 5) = bswap (V (.R 1 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 309)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 309)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 309)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 309)) 0) (.const 255)) 24))) = V (.W 1 0 5) :=
  shape1 (env (.n 309)) (V (.R 1 5)) (V (.W 1 0 5)) h0 h1

theorem core7_1120 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 309) = V (.R 1 5))
    (h1 : V (.W 1 0 5) = bswap (V (.R 1 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 309)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 309)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 309)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 309)) 0) (.const 255)) 24))) = V (.W 1 0 5) :=
  shape1 (env (.n 309)) (V (.R 1 5)) (V (.W 1 0 5)) h0 h1

theorem core7_1119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 325) = V (.R 2 5))
    (h1 : V (.W 2 0 5) = bswap (V (.R 2 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 325)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 325)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 325)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 325)) 0) (.const 255)) 24))) = V (.W 2 0 5) :=
  shape1 (env (.n 325)) (V (.R 2 5)) (V (.W 2 0 5)) h0 h1

theorem core7_1118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 325) = V (.R 2 5))
    (h1 : V (.W 2 0 5) = bswap (V (.R 2 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 325)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 325)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 325)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 325)) 0) (.const 255)) 24))) = V (.W 2 0 5) :=
  shape1 (env (.n 325)) (V (.R 2 5)) (V (.W 2 0 5)) h0 h1

theorem core7_1117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 325) = V (.R 2 5))
    (h1 : V (.W 2 0 5) = bswap (V (.R 2 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 325)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 325)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 325)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 325)) 0) (.const 255)) 24))) = V (.W 2 0 5) :=
  shape1 (env (.n 325)) (V (.R 2 5)) (V (.W 2 0 5)) h0 h1

theorem core7_1116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 325) = V (.R 2 5))
    (h1 : V (.W 2 0 5) = bswap (V (.R 2 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 325)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 325)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 325)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 325)) 0) (.const 255)) 24))) = V (.W 2 0 5) :=
  shape1 (env (.n 325)) (V (.R 2 5)) (V (.W 2 0 5)) h0 h1

theorem core7_1115 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 341) = V (.R 3 5))
    (h1 : V (.W 3 0 5) = bswap (V (.R 3 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 341)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 341)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 341)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 341)) 0) (.const 255)) 24))) = V (.W 3 0 5) :=
  shape1 (env (.n 341)) (V (.R 3 5)) (V (.W 3 0 5)) h0 h1

theorem core7_1114 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 341) = V (.R 3 5))
    (h1 : V (.W 3 0 5) = bswap (V (.R 3 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 341)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 341)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 341)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 341)) 0) (.const 255)) 24))) = V (.W 3 0 5) :=
  shape1 (env (.n 341)) (V (.R 3 5)) (V (.W 3 0 5)) h0 h1

theorem core7_1113 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 341) = V (.R 3 5))
    (h1 : V (.W 3 0 5) = bswap (V (.R 3 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 341)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 341)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 341)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 341)) 0) (.const 255)) 24))) = V (.W 3 0 5) :=
  shape1 (env (.n 341)) (V (.R 3 5)) (V (.W 3 0 5)) h0 h1

theorem core7_1112 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 341) = V (.R 3 5))
    (h1 : V (.W 3 0 5) = bswap (V (.R 3 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 341)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 341)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 341)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 341)) 0) (.const 255)) 24))) = V (.W 3 0 5) :=
  shape1 (env (.n 341)) (V (.R 3 5)) (V (.W 3 0 5)) h0 h1

theorem core7_1111 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 297) = V (.R 4 5))
    (h1 : V (.W 4 0 5) = bswap (V (.R 4 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 297)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 297)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 297)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 297)) 0) (.const 255)) 24))) = V (.W 4 0 5) :=
  shape1 (env (.n 297)) (V (.R 4 5)) (V (.W 4 0 5)) h0 h1

theorem core7_1110 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 297) = V (.R 4 5))
    (h1 : V (.W 4 0 5) = bswap (V (.R 4 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 297)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 297)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 297)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 297)) 0) (.const 255)) 24))) = V (.W 4 0 5) :=
  shape1 (env (.n 297)) (V (.R 4 5)) (V (.W 4 0 5)) h0 h1

theorem core7_1109 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 297) = V (.R 4 5))
    (h1 : V (.W 4 0 5) = bswap (V (.R 4 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 297)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 297)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 297)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 297)) 0) (.const 255)) 24))) = V (.W 4 0 5) :=
  shape1 (env (.n 297)) (V (.R 4 5)) (V (.W 4 0 5)) h0 h1

theorem core7_1108 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 297) = V (.R 4 5))
    (h1 : V (.W 4 0 5) = bswap (V (.R 4 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 297)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 297)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 297)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 297)) 0) (.const 255)) 24))) = V (.W 4 0 5) :=
  shape1 (env (.n 297)) (V (.R 4 5)) (V (.W 4 0 5)) h0 h1

theorem core7_1107 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 313) = V (.R 5 5))
    (h1 : V (.W 5 0 5) = bswap (V (.R 5 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 313)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 313)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 313)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 313)) 0) (.const 255)) 24))) = V (.W 5 0 5) :=
  shape1 (env (.n 313)) (V (.R 5 5)) (V (.W 5 0 5)) h0 h1

theorem core7_1106 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 313) = V (.R 5 5))
    (h1 : V (.W 5 0 5) = bswap (V (.R 5 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 313)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 313)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 313)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 313)) 0) (.const 255)) 24))) = V (.W 5 0 5) :=
  shape1 (env (.n 313)) (V (.R 5 5)) (V (.W 5 0 5)) h0 h1

theorem core7_1105 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 313) = V (.R 5 5))
    (h1 : V (.W 5 0 5) = bswap (V (.R 5 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 313)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 313)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 313)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 313)) 0) (.const 255)) 24))) = V (.W 5 0 5) :=
  shape1 (env (.n 313)) (V (.R 5 5)) (V (.W 5 0 5)) h0 h1

theorem core7_1104 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 313) = V (.R 5 5))
    (h1 : V (.W 5 0 5) = bswap (V (.R 5 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 313)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 313)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 313)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 313)) 0) (.const 255)) 24))) = V (.W 5 0 5) :=
  shape1 (env (.n 313)) (V (.R 5 5)) (V (.W 5 0 5)) h0 h1

theorem core7_1103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 329) = V (.R 6 5))
    (h1 : V (.W 6 0 5) = bswap (V (.R 6 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 329)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 329)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 329)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 329)) 0) (.const 255)) 24))) = V (.W 6 0 5) :=
  shape1 (env (.n 329)) (V (.R 6 5)) (V (.W 6 0 5)) h0 h1

theorem core7_1102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 329) = V (.R 6 5))
    (h1 : V (.W 6 0 5) = bswap (V (.R 6 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 329)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 329)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 329)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 329)) 0) (.const 255)) 24))) = V (.W 6 0 5) :=
  shape1 (env (.n 329)) (V (.R 6 5)) (V (.W 6 0 5)) h0 h1

theorem core7_1101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 329) = V (.R 6 5))
    (h1 : V (.W 6 0 5) = bswap (V (.R 6 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 329)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 329)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 329)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 329)) 0) (.const 255)) 24))) = V (.W 6 0 5) :=
  shape1 (env (.n 329)) (V (.R 6 5)) (V (.W 6 0 5)) h0 h1

theorem core7_1100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 329) = V (.R 6 5))
    (h1 : V (.W 6 0 5) = bswap (V (.R 6 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 329)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 329)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 329)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 329)) 0) (.const 255)) 24))) = V (.W 6 0 5) :=
  shape1 (env (.n 329)) (V (.R 6 5)) (V (.W 6 0 5)) h0 h1

theorem core7_1099 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 345) = V (.R 7 5))
    (h1 : V (.W 7 0 5) = bswap (V (.R 7 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 345)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 345)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 345)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 345)) 0) (.const 255)) 24))) = V (.W 7 0 5) :=
  shape1 (env (.n 345)) (V (.R 7 5)) (V (.W 7 0 5)) h0 h1

theorem core7_1098 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 345) = V (.R 7 5))
    (h1 : V (.W 7 0 5) = bswap (V (.R 7 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 345)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 345)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 345)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 345)) 0) (.const 255)) 24))) = V (.W 7 0 5) :=
  shape1 (env (.n 345)) (V (.R 7 5)) (V (.W 7 0 5)) h0 h1

theorem core7_1097 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 345) = V (.R 7 5))
    (h1 : V (.W 7 0 5) = bswap (V (.R 7 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 345)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 345)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 345)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 345)) 0) (.const 255)) 24))) = V (.W 7 0 5) :=
  shape1 (env (.n 345)) (V (.R 7 5)) (V (.W 7 0 5)) h0 h1

theorem core7_1096 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 345) = V (.R 7 5))
    (h1 : V (.W 7 0 5) = bswap (V (.R 7 5))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 345)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 345)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 345)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 345)) 0) (.const 255)) 24))) = V (.W 7 0 5) :=
  shape1 (env (.n 345)) (V (.R 7 5)) (V (.W 7 0 5)) h0 h1

theorem core7_1095 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 294) = V (.R 0 6))
    (h1 : V (.W 0 0 6) = bswap (V (.R 0 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 294)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 294)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 294)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 294)) 0) (.const 255)) 24))) = V (.W 0 0 6) :=
  shape1 (env (.n 294)) (V (.R 0 6)) (V (.W 0 0 6)) h0 h1

theorem core7_1094 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 294) = V (.R 0 6))
    (h1 : V (.W 0 0 6) = bswap (V (.R 0 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 294)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 294)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 294)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 294)) 0) (.const 255)) 24))) = V (.W 0 0 6) :=
  shape1 (env (.n 294)) (V (.R 0 6)) (V (.W 0 0 6)) h0 h1

theorem core7_1093 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 294) = V (.R 0 6))
    (h1 : V (.W 0 0 6) = bswap (V (.R 0 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 294)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 294)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 294)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 294)) 0) (.const 255)) 24))) = V (.W 0 0 6) :=
  shape1 (env (.n 294)) (V (.R 0 6)) (V (.W 0 0 6)) h0 h1

theorem core7_1092 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 294) = V (.R 0 6))
    (h1 : V (.W 0 0 6) = bswap (V (.R 0 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 294)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 294)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 294)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 294)) 0) (.const 255)) 24))) = V (.W 0 0 6) :=
  shape1 (env (.n 294)) (V (.R 0 6)) (V (.W 0 0 6)) h0 h1

theorem core7_1091 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 310) = V (.R 1 6))
    (h1 : V (.W 1 0 6) = bswap (V (.R 1 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 310)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 310)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 310)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 310)) 0) (.const 255)) 24))) = V (.W 1 0 6) :=
  shape1 (env (.n 310)) (V (.R 1 6)) (V (.W 1 0 6)) h0 h1

theorem core7_1090 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 310) = V (.R 1 6))
    (h1 : V (.W 1 0 6) = bswap (V (.R 1 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 310)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 310)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 310)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 310)) 0) (.const 255)) 24))) = V (.W 1 0 6) :=
  shape1 (env (.n 310)) (V (.R 1 6)) (V (.W 1 0 6)) h0 h1

theorem core7_1089 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 310) = V (.R 1 6))
    (h1 : V (.W 1 0 6) = bswap (V (.R 1 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 310)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 310)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 310)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 310)) 0) (.const 255)) 24))) = V (.W 1 0 6) :=
  shape1 (env (.n 310)) (V (.R 1 6)) (V (.W 1 0 6)) h0 h1

theorem core7_1088 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 310) = V (.R 1 6))
    (h1 : V (.W 1 0 6) = bswap (V (.R 1 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 310)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 310)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 310)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 310)) 0) (.const 255)) 24))) = V (.W 1 0 6) :=
  shape1 (env (.n 310)) (V (.R 1 6)) (V (.W 1 0 6)) h0 h1

theorem core7_1087 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 326) = V (.R 2 6))
    (h1 : V (.W 2 0 6) = bswap (V (.R 2 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 326)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 326)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 326)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 326)) 0) (.const 255)) 24))) = V (.W 2 0 6) :=
  shape1 (env (.n 326)) (V (.R 2 6)) (V (.W 2 0 6)) h0 h1

theorem core7_1086 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 326) = V (.R 2 6))
    (h1 : V (.W 2 0 6) = bswap (V (.R 2 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 326)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 326)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 326)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 326)) 0) (.const 255)) 24))) = V (.W 2 0 6) :=
  shape1 (env (.n 326)) (V (.R 2 6)) (V (.W 2 0 6)) h0 h1

theorem core7_1085 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 326) = V (.R 2 6))
    (h1 : V (.W 2 0 6) = bswap (V (.R 2 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 326)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 326)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 326)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 326)) 0) (.const 255)) 24))) = V (.W 2 0 6) :=
  shape1 (env (.n 326)) (V (.R 2 6)) (V (.W 2 0 6)) h0 h1

theorem core7_1084 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 326) = V (.R 2 6))
    (h1 : V (.W 2 0 6) = bswap (V (.R 2 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 326)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 326)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 326)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 326)) 0) (.const 255)) 24))) = V (.W 2 0 6) :=
  shape1 (env (.n 326)) (V (.R 2 6)) (V (.W 2 0 6)) h0 h1

theorem core7_1083 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 342) = V (.R 3 6))
    (h1 : V (.W 3 0 6) = bswap (V (.R 3 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 342)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 342)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 342)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 342)) 0) (.const 255)) 24))) = V (.W 3 0 6) :=
  shape1 (env (.n 342)) (V (.R 3 6)) (V (.W 3 0 6)) h0 h1

theorem core7_1082 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 342) = V (.R 3 6))
    (h1 : V (.W 3 0 6) = bswap (V (.R 3 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 342)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 342)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 342)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 342)) 0) (.const 255)) 24))) = V (.W 3 0 6) :=
  shape1 (env (.n 342)) (V (.R 3 6)) (V (.W 3 0 6)) h0 h1

theorem core7_1081 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 342) = V (.R 3 6))
    (h1 : V (.W 3 0 6) = bswap (V (.R 3 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 342)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 342)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 342)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 342)) 0) (.const 255)) 24))) = V (.W 3 0 6) :=
  shape1 (env (.n 342)) (V (.R 3 6)) (V (.W 3 0 6)) h0 h1

theorem core7_1080 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 342) = V (.R 3 6))
    (h1 : V (.W 3 0 6) = bswap (V (.R 3 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 342)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 342)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 342)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 342)) 0) (.const 255)) 24))) = V (.W 3 0 6) :=
  shape1 (env (.n 342)) (V (.R 3 6)) (V (.W 3 0 6)) h0 h1

theorem core7_1079 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 298) = V (.R 4 6))
    (h1 : V (.W 4 0 6) = bswap (V (.R 4 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 298)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 298)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 298)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 298)) 0) (.const 255)) 24))) = V (.W 4 0 6) :=
  shape1 (env (.n 298)) (V (.R 4 6)) (V (.W 4 0 6)) h0 h1

theorem core7_1078 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 298) = V (.R 4 6))
    (h1 : V (.W 4 0 6) = bswap (V (.R 4 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 298)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 298)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 298)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 298)) 0) (.const 255)) 24))) = V (.W 4 0 6) :=
  shape1 (env (.n 298)) (V (.R 4 6)) (V (.W 4 0 6)) h0 h1

theorem core7_1077 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 298) = V (.R 4 6))
    (h1 : V (.W 4 0 6) = bswap (V (.R 4 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 298)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 298)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 298)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 298)) 0) (.const 255)) 24))) = V (.W 4 0 6) :=
  shape1 (env (.n 298)) (V (.R 4 6)) (V (.W 4 0 6)) h0 h1

theorem core7_1076 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 298) = V (.R 4 6))
    (h1 : V (.W 4 0 6) = bswap (V (.R 4 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 298)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 298)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 298)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 298)) 0) (.const 255)) 24))) = V (.W 4 0 6) :=
  shape1 (env (.n 298)) (V (.R 4 6)) (V (.W 4 0 6)) h0 h1

theorem core7_1075 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 314) = V (.R 5 6))
    (h1 : V (.W 5 0 6) = bswap (V (.R 5 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 314)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 314)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 314)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 314)) 0) (.const 255)) 24))) = V (.W 5 0 6) :=
  shape1 (env (.n 314)) (V (.R 5 6)) (V (.W 5 0 6)) h0 h1

theorem core7_1074 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 314) = V (.R 5 6))
    (h1 : V (.W 5 0 6) = bswap (V (.R 5 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 314)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 314)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 314)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 314)) 0) (.const 255)) 24))) = V (.W 5 0 6) :=
  shape1 (env (.n 314)) (V (.R 5 6)) (V (.W 5 0 6)) h0 h1

theorem core7_1073 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 314) = V (.R 5 6))
    (h1 : V (.W 5 0 6) = bswap (V (.R 5 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 314)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 314)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 314)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 314)) 0) (.const 255)) 24))) = V (.W 5 0 6) :=
  shape1 (env (.n 314)) (V (.R 5 6)) (V (.W 5 0 6)) h0 h1

theorem core7_1072 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 314) = V (.R 5 6))
    (h1 : V (.W 5 0 6) = bswap (V (.R 5 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 314)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 314)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 314)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 314)) 0) (.const 255)) 24))) = V (.W 5 0 6) :=
  shape1 (env (.n 314)) (V (.R 5 6)) (V (.W 5 0 6)) h0 h1

theorem core7_1071 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 330) = V (.R 6 6))
    (h1 : V (.W 6 0 6) = bswap (V (.R 6 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 330)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 330)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 330)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 330)) 0) (.const 255)) 24))) = V (.W 6 0 6) :=
  shape1 (env (.n 330)) (V (.R 6 6)) (V (.W 6 0 6)) h0 h1

theorem core7_1070 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 330) = V (.R 6 6))
    (h1 : V (.W 6 0 6) = bswap (V (.R 6 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 330)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 330)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 330)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 330)) 0) (.const 255)) 24))) = V (.W 6 0 6) :=
  shape1 (env (.n 330)) (V (.R 6 6)) (V (.W 6 0 6)) h0 h1

theorem core7_1069 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 330) = V (.R 6 6))
    (h1 : V (.W 6 0 6) = bswap (V (.R 6 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 330)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 330)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 330)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 330)) 0) (.const 255)) 24))) = V (.W 6 0 6) :=
  shape1 (env (.n 330)) (V (.R 6 6)) (V (.W 6 0 6)) h0 h1

theorem core7_1068 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 330) = V (.R 6 6))
    (h1 : V (.W 6 0 6) = bswap (V (.R 6 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 330)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 330)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 330)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 330)) 0) (.const 255)) 24))) = V (.W 6 0 6) :=
  shape1 (env (.n 330)) (V (.R 6 6)) (V (.W 6 0 6)) h0 h1

theorem core7_1067 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 346) = V (.R 7 6))
    (h1 : V (.W 7 0 6) = bswap (V (.R 7 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 346)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 346)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 346)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 346)) 0) (.const 255)) 24))) = V (.W 7 0 6) :=
  shape1 (env (.n 346)) (V (.R 7 6)) (V (.W 7 0 6)) h0 h1

theorem core7_1066 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 346) = V (.R 7 6))
    (h1 : V (.W 7 0 6) = bswap (V (.R 7 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 346)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 346)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 346)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 346)) 0) (.const 255)) 24))) = V (.W 7 0 6) :=
  shape1 (env (.n 346)) (V (.R 7 6)) (V (.W 7 0 6)) h0 h1

theorem core7_1065 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 346) = V (.R 7 6))
    (h1 : V (.W 7 0 6) = bswap (V (.R 7 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 346)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 346)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 346)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 346)) 0) (.const 255)) 24))) = V (.W 7 0 6) :=
  shape1 (env (.n 346)) (V (.R 7 6)) (V (.W 7 0 6)) h0 h1

theorem core7_1064 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 346) = V (.R 7 6))
    (h1 : V (.W 7 0 6) = bswap (V (.R 7 6))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 346)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 346)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 346)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 346)) 0) (.const 255)) 24))) = V (.W 7 0 6) :=
  shape1 (env (.n 346)) (V (.R 7 6)) (V (.W 7 0 6)) h0 h1

theorem core7_1063 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 295) = V (.R 0 7))
    (h1 : V (.W 0 0 7) = bswap (V (.R 0 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 295)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 295)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 295)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 295)) 0) (.const 255)) 24))) = V (.W 0 0 7) :=
  shape1 (env (.n 295)) (V (.R 0 7)) (V (.W 0 0 7)) h0 h1

theorem core7_1062 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 295) = V (.R 0 7))
    (h1 : V (.W 0 0 7) = bswap (V (.R 0 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 295)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 295)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 295)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 295)) 0) (.const 255)) 24))) = V (.W 0 0 7) :=
  shape1 (env (.n 295)) (V (.R 0 7)) (V (.W 0 0 7)) h0 h1

theorem core7_1061 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 295) = V (.R 0 7))
    (h1 : V (.W 0 0 7) = bswap (V (.R 0 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 295)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 295)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 295)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 295)) 0) (.const 255)) 24))) = V (.W 0 0 7) :=
  shape1 (env (.n 295)) (V (.R 0 7)) (V (.W 0 0 7)) h0 h1

theorem core7_1060 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 295) = V (.R 0 7))
    (h1 : V (.W 0 0 7) = bswap (V (.R 0 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 295)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 295)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 295)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 295)) 0) (.const 255)) 24))) = V (.W 0 0 7) :=
  shape1 (env (.n 295)) (V (.R 0 7)) (V (.W 0 0 7)) h0 h1

theorem core7_1059 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 311) = V (.R 1 7))
    (h1 : V (.W 1 0 7) = bswap (V (.R 1 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 311)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 311)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 311)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 311)) 0) (.const 255)) 24))) = V (.W 1 0 7) :=
  shape1 (env (.n 311)) (V (.R 1 7)) (V (.W 1 0 7)) h0 h1

theorem core7_1058 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 311) = V (.R 1 7))
    (h1 : V (.W 1 0 7) = bswap (V (.R 1 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 311)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 311)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 311)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 311)) 0) (.const 255)) 24))) = V (.W 1 0 7) :=
  shape1 (env (.n 311)) (V (.R 1 7)) (V (.W 1 0 7)) h0 h1

theorem core7_1057 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 311) = V (.R 1 7))
    (h1 : V (.W 1 0 7) = bswap (V (.R 1 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 311)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 311)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 311)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 311)) 0) (.const 255)) 24))) = V (.W 1 0 7) :=
  shape1 (env (.n 311)) (V (.R 1 7)) (V (.W 1 0 7)) h0 h1

theorem core7_1056 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 311) = V (.R 1 7))
    (h1 : V (.W 1 0 7) = bswap (V (.R 1 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 311)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 311)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 311)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 311)) 0) (.const 255)) 24))) = V (.W 1 0 7) :=
  shape1 (env (.n 311)) (V (.R 1 7)) (V (.W 1 0 7)) h0 h1

theorem core7_1055 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 327) = V (.R 2 7))
    (h1 : V (.W 2 0 7) = bswap (V (.R 2 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 327)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 327)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 327)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 327)) 0) (.const 255)) 24))) = V (.W 2 0 7) :=
  shape1 (env (.n 327)) (V (.R 2 7)) (V (.W 2 0 7)) h0 h1

theorem core7_1054 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 327) = V (.R 2 7))
    (h1 : V (.W 2 0 7) = bswap (V (.R 2 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 327)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 327)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 327)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 327)) 0) (.const 255)) 24))) = V (.W 2 0 7) :=
  shape1 (env (.n 327)) (V (.R 2 7)) (V (.W 2 0 7)) h0 h1

theorem core7_1053 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 327) = V (.R 2 7))
    (h1 : V (.W 2 0 7) = bswap (V (.R 2 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 327)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 327)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 327)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 327)) 0) (.const 255)) 24))) = V (.W 2 0 7) :=
  shape1 (env (.n 327)) (V (.R 2 7)) (V (.W 2 0 7)) h0 h1

theorem core7_1052 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 327) = V (.R 2 7))
    (h1 : V (.W 2 0 7) = bswap (V (.R 2 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 327)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 327)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 327)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 327)) 0) (.const 255)) 24))) = V (.W 2 0 7) :=
  shape1 (env (.n 327)) (V (.R 2 7)) (V (.W 2 0 7)) h0 h1

theorem core7_1051 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 343) = V (.R 3 7))
    (h1 : V (.W 3 0 7) = bswap (V (.R 3 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 343)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 343)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 343)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 343)) 0) (.const 255)) 24))) = V (.W 3 0 7) :=
  shape1 (env (.n 343)) (V (.R 3 7)) (V (.W 3 0 7)) h0 h1

theorem core7_1050 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 343) = V (.R 3 7))
    (h1 : V (.W 3 0 7) = bswap (V (.R 3 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 343)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 343)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 343)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 343)) 0) (.const 255)) 24))) = V (.W 3 0 7) :=
  shape1 (env (.n 343)) (V (.R 3 7)) (V (.W 3 0 7)) h0 h1

theorem core7_1049 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 343) = V (.R 3 7))
    (h1 : V (.W 3 0 7) = bswap (V (.R 3 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 343)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 343)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 343)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 343)) 0) (.const 255)) 24))) = V (.W 3 0 7) :=
  shape1 (env (.n 343)) (V (.R 3 7)) (V (.W 3 0 7)) h0 h1

theorem core7_1048 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 343) = V (.R 3 7))
    (h1 : V (.W 3 0 7) = bswap (V (.R 3 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 343)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 343)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 343)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 343)) 0) (.const 255)) 24))) = V (.W 3 0 7) :=
  shape1 (env (.n 343)) (V (.R 3 7)) (V (.W 3 0 7)) h0 h1

theorem core7_1047 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 299) = V (.R 4 7))
    (h1 : V (.W 4 0 7) = bswap (V (.R 4 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 299)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 299)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 299)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 299)) 0) (.const 255)) 24))) = V (.W 4 0 7) :=
  shape1 (env (.n 299)) (V (.R 4 7)) (V (.W 4 0 7)) h0 h1

theorem core7_1046 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 299) = V (.R 4 7))
    (h1 : V (.W 4 0 7) = bswap (V (.R 4 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 299)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 299)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 299)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 299)) 0) (.const 255)) 24))) = V (.W 4 0 7) :=
  shape1 (env (.n 299)) (V (.R 4 7)) (V (.W 4 0 7)) h0 h1

theorem core7_1045 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 299) = V (.R 4 7))
    (h1 : V (.W 4 0 7) = bswap (V (.R 4 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 299)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 299)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 299)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 299)) 0) (.const 255)) 24))) = V (.W 4 0 7) :=
  shape1 (env (.n 299)) (V (.R 4 7)) (V (.W 4 0 7)) h0 h1

theorem core7_1044 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 299) = V (.R 4 7))
    (h1 : V (.W 4 0 7) = bswap (V (.R 4 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 299)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 299)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 299)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 299)) 0) (.const 255)) 24))) = V (.W 4 0 7) :=
  shape1 (env (.n 299)) (V (.R 4 7)) (V (.W 4 0 7)) h0 h1

theorem core7_1043 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 315) = V (.R 5 7))
    (h1 : V (.W 5 0 7) = bswap (V (.R 5 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 315)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 315)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 315)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 315)) 0) (.const 255)) 24))) = V (.W 5 0 7) :=
  shape1 (env (.n 315)) (V (.R 5 7)) (V (.W 5 0 7)) h0 h1

theorem core7_1042 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 315) = V (.R 5 7))
    (h1 : V (.W 5 0 7) = bswap (V (.R 5 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 315)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 315)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 315)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 315)) 0) (.const 255)) 24))) = V (.W 5 0 7) :=
  shape1 (env (.n 315)) (V (.R 5 7)) (V (.W 5 0 7)) h0 h1

theorem core7_1041 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 315) = V (.R 5 7))
    (h1 : V (.W 5 0 7) = bswap (V (.R 5 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 315)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 315)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 315)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 315)) 0) (.const 255)) 24))) = V (.W 5 0 7) :=
  shape1 (env (.n 315)) (V (.R 5 7)) (V (.W 5 0 7)) h0 h1

theorem core7_1040 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 315) = V (.R 5 7))
    (h1 : V (.W 5 0 7) = bswap (V (.R 5 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 315)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 315)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 315)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 315)) 0) (.const 255)) 24))) = V (.W 5 0 7) :=
  shape1 (env (.n 315)) (V (.R 5 7)) (V (.W 5 0 7)) h0 h1

theorem core7_1039 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 331) = V (.R 6 7))
    (h1 : V (.W 6 0 7) = bswap (V (.R 6 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 331)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 331)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 331)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 331)) 0) (.const 255)) 24))) = V (.W 6 0 7) :=
  shape1 (env (.n 331)) (V (.R 6 7)) (V (.W 6 0 7)) h0 h1

theorem core7_1038 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 331) = V (.R 6 7))
    (h1 : V (.W 6 0 7) = bswap (V (.R 6 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 331)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 331)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 331)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 331)) 0) (.const 255)) 24))) = V (.W 6 0 7) :=
  shape1 (env (.n 331)) (V (.R 6 7)) (V (.W 6 0 7)) h0 h1

theorem core7_1037 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 331) = V (.R 6 7))
    (h1 : V (.W 6 0 7) = bswap (V (.R 6 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 331)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 331)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 331)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 331)) 0) (.const 255)) 24))) = V (.W 6 0 7) :=
  shape1 (env (.n 331)) (V (.R 6 7)) (V (.W 6 0 7)) h0 h1

theorem core7_1036 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 331) = V (.R 6 7))
    (h1 : V (.W 6 0 7) = bswap (V (.R 6 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 331)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 331)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 331)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 331)) 0) (.const 255)) 24))) = V (.W 6 0 7) :=
  shape1 (env (.n 331)) (V (.R 6 7)) (V (.W 6 0 7)) h0 h1

theorem core7_1035 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 347) = V (.R 7 7))
    (h1 : V (.W 7 0 7) = bswap (V (.R 7 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 347)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 347)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 347)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 347)) 0) (.const 255)) 24))) = V (.W 7 0 7) :=
  shape1 (env (.n 347)) (V (.R 7 7)) (V (.W 7 0 7)) h0 h1

theorem core7_1034 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 347) = V (.R 7 7))
    (h1 : V (.W 7 0 7) = bswap (V (.R 7 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 347)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 347)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 347)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 347)) 0) (.const 255)) 24))) = V (.W 7 0 7) :=
  shape1 (env (.n 347)) (V (.R 7 7)) (V (.W 7 0 7)) h0 h1

theorem core7_1033 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 347) = V (.R 7 7))
    (h1 : V (.W 7 0 7) = bswap (V (.R 7 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 347)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 347)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 347)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 347)) 0) (.const 255)) 24))) = V (.W 7 0 7) :=
  shape1 (env (.n 347)) (V (.R 7 7)) (V (.W 7 0 7)) h0 h1

theorem core7_1032 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 347) = V (.R 7 7))
    (h1 : V (.W 7 0 7) = bswap (V (.R 7 7))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 347)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 347)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 347)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 347)) 0) (.const 255)) 24))) = V (.W 7 0 7) :=
  shape1 (env (.n 347)) (V (.R 7 7)) (V (.W 7 0 7)) h0 h1

theorem core7_1031 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 196) = V (.R 0 0))
    (h1 : V (.W 0 0 0) = bswap (V (.R 0 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 196)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 196)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 196)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 196)) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape1 (env (.n 196)) (V (.R 0 0)) (V (.W 0 0 0)) h0 h1

theorem core7_1030 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 196) = V (.R 0 0))
    (h1 : V (.W 0 0 0) = bswap (V (.R 0 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 196)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 196)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 196)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 196)) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape1 (env (.n 196)) (V (.R 0 0)) (V (.W 0 0 0)) h0 h1

theorem core7_1029 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 196) = V (.R 0 0))
    (h1 : V (.W 0 0 0) = bswap (V (.R 0 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 196)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 196)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 196)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 196)) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape1 (env (.n 196)) (V (.R 0 0)) (V (.W 0 0 0)) h0 h1

theorem core7_1028 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 196) = V (.R 0 0))
    (h1 : V (.W 0 0 0) = bswap (V (.R 0 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 196)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 196)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 196)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 196)) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape1 (env (.n 196)) (V (.R 0 0)) (V (.W 0 0 0)) h0 h1

theorem core7_1027 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 198) = V (.R 1 0))
    (h1 : V (.W 1 0 0) = bswap (V (.R 1 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 198)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 198)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 198)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 198)) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape1 (env (.n 198)) (V (.R 1 0)) (V (.W 1 0 0)) h0 h1

theorem core7_1026 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 198) = V (.R 1 0))
    (h1 : V (.W 1 0 0) = bswap (V (.R 1 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 198)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 198)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 198)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 198)) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape1 (env (.n 198)) (V (.R 1 0)) (V (.W 1 0 0)) h0 h1

theorem core7_1025 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 198) = V (.R 1 0))
    (h1 : V (.W 1 0 0) = bswap (V (.R 1 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 198)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 198)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 198)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 198)) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape1 (env (.n 198)) (V (.R 1 0)) (V (.W 1 0 0)) h0 h1

theorem core7_1024 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 198) = V (.R 1 0))
    (h1 : V (.W 1 0 0) = bswap (V (.R 1 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 198)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 198)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 198)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 198)) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape1 (env (.n 198)) (V (.R 1 0)) (V (.W 1 0 0)) h0 h1

theorem core7_1023 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.R 2 0))
    (h1 : V (.W 2 0 0) = bswap (V (.R 2 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 212)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 212)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 212)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 212)) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape1 (env (.n 212)) (V (.R 2 0)) (V (.W 2 0 0)) h0 h1

theorem core7_1022 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.R 2 0))
    (h1 : V (.W 2 0 0) = bswap (V (.R 2 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 212)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 212)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 212)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 212)) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape1 (env (.n 212)) (V (.R 2 0)) (V (.W 2 0 0)) h0 h1

theorem core7_1021 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.R 2 0))
    (h1 : V (.W 2 0 0) = bswap (V (.R 2 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 212)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 212)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 212)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 212)) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape1 (env (.n 212)) (V (.R 2 0)) (V (.W 2 0 0)) h0 h1

theorem core7_1020 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.R 2 0))
    (h1 : V (.W 2 0 0) = bswap (V (.R 2 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 212)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 212)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 212)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 212)) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape1 (env (.n 212)) (V (.R 2 0)) (V (.W 2 0 0)) h0 h1

theorem core7_1019 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.R 3 0))
    (h1 : V (.W 3 0 0) = bswap (V (.R 3 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 214)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 214)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 214)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 214)) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape1 (env (.n 214)) (V (.R 3 0)) (V (.W 3 0 0)) h0 h1

theorem core7_1018 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.R 3 0))
    (h1 : V (.W 3 0 0) = bswap (V (.R 3 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 214)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 214)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 214)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 214)) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape1 (env (.n 214)) (V (.R 3 0)) (V (.W 3 0 0)) h0 h1

theorem core7_1017 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.R 3 0))
    (h1 : V (.W 3 0 0) = bswap (V (.R 3 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 214)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 214)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 214)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 214)) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape1 (env (.n 214)) (V (.R 3 0)) (V (.W 3 0 0)) h0 h1

theorem core7_1016 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.R 3 0))
    (h1 : V (.W 3 0 0) = bswap (V (.R 3 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 214)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 214)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 214)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 214)) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape1 (env (.n 214)) (V (.R 3 0)) (V (.W 3 0 0)) h0 h1

theorem core7_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 200) = V (.R 4 0))
    (h1 : V (.W 4 0 0) = bswap (V (.R 4 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 200)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 200)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 200)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 200)) 0) (.const 255)) 24))) = V (.W 4 0 0) :=
  shape1 (env (.n 200)) (V (.R 4 0)) (V (.W 4 0 0)) h0 h1

theorem core7_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 200) = V (.R 4 0))
    (h1 : V (.W 4 0 0) = bswap (V (.R 4 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 200)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 200)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 200)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 200)) 0) (.const 255)) 24))) = V (.W 4 0 0) :=
  shape1 (env (.n 200)) (V (.R 4 0)) (V (.W 4 0 0)) h0 h1

theorem core7_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 200) = V (.R 4 0))
    (h1 : V (.W 4 0 0) = bswap (V (.R 4 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 200)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 200)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 200)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 200)) 0) (.const 255)) 24))) = V (.W 4 0 0) :=
  shape1 (env (.n 200)) (V (.R 4 0)) (V (.W 4 0 0)) h0 h1

theorem core7_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 200) = V (.R 4 0))
    (h1 : V (.W 4 0 0) = bswap (V (.R 4 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 200)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 200)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 200)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 200)) 0) (.const 255)) 24))) = V (.W 4 0 0) :=
  shape1 (env (.n 200)) (V (.R 4 0)) (V (.W 4 0 0)) h0 h1

theorem core7_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 202) = V (.R 5 0))
    (h1 : V (.W 5 0 0) = bswap (V (.R 5 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 202)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 202)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 202)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 202)) 0) (.const 255)) 24))) = V (.W 5 0 0) :=
  shape1 (env (.n 202)) (V (.R 5 0)) (V (.W 5 0 0)) h0 h1

theorem core7_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 202) = V (.R 5 0))
    (h1 : V (.W 5 0 0) = bswap (V (.R 5 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 202)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 202)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 202)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 202)) 0) (.const 255)) 24))) = V (.W 5 0 0) :=
  shape1 (env (.n 202)) (V (.R 5 0)) (V (.W 5 0 0)) h0 h1

theorem core7_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 202) = V (.R 5 0))
    (h1 : V (.W 5 0 0) = bswap (V (.R 5 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 202)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 202)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 202)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 202)) 0) (.const 255)) 24))) = V (.W 5 0 0) :=
  shape1 (env (.n 202)) (V (.R 5 0)) (V (.W 5 0 0)) h0 h1

theorem core7_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 202) = V (.R 5 0))
    (h1 : V (.W 5 0 0) = bswap (V (.R 5 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 202)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 202)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 202)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 202)) 0) (.const 255)) 24))) = V (.W 5 0 0) :=
  shape1 (env (.n 202)) (V (.R 5 0)) (V (.W 5 0 0)) h0 h1

theorem core7_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.R 6 0))
    (h1 : V (.W 6 0 0) = bswap (V (.R 6 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 216)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 216)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 216)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 216)) 0) (.const 255)) 24))) = V (.W 6 0 0) :=
  shape1 (env (.n 216)) (V (.R 6 0)) (V (.W 6 0 0)) h0 h1

theorem core7_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.R 6 0))
    (h1 : V (.W 6 0 0) = bswap (V (.R 6 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 216)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 216)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 216)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 216)) 0) (.const 255)) 24))) = V (.W 6 0 0) :=
  shape1 (env (.n 216)) (V (.R 6 0)) (V (.W 6 0 0)) h0 h1

theorem core7_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.R 6 0))
    (h1 : V (.W 6 0 0) = bswap (V (.R 6 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 216)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 216)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 216)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 216)) 0) (.const 255)) 24))) = V (.W 6 0 0) :=
  shape1 (env (.n 216)) (V (.R 6 0)) (V (.W 6 0 0)) h0 h1

theorem core7_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.R 6 0))
    (h1 : V (.W 6 0 0) = bswap (V (.R 6 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 216)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 216)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 216)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 216)) 0) (.const 255)) 24))) = V (.W 6 0 0) :=
  shape1 (env (.n 216)) (V (.R 6 0)) (V (.W 6 0 0)) h0 h1

theorem core7_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.R 7 0))
    (h1 : V (.W 7 0 0) = bswap (V (.R 7 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 218)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 218)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 218)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 218)) 0) (.const 255)) 24))) = V (.W 7 0 0) :=
  shape1 (env (.n 218)) (V (.R 7 0)) (V (.W 7 0 0)) h0 h1

theorem core7_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.R 7 0))
    (h1 : V (.W 7 0 0) = bswap (V (.R 7 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 218)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 218)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 218)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 218)) 0) (.const 255)) 24))) = V (.W 7 0 0) :=
  shape1 (env (.n 218)) (V (.R 7 0)) (V (.W 7 0 0)) h0 h1

theorem core7_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.R 7 0))
    (h1 : V (.W 7 0 0) = bswap (V (.R 7 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 218)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 218)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 218)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 218)) 0) (.const 255)) 24))) = V (.W 7 0 0) :=
  shape1 (env (.n 218)) (V (.R 7 0)) (V (.W 7 0 0)) h0 h1

theorem core7_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.R 7 0))
    (h1 : V (.W 7 0 0) = bswap (V (.R 7 0))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 218)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 218)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 218)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 218)) 0) (.const 255)) 24))) = V (.W 7 0 0) :=
  shape1 (env (.n 218)) (V (.R 7 0)) (V (.W 7 0 0)) h0 h1

theorem core7_283 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 267) = V (.R 7 3))
    (h1 : V (.W 7 0 3) = bswap (V (.R 7 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 267)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 267)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 267)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 267)) 0) (.const 255)) 24))) = V (.W 7 0 3) :=
  shape1 (env (.n 267)) (V (.R 7 3)) (V (.W 7 0 3)) h0 h1

theorem core7_282 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 265) = V (.R 6 3))
    (h1 : V (.W 6 0 3) = bswap (V (.R 6 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 265)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 265)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 265)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 265)) 0) (.const 255)) 24))) = V (.W 6 0 3) :=
  shape1 (env (.n 265)) (V (.R 6 3)) (V (.W 6 0 3)) h0 h1

theorem core7_281 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 235) = V (.R 5 3))
    (h1 : V (.W 5 0 3) = bswap (V (.R 5 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 235)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 235)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 235)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 235)) 0) (.const 255)) 24))) = V (.W 5 0 3) :=
  shape1 (env (.n 235)) (V (.R 5 3)) (V (.W 5 0 3)) h0 h1

theorem core7_280 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 233) = V (.R 4 3))
    (h1 : V (.W 4 0 3) = bswap (V (.R 4 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 233)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 233)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 233)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 233)) 0) (.const 255)) 24))) = V (.W 4 0 3) :=
  shape1 (env (.n 233)) (V (.R 4 3)) (V (.W 4 0 3)) h0 h1

theorem core7_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 263) = V (.R 3 3))
    (h1 : V (.W 3 0 3) = bswap (V (.R 3 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 263)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 263)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 263)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 263)) 0) (.const 255)) 24))) = V (.W 3 0 3) :=
  shape1 (env (.n 263)) (V (.R 3 3)) (V (.W 3 0 3)) h0 h1

theorem core7_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 261) = V (.R 2 3))
    (h1 : V (.W 2 0 3) = bswap (V (.R 2 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 261)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 261)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 261)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 261)) 0) (.const 255)) 24))) = V (.W 2 0 3) :=
  shape1 (env (.n 261)) (V (.R 2 3)) (V (.W 2 0 3)) h0 h1

theorem core7_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 231) = V (.R 1 3))
    (h1 : V (.W 1 0 3) = bswap (V (.R 1 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 231)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 231)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 231)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 231)) 0) (.const 255)) 24))) = V (.W 1 0 3) :=
  shape1 (env (.n 231)) (V (.R 1 3)) (V (.W 1 0 3)) h0 h1

theorem core7_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 229) = V (.R 0 3))
    (h1 : V (.W 0 0 3) = bswap (V (.R 0 3))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 229)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 229)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 229)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 229)) 0) (.const 255)) 24))) = V (.W 0 0 3) :=
  shape1 (env (.n 229)) (V (.R 0 3)) (V (.W 0 0 3)) h0 h1

theorem core7_267 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 266) = V (.R 7 2))
    (h1 : V (.W 7 0 2) = bswap (V (.R 7 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 266)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 266)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 266)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 266)) 0) (.const 255)) 24))) = V (.W 7 0 2) :=
  shape1 (env (.n 266)) (V (.R 7 2)) (V (.W 7 0 2)) h0 h1

theorem core7_266 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 264) = V (.R 6 2))
    (h1 : V (.W 6 0 2) = bswap (V (.R 6 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 264)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 264)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 264)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 264)) 0) (.const 255)) 24))) = V (.W 6 0 2) :=
  shape1 (env (.n 264)) (V (.R 6 2)) (V (.W 6 0 2)) h0 h1

theorem core7_265 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 234) = V (.R 5 2))
    (h1 : V (.W 5 0 2) = bswap (V (.R 5 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 234)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 234)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 234)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 234)) 0) (.const 255)) 24))) = V (.W 5 0 2) :=
  shape1 (env (.n 234)) (V (.R 5 2)) (V (.W 5 0 2)) h0 h1

theorem core7_264 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 232) = V (.R 4 2))
    (h1 : V (.W 4 0 2) = bswap (V (.R 4 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 232)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 232)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 232)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 232)) 0) (.const 255)) 24))) = V (.W 4 0 2) :=
  shape1 (env (.n 232)) (V (.R 4 2)) (V (.W 4 0 2)) h0 h1

theorem core7_263 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 262) = V (.R 3 2))
    (h1 : V (.W 3 0 2) = bswap (V (.R 3 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 262)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 262)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 262)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 262)) 0) (.const 255)) 24))) = V (.W 3 0 2) :=
  shape1 (env (.n 262)) (V (.R 3 2)) (V (.W 3 0 2)) h0 h1

theorem core7_262 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 260) = V (.R 2 2))
    (h1 : V (.W 2 0 2) = bswap (V (.R 2 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 260)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 260)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 260)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 260)) 0) (.const 255)) 24))) = V (.W 2 0 2) :=
  shape1 (env (.n 260)) (V (.R 2 2)) (V (.W 2 0 2)) h0 h1

theorem core7_261 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 230) = V (.R 1 2))
    (h1 : V (.W 1 0 2) = bswap (V (.R 1 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 230)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 230)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 230)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 230)) 0) (.const 255)) 24))) = V (.W 1 0 2) :=
  shape1 (env (.n 230)) (V (.R 1 2)) (V (.W 1 0 2)) h0 h1

theorem core7_260 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 228) = V (.R 0 2))
    (h1 : V (.W 0 0 2) = bswap (V (.R 0 2))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 228)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 228)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 228)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 228)) 0) (.const 255)) 24))) = V (.W 0 0 2) :=
  shape1 (env (.n 228)) (V (.R 0 2)) (V (.W 0 0 2)) h0 h1

theorem core7_251 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 219) = V (.R 7 1))
    (h1 : V (.W 7 0 1) = bswap (V (.R 7 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 219)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 219)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 219)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 219)) 0) (.const 255)) 24))) = V (.W 7 0 1) :=
  shape1 (env (.n 219)) (V (.R 7 1)) (V (.W 7 0 1)) h0 h1

theorem core7_250 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 217) = V (.R 6 1))
    (h1 : V (.W 6 0 1) = bswap (V (.R 6 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 217)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 217)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 217)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 217)) 0) (.const 255)) 24))) = V (.W 6 0 1) :=
  shape1 (env (.n 217)) (V (.R 6 1)) (V (.W 6 0 1)) h0 h1

theorem core7_249 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 203) = V (.R 5 1))
    (h1 : V (.W 5 0 1) = bswap (V (.R 5 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 203)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 203)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 203)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 203)) 0) (.const 255)) 24))) = V (.W 5 0 1) :=
  shape1 (env (.n 203)) (V (.R 5 1)) (V (.W 5 0 1)) h0 h1

theorem core7_248 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 201) = V (.R 4 1))
    (h1 : V (.W 4 0 1) = bswap (V (.R 4 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 201)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 201)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 201)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 201)) 0) (.const 255)) 24))) = V (.W 4 0 1) :=
  shape1 (env (.n 201)) (V (.R 4 1)) (V (.W 4 0 1)) h0 h1

theorem core7_247 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 215) = V (.R 3 1))
    (h1 : V (.W 3 0 1) = bswap (V (.R 3 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 215)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 215)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 215)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 215)) 0) (.const 255)) 24))) = V (.W 3 0 1) :=
  shape1 (env (.n 215)) (V (.R 3 1)) (V (.W 3 0 1)) h0 h1

theorem core7_246 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 213) = V (.R 2 1))
    (h1 : V (.W 2 0 1) = bswap (V (.R 2 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 213)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 213)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 213)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 213)) 0) (.const 255)) 24))) = V (.W 2 0 1) :=
  shape1 (env (.n 213)) (V (.R 2 1)) (V (.W 2 0 1)) h0 h1

theorem core7_245 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 199) = V (.R 1 1))
    (h1 : V (.W 1 0 1) = bswap (V (.R 1 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 199)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 199)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 199)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 199)) 0) (.const 255)) 24))) = V (.W 1 0 1) :=
  shape1 (env (.n 199)) (V (.R 1 1)) (V (.W 1 0 1)) h0 h1

theorem core7_244 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 197) = V (.R 0 1))
    (h1 : V (.W 0 0 1) = bswap (V (.R 0 1))) :
    E.eval env (.or (.or (.and (.shr (.var (.n 197)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 197)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 197)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 197)) 0) (.const 255)) 24))) = V (.W 0 0 1) :=
  shape1 (env (.n 197)) (V (.R 0 1)) (V (.W 0 0 1)) h0 h1

theorem core7_219 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.R 7 0))
    (h1 : V (.A 7 0 (1)) = (V (.E 7 0 (-3)) + Sigma1 (V (.E 7 0 (0))) + Ch (V (.E 7 0 (0))) (V (.E 7 0 (-1))) (V (.E 7 0 (-2))) + V (.KW 7 0 0)) + (Sigma0 (V (.A 7 0 (0))) + Maj (V (.A 7 0 (0))) (V (.A 7 0 (-1))) (V (.A 7 0 (-2)))))
    (h2 : V (.E 7 0 (-3)) = V (.H 7 0 7))
    (h3 : V (.H 7 0 7) = 1541459225#32)
    (h4 : V (.E 7 0 (0)) = V (.H 7 0 4))
    (h5 : V (.H 7 0 4) = 1359893119#32)
    (h6 : V (.E 7 0 (-1)) = V (.H 7 0 5))
    (h7 : V (.H 7 0 5) = 2600822924#32)
    (h8 : V (.E 7 0 (-2)) = V (.H 7 0 6))
    (h9 : V (.H 7 0 6) = 528734635#32)
    (h10 : V (.KW 7 0 0) = 1116352408#32 + V (.W 7 0 0))
    (h11 : V (.W 7 0 0) = bswap (V (.R 7 0)))
    (h12 : V (.A 7 0 (0)) = V (.H 7 0 0))
    (h13 : V (.H 7 0 0) = 1779033703#32)
    (h14 : V (.A 7 0 (-1)) = V (.H 7 0 1))
    (h15 : V (.H 7 0 1) = 3144134277#32)
    (h16 : V (.A 7 0 (-2)) = V (.H 7 0 2))
    (h17 : V (.H 7 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 218)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 218)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 218)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 218)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 7 0 (1)) :=
  shape2 (env (.n 218)) (V (.R 7 0)) (V (.A 7 0 (1))) (V (.E 7 0 (-3))) (V (.E 7 0 (0))) (V (.E 7 0 (-1))) (V (.E 7 0 (-2))) (V (.KW 7 0 0)) (V (.A 7 0 (0))) (V (.A 7 0 (-1))) (V (.A 7 0 (-2))) (V (.H 7 0 7)) (V (.H 7 0 4)) (V (.H 7 0 5)) (V (.H 7 0 6)) (V (.W 7 0 0)) (V (.H 7 0 0)) (V (.H 7 0 1)) (V (.H 7 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_218 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.R 6 0))
    (h1 : V (.A 6 0 (1)) = (V (.E 6 0 (-3)) + Sigma1 (V (.E 6 0 (0))) + Ch (V (.E 6 0 (0))) (V (.E 6 0 (-1))) (V (.E 6 0 (-2))) + V (.KW 6 0 0)) + (Sigma0 (V (.A 6 0 (0))) + Maj (V (.A 6 0 (0))) (V (.A 6 0 (-1))) (V (.A 6 0 (-2)))))
    (h2 : V (.E 6 0 (-3)) = V (.H 6 0 7))
    (h3 : V (.H 6 0 7) = 1541459225#32)
    (h4 : V (.E 6 0 (0)) = V (.H 6 0 4))
    (h5 : V (.H 6 0 4) = 1359893119#32)
    (h6 : V (.E 6 0 (-1)) = V (.H 6 0 5))
    (h7 : V (.H 6 0 5) = 2600822924#32)
    (h8 : V (.E 6 0 (-2)) = V (.H 6 0 6))
    (h9 : V (.H 6 0 6) = 528734635#32)
    (h10 : V (.KW 6 0 0) = 1116352408#32 + V (.W 6 0 0))
    (h11 : V (.W 6 0 0) = bswap (V (.R 6 0)))
    (h12 : V (.A 6 0 (0)) = V (.H 6 0 0))
    (h13 : V (.H 6 0 0) = 1779033703#32)
    (h14 : V (.A 6 0 (-1)) = V (.H 6 0 1))
    (h15 : V (.H 6 0 1) = 3144134277#32)
    (h16 : V (.A 6 0 (-2)) = V (.H 6 0 2))
    (h17 : V (.H 6 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 216)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 216)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 216)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 216)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 6 0 (1)) :=
  shape2 (env (.n 216)) (V (.R 6 0)) (V (.A 6 0 (1))) (V (.E 6 0 (-3))) (V (.E 6 0 (0))) (V (.E 6 0 (-1))) (V (.E 6 0 (-2))) (V (.KW 6 0 0)) (V (.A 6 0 (0))) (V (.A 6 0 (-1))) (V (.A 6 0 (-2))) (V (.H 6 0 7)) (V (.H 6 0 4)) (V (.H 6 0 5)) (V (.H 6 0 6)) (V (.W 6 0 0)) (V (.H 6 0 0)) (V (.H 6 0 1)) (V (.H 6 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_217 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 202) = V (.R 5 0))
    (h1 : V (.A 5 0 (1)) = (V (.E 5 0 (-3)) + Sigma1 (V (.E 5 0 (0))) + Ch (V (.E 5 0 (0))) (V (.E 5 0 (-1))) (V (.E 5 0 (-2))) + V (.KW 5 0 0)) + (Sigma0 (V (.A 5 0 (0))) + Maj (V (.A 5 0 (0))) (V (.A 5 0 (-1))) (V (.A 5 0 (-2)))))
    (h2 : V (.E 5 0 (-3)) = V (.H 5 0 7))
    (h3 : V (.H 5 0 7) = 1541459225#32)
    (h4 : V (.E 5 0 (0)) = V (.H 5 0 4))
    (h5 : V (.H 5 0 4) = 1359893119#32)
    (h6 : V (.E 5 0 (-1)) = V (.H 5 0 5))
    (h7 : V (.H 5 0 5) = 2600822924#32)
    (h8 : V (.E 5 0 (-2)) = V (.H 5 0 6))
    (h9 : V (.H 5 0 6) = 528734635#32)
    (h10 : V (.KW 5 0 0) = 1116352408#32 + V (.W 5 0 0))
    (h11 : V (.W 5 0 0) = bswap (V (.R 5 0)))
    (h12 : V (.A 5 0 (0)) = V (.H 5 0 0))
    (h13 : V (.H 5 0 0) = 1779033703#32)
    (h14 : V (.A 5 0 (-1)) = V (.H 5 0 1))
    (h15 : V (.H 5 0 1) = 3144134277#32)
    (h16 : V (.A 5 0 (-2)) = V (.H 5 0 2))
    (h17 : V (.H 5 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 202)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 202)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 202)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 202)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 5 0 (1)) :=
  shape2 (env (.n 202)) (V (.R 5 0)) (V (.A 5 0 (1))) (V (.E 5 0 (-3))) (V (.E 5 0 (0))) (V (.E 5 0 (-1))) (V (.E 5 0 (-2))) (V (.KW 5 0 0)) (V (.A 5 0 (0))) (V (.A 5 0 (-1))) (V (.A 5 0 (-2))) (V (.H 5 0 7)) (V (.H 5 0 4)) (V (.H 5 0 5)) (V (.H 5 0 6)) (V (.W 5 0 0)) (V (.H 5 0 0)) (V (.H 5 0 1)) (V (.H 5 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_216 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 200) = V (.R 4 0))
    (h1 : V (.A 4 0 (1)) = (V (.E 4 0 (-3)) + Sigma1 (V (.E 4 0 (0))) + Ch (V (.E 4 0 (0))) (V (.E 4 0 (-1))) (V (.E 4 0 (-2))) + V (.KW 4 0 0)) + (Sigma0 (V (.A 4 0 (0))) + Maj (V (.A 4 0 (0))) (V (.A 4 0 (-1))) (V (.A 4 0 (-2)))))
    (h2 : V (.E 4 0 (-3)) = V (.H 4 0 7))
    (h3 : V (.H 4 0 7) = 1541459225#32)
    (h4 : V (.E 4 0 (0)) = V (.H 4 0 4))
    (h5 : V (.H 4 0 4) = 1359893119#32)
    (h6 : V (.E 4 0 (-1)) = V (.H 4 0 5))
    (h7 : V (.H 4 0 5) = 2600822924#32)
    (h8 : V (.E 4 0 (-2)) = V (.H 4 0 6))
    (h9 : V (.H 4 0 6) = 528734635#32)
    (h10 : V (.KW 4 0 0) = 1116352408#32 + V (.W 4 0 0))
    (h11 : V (.W 4 0 0) = bswap (V (.R 4 0)))
    (h12 : V (.A 4 0 (0)) = V (.H 4 0 0))
    (h13 : V (.H 4 0 0) = 1779033703#32)
    (h14 : V (.A 4 0 (-1)) = V (.H 4 0 1))
    (h15 : V (.H 4 0 1) = 3144134277#32)
    (h16 : V (.A 4 0 (-2)) = V (.H 4 0 2))
    (h17 : V (.H 4 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 200)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 200)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 200)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 200)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 4 0 (1)) :=
  shape2 (env (.n 200)) (V (.R 4 0)) (V (.A 4 0 (1))) (V (.E 4 0 (-3))) (V (.E 4 0 (0))) (V (.E 4 0 (-1))) (V (.E 4 0 (-2))) (V (.KW 4 0 0)) (V (.A 4 0 (0))) (V (.A 4 0 (-1))) (V (.A 4 0 (-2))) (V (.H 4 0 7)) (V (.H 4 0 4)) (V (.H 4 0 5)) (V (.H 4 0 6)) (V (.W 4 0 0)) (V (.H 4 0 0)) (V (.H 4 0 1)) (V (.H 4 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.R 3 0))
    (h1 : V (.A 3 0 (1)) = (V (.E 3 0 (-3)) + Sigma1 (V (.E 3 0 (0))) + Ch (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) + V (.KW 3 0 0)) + (Sigma0 (V (.A 3 0 (0))) + Maj (V (.A 3 0 (0))) (V (.A 3 0 (-1))) (V (.A 3 0 (-2)))))
    (h2 : V (.E 3 0 (-3)) = V (.H 3 0 7))
    (h3 : V (.H 3 0 7) = 1541459225#32)
    (h4 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h5 : V (.H 3 0 4) = 1359893119#32)
    (h6 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h7 : V (.H 3 0 5) = 2600822924#32)
    (h8 : V (.E 3 0 (-2)) = V (.H 3 0 6))
    (h9 : V (.H 3 0 6) = 528734635#32)
    (h10 : V (.KW 3 0 0) = 1116352408#32 + V (.W 3 0 0))
    (h11 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h12 : V (.A 3 0 (0)) = V (.H 3 0 0))
    (h13 : V (.H 3 0 0) = 1779033703#32)
    (h14 : V (.A 3 0 (-1)) = V (.H 3 0 1))
    (h15 : V (.H 3 0 1) = 3144134277#32)
    (h16 : V (.A 3 0 (-2)) = V (.H 3 0 2))
    (h17 : V (.H 3 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 214)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 214)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 214)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 214)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 3 0 (1)) :=
  shape2 (env (.n 214)) (V (.R 3 0)) (V (.A 3 0 (1))) (V (.E 3 0 (-3))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) (V (.KW 3 0 0)) (V (.A 3 0 (0))) (V (.A 3 0 (-1))) (V (.A 3 0 (-2))) (V (.H 3 0 7)) (V (.H 3 0 4)) (V (.H 3 0 5)) (V (.H 3 0 6)) (V (.W 3 0 0)) (V (.H 3 0 0)) (V (.H 3 0 1)) (V (.H 3 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.R 2 0))
    (h1 : V (.A 2 0 (1)) = (V (.E 2 0 (-3)) + Sigma1 (V (.E 2 0 (0))) + Ch (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) + V (.KW 2 0 0)) + (Sigma0 (V (.A 2 0 (0))) + Maj (V (.A 2 0 (0))) (V (.A 2 0 (-1))) (V (.A 2 0 (-2)))))
    (h2 : V (.E 2 0 (-3)) = V (.H 2 0 7))
    (h3 : V (.H 2 0 7) = 1541459225#32)
    (h4 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h5 : V (.H 2 0 4) = 1359893119#32)
    (h6 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h7 : V (.H 2 0 5) = 2600822924#32)
    (h8 : V (.E 2 0 (-2)) = V (.H 2 0 6))
    (h9 : V (.H 2 0 6) = 528734635#32)
    (h10 : V (.KW 2 0 0) = 1116352408#32 + V (.W 2 0 0))
    (h11 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h12 : V (.A 2 0 (0)) = V (.H 2 0 0))
    (h13 : V (.H 2 0 0) = 1779033703#32)
    (h14 : V (.A 2 0 (-1)) = V (.H 2 0 1))
    (h15 : V (.H 2 0 1) = 3144134277#32)
    (h16 : V (.A 2 0 (-2)) = V (.H 2 0 2))
    (h17 : V (.H 2 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 212)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 212)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 212)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 212)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 2 0 (1)) :=
  shape2 (env (.n 212)) (V (.R 2 0)) (V (.A 2 0 (1))) (V (.E 2 0 (-3))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) (V (.KW 2 0 0)) (V (.A 2 0 (0))) (V (.A 2 0 (-1))) (V (.A 2 0 (-2))) (V (.H 2 0 7)) (V (.H 2 0 4)) (V (.H 2 0 5)) (V (.H 2 0 6)) (V (.W 2 0 0)) (V (.H 2 0 0)) (V (.H 2 0 1)) (V (.H 2 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 198) = V (.R 1 0))
    (h1 : V (.A 1 0 (1)) = (V (.E 1 0 (-3)) + Sigma1 (V (.E 1 0 (0))) + Ch (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) + V (.KW 1 0 0)) + (Sigma0 (V (.A 1 0 (0))) + Maj (V (.A 1 0 (0))) (V (.A 1 0 (-1))) (V (.A 1 0 (-2)))))
    (h2 : V (.E 1 0 (-3)) = V (.H 1 0 7))
    (h3 : V (.H 1 0 7) = 1541459225#32)
    (h4 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h5 : V (.H 1 0 4) = 1359893119#32)
    (h6 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h7 : V (.H 1 0 5) = 2600822924#32)
    (h8 : V (.E 1 0 (-2)) = V (.H 1 0 6))
    (h9 : V (.H 1 0 6) = 528734635#32)
    (h10 : V (.KW 1 0 0) = 1116352408#32 + V (.W 1 0 0))
    (h11 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h12 : V (.A 1 0 (0)) = V (.H 1 0 0))
    (h13 : V (.H 1 0 0) = 1779033703#32)
    (h14 : V (.A 1 0 (-1)) = V (.H 1 0 1))
    (h15 : V (.H 1 0 1) = 3144134277#32)
    (h16 : V (.A 1 0 (-2)) = V (.H 1 0 2))
    (h17 : V (.H 1 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 198)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 198)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 198)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 198)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 1 0 (1)) :=
  shape2 (env (.n 198)) (V (.R 1 0)) (V (.A 1 0 (1))) (V (.E 1 0 (-3))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) (V (.KW 1 0 0)) (V (.A 1 0 (0))) (V (.A 1 0 (-1))) (V (.A 1 0 (-2))) (V (.H 1 0 7)) (V (.H 1 0 4)) (V (.H 1 0 5)) (V (.H 1 0 6)) (V (.W 1 0 0)) (V (.H 1 0 0)) (V (.H 1 0 1)) (V (.H 1 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 196) = V (.R 0 0))
    (h1 : V (.A 0 0 (1)) = (V (.E 0 0 (-3)) + Sigma1 (V (.E 0 0 (0))) + Ch (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) + V (.KW 0 0 0)) + (Sigma0 (V (.A 0 0 (0))) + Maj (V (.A 0 0 (0))) (V (.A 0 0 (-1))) (V (.A 0 0 (-2)))))
    (h2 : V (.E 0 0 (-3)) = V (.H 0 0 7))
    (h3 : V (.H 0 0 7) = 1541459225#32)
    (h4 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h5 : V (.H 0 0 4) = 1359893119#32)
    (h6 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h7 : V (.H 0 0 5) = 2600822924#32)
    (h8 : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (h9 : V (.H 0 0 6) = 528734635#32)
    (h10 : V (.KW 0 0 0) = 1116352408#32 + V (.W 0 0 0))
    (h11 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h12 : V (.A 0 0 (0)) = V (.H 0 0 0))
    (h13 : V (.H 0 0 0) = 1779033703#32)
    (h14 : V (.A 0 0 (-1)) = V (.H 0 0 1))
    (h15 : V (.H 0 0 1) = 3144134277#32)
    (h16 : V (.A 0 0 (-2)) = V (.H 0 0 2))
    (h17 : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 196)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 196)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 196)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 196)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 0 0 (1)) :=
  shape2 (env (.n 196)) (V (.R 0 0)) (V (.A 0 0 (1))) (V (.E 0 0 (-3))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) (V (.KW 0 0 0)) (V (.A 0 0 (0))) (V (.A 0 0 (-1))) (V (.A 0 0 (-2))) (V (.H 0 0 7)) (V (.H 0 0 4)) (V (.H 0 0 5)) (V (.H 0 0 6)) (V (.W 0 0 0)) (V (.H 0 0 0)) (V (.H 0 0 1)) (V (.H 0 0 2)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core7_155 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.R 7 0))
    (h1 : V (.E 7 0 (1)) = V (.A 7 0 (-3)) + (V (.E 7 0 (-3)) + Sigma1 (V (.E 7 0 (0))) + Ch (V (.E 7 0 (0))) (V (.E 7 0 (-1))) (V (.E 7 0 (-2))) + V (.KW 7 0 0)))
    (h2 : V (.A 7 0 (-3)) = V (.H 7 0 3))
    (h3 : V (.H 7 0 3) = 2773480762#32)
    (h4 : V (.E 7 0 (-3)) = V (.H 7 0 7))
    (h5 : V (.H 7 0 7) = 1541459225#32)
    (h6 : V (.E 7 0 (0)) = V (.H 7 0 4))
    (h7 : V (.H 7 0 4) = 1359893119#32)
    (h8 : V (.E 7 0 (-1)) = V (.H 7 0 5))
    (h9 : V (.H 7 0 5) = 2600822924#32)
    (h10 : V (.E 7 0 (-2)) = V (.H 7 0 6))
    (h11 : V (.H 7 0 6) = 528734635#32)
    (h12 : V (.KW 7 0 0) = 1116352408#32 + V (.W 7 0 0))
    (h13 : V (.W 7 0 0) = bswap (V (.R 7 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 218)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 218)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 218)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 218)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 7 0 (1)) :=
  shape3 (env (.n 218)) (V (.R 7 0)) (V (.E 7 0 (1))) (V (.A 7 0 (-3))) (V (.E 7 0 (-3))) (V (.E 7 0 (0))) (V (.E 7 0 (-1))) (V (.E 7 0 (-2))) (V (.KW 7 0 0)) (V (.H 7 0 3)) (V (.H 7 0 7)) (V (.H 7 0 4)) (V (.H 7 0 5)) (V (.H 7 0 6)) (V (.W 7 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_154 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.R 6 0))
    (h1 : V (.E 6 0 (1)) = V (.A 6 0 (-3)) + (V (.E 6 0 (-3)) + Sigma1 (V (.E 6 0 (0))) + Ch (V (.E 6 0 (0))) (V (.E 6 0 (-1))) (V (.E 6 0 (-2))) + V (.KW 6 0 0)))
    (h2 : V (.A 6 0 (-3)) = V (.H 6 0 3))
    (h3 : V (.H 6 0 3) = 2773480762#32)
    (h4 : V (.E 6 0 (-3)) = V (.H 6 0 7))
    (h5 : V (.H 6 0 7) = 1541459225#32)
    (h6 : V (.E 6 0 (0)) = V (.H 6 0 4))
    (h7 : V (.H 6 0 4) = 1359893119#32)
    (h8 : V (.E 6 0 (-1)) = V (.H 6 0 5))
    (h9 : V (.H 6 0 5) = 2600822924#32)
    (h10 : V (.E 6 0 (-2)) = V (.H 6 0 6))
    (h11 : V (.H 6 0 6) = 528734635#32)
    (h12 : V (.KW 6 0 0) = 1116352408#32 + V (.W 6 0 0))
    (h13 : V (.W 6 0 0) = bswap (V (.R 6 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 216)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 216)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 216)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 216)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 6 0 (1)) :=
  shape3 (env (.n 216)) (V (.R 6 0)) (V (.E 6 0 (1))) (V (.A 6 0 (-3))) (V (.E 6 0 (-3))) (V (.E 6 0 (0))) (V (.E 6 0 (-1))) (V (.E 6 0 (-2))) (V (.KW 6 0 0)) (V (.H 6 0 3)) (V (.H 6 0 7)) (V (.H 6 0 4)) (V (.H 6 0 5)) (V (.H 6 0 6)) (V (.W 6 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_153 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 202) = V (.R 5 0))
    (h1 : V (.E 5 0 (1)) = V (.A 5 0 (-3)) + (V (.E 5 0 (-3)) + Sigma1 (V (.E 5 0 (0))) + Ch (V (.E 5 0 (0))) (V (.E 5 0 (-1))) (V (.E 5 0 (-2))) + V (.KW 5 0 0)))
    (h2 : V (.A 5 0 (-3)) = V (.H 5 0 3))
    (h3 : V (.H 5 0 3) = 2773480762#32)
    (h4 : V (.E 5 0 (-3)) = V (.H 5 0 7))
    (h5 : V (.H 5 0 7) = 1541459225#32)
    (h6 : V (.E 5 0 (0)) = V (.H 5 0 4))
    (h7 : V (.H 5 0 4) = 1359893119#32)
    (h8 : V (.E 5 0 (-1)) = V (.H 5 0 5))
    (h9 : V (.H 5 0 5) = 2600822924#32)
    (h10 : V (.E 5 0 (-2)) = V (.H 5 0 6))
    (h11 : V (.H 5 0 6) = 528734635#32)
    (h12 : V (.KW 5 0 0) = 1116352408#32 + V (.W 5 0 0))
    (h13 : V (.W 5 0 0) = bswap (V (.R 5 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 202)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 202)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 202)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 202)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 5 0 (1)) :=
  shape3 (env (.n 202)) (V (.R 5 0)) (V (.E 5 0 (1))) (V (.A 5 0 (-3))) (V (.E 5 0 (-3))) (V (.E 5 0 (0))) (V (.E 5 0 (-1))) (V (.E 5 0 (-2))) (V (.KW 5 0 0)) (V (.H 5 0 3)) (V (.H 5 0 7)) (V (.H 5 0 4)) (V (.H 5 0 5)) (V (.H 5 0 6)) (V (.W 5 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_152 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 200) = V (.R 4 0))
    (h1 : V (.E 4 0 (1)) = V (.A 4 0 (-3)) + (V (.E 4 0 (-3)) + Sigma1 (V (.E 4 0 (0))) + Ch (V (.E 4 0 (0))) (V (.E 4 0 (-1))) (V (.E 4 0 (-2))) + V (.KW 4 0 0)))
    (h2 : V (.A 4 0 (-3)) = V (.H 4 0 3))
    (h3 : V (.H 4 0 3) = 2773480762#32)
    (h4 : V (.E 4 0 (-3)) = V (.H 4 0 7))
    (h5 : V (.H 4 0 7) = 1541459225#32)
    (h6 : V (.E 4 0 (0)) = V (.H 4 0 4))
    (h7 : V (.H 4 0 4) = 1359893119#32)
    (h8 : V (.E 4 0 (-1)) = V (.H 4 0 5))
    (h9 : V (.H 4 0 5) = 2600822924#32)
    (h10 : V (.E 4 0 (-2)) = V (.H 4 0 6))
    (h11 : V (.H 4 0 6) = 528734635#32)
    (h12 : V (.KW 4 0 0) = 1116352408#32 + V (.W 4 0 0))
    (h13 : V (.W 4 0 0) = bswap (V (.R 4 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 200)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 200)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 200)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 200)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 4 0 (1)) :=
  shape3 (env (.n 200)) (V (.R 4 0)) (V (.E 4 0 (1))) (V (.A 4 0 (-3))) (V (.E 4 0 (-3))) (V (.E 4 0 (0))) (V (.E 4 0 (-1))) (V (.E 4 0 (-2))) (V (.KW 4 0 0)) (V (.H 4 0 3)) (V (.H 4 0 7)) (V (.H 4 0 4)) (V (.H 4 0 5)) (V (.H 4 0 6)) (V (.W 4 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.R 3 0))
    (h1 : V (.E 3 0 (1)) = V (.A 3 0 (-3)) + (V (.E 3 0 (-3)) + Sigma1 (V (.E 3 0 (0))) + Ch (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) + V (.KW 3 0 0)))
    (h2 : V (.A 3 0 (-3)) = V (.H 3 0 3))
    (h3 : V (.H 3 0 3) = 2773480762#32)
    (h4 : V (.E 3 0 (-3)) = V (.H 3 0 7))
    (h5 : V (.H 3 0 7) = 1541459225#32)
    (h6 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h7 : V (.H 3 0 4) = 1359893119#32)
    (h8 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h9 : V (.H 3 0 5) = 2600822924#32)
    (h10 : V (.E 3 0 (-2)) = V (.H 3 0 6))
    (h11 : V (.H 3 0 6) = 528734635#32)
    (h12 : V (.KW 3 0 0) = 1116352408#32 + V (.W 3 0 0))
    (h13 : V (.W 3 0 0) = bswap (V (.R 3 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 214)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 214)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 214)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 214)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 3 0 (1)) :=
  shape3 (env (.n 214)) (V (.R 3 0)) (V (.E 3 0 (1))) (V (.A 3 0 (-3))) (V (.E 3 0 (-3))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) (V (.KW 3 0 0)) (V (.H 3 0 3)) (V (.H 3 0 7)) (V (.H 3 0 4)) (V (.H 3 0 5)) (V (.H 3 0 6)) (V (.W 3 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.R 2 0))
    (h1 : V (.E 2 0 (1)) = V (.A 2 0 (-3)) + (V (.E 2 0 (-3)) + Sigma1 (V (.E 2 0 (0))) + Ch (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) + V (.KW 2 0 0)))
    (h2 : V (.A 2 0 (-3)) = V (.H 2 0 3))
    (h3 : V (.H 2 0 3) = 2773480762#32)
    (h4 : V (.E 2 0 (-3)) = V (.H 2 0 7))
    (h5 : V (.H 2 0 7) = 1541459225#32)
    (h6 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h7 : V (.H 2 0 4) = 1359893119#32)
    (h8 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h9 : V (.H 2 0 5) = 2600822924#32)
    (h10 : V (.E 2 0 (-2)) = V (.H 2 0 6))
    (h11 : V (.H 2 0 6) = 528734635#32)
    (h12 : V (.KW 2 0 0) = 1116352408#32 + V (.W 2 0 0))
    (h13 : V (.W 2 0 0) = bswap (V (.R 2 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 212)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 212)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 212)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 212)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 2 0 (1)) :=
  shape3 (env (.n 212)) (V (.R 2 0)) (V (.E 2 0 (1))) (V (.A 2 0 (-3))) (V (.E 2 0 (-3))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) (V (.KW 2 0 0)) (V (.H 2 0 3)) (V (.H 2 0 7)) (V (.H 2 0 4)) (V (.H 2 0 5)) (V (.H 2 0 6)) (V (.W 2 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 198) = V (.R 1 0))
    (h1 : V (.E 1 0 (1)) = V (.A 1 0 (-3)) + (V (.E 1 0 (-3)) + Sigma1 (V (.E 1 0 (0))) + Ch (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) + V (.KW 1 0 0)))
    (h2 : V (.A 1 0 (-3)) = V (.H 1 0 3))
    (h3 : V (.H 1 0 3) = 2773480762#32)
    (h4 : V (.E 1 0 (-3)) = V (.H 1 0 7))
    (h5 : V (.H 1 0 7) = 1541459225#32)
    (h6 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h7 : V (.H 1 0 4) = 1359893119#32)
    (h8 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h9 : V (.H 1 0 5) = 2600822924#32)
    (h10 : V (.E 1 0 (-2)) = V (.H 1 0 6))
    (h11 : V (.H 1 0 6) = 528734635#32)
    (h12 : V (.KW 1 0 0) = 1116352408#32 + V (.W 1 0 0))
    (h13 : V (.W 1 0 0) = bswap (V (.R 1 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 198)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 198)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 198)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 198)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 1 0 (1)) :=
  shape3 (env (.n 198)) (V (.R 1 0)) (V (.E 1 0 (1))) (V (.A 1 0 (-3))) (V (.E 1 0 (-3))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) (V (.KW 1 0 0)) (V (.H 1 0 3)) (V (.H 1 0 7)) (V (.H 1 0 4)) (V (.H 1 0 5)) (V (.H 1 0 6)) (V (.W 1 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem core7_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 196) = V (.R 0 0))
    (h1 : V (.E 0 0 (1)) = V (.A 0 0 (-3)) + (V (.E 0 0 (-3)) + Sigma1 (V (.E 0 0 (0))) + Ch (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) + V (.KW 0 0 0)))
    (h2 : V (.A 0 0 (-3)) = V (.H 0 0 3))
    (h3 : V (.H 0 0 3) = 2773480762#32)
    (h4 : V (.E 0 0 (-3)) = V (.H 0 0 7))
    (h5 : V (.H 0 0 7) = 1541459225#32)
    (h6 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h7 : V (.H 0 0 4) = 1359893119#32)
    (h8 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h9 : V (.H 0 0 5) = 2600822924#32)
    (h10 : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (h11 : V (.H 0 0 6) = 528734635#32)
    (h12 : V (.KW 0 0 0) = 1116352408#32 + V (.W 0 0 0))
    (h13 : V (.W 0 0 0) = bswap (V (.R 0 0))) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.var (.n 196)) 24) (.const 255)) (.shl (.and (.shr (.var (.n 196)) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 196)) 8) (.const 255)) 16) (.shl (.and (.shr (.var (.n 196)) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 0 0 (1)) :=
  shape3 (env (.n 196)) (V (.R 0 0)) (V (.E 0 0 (1))) (V (.A 0 0 (-3))) (V (.E 0 0 (-3))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) (V (.KW 0 0 0)) (V (.H 0 0 3)) (V (.H 0 0 7)) (V (.H 0 0 4)) (V (.H 0 0 5)) (V (.H 0 0 6)) (V (.W 0 0 0)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem step7 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L7) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 64 K7)) L8 := by
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
  exact invC_of_trees inp env _ T7 L8 (slice_trees_mem prog 4 _ _ 64 K7 K8 T7 slice7 env)
      (And.intro ⟨rfl, core7_1159 (qv inp) inp env h31 (qW_R inp 0 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1158 (qv inp) inp env h31 (qW_R inp 0 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1157 (qv inp) inp env h31 (qW_R inp 0 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1156 (qv inp) inp env h31 (qW_R inp 0 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1155 (qv inp) inp env h23 (qW_R inp 1 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1154 (qv inp) inp env h23 (qW_R inp 1 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1153 (qv inp) inp env h23 (qW_R inp 1 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1152 (qv inp) inp env h23 (qW_R inp 1 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1151 (qv inp) inp env h15 (qW_R inp 2 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1150 (qv inp) inp env h15 (qW_R inp 2 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1149 (qv inp) inp env h15 (qW_R inp 2 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1148 (qv inp) inp env h15 (qW_R inp 2 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1147 (qv inp) inp env h7 (qW_R inp 3 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1146 (qv inp) inp env h7 (qW_R inp 3 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1145 (qv inp) inp env h7 (qW_R inp 3 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1144 (qv inp) inp env h7 (qW_R inp 3 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1143 (qv inp) inp env h27 (qW_R inp 4 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1142 (qv inp) inp env h27 (qW_R inp 4 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1141 (qv inp) inp env h27 (qW_R inp 4 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1140 (qv inp) inp env h27 (qW_R inp 4 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1139 (qv inp) inp env h19 (qW_R inp 5 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1138 (qv inp) inp env h19 (qW_R inp 5 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1137 (qv inp) inp env h19 (qW_R inp 5 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1136 (qv inp) inp env h19 (qW_R inp 5 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1135 (qv inp) inp env h11 (qW_R inp 6 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1134 (qv inp) inp env h11 (qW_R inp 6 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1133 (qv inp) inp env h11 (qW_R inp 6 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1132 (qv inp) inp env h11 (qW_R inp 6 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1131 (qv inp) inp env h3 (qW_R inp 7 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1130 (qv inp) inp env h3 (qW_R inp 7 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1129 (qv inp) inp env h3 (qW_R inp 7 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1128 (qv inp) inp env h3 (qW_R inp 7 4 (by decide))⟩
      (And.intro ⟨rfl, core7_1127 (qv inp) inp env h30 (qW_R inp 0 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1126 (qv inp) inp env h30 (qW_R inp 0 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1125 (qv inp) inp env h30 (qW_R inp 0 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1124 (qv inp) inp env h30 (qW_R inp 0 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1123 (qv inp) inp env h22 (qW_R inp 1 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1122 (qv inp) inp env h22 (qW_R inp 1 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1121 (qv inp) inp env h22 (qW_R inp 1 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1120 (qv inp) inp env h22 (qW_R inp 1 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1119 (qv inp) inp env h14 (qW_R inp 2 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1118 (qv inp) inp env h14 (qW_R inp 2 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1117 (qv inp) inp env h14 (qW_R inp 2 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1116 (qv inp) inp env h14 (qW_R inp 2 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1115 (qv inp) inp env h6 (qW_R inp 3 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1114 (qv inp) inp env h6 (qW_R inp 3 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1113 (qv inp) inp env h6 (qW_R inp 3 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1112 (qv inp) inp env h6 (qW_R inp 3 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1111 (qv inp) inp env h26 (qW_R inp 4 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1110 (qv inp) inp env h26 (qW_R inp 4 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1109 (qv inp) inp env h26 (qW_R inp 4 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1108 (qv inp) inp env h26 (qW_R inp 4 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1107 (qv inp) inp env h18 (qW_R inp 5 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1106 (qv inp) inp env h18 (qW_R inp 5 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1105 (qv inp) inp env h18 (qW_R inp 5 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1104 (qv inp) inp env h18 (qW_R inp 5 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1103 (qv inp) inp env h10 (qW_R inp 6 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1102 (qv inp) inp env h10 (qW_R inp 6 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1101 (qv inp) inp env h10 (qW_R inp 6 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1100 (qv inp) inp env h10 (qW_R inp 6 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1099 (qv inp) inp env h2 (qW_R inp 7 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1098 (qv inp) inp env h2 (qW_R inp 7 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1097 (qv inp) inp env h2 (qW_R inp 7 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1096 (qv inp) inp env h2 (qW_R inp 7 5 (by decide))⟩
      (And.intro ⟨rfl, core7_1095 (qv inp) inp env h29 (qW_R inp 0 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1094 (qv inp) inp env h29 (qW_R inp 0 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1093 (qv inp) inp env h29 (qW_R inp 0 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1092 (qv inp) inp env h29 (qW_R inp 0 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1091 (qv inp) inp env h21 (qW_R inp 1 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1090 (qv inp) inp env h21 (qW_R inp 1 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1089 (qv inp) inp env h21 (qW_R inp 1 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1088 (qv inp) inp env h21 (qW_R inp 1 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1087 (qv inp) inp env h13 (qW_R inp 2 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1086 (qv inp) inp env h13 (qW_R inp 2 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1085 (qv inp) inp env h13 (qW_R inp 2 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1084 (qv inp) inp env h13 (qW_R inp 2 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1083 (qv inp) inp env h5 (qW_R inp 3 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1082 (qv inp) inp env h5 (qW_R inp 3 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1081 (qv inp) inp env h5 (qW_R inp 3 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1080 (qv inp) inp env h5 (qW_R inp 3 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1079 (qv inp) inp env h25 (qW_R inp 4 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1078 (qv inp) inp env h25 (qW_R inp 4 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1077 (qv inp) inp env h25 (qW_R inp 4 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1076 (qv inp) inp env h25 (qW_R inp 4 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1075 (qv inp) inp env h17 (qW_R inp 5 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1074 (qv inp) inp env h17 (qW_R inp 5 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1073 (qv inp) inp env h17 (qW_R inp 5 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1072 (qv inp) inp env h17 (qW_R inp 5 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1071 (qv inp) inp env h9 (qW_R inp 6 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1070 (qv inp) inp env h9 (qW_R inp 6 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1069 (qv inp) inp env h9 (qW_R inp 6 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1068 (qv inp) inp env h9 (qW_R inp 6 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1067 (qv inp) inp env h1 (qW_R inp 7 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1066 (qv inp) inp env h1 (qW_R inp 7 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1065 (qv inp) inp env h1 (qW_R inp 7 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1064 (qv inp) inp env h1 (qW_R inp 7 6 (by decide))⟩
      (And.intro ⟨rfl, core7_1063 (qv inp) inp env h28 (qW_R inp 0 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1062 (qv inp) inp env h28 (qW_R inp 0 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1061 (qv inp) inp env h28 (qW_R inp 0 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1060 (qv inp) inp env h28 (qW_R inp 0 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1059 (qv inp) inp env h20 (qW_R inp 1 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1058 (qv inp) inp env h20 (qW_R inp 1 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1057 (qv inp) inp env h20 (qW_R inp 1 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1056 (qv inp) inp env h20 (qW_R inp 1 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1055 (qv inp) inp env h12 (qW_R inp 2 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1054 (qv inp) inp env h12 (qW_R inp 2 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1053 (qv inp) inp env h12 (qW_R inp 2 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1052 (qv inp) inp env h12 (qW_R inp 2 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1051 (qv inp) inp env h4 (qW_R inp 3 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1050 (qv inp) inp env h4 (qW_R inp 3 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1049 (qv inp) inp env h4 (qW_R inp 3 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1048 (qv inp) inp env h4 (qW_R inp 3 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1047 (qv inp) inp env h24 (qW_R inp 4 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1046 (qv inp) inp env h24 (qW_R inp 4 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1045 (qv inp) inp env h24 (qW_R inp 4 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1044 (qv inp) inp env h24 (qW_R inp 4 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1043 (qv inp) inp env h16 (qW_R inp 5 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1042 (qv inp) inp env h16 (qW_R inp 5 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1041 (qv inp) inp env h16 (qW_R inp 5 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1040 (qv inp) inp env h16 (qW_R inp 5 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1039 (qv inp) inp env h8 (qW_R inp 6 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1038 (qv inp) inp env h8 (qW_R inp 6 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1037 (qv inp) inp env h8 (qW_R inp 6 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1036 (qv inp) inp env h8 (qW_R inp 6 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1035 (qv inp) inp env h0 (qW_R inp 7 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1034 (qv inp) inp env h0 (qW_R inp 7 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1033 (qv inp) inp env h0 (qW_R inp 7 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1032 (qv inp) inp env h0 (qW_R inp 7 7 (by decide))⟩
      (And.intro ⟨rfl, core7_1031 (qv inp) inp env h79 (qW_R inp 0 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1030 (qv inp) inp env h79 (qW_R inp 0 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1029 (qv inp) inp env h79 (qW_R inp 0 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1028 (qv inp) inp env h79 (qW_R inp 0 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1027 (qv inp) inp env h77 (qW_R inp 1 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1026 (qv inp) inp env h77 (qW_R inp 1 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1025 (qv inp) inp env h77 (qW_R inp 1 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1024 (qv inp) inp env h77 (qW_R inp 1 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1023 (qv inp) inp env h71 (qW_R inp 2 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1022 (qv inp) inp env h71 (qW_R inp 2 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1021 (qv inp) inp env h71 (qW_R inp 2 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1020 (qv inp) inp env h71 (qW_R inp 2 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1019 (qv inp) inp env h69 (qW_R inp 3 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1018 (qv inp) inp env h69 (qW_R inp 3 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1017 (qv inp) inp env h69 (qW_R inp 3 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1016 (qv inp) inp env h69 (qW_R inp 3 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1015 (qv inp) inp env h75 (qW_R inp 4 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1014 (qv inp) inp env h75 (qW_R inp 4 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1013 (qv inp) inp env h75 (qW_R inp 4 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1012 (qv inp) inp env h75 (qW_R inp 4 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1011 (qv inp) inp env h73 (qW_R inp 5 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1010 (qv inp) inp env h73 (qW_R inp 5 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1009 (qv inp) inp env h73 (qW_R inp 5 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1008 (qv inp) inp env h73 (qW_R inp 5 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1007 (qv inp) inp env h67 (qW_R inp 6 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1006 (qv inp) inp env h67 (qW_R inp 6 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1005 (qv inp) inp env h67 (qW_R inp 6 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1004 (qv inp) inp env h67 (qW_R inp 6 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1003 (qv inp) inp env h65 (qW_R inp 7 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1002 (qv inp) inp env h65 (qW_R inp 7 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1001 (qv inp) inp env h65 (qW_R inp 7 0 (by decide))⟩
      (And.intro ⟨rfl, core7_1000 (qv inp) inp env h65 (qW_R inp 7 0 (by decide))⟩
      (And.intro ⟨rfl, core7_283 (qv inp) inp env h40 (qW_R inp 7 3 (by decide))⟩
      (And.intro ⟨rfl, core7_282 (qv inp) inp env h42 (qW_R inp 6 3 (by decide))⟩
      (And.intro ⟨rfl, core7_281 (qv inp) inp env h56 (qW_R inp 5 3 (by decide))⟩
      (And.intro ⟨rfl, core7_280 (qv inp) inp env h58 (qW_R inp 4 3 (by decide))⟩
      (And.intro ⟨rfl, core7_279 (qv inp) inp env h44 (qW_R inp 3 3 (by decide))⟩
      (And.intro ⟨rfl, core7_278 (qv inp) inp env h46 (qW_R inp 2 3 (by decide))⟩
      (And.intro ⟨rfl, core7_277 (qv inp) inp env h60 (qW_R inp 1 3 (by decide))⟩
      (And.intro ⟨rfl, core7_276 (qv inp) inp env h62 (qW_R inp 0 3 (by decide))⟩
      (And.intro ⟨rfl, core7_267 (qv inp) inp env h41 (qW_R inp 7 2 (by decide))⟩
      (And.intro ⟨rfl, core7_266 (qv inp) inp env h43 (qW_R inp 6 2 (by decide))⟩
      (And.intro ⟨rfl, core7_265 (qv inp) inp env h57 (qW_R inp 5 2 (by decide))⟩
      (And.intro ⟨rfl, core7_264 (qv inp) inp env h59 (qW_R inp 4 2 (by decide))⟩
      (And.intro ⟨rfl, core7_263 (qv inp) inp env h45 (qW_R inp 3 2 (by decide))⟩
      (And.intro ⟨rfl, core7_262 (qv inp) inp env h47 (qW_R inp 2 2 (by decide))⟩
      (And.intro ⟨rfl, core7_261 (qv inp) inp env h61 (qW_R inp 1 2 (by decide))⟩
      (And.intro ⟨rfl, core7_260 (qv inp) inp env h63 (qW_R inp 0 2 (by decide))⟩
      (And.intro ⟨rfl, core7_251 (qv inp) inp env h64 (qW_R inp 7 1 (by decide))⟩
      (And.intro ⟨rfl, core7_250 (qv inp) inp env h66 (qW_R inp 6 1 (by decide))⟩
      (And.intro ⟨rfl, core7_249 (qv inp) inp env h72 (qW_R inp 5 1 (by decide))⟩
      (And.intro ⟨rfl, core7_248 (qv inp) inp env h74 (qW_R inp 4 1 (by decide))⟩
      (And.intro ⟨rfl, core7_247 (qv inp) inp env h68 (qW_R inp 3 1 (by decide))⟩
      (And.intro ⟨rfl, core7_246 (qv inp) inp env h70 (qW_R inp 2 1 (by decide))⟩
      (And.intro ⟨rfl, core7_245 (qv inp) inp env h76 (qW_R inp 1 1 (by decide))⟩
      (And.intro ⟨rfl, core7_244 (qv inp) inp env h78 (qW_R inp 0 1 (by decide))⟩
      (And.intro ⟨rfl, core7_219 (qv inp) inp env h65 (qA_succI inp 7 0 (0) (by decide)) (qE_initI inp 7 0 3 (-3) (by decide) (by decide)) ((qH0 inp 7 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 7 0 0 (0) (by decide) (by decide)) ((qH0 inp 7 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 7 0 1 (-1) (by decide) (by decide)) ((qH0 inp 7 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 7 0 2 (-2) (by decide) (by decide)) ((qH0 inp 7 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 7 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 7 0 (by decide)) (qA_initI inp 7 0 0 (0) (by decide) (by decide)) ((qH0 inp 7 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 7 0 1 (-1) (by decide) (by decide)) ((qH0 inp 7 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 7 0 2 (-2) (by decide) (by decide)) ((qH0 inp 7 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_218 (qv inp) inp env h67 (qA_succI inp 6 0 (0) (by decide)) (qE_initI inp 6 0 3 (-3) (by decide) (by decide)) ((qH0 inp 6 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 6 0 0 (0) (by decide) (by decide)) ((qH0 inp 6 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 6 0 1 (-1) (by decide) (by decide)) ((qH0 inp 6 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 6 0 2 (-2) (by decide) (by decide)) ((qH0 inp 6 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 6 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 6 0 (by decide)) (qA_initI inp 6 0 0 (0) (by decide) (by decide)) ((qH0 inp 6 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 6 0 1 (-1) (by decide) (by decide)) ((qH0 inp 6 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 6 0 2 (-2) (by decide) (by decide)) ((qH0 inp 6 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_217 (qv inp) inp env h73 (qA_succI inp 5 0 (0) (by decide)) (qE_initI inp 5 0 3 (-3) (by decide) (by decide)) ((qH0 inp 5 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 5 0 0 (0) (by decide) (by decide)) ((qH0 inp 5 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 5 0 1 (-1) (by decide) (by decide)) ((qH0 inp 5 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 5 0 2 (-2) (by decide) (by decide)) ((qH0 inp 5 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 5 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 5 0 (by decide)) (qA_initI inp 5 0 0 (0) (by decide) (by decide)) ((qH0 inp 5 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 5 0 1 (-1) (by decide) (by decide)) ((qH0 inp 5 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 5 0 2 (-2) (by decide) (by decide)) ((qH0 inp 5 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_216 (qv inp) inp env h75 (qA_succI inp 4 0 (0) (by decide)) (qE_initI inp 4 0 3 (-3) (by decide) (by decide)) ((qH0 inp 4 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 4 0 0 (0) (by decide) (by decide)) ((qH0 inp 4 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 4 0 1 (-1) (by decide) (by decide)) ((qH0 inp 4 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 4 0 2 (-2) (by decide) (by decide)) ((qH0 inp 4 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 4 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 4 0 (by decide)) (qA_initI inp 4 0 0 (0) (by decide) (by decide)) ((qH0 inp 4 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 4 0 1 (-1) (by decide) (by decide)) ((qH0 inp 4 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 4 0 2 (-2) (by decide) (by decide)) ((qH0 inp 4 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_215 (qv inp) inp env h69 (qA_succI inp 3 0 (0) (by decide)) (qE_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 3 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 3 0 (by decide)) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_214 (qv inp) inp env h71 (qA_succI inp 2 0 (0) (by decide)) (qE_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 2 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 2 0 (by decide)) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_213 (qv inp) inp env h77 (qA_succI inp 1 0 (0) (by decide)) (qE_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 1 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 1 0 (by decide)) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_212 (qv inp) inp env h79 (qA_succI inp 0 0 (0) (by decide)) (qE_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 0 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 0 0 (by decide)) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core7_155 (qv inp) inp env h65 (qE_succI inp 7 0 (0) (by decide)) (qA_initI inp 7 0 3 (-3) (by decide) (by decide)) ((qH0 inp 7 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 7 0 3 (-3) (by decide) (by decide)) ((qH0 inp 7 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 7 0 0 (0) (by decide) (by decide)) ((qH0 inp 7 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 7 0 1 (-1) (by decide) (by decide)) ((qH0 inp 7 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 7 0 2 (-2) (by decide) (by decide)) ((qH0 inp 7 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 7 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 7 0 (by decide))⟩
      (And.intro ⟨rfl, core7_154 (qv inp) inp env h67 (qE_succI inp 6 0 (0) (by decide)) (qA_initI inp 6 0 3 (-3) (by decide) (by decide)) ((qH0 inp 6 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 6 0 3 (-3) (by decide) (by decide)) ((qH0 inp 6 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 6 0 0 (0) (by decide) (by decide)) ((qH0 inp 6 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 6 0 1 (-1) (by decide) (by decide)) ((qH0 inp 6 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 6 0 2 (-2) (by decide) (by decide)) ((qH0 inp 6 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 6 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 6 0 (by decide))⟩
      (And.intro ⟨rfl, core7_153 (qv inp) inp env h73 (qE_succI inp 5 0 (0) (by decide)) (qA_initI inp 5 0 3 (-3) (by decide) (by decide)) ((qH0 inp 5 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 5 0 3 (-3) (by decide) (by decide)) ((qH0 inp 5 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 5 0 0 (0) (by decide) (by decide)) ((qH0 inp 5 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 5 0 1 (-1) (by decide) (by decide)) ((qH0 inp 5 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 5 0 2 (-2) (by decide) (by decide)) ((qH0 inp 5 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 5 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 5 0 (by decide))⟩
      (And.intro ⟨rfl, core7_152 (qv inp) inp env h75 (qE_succI inp 4 0 (0) (by decide)) (qA_initI inp 4 0 3 (-3) (by decide) (by decide)) ((qH0 inp 4 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 4 0 3 (-3) (by decide) (by decide)) ((qH0 inp 4 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 4 0 0 (0) (by decide) (by decide)) ((qH0 inp 4 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 4 0 1 (-1) (by decide) (by decide)) ((qH0 inp 4 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 4 0 2 (-2) (by decide) (by decide)) ((qH0 inp 4 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 4 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 4 0 (by decide))⟩
      (And.intro ⟨rfl, core7_151 (qv inp) inp env h69 (qE_succI inp 3 0 (0) (by decide)) (qA_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 3 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 3 0 (by decide))⟩
      (And.intro ⟨rfl, core7_150 (qv inp) inp env h71 (qE_succI inp 2 0 (0) (by decide)) (qA_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 2 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 2 0 (by decide))⟩
      (And.intro ⟨rfl, core7_149 (qv inp) inp env h77 (qE_succI inp 1 0 (0) (by decide)) (qA_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 1 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 1 0 (by decide))⟩
      (And.intro ⟨rfl, core7_148 (qv inp) inp env h79 (qE_succI inp 0 0 (0) (by decide)) (qA_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 0 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 0 0 (by decide))⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
