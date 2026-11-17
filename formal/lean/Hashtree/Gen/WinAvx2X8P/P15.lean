import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D15
import Hashtree.Gen.WinAvx2X8P.D14

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice15 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 86 K15 K16 T15 = true := by
  decide +kernel

theorem core15_1159 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape19 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1158 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape19 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1157 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape19 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1156 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape19 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1155 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape19 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1154 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape19 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1153 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape19 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1152 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape19 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape19 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape19 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape19 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape19 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1147 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape19 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1146 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape19 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1145 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape19 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1144 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape19 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1143 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨304, [1]⟩ : Lin)) = (inp 304).zeroExtend 32)
    (h1 : env (.m 1 (⟨305, [1]⟩ : Lin)) = (inp 305).zeroExtend 32)
    (h2 : env (.m 1 (⟨306, [1]⟩ : Lin)) = (inp 306).zeroExtend 32)
    (h3 : env (.m 1 (⟨307, [1]⟩ : Lin)) = (inp 307).zeroExtend 32)
    (h4 : V (.W 4 0 12) = bswap (V (.R 4 12)))
    (h5 : V (.R 4 12) = ((((0 : Word) ||| (inp 304).zeroExtend 32 <<< 0) ||| (inp 305).zeroExtend 32 <<< 8) ||| (inp 306).zeroExtend 32 <<< 16) ||| (inp 307).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 12) :=
  shape19 (env (.m 1 (⟨304, [1]⟩ : Lin))) (env (.m 1 (⟨305, [1]⟩ : Lin))) (env (.m 1 (⟨306, [1]⟩ : Lin))) (env (.m 1 (⟨307, [1]⟩ : Lin))) (V (.W 4 0 12)) (V (.R 4 12)) ((inp 304)) ((inp 305)) ((inp 306)) ((inp 307)) h0 h1 h2 h3 h4 h5

theorem core15_1142 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨304, [1]⟩ : Lin)) = (inp 304).zeroExtend 32)
    (h1 : env (.m 1 (⟨305, [1]⟩ : Lin)) = (inp 305).zeroExtend 32)
    (h2 : env (.m 1 (⟨306, [1]⟩ : Lin)) = (inp 306).zeroExtend 32)
    (h3 : env (.m 1 (⟨307, [1]⟩ : Lin)) = (inp 307).zeroExtend 32)
    (h4 : V (.W 4 0 12) = bswap (V (.R 4 12)))
    (h5 : V (.R 4 12) = ((((0 : Word) ||| (inp 304).zeroExtend 32 <<< 0) ||| (inp 305).zeroExtend 32 <<< 8) ||| (inp 306).zeroExtend 32 <<< 16) ||| (inp 307).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 12) :=
  shape19 (env (.m 1 (⟨304, [1]⟩ : Lin))) (env (.m 1 (⟨305, [1]⟩ : Lin))) (env (.m 1 (⟨306, [1]⟩ : Lin))) (env (.m 1 (⟨307, [1]⟩ : Lin))) (V (.W 4 0 12)) (V (.R 4 12)) ((inp 304)) ((inp 305)) ((inp 306)) ((inp 307)) h0 h1 h2 h3 h4 h5

theorem core15_1141 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨304, [1]⟩ : Lin)) = (inp 304).zeroExtend 32)
    (h1 : env (.m 1 (⟨305, [1]⟩ : Lin)) = (inp 305).zeroExtend 32)
    (h2 : env (.m 1 (⟨306, [1]⟩ : Lin)) = (inp 306).zeroExtend 32)
    (h3 : env (.m 1 (⟨307, [1]⟩ : Lin)) = (inp 307).zeroExtend 32)
    (h4 : V (.W 4 0 12) = bswap (V (.R 4 12)))
    (h5 : V (.R 4 12) = ((((0 : Word) ||| (inp 304).zeroExtend 32 <<< 0) ||| (inp 305).zeroExtend 32 <<< 8) ||| (inp 306).zeroExtend 32 <<< 16) ||| (inp 307).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 12) :=
  shape19 (env (.m 1 (⟨304, [1]⟩ : Lin))) (env (.m 1 (⟨305, [1]⟩ : Lin))) (env (.m 1 (⟨306, [1]⟩ : Lin))) (env (.m 1 (⟨307, [1]⟩ : Lin))) (V (.W 4 0 12)) (V (.R 4 12)) ((inp 304)) ((inp 305)) ((inp 306)) ((inp 307)) h0 h1 h2 h3 h4 h5

theorem core15_1140 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨304, [1]⟩ : Lin)) = (inp 304).zeroExtend 32)
    (h1 : env (.m 1 (⟨305, [1]⟩ : Lin)) = (inp 305).zeroExtend 32)
    (h2 : env (.m 1 (⟨306, [1]⟩ : Lin)) = (inp 306).zeroExtend 32)
    (h3 : env (.m 1 (⟨307, [1]⟩ : Lin)) = (inp 307).zeroExtend 32)
    (h4 : V (.W 4 0 12) = bswap (V (.R 4 12)))
    (h5 : V (.R 4 12) = ((((0 : Word) ||| (inp 304).zeroExtend 32 <<< 0) ||| (inp 305).zeroExtend 32 <<< 8) ||| (inp 306).zeroExtend 32 <<< 16) ||| (inp 307).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨304, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨305, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨306, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨307, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 12) :=
  shape19 (env (.m 1 (⟨304, [1]⟩ : Lin))) (env (.m 1 (⟨305, [1]⟩ : Lin))) (env (.m 1 (⟨306, [1]⟩ : Lin))) (env (.m 1 (⟨307, [1]⟩ : Lin))) (V (.W 4 0 12)) (V (.R 4 12)) ((inp 304)) ((inp 305)) ((inp 306)) ((inp 307)) h0 h1 h2 h3 h4 h5

theorem core15_1139 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨368, [1]⟩ : Lin)) = (inp 368).zeroExtend 32)
    (h1 : env (.m 1 (⟨369, [1]⟩ : Lin)) = (inp 369).zeroExtend 32)
    (h2 : env (.m 1 (⟨370, [1]⟩ : Lin)) = (inp 370).zeroExtend 32)
    (h3 : env (.m 1 (⟨371, [1]⟩ : Lin)) = (inp 371).zeroExtend 32)
    (h4 : V (.W 5 0 12) = bswap (V (.R 5 12)))
    (h5 : V (.R 5 12) = ((((0 : Word) ||| (inp 368).zeroExtend 32 <<< 0) ||| (inp 369).zeroExtend 32 <<< 8) ||| (inp 370).zeroExtend 32 <<< 16) ||| (inp 371).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 12) :=
  shape19 (env (.m 1 (⟨368, [1]⟩ : Lin))) (env (.m 1 (⟨369, [1]⟩ : Lin))) (env (.m 1 (⟨370, [1]⟩ : Lin))) (env (.m 1 (⟨371, [1]⟩ : Lin))) (V (.W 5 0 12)) (V (.R 5 12)) ((inp 368)) ((inp 369)) ((inp 370)) ((inp 371)) h0 h1 h2 h3 h4 h5

theorem core15_1138 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨368, [1]⟩ : Lin)) = (inp 368).zeroExtend 32)
    (h1 : env (.m 1 (⟨369, [1]⟩ : Lin)) = (inp 369).zeroExtend 32)
    (h2 : env (.m 1 (⟨370, [1]⟩ : Lin)) = (inp 370).zeroExtend 32)
    (h3 : env (.m 1 (⟨371, [1]⟩ : Lin)) = (inp 371).zeroExtend 32)
    (h4 : V (.W 5 0 12) = bswap (V (.R 5 12)))
    (h5 : V (.R 5 12) = ((((0 : Word) ||| (inp 368).zeroExtend 32 <<< 0) ||| (inp 369).zeroExtend 32 <<< 8) ||| (inp 370).zeroExtend 32 <<< 16) ||| (inp 371).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 12) :=
  shape19 (env (.m 1 (⟨368, [1]⟩ : Lin))) (env (.m 1 (⟨369, [1]⟩ : Lin))) (env (.m 1 (⟨370, [1]⟩ : Lin))) (env (.m 1 (⟨371, [1]⟩ : Lin))) (V (.W 5 0 12)) (V (.R 5 12)) ((inp 368)) ((inp 369)) ((inp 370)) ((inp 371)) h0 h1 h2 h3 h4 h5

theorem core15_1137 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨368, [1]⟩ : Lin)) = (inp 368).zeroExtend 32)
    (h1 : env (.m 1 (⟨369, [1]⟩ : Lin)) = (inp 369).zeroExtend 32)
    (h2 : env (.m 1 (⟨370, [1]⟩ : Lin)) = (inp 370).zeroExtend 32)
    (h3 : env (.m 1 (⟨371, [1]⟩ : Lin)) = (inp 371).zeroExtend 32)
    (h4 : V (.W 5 0 12) = bswap (V (.R 5 12)))
    (h5 : V (.R 5 12) = ((((0 : Word) ||| (inp 368).zeroExtend 32 <<< 0) ||| (inp 369).zeroExtend 32 <<< 8) ||| (inp 370).zeroExtend 32 <<< 16) ||| (inp 371).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 12) :=
  shape19 (env (.m 1 (⟨368, [1]⟩ : Lin))) (env (.m 1 (⟨369, [1]⟩ : Lin))) (env (.m 1 (⟨370, [1]⟩ : Lin))) (env (.m 1 (⟨371, [1]⟩ : Lin))) (V (.W 5 0 12)) (V (.R 5 12)) ((inp 368)) ((inp 369)) ((inp 370)) ((inp 371)) h0 h1 h2 h3 h4 h5

theorem core15_1136 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨368, [1]⟩ : Lin)) = (inp 368).zeroExtend 32)
    (h1 : env (.m 1 (⟨369, [1]⟩ : Lin)) = (inp 369).zeroExtend 32)
    (h2 : env (.m 1 (⟨370, [1]⟩ : Lin)) = (inp 370).zeroExtend 32)
    (h3 : env (.m 1 (⟨371, [1]⟩ : Lin)) = (inp 371).zeroExtend 32)
    (h4 : V (.W 5 0 12) = bswap (V (.R 5 12)))
    (h5 : V (.R 5 12) = ((((0 : Word) ||| (inp 368).zeroExtend 32 <<< 0) ||| (inp 369).zeroExtend 32 <<< 8) ||| (inp 370).zeroExtend 32 <<< 16) ||| (inp 371).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨368, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨369, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨370, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨371, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 12) :=
  shape19 (env (.m 1 (⟨368, [1]⟩ : Lin))) (env (.m 1 (⟨369, [1]⟩ : Lin))) (env (.m 1 (⟨370, [1]⟩ : Lin))) (env (.m 1 (⟨371, [1]⟩ : Lin))) (V (.W 5 0 12)) (V (.R 5 12)) ((inp 368)) ((inp 369)) ((inp 370)) ((inp 371)) h0 h1 h2 h3 h4 h5

theorem core15_1135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨432, [1]⟩ : Lin)) = (inp 432).zeroExtend 32)
    (h1 : env (.m 1 (⟨433, [1]⟩ : Lin)) = (inp 433).zeroExtend 32)
    (h2 : env (.m 1 (⟨434, [1]⟩ : Lin)) = (inp 434).zeroExtend 32)
    (h3 : env (.m 1 (⟨435, [1]⟩ : Lin)) = (inp 435).zeroExtend 32)
    (h4 : V (.W 6 0 12) = bswap (V (.R 6 12)))
    (h5 : V (.R 6 12) = ((((0 : Word) ||| (inp 432).zeroExtend 32 <<< 0) ||| (inp 433).zeroExtend 32 <<< 8) ||| (inp 434).zeroExtend 32 <<< 16) ||| (inp 435).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 12) :=
  shape19 (env (.m 1 (⟨432, [1]⟩ : Lin))) (env (.m 1 (⟨433, [1]⟩ : Lin))) (env (.m 1 (⟨434, [1]⟩ : Lin))) (env (.m 1 (⟨435, [1]⟩ : Lin))) (V (.W 6 0 12)) (V (.R 6 12)) ((inp 432)) ((inp 433)) ((inp 434)) ((inp 435)) h0 h1 h2 h3 h4 h5

theorem core15_1134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨432, [1]⟩ : Lin)) = (inp 432).zeroExtend 32)
    (h1 : env (.m 1 (⟨433, [1]⟩ : Lin)) = (inp 433).zeroExtend 32)
    (h2 : env (.m 1 (⟨434, [1]⟩ : Lin)) = (inp 434).zeroExtend 32)
    (h3 : env (.m 1 (⟨435, [1]⟩ : Lin)) = (inp 435).zeroExtend 32)
    (h4 : V (.W 6 0 12) = bswap (V (.R 6 12)))
    (h5 : V (.R 6 12) = ((((0 : Word) ||| (inp 432).zeroExtend 32 <<< 0) ||| (inp 433).zeroExtend 32 <<< 8) ||| (inp 434).zeroExtend 32 <<< 16) ||| (inp 435).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 12) :=
  shape19 (env (.m 1 (⟨432, [1]⟩ : Lin))) (env (.m 1 (⟨433, [1]⟩ : Lin))) (env (.m 1 (⟨434, [1]⟩ : Lin))) (env (.m 1 (⟨435, [1]⟩ : Lin))) (V (.W 6 0 12)) (V (.R 6 12)) ((inp 432)) ((inp 433)) ((inp 434)) ((inp 435)) h0 h1 h2 h3 h4 h5

theorem core15_1133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨432, [1]⟩ : Lin)) = (inp 432).zeroExtend 32)
    (h1 : env (.m 1 (⟨433, [1]⟩ : Lin)) = (inp 433).zeroExtend 32)
    (h2 : env (.m 1 (⟨434, [1]⟩ : Lin)) = (inp 434).zeroExtend 32)
    (h3 : env (.m 1 (⟨435, [1]⟩ : Lin)) = (inp 435).zeroExtend 32)
    (h4 : V (.W 6 0 12) = bswap (V (.R 6 12)))
    (h5 : V (.R 6 12) = ((((0 : Word) ||| (inp 432).zeroExtend 32 <<< 0) ||| (inp 433).zeroExtend 32 <<< 8) ||| (inp 434).zeroExtend 32 <<< 16) ||| (inp 435).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 12) :=
  shape19 (env (.m 1 (⟨432, [1]⟩ : Lin))) (env (.m 1 (⟨433, [1]⟩ : Lin))) (env (.m 1 (⟨434, [1]⟩ : Lin))) (env (.m 1 (⟨435, [1]⟩ : Lin))) (V (.W 6 0 12)) (V (.R 6 12)) ((inp 432)) ((inp 433)) ((inp 434)) ((inp 435)) h0 h1 h2 h3 h4 h5

theorem core15_1132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨432, [1]⟩ : Lin)) = (inp 432).zeroExtend 32)
    (h1 : env (.m 1 (⟨433, [1]⟩ : Lin)) = (inp 433).zeroExtend 32)
    (h2 : env (.m 1 (⟨434, [1]⟩ : Lin)) = (inp 434).zeroExtend 32)
    (h3 : env (.m 1 (⟨435, [1]⟩ : Lin)) = (inp 435).zeroExtend 32)
    (h4 : V (.W 6 0 12) = bswap (V (.R 6 12)))
    (h5 : V (.R 6 12) = ((((0 : Word) ||| (inp 432).zeroExtend 32 <<< 0) ||| (inp 433).zeroExtend 32 <<< 8) ||| (inp 434).zeroExtend 32 <<< 16) ||| (inp 435).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨432, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨433, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨434, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨435, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 12) :=
  shape19 (env (.m 1 (⟨432, [1]⟩ : Lin))) (env (.m 1 (⟨433, [1]⟩ : Lin))) (env (.m 1 (⟨434, [1]⟩ : Lin))) (env (.m 1 (⟨435, [1]⟩ : Lin))) (V (.W 6 0 12)) (V (.R 6 12)) ((inp 432)) ((inp 433)) ((inp 434)) ((inp 435)) h0 h1 h2 h3 h4 h5

theorem core15_1131 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨496, [1]⟩ : Lin)) = (inp 496).zeroExtend 32)
    (h1 : env (.m 1 (⟨497, [1]⟩ : Lin)) = (inp 497).zeroExtend 32)
    (h2 : env (.m 1 (⟨498, [1]⟩ : Lin)) = (inp 498).zeroExtend 32)
    (h3 : env (.m 1 (⟨499, [1]⟩ : Lin)) = (inp 499).zeroExtend 32)
    (h4 : V (.W 7 0 12) = bswap (V (.R 7 12)))
    (h5 : V (.R 7 12) = ((((0 : Word) ||| (inp 496).zeroExtend 32 <<< 0) ||| (inp 497).zeroExtend 32 <<< 8) ||| (inp 498).zeroExtend 32 <<< 16) ||| (inp 499).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 12) :=
  shape19 (env (.m 1 (⟨496, [1]⟩ : Lin))) (env (.m 1 (⟨497, [1]⟩ : Lin))) (env (.m 1 (⟨498, [1]⟩ : Lin))) (env (.m 1 (⟨499, [1]⟩ : Lin))) (V (.W 7 0 12)) (V (.R 7 12)) ((inp 496)) ((inp 497)) ((inp 498)) ((inp 499)) h0 h1 h2 h3 h4 h5

theorem core15_1130 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨496, [1]⟩ : Lin)) = (inp 496).zeroExtend 32)
    (h1 : env (.m 1 (⟨497, [1]⟩ : Lin)) = (inp 497).zeroExtend 32)
    (h2 : env (.m 1 (⟨498, [1]⟩ : Lin)) = (inp 498).zeroExtend 32)
    (h3 : env (.m 1 (⟨499, [1]⟩ : Lin)) = (inp 499).zeroExtend 32)
    (h4 : V (.W 7 0 12) = bswap (V (.R 7 12)))
    (h5 : V (.R 7 12) = ((((0 : Word) ||| (inp 496).zeroExtend 32 <<< 0) ||| (inp 497).zeroExtend 32 <<< 8) ||| (inp 498).zeroExtend 32 <<< 16) ||| (inp 499).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 12) :=
  shape19 (env (.m 1 (⟨496, [1]⟩ : Lin))) (env (.m 1 (⟨497, [1]⟩ : Lin))) (env (.m 1 (⟨498, [1]⟩ : Lin))) (env (.m 1 (⟨499, [1]⟩ : Lin))) (V (.W 7 0 12)) (V (.R 7 12)) ((inp 496)) ((inp 497)) ((inp 498)) ((inp 499)) h0 h1 h2 h3 h4 h5

theorem core15_1129 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨496, [1]⟩ : Lin)) = (inp 496).zeroExtend 32)
    (h1 : env (.m 1 (⟨497, [1]⟩ : Lin)) = (inp 497).zeroExtend 32)
    (h2 : env (.m 1 (⟨498, [1]⟩ : Lin)) = (inp 498).zeroExtend 32)
    (h3 : env (.m 1 (⟨499, [1]⟩ : Lin)) = (inp 499).zeroExtend 32)
    (h4 : V (.W 7 0 12) = bswap (V (.R 7 12)))
    (h5 : V (.R 7 12) = ((((0 : Word) ||| (inp 496).zeroExtend 32 <<< 0) ||| (inp 497).zeroExtend 32 <<< 8) ||| (inp 498).zeroExtend 32 <<< 16) ||| (inp 499).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 12) :=
  shape19 (env (.m 1 (⟨496, [1]⟩ : Lin))) (env (.m 1 (⟨497, [1]⟩ : Lin))) (env (.m 1 (⟨498, [1]⟩ : Lin))) (env (.m 1 (⟨499, [1]⟩ : Lin))) (V (.W 7 0 12)) (V (.R 7 12)) ((inp 496)) ((inp 497)) ((inp 498)) ((inp 499)) h0 h1 h2 h3 h4 h5

theorem core15_1128 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨496, [1]⟩ : Lin)) = (inp 496).zeroExtend 32)
    (h1 : env (.m 1 (⟨497, [1]⟩ : Lin)) = (inp 497).zeroExtend 32)
    (h2 : env (.m 1 (⟨498, [1]⟩ : Lin)) = (inp 498).zeroExtend 32)
    (h3 : env (.m 1 (⟨499, [1]⟩ : Lin)) = (inp 499).zeroExtend 32)
    (h4 : V (.W 7 0 12) = bswap (V (.R 7 12)))
    (h5 : V (.R 7 12) = ((((0 : Word) ||| (inp 496).zeroExtend 32 <<< 0) ||| (inp 497).zeroExtend 32 <<< 8) ||| (inp 498).zeroExtend 32 <<< 16) ||| (inp 499).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨496, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨497, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨498, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨499, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 12) :=
  shape19 (env (.m 1 (⟨496, [1]⟩ : Lin))) (env (.m 1 (⟨497, [1]⟩ : Lin))) (env (.m 1 (⟨498, [1]⟩ : Lin))) (env (.m 1 (⟨499, [1]⟩ : Lin))) (V (.W 7 0 12)) (V (.R 7 12)) ((inp 496)) ((inp 497)) ((inp 498)) ((inp 499)) h0 h1 h2 h3 h4 h5

theorem core15_1127 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨52, [1]⟩ : Lin)) = (inp 52).zeroExtend 32)
    (h1 : env (.m 1 (⟨53, [1]⟩ : Lin)) = (inp 53).zeroExtend 32)
    (h2 : env (.m 1 (⟨54, [1]⟩ : Lin)) = (inp 54).zeroExtend 32)
    (h3 : env (.m 1 (⟨55, [1]⟩ : Lin)) = (inp 55).zeroExtend 32)
    (h4 : V (.W 0 0 13) = bswap (V (.R 0 13)))
    (h5 : V (.R 0 13) = ((((0 : Word) ||| (inp 52).zeroExtend 32 <<< 0) ||| (inp 53).zeroExtend 32 <<< 8) ||| (inp 54).zeroExtend 32 <<< 16) ||| (inp 55).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 13) :=
  shape19 (env (.m 1 (⟨52, [1]⟩ : Lin))) (env (.m 1 (⟨53, [1]⟩ : Lin))) (env (.m 1 (⟨54, [1]⟩ : Lin))) (env (.m 1 (⟨55, [1]⟩ : Lin))) (V (.W 0 0 13)) (V (.R 0 13)) ((inp 52)) ((inp 53)) ((inp 54)) ((inp 55)) h0 h1 h2 h3 h4 h5

theorem core15_1126 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨52, [1]⟩ : Lin)) = (inp 52).zeroExtend 32)
    (h1 : env (.m 1 (⟨53, [1]⟩ : Lin)) = (inp 53).zeroExtend 32)
    (h2 : env (.m 1 (⟨54, [1]⟩ : Lin)) = (inp 54).zeroExtend 32)
    (h3 : env (.m 1 (⟨55, [1]⟩ : Lin)) = (inp 55).zeroExtend 32)
    (h4 : V (.W 0 0 13) = bswap (V (.R 0 13)))
    (h5 : V (.R 0 13) = ((((0 : Word) ||| (inp 52).zeroExtend 32 <<< 0) ||| (inp 53).zeroExtend 32 <<< 8) ||| (inp 54).zeroExtend 32 <<< 16) ||| (inp 55).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 13) :=
  shape19 (env (.m 1 (⟨52, [1]⟩ : Lin))) (env (.m 1 (⟨53, [1]⟩ : Lin))) (env (.m 1 (⟨54, [1]⟩ : Lin))) (env (.m 1 (⟨55, [1]⟩ : Lin))) (V (.W 0 0 13)) (V (.R 0 13)) ((inp 52)) ((inp 53)) ((inp 54)) ((inp 55)) h0 h1 h2 h3 h4 h5

theorem core15_1125 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨52, [1]⟩ : Lin)) = (inp 52).zeroExtend 32)
    (h1 : env (.m 1 (⟨53, [1]⟩ : Lin)) = (inp 53).zeroExtend 32)
    (h2 : env (.m 1 (⟨54, [1]⟩ : Lin)) = (inp 54).zeroExtend 32)
    (h3 : env (.m 1 (⟨55, [1]⟩ : Lin)) = (inp 55).zeroExtend 32)
    (h4 : V (.W 0 0 13) = bswap (V (.R 0 13)))
    (h5 : V (.R 0 13) = ((((0 : Word) ||| (inp 52).zeroExtend 32 <<< 0) ||| (inp 53).zeroExtend 32 <<< 8) ||| (inp 54).zeroExtend 32 <<< 16) ||| (inp 55).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 13) :=
  shape19 (env (.m 1 (⟨52, [1]⟩ : Lin))) (env (.m 1 (⟨53, [1]⟩ : Lin))) (env (.m 1 (⟨54, [1]⟩ : Lin))) (env (.m 1 (⟨55, [1]⟩ : Lin))) (V (.W 0 0 13)) (V (.R 0 13)) ((inp 52)) ((inp 53)) ((inp 54)) ((inp 55)) h0 h1 h2 h3 h4 h5

theorem core15_1124 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨52, [1]⟩ : Lin)) = (inp 52).zeroExtend 32)
    (h1 : env (.m 1 (⟨53, [1]⟩ : Lin)) = (inp 53).zeroExtend 32)
    (h2 : env (.m 1 (⟨54, [1]⟩ : Lin)) = (inp 54).zeroExtend 32)
    (h3 : env (.m 1 (⟨55, [1]⟩ : Lin)) = (inp 55).zeroExtend 32)
    (h4 : V (.W 0 0 13) = bswap (V (.R 0 13)))
    (h5 : V (.R 0 13) = ((((0 : Word) ||| (inp 52).zeroExtend 32 <<< 0) ||| (inp 53).zeroExtend 32 <<< 8) ||| (inp 54).zeroExtend 32 <<< 16) ||| (inp 55).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 13) :=
  shape19 (env (.m 1 (⟨52, [1]⟩ : Lin))) (env (.m 1 (⟨53, [1]⟩ : Lin))) (env (.m 1 (⟨54, [1]⟩ : Lin))) (env (.m 1 (⟨55, [1]⟩ : Lin))) (V (.W 0 0 13)) (V (.R 0 13)) ((inp 52)) ((inp 53)) ((inp 54)) ((inp 55)) h0 h1 h2 h3 h4 h5

theorem core15_1123 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨116, [1]⟩ : Lin)) = (inp 116).zeroExtend 32)
    (h1 : env (.m 1 (⟨117, [1]⟩ : Lin)) = (inp 117).zeroExtend 32)
    (h2 : env (.m 1 (⟨118, [1]⟩ : Lin)) = (inp 118).zeroExtend 32)
    (h3 : env (.m 1 (⟨119, [1]⟩ : Lin)) = (inp 119).zeroExtend 32)
    (h4 : V (.W 1 0 13) = bswap (V (.R 1 13)))
    (h5 : V (.R 1 13) = ((((0 : Word) ||| (inp 116).zeroExtend 32 <<< 0) ||| (inp 117).zeroExtend 32 <<< 8) ||| (inp 118).zeroExtend 32 <<< 16) ||| (inp 119).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 13) :=
  shape19 (env (.m 1 (⟨116, [1]⟩ : Lin))) (env (.m 1 (⟨117, [1]⟩ : Lin))) (env (.m 1 (⟨118, [1]⟩ : Lin))) (env (.m 1 (⟨119, [1]⟩ : Lin))) (V (.W 1 0 13)) (V (.R 1 13)) ((inp 116)) ((inp 117)) ((inp 118)) ((inp 119)) h0 h1 h2 h3 h4 h5

theorem core15_1122 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨116, [1]⟩ : Lin)) = (inp 116).zeroExtend 32)
    (h1 : env (.m 1 (⟨117, [1]⟩ : Lin)) = (inp 117).zeroExtend 32)
    (h2 : env (.m 1 (⟨118, [1]⟩ : Lin)) = (inp 118).zeroExtend 32)
    (h3 : env (.m 1 (⟨119, [1]⟩ : Lin)) = (inp 119).zeroExtend 32)
    (h4 : V (.W 1 0 13) = bswap (V (.R 1 13)))
    (h5 : V (.R 1 13) = ((((0 : Word) ||| (inp 116).zeroExtend 32 <<< 0) ||| (inp 117).zeroExtend 32 <<< 8) ||| (inp 118).zeroExtend 32 <<< 16) ||| (inp 119).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 13) :=
  shape19 (env (.m 1 (⟨116, [1]⟩ : Lin))) (env (.m 1 (⟨117, [1]⟩ : Lin))) (env (.m 1 (⟨118, [1]⟩ : Lin))) (env (.m 1 (⟨119, [1]⟩ : Lin))) (V (.W 1 0 13)) (V (.R 1 13)) ((inp 116)) ((inp 117)) ((inp 118)) ((inp 119)) h0 h1 h2 h3 h4 h5

theorem core15_1121 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨116, [1]⟩ : Lin)) = (inp 116).zeroExtend 32)
    (h1 : env (.m 1 (⟨117, [1]⟩ : Lin)) = (inp 117).zeroExtend 32)
    (h2 : env (.m 1 (⟨118, [1]⟩ : Lin)) = (inp 118).zeroExtend 32)
    (h3 : env (.m 1 (⟨119, [1]⟩ : Lin)) = (inp 119).zeroExtend 32)
    (h4 : V (.W 1 0 13) = bswap (V (.R 1 13)))
    (h5 : V (.R 1 13) = ((((0 : Word) ||| (inp 116).zeroExtend 32 <<< 0) ||| (inp 117).zeroExtend 32 <<< 8) ||| (inp 118).zeroExtend 32 <<< 16) ||| (inp 119).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 13) :=
  shape19 (env (.m 1 (⟨116, [1]⟩ : Lin))) (env (.m 1 (⟨117, [1]⟩ : Lin))) (env (.m 1 (⟨118, [1]⟩ : Lin))) (env (.m 1 (⟨119, [1]⟩ : Lin))) (V (.W 1 0 13)) (V (.R 1 13)) ((inp 116)) ((inp 117)) ((inp 118)) ((inp 119)) h0 h1 h2 h3 h4 h5

theorem core15_1120 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨116, [1]⟩ : Lin)) = (inp 116).zeroExtend 32)
    (h1 : env (.m 1 (⟨117, [1]⟩ : Lin)) = (inp 117).zeroExtend 32)
    (h2 : env (.m 1 (⟨118, [1]⟩ : Lin)) = (inp 118).zeroExtend 32)
    (h3 : env (.m 1 (⟨119, [1]⟩ : Lin)) = (inp 119).zeroExtend 32)
    (h4 : V (.W 1 0 13) = bswap (V (.R 1 13)))
    (h5 : V (.R 1 13) = ((((0 : Word) ||| (inp 116).zeroExtend 32 <<< 0) ||| (inp 117).zeroExtend 32 <<< 8) ||| (inp 118).zeroExtend 32 <<< 16) ||| (inp 119).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 13) :=
  shape19 (env (.m 1 (⟨116, [1]⟩ : Lin))) (env (.m 1 (⟨117, [1]⟩ : Lin))) (env (.m 1 (⟨118, [1]⟩ : Lin))) (env (.m 1 (⟨119, [1]⟩ : Lin))) (V (.W 1 0 13)) (V (.R 1 13)) ((inp 116)) ((inp 117)) ((inp 118)) ((inp 119)) h0 h1 h2 h3 h4 h5

theorem core15_1119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨180, [1]⟩ : Lin)) = (inp 180).zeroExtend 32)
    (h1 : env (.m 1 (⟨181, [1]⟩ : Lin)) = (inp 181).zeroExtend 32)
    (h2 : env (.m 1 (⟨182, [1]⟩ : Lin)) = (inp 182).zeroExtend 32)
    (h3 : env (.m 1 (⟨183, [1]⟩ : Lin)) = (inp 183).zeroExtend 32)
    (h4 : V (.W 2 0 13) = bswap (V (.R 2 13)))
    (h5 : V (.R 2 13) = ((((0 : Word) ||| (inp 180).zeroExtend 32 <<< 0) ||| (inp 181).zeroExtend 32 <<< 8) ||| (inp 182).zeroExtend 32 <<< 16) ||| (inp 183).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 13) :=
  shape19 (env (.m 1 (⟨180, [1]⟩ : Lin))) (env (.m 1 (⟨181, [1]⟩ : Lin))) (env (.m 1 (⟨182, [1]⟩ : Lin))) (env (.m 1 (⟨183, [1]⟩ : Lin))) (V (.W 2 0 13)) (V (.R 2 13)) ((inp 180)) ((inp 181)) ((inp 182)) ((inp 183)) h0 h1 h2 h3 h4 h5

theorem core15_1118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨180, [1]⟩ : Lin)) = (inp 180).zeroExtend 32)
    (h1 : env (.m 1 (⟨181, [1]⟩ : Lin)) = (inp 181).zeroExtend 32)
    (h2 : env (.m 1 (⟨182, [1]⟩ : Lin)) = (inp 182).zeroExtend 32)
    (h3 : env (.m 1 (⟨183, [1]⟩ : Lin)) = (inp 183).zeroExtend 32)
    (h4 : V (.W 2 0 13) = bswap (V (.R 2 13)))
    (h5 : V (.R 2 13) = ((((0 : Word) ||| (inp 180).zeroExtend 32 <<< 0) ||| (inp 181).zeroExtend 32 <<< 8) ||| (inp 182).zeroExtend 32 <<< 16) ||| (inp 183).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 13) :=
  shape19 (env (.m 1 (⟨180, [1]⟩ : Lin))) (env (.m 1 (⟨181, [1]⟩ : Lin))) (env (.m 1 (⟨182, [1]⟩ : Lin))) (env (.m 1 (⟨183, [1]⟩ : Lin))) (V (.W 2 0 13)) (V (.R 2 13)) ((inp 180)) ((inp 181)) ((inp 182)) ((inp 183)) h0 h1 h2 h3 h4 h5

theorem core15_1117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨180, [1]⟩ : Lin)) = (inp 180).zeroExtend 32)
    (h1 : env (.m 1 (⟨181, [1]⟩ : Lin)) = (inp 181).zeroExtend 32)
    (h2 : env (.m 1 (⟨182, [1]⟩ : Lin)) = (inp 182).zeroExtend 32)
    (h3 : env (.m 1 (⟨183, [1]⟩ : Lin)) = (inp 183).zeroExtend 32)
    (h4 : V (.W 2 0 13) = bswap (V (.R 2 13)))
    (h5 : V (.R 2 13) = ((((0 : Word) ||| (inp 180).zeroExtend 32 <<< 0) ||| (inp 181).zeroExtend 32 <<< 8) ||| (inp 182).zeroExtend 32 <<< 16) ||| (inp 183).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 13) :=
  shape19 (env (.m 1 (⟨180, [1]⟩ : Lin))) (env (.m 1 (⟨181, [1]⟩ : Lin))) (env (.m 1 (⟨182, [1]⟩ : Lin))) (env (.m 1 (⟨183, [1]⟩ : Lin))) (V (.W 2 0 13)) (V (.R 2 13)) ((inp 180)) ((inp 181)) ((inp 182)) ((inp 183)) h0 h1 h2 h3 h4 h5

theorem core15_1116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨180, [1]⟩ : Lin)) = (inp 180).zeroExtend 32)
    (h1 : env (.m 1 (⟨181, [1]⟩ : Lin)) = (inp 181).zeroExtend 32)
    (h2 : env (.m 1 (⟨182, [1]⟩ : Lin)) = (inp 182).zeroExtend 32)
    (h3 : env (.m 1 (⟨183, [1]⟩ : Lin)) = (inp 183).zeroExtend 32)
    (h4 : V (.W 2 0 13) = bswap (V (.R 2 13)))
    (h5 : V (.R 2 13) = ((((0 : Word) ||| (inp 180).zeroExtend 32 <<< 0) ||| (inp 181).zeroExtend 32 <<< 8) ||| (inp 182).zeroExtend 32 <<< 16) ||| (inp 183).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 13) :=
  shape19 (env (.m 1 (⟨180, [1]⟩ : Lin))) (env (.m 1 (⟨181, [1]⟩ : Lin))) (env (.m 1 (⟨182, [1]⟩ : Lin))) (env (.m 1 (⟨183, [1]⟩ : Lin))) (V (.W 2 0 13)) (V (.R 2 13)) ((inp 180)) ((inp 181)) ((inp 182)) ((inp 183)) h0 h1 h2 h3 h4 h5

theorem core15_1115 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨244, [1]⟩ : Lin)) = (inp 244).zeroExtend 32)
    (h1 : env (.m 1 (⟨245, [1]⟩ : Lin)) = (inp 245).zeroExtend 32)
    (h2 : env (.m 1 (⟨246, [1]⟩ : Lin)) = (inp 246).zeroExtend 32)
    (h3 : env (.m 1 (⟨247, [1]⟩ : Lin)) = (inp 247).zeroExtend 32)
    (h4 : V (.W 3 0 13) = bswap (V (.R 3 13)))
    (h5 : V (.R 3 13) = ((((0 : Word) ||| (inp 244).zeroExtend 32 <<< 0) ||| (inp 245).zeroExtend 32 <<< 8) ||| (inp 246).zeroExtend 32 <<< 16) ||| (inp 247).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 13) :=
  shape19 (env (.m 1 (⟨244, [1]⟩ : Lin))) (env (.m 1 (⟨245, [1]⟩ : Lin))) (env (.m 1 (⟨246, [1]⟩ : Lin))) (env (.m 1 (⟨247, [1]⟩ : Lin))) (V (.W 3 0 13)) (V (.R 3 13)) ((inp 244)) ((inp 245)) ((inp 246)) ((inp 247)) h0 h1 h2 h3 h4 h5

theorem core15_1114 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨244, [1]⟩ : Lin)) = (inp 244).zeroExtend 32)
    (h1 : env (.m 1 (⟨245, [1]⟩ : Lin)) = (inp 245).zeroExtend 32)
    (h2 : env (.m 1 (⟨246, [1]⟩ : Lin)) = (inp 246).zeroExtend 32)
    (h3 : env (.m 1 (⟨247, [1]⟩ : Lin)) = (inp 247).zeroExtend 32)
    (h4 : V (.W 3 0 13) = bswap (V (.R 3 13)))
    (h5 : V (.R 3 13) = ((((0 : Word) ||| (inp 244).zeroExtend 32 <<< 0) ||| (inp 245).zeroExtend 32 <<< 8) ||| (inp 246).zeroExtend 32 <<< 16) ||| (inp 247).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 13) :=
  shape19 (env (.m 1 (⟨244, [1]⟩ : Lin))) (env (.m 1 (⟨245, [1]⟩ : Lin))) (env (.m 1 (⟨246, [1]⟩ : Lin))) (env (.m 1 (⟨247, [1]⟩ : Lin))) (V (.W 3 0 13)) (V (.R 3 13)) ((inp 244)) ((inp 245)) ((inp 246)) ((inp 247)) h0 h1 h2 h3 h4 h5

theorem core15_1113 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨244, [1]⟩ : Lin)) = (inp 244).zeroExtend 32)
    (h1 : env (.m 1 (⟨245, [1]⟩ : Lin)) = (inp 245).zeroExtend 32)
    (h2 : env (.m 1 (⟨246, [1]⟩ : Lin)) = (inp 246).zeroExtend 32)
    (h3 : env (.m 1 (⟨247, [1]⟩ : Lin)) = (inp 247).zeroExtend 32)
    (h4 : V (.W 3 0 13) = bswap (V (.R 3 13)))
    (h5 : V (.R 3 13) = ((((0 : Word) ||| (inp 244).zeroExtend 32 <<< 0) ||| (inp 245).zeroExtend 32 <<< 8) ||| (inp 246).zeroExtend 32 <<< 16) ||| (inp 247).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 13) :=
  shape19 (env (.m 1 (⟨244, [1]⟩ : Lin))) (env (.m 1 (⟨245, [1]⟩ : Lin))) (env (.m 1 (⟨246, [1]⟩ : Lin))) (env (.m 1 (⟨247, [1]⟩ : Lin))) (V (.W 3 0 13)) (V (.R 3 13)) ((inp 244)) ((inp 245)) ((inp 246)) ((inp 247)) h0 h1 h2 h3 h4 h5

theorem core15_1112 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨244, [1]⟩ : Lin)) = (inp 244).zeroExtend 32)
    (h1 : env (.m 1 (⟨245, [1]⟩ : Lin)) = (inp 245).zeroExtend 32)
    (h2 : env (.m 1 (⟨246, [1]⟩ : Lin)) = (inp 246).zeroExtend 32)
    (h3 : env (.m 1 (⟨247, [1]⟩ : Lin)) = (inp 247).zeroExtend 32)
    (h4 : V (.W 3 0 13) = bswap (V (.R 3 13)))
    (h5 : V (.R 3 13) = ((((0 : Word) ||| (inp 244).zeroExtend 32 <<< 0) ||| (inp 245).zeroExtend 32 <<< 8) ||| (inp 246).zeroExtend 32 <<< 16) ||| (inp 247).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 13) :=
  shape19 (env (.m 1 (⟨244, [1]⟩ : Lin))) (env (.m 1 (⟨245, [1]⟩ : Lin))) (env (.m 1 (⟨246, [1]⟩ : Lin))) (env (.m 1 (⟨247, [1]⟩ : Lin))) (V (.W 3 0 13)) (V (.R 3 13)) ((inp 244)) ((inp 245)) ((inp 246)) ((inp 247)) h0 h1 h2 h3 h4 h5

theorem core15_1111 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨308, [1]⟩ : Lin)) = (inp 308).zeroExtend 32)
    (h1 : env (.m 1 (⟨309, [1]⟩ : Lin)) = (inp 309).zeroExtend 32)
    (h2 : env (.m 1 (⟨310, [1]⟩ : Lin)) = (inp 310).zeroExtend 32)
    (h3 : env (.m 1 (⟨311, [1]⟩ : Lin)) = (inp 311).zeroExtend 32)
    (h4 : V (.W 4 0 13) = bswap (V (.R 4 13)))
    (h5 : V (.R 4 13) = ((((0 : Word) ||| (inp 308).zeroExtend 32 <<< 0) ||| (inp 309).zeroExtend 32 <<< 8) ||| (inp 310).zeroExtend 32 <<< 16) ||| (inp 311).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 13) :=
  shape19 (env (.m 1 (⟨308, [1]⟩ : Lin))) (env (.m 1 (⟨309, [1]⟩ : Lin))) (env (.m 1 (⟨310, [1]⟩ : Lin))) (env (.m 1 (⟨311, [1]⟩ : Lin))) (V (.W 4 0 13)) (V (.R 4 13)) ((inp 308)) ((inp 309)) ((inp 310)) ((inp 311)) h0 h1 h2 h3 h4 h5

theorem core15_1110 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨308, [1]⟩ : Lin)) = (inp 308).zeroExtend 32)
    (h1 : env (.m 1 (⟨309, [1]⟩ : Lin)) = (inp 309).zeroExtend 32)
    (h2 : env (.m 1 (⟨310, [1]⟩ : Lin)) = (inp 310).zeroExtend 32)
    (h3 : env (.m 1 (⟨311, [1]⟩ : Lin)) = (inp 311).zeroExtend 32)
    (h4 : V (.W 4 0 13) = bswap (V (.R 4 13)))
    (h5 : V (.R 4 13) = ((((0 : Word) ||| (inp 308).zeroExtend 32 <<< 0) ||| (inp 309).zeroExtend 32 <<< 8) ||| (inp 310).zeroExtend 32 <<< 16) ||| (inp 311).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 13) :=
  shape19 (env (.m 1 (⟨308, [1]⟩ : Lin))) (env (.m 1 (⟨309, [1]⟩ : Lin))) (env (.m 1 (⟨310, [1]⟩ : Lin))) (env (.m 1 (⟨311, [1]⟩ : Lin))) (V (.W 4 0 13)) (V (.R 4 13)) ((inp 308)) ((inp 309)) ((inp 310)) ((inp 311)) h0 h1 h2 h3 h4 h5

theorem core15_1109 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨308, [1]⟩ : Lin)) = (inp 308).zeroExtend 32)
    (h1 : env (.m 1 (⟨309, [1]⟩ : Lin)) = (inp 309).zeroExtend 32)
    (h2 : env (.m 1 (⟨310, [1]⟩ : Lin)) = (inp 310).zeroExtend 32)
    (h3 : env (.m 1 (⟨311, [1]⟩ : Lin)) = (inp 311).zeroExtend 32)
    (h4 : V (.W 4 0 13) = bswap (V (.R 4 13)))
    (h5 : V (.R 4 13) = ((((0 : Word) ||| (inp 308).zeroExtend 32 <<< 0) ||| (inp 309).zeroExtend 32 <<< 8) ||| (inp 310).zeroExtend 32 <<< 16) ||| (inp 311).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 13) :=
  shape19 (env (.m 1 (⟨308, [1]⟩ : Lin))) (env (.m 1 (⟨309, [1]⟩ : Lin))) (env (.m 1 (⟨310, [1]⟩ : Lin))) (env (.m 1 (⟨311, [1]⟩ : Lin))) (V (.W 4 0 13)) (V (.R 4 13)) ((inp 308)) ((inp 309)) ((inp 310)) ((inp 311)) h0 h1 h2 h3 h4 h5

theorem core15_1108 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨308, [1]⟩ : Lin)) = (inp 308).zeroExtend 32)
    (h1 : env (.m 1 (⟨309, [1]⟩ : Lin)) = (inp 309).zeroExtend 32)
    (h2 : env (.m 1 (⟨310, [1]⟩ : Lin)) = (inp 310).zeroExtend 32)
    (h3 : env (.m 1 (⟨311, [1]⟩ : Lin)) = (inp 311).zeroExtend 32)
    (h4 : V (.W 4 0 13) = bswap (V (.R 4 13)))
    (h5 : V (.R 4 13) = ((((0 : Word) ||| (inp 308).zeroExtend 32 <<< 0) ||| (inp 309).zeroExtend 32 <<< 8) ||| (inp 310).zeroExtend 32 <<< 16) ||| (inp 311).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨308, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨309, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨310, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨311, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 13) :=
  shape19 (env (.m 1 (⟨308, [1]⟩ : Lin))) (env (.m 1 (⟨309, [1]⟩ : Lin))) (env (.m 1 (⟨310, [1]⟩ : Lin))) (env (.m 1 (⟨311, [1]⟩ : Lin))) (V (.W 4 0 13)) (V (.R 4 13)) ((inp 308)) ((inp 309)) ((inp 310)) ((inp 311)) h0 h1 h2 h3 h4 h5

theorem core15_1107 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨372, [1]⟩ : Lin)) = (inp 372).zeroExtend 32)
    (h1 : env (.m 1 (⟨373, [1]⟩ : Lin)) = (inp 373).zeroExtend 32)
    (h2 : env (.m 1 (⟨374, [1]⟩ : Lin)) = (inp 374).zeroExtend 32)
    (h3 : env (.m 1 (⟨375, [1]⟩ : Lin)) = (inp 375).zeroExtend 32)
    (h4 : V (.W 5 0 13) = bswap (V (.R 5 13)))
    (h5 : V (.R 5 13) = ((((0 : Word) ||| (inp 372).zeroExtend 32 <<< 0) ||| (inp 373).zeroExtend 32 <<< 8) ||| (inp 374).zeroExtend 32 <<< 16) ||| (inp 375).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 13) :=
  shape19 (env (.m 1 (⟨372, [1]⟩ : Lin))) (env (.m 1 (⟨373, [1]⟩ : Lin))) (env (.m 1 (⟨374, [1]⟩ : Lin))) (env (.m 1 (⟨375, [1]⟩ : Lin))) (V (.W 5 0 13)) (V (.R 5 13)) ((inp 372)) ((inp 373)) ((inp 374)) ((inp 375)) h0 h1 h2 h3 h4 h5

theorem core15_1106 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨372, [1]⟩ : Lin)) = (inp 372).zeroExtend 32)
    (h1 : env (.m 1 (⟨373, [1]⟩ : Lin)) = (inp 373).zeroExtend 32)
    (h2 : env (.m 1 (⟨374, [1]⟩ : Lin)) = (inp 374).zeroExtend 32)
    (h3 : env (.m 1 (⟨375, [1]⟩ : Lin)) = (inp 375).zeroExtend 32)
    (h4 : V (.W 5 0 13) = bswap (V (.R 5 13)))
    (h5 : V (.R 5 13) = ((((0 : Word) ||| (inp 372).zeroExtend 32 <<< 0) ||| (inp 373).zeroExtend 32 <<< 8) ||| (inp 374).zeroExtend 32 <<< 16) ||| (inp 375).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 13) :=
  shape19 (env (.m 1 (⟨372, [1]⟩ : Lin))) (env (.m 1 (⟨373, [1]⟩ : Lin))) (env (.m 1 (⟨374, [1]⟩ : Lin))) (env (.m 1 (⟨375, [1]⟩ : Lin))) (V (.W 5 0 13)) (V (.R 5 13)) ((inp 372)) ((inp 373)) ((inp 374)) ((inp 375)) h0 h1 h2 h3 h4 h5

theorem core15_1105 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨372, [1]⟩ : Lin)) = (inp 372).zeroExtend 32)
    (h1 : env (.m 1 (⟨373, [1]⟩ : Lin)) = (inp 373).zeroExtend 32)
    (h2 : env (.m 1 (⟨374, [1]⟩ : Lin)) = (inp 374).zeroExtend 32)
    (h3 : env (.m 1 (⟨375, [1]⟩ : Lin)) = (inp 375).zeroExtend 32)
    (h4 : V (.W 5 0 13) = bswap (V (.R 5 13)))
    (h5 : V (.R 5 13) = ((((0 : Word) ||| (inp 372).zeroExtend 32 <<< 0) ||| (inp 373).zeroExtend 32 <<< 8) ||| (inp 374).zeroExtend 32 <<< 16) ||| (inp 375).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 13) :=
  shape19 (env (.m 1 (⟨372, [1]⟩ : Lin))) (env (.m 1 (⟨373, [1]⟩ : Lin))) (env (.m 1 (⟨374, [1]⟩ : Lin))) (env (.m 1 (⟨375, [1]⟩ : Lin))) (V (.W 5 0 13)) (V (.R 5 13)) ((inp 372)) ((inp 373)) ((inp 374)) ((inp 375)) h0 h1 h2 h3 h4 h5

theorem core15_1104 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨372, [1]⟩ : Lin)) = (inp 372).zeroExtend 32)
    (h1 : env (.m 1 (⟨373, [1]⟩ : Lin)) = (inp 373).zeroExtend 32)
    (h2 : env (.m 1 (⟨374, [1]⟩ : Lin)) = (inp 374).zeroExtend 32)
    (h3 : env (.m 1 (⟨375, [1]⟩ : Lin)) = (inp 375).zeroExtend 32)
    (h4 : V (.W 5 0 13) = bswap (V (.R 5 13)))
    (h5 : V (.R 5 13) = ((((0 : Word) ||| (inp 372).zeroExtend 32 <<< 0) ||| (inp 373).zeroExtend 32 <<< 8) ||| (inp 374).zeroExtend 32 <<< 16) ||| (inp 375).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨372, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨373, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨374, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨375, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 13) :=
  shape19 (env (.m 1 (⟨372, [1]⟩ : Lin))) (env (.m 1 (⟨373, [1]⟩ : Lin))) (env (.m 1 (⟨374, [1]⟩ : Lin))) (env (.m 1 (⟨375, [1]⟩ : Lin))) (V (.W 5 0 13)) (V (.R 5 13)) ((inp 372)) ((inp 373)) ((inp 374)) ((inp 375)) h0 h1 h2 h3 h4 h5

theorem core15_1103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨436, [1]⟩ : Lin)) = (inp 436).zeroExtend 32)
    (h1 : env (.m 1 (⟨437, [1]⟩ : Lin)) = (inp 437).zeroExtend 32)
    (h2 : env (.m 1 (⟨438, [1]⟩ : Lin)) = (inp 438).zeroExtend 32)
    (h3 : env (.m 1 (⟨439, [1]⟩ : Lin)) = (inp 439).zeroExtend 32)
    (h4 : V (.W 6 0 13) = bswap (V (.R 6 13)))
    (h5 : V (.R 6 13) = ((((0 : Word) ||| (inp 436).zeroExtend 32 <<< 0) ||| (inp 437).zeroExtend 32 <<< 8) ||| (inp 438).zeroExtend 32 <<< 16) ||| (inp 439).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 13) :=
  shape19 (env (.m 1 (⟨436, [1]⟩ : Lin))) (env (.m 1 (⟨437, [1]⟩ : Lin))) (env (.m 1 (⟨438, [1]⟩ : Lin))) (env (.m 1 (⟨439, [1]⟩ : Lin))) (V (.W 6 0 13)) (V (.R 6 13)) ((inp 436)) ((inp 437)) ((inp 438)) ((inp 439)) h0 h1 h2 h3 h4 h5

theorem core15_1102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨436, [1]⟩ : Lin)) = (inp 436).zeroExtend 32)
    (h1 : env (.m 1 (⟨437, [1]⟩ : Lin)) = (inp 437).zeroExtend 32)
    (h2 : env (.m 1 (⟨438, [1]⟩ : Lin)) = (inp 438).zeroExtend 32)
    (h3 : env (.m 1 (⟨439, [1]⟩ : Lin)) = (inp 439).zeroExtend 32)
    (h4 : V (.W 6 0 13) = bswap (V (.R 6 13)))
    (h5 : V (.R 6 13) = ((((0 : Word) ||| (inp 436).zeroExtend 32 <<< 0) ||| (inp 437).zeroExtend 32 <<< 8) ||| (inp 438).zeroExtend 32 <<< 16) ||| (inp 439).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 13) :=
  shape19 (env (.m 1 (⟨436, [1]⟩ : Lin))) (env (.m 1 (⟨437, [1]⟩ : Lin))) (env (.m 1 (⟨438, [1]⟩ : Lin))) (env (.m 1 (⟨439, [1]⟩ : Lin))) (V (.W 6 0 13)) (V (.R 6 13)) ((inp 436)) ((inp 437)) ((inp 438)) ((inp 439)) h0 h1 h2 h3 h4 h5

theorem core15_1101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨436, [1]⟩ : Lin)) = (inp 436).zeroExtend 32)
    (h1 : env (.m 1 (⟨437, [1]⟩ : Lin)) = (inp 437).zeroExtend 32)
    (h2 : env (.m 1 (⟨438, [1]⟩ : Lin)) = (inp 438).zeroExtend 32)
    (h3 : env (.m 1 (⟨439, [1]⟩ : Lin)) = (inp 439).zeroExtend 32)
    (h4 : V (.W 6 0 13) = bswap (V (.R 6 13)))
    (h5 : V (.R 6 13) = ((((0 : Word) ||| (inp 436).zeroExtend 32 <<< 0) ||| (inp 437).zeroExtend 32 <<< 8) ||| (inp 438).zeroExtend 32 <<< 16) ||| (inp 439).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 13) :=
  shape19 (env (.m 1 (⟨436, [1]⟩ : Lin))) (env (.m 1 (⟨437, [1]⟩ : Lin))) (env (.m 1 (⟨438, [1]⟩ : Lin))) (env (.m 1 (⟨439, [1]⟩ : Lin))) (V (.W 6 0 13)) (V (.R 6 13)) ((inp 436)) ((inp 437)) ((inp 438)) ((inp 439)) h0 h1 h2 h3 h4 h5

theorem core15_1100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨436, [1]⟩ : Lin)) = (inp 436).zeroExtend 32)
    (h1 : env (.m 1 (⟨437, [1]⟩ : Lin)) = (inp 437).zeroExtend 32)
    (h2 : env (.m 1 (⟨438, [1]⟩ : Lin)) = (inp 438).zeroExtend 32)
    (h3 : env (.m 1 (⟨439, [1]⟩ : Lin)) = (inp 439).zeroExtend 32)
    (h4 : V (.W 6 0 13) = bswap (V (.R 6 13)))
    (h5 : V (.R 6 13) = ((((0 : Word) ||| (inp 436).zeroExtend 32 <<< 0) ||| (inp 437).zeroExtend 32 <<< 8) ||| (inp 438).zeroExtend 32 <<< 16) ||| (inp 439).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨436, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨437, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨438, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨439, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 13) :=
  shape19 (env (.m 1 (⟨436, [1]⟩ : Lin))) (env (.m 1 (⟨437, [1]⟩ : Lin))) (env (.m 1 (⟨438, [1]⟩ : Lin))) (env (.m 1 (⟨439, [1]⟩ : Lin))) (V (.W 6 0 13)) (V (.R 6 13)) ((inp 436)) ((inp 437)) ((inp 438)) ((inp 439)) h0 h1 h2 h3 h4 h5

theorem core15_1099 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨500, [1]⟩ : Lin)) = (inp 500).zeroExtend 32)
    (h1 : env (.m 1 (⟨501, [1]⟩ : Lin)) = (inp 501).zeroExtend 32)
    (h2 : env (.m 1 (⟨502, [1]⟩ : Lin)) = (inp 502).zeroExtend 32)
    (h3 : env (.m 1 (⟨503, [1]⟩ : Lin)) = (inp 503).zeroExtend 32)
    (h4 : V (.W 7 0 13) = bswap (V (.R 7 13)))
    (h5 : V (.R 7 13) = ((((0 : Word) ||| (inp 500).zeroExtend 32 <<< 0) ||| (inp 501).zeroExtend 32 <<< 8) ||| (inp 502).zeroExtend 32 <<< 16) ||| (inp 503).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 13) :=
  shape19 (env (.m 1 (⟨500, [1]⟩ : Lin))) (env (.m 1 (⟨501, [1]⟩ : Lin))) (env (.m 1 (⟨502, [1]⟩ : Lin))) (env (.m 1 (⟨503, [1]⟩ : Lin))) (V (.W 7 0 13)) (V (.R 7 13)) ((inp 500)) ((inp 501)) ((inp 502)) ((inp 503)) h0 h1 h2 h3 h4 h5

theorem core15_1098 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨500, [1]⟩ : Lin)) = (inp 500).zeroExtend 32)
    (h1 : env (.m 1 (⟨501, [1]⟩ : Lin)) = (inp 501).zeroExtend 32)
    (h2 : env (.m 1 (⟨502, [1]⟩ : Lin)) = (inp 502).zeroExtend 32)
    (h3 : env (.m 1 (⟨503, [1]⟩ : Lin)) = (inp 503).zeroExtend 32)
    (h4 : V (.W 7 0 13) = bswap (V (.R 7 13)))
    (h5 : V (.R 7 13) = ((((0 : Word) ||| (inp 500).zeroExtend 32 <<< 0) ||| (inp 501).zeroExtend 32 <<< 8) ||| (inp 502).zeroExtend 32 <<< 16) ||| (inp 503).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 13) :=
  shape19 (env (.m 1 (⟨500, [1]⟩ : Lin))) (env (.m 1 (⟨501, [1]⟩ : Lin))) (env (.m 1 (⟨502, [1]⟩ : Lin))) (env (.m 1 (⟨503, [1]⟩ : Lin))) (V (.W 7 0 13)) (V (.R 7 13)) ((inp 500)) ((inp 501)) ((inp 502)) ((inp 503)) h0 h1 h2 h3 h4 h5

theorem core15_1097 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨500, [1]⟩ : Lin)) = (inp 500).zeroExtend 32)
    (h1 : env (.m 1 (⟨501, [1]⟩ : Lin)) = (inp 501).zeroExtend 32)
    (h2 : env (.m 1 (⟨502, [1]⟩ : Lin)) = (inp 502).zeroExtend 32)
    (h3 : env (.m 1 (⟨503, [1]⟩ : Lin)) = (inp 503).zeroExtend 32)
    (h4 : V (.W 7 0 13) = bswap (V (.R 7 13)))
    (h5 : V (.R 7 13) = ((((0 : Word) ||| (inp 500).zeroExtend 32 <<< 0) ||| (inp 501).zeroExtend 32 <<< 8) ||| (inp 502).zeroExtend 32 <<< 16) ||| (inp 503).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 13) :=
  shape19 (env (.m 1 (⟨500, [1]⟩ : Lin))) (env (.m 1 (⟨501, [1]⟩ : Lin))) (env (.m 1 (⟨502, [1]⟩ : Lin))) (env (.m 1 (⟨503, [1]⟩ : Lin))) (V (.W 7 0 13)) (V (.R 7 13)) ((inp 500)) ((inp 501)) ((inp 502)) ((inp 503)) h0 h1 h2 h3 h4 h5

theorem core15_1096 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨500, [1]⟩ : Lin)) = (inp 500).zeroExtend 32)
    (h1 : env (.m 1 (⟨501, [1]⟩ : Lin)) = (inp 501).zeroExtend 32)
    (h2 : env (.m 1 (⟨502, [1]⟩ : Lin)) = (inp 502).zeroExtend 32)
    (h3 : env (.m 1 (⟨503, [1]⟩ : Lin)) = (inp 503).zeroExtend 32)
    (h4 : V (.W 7 0 13) = bswap (V (.R 7 13)))
    (h5 : V (.R 7 13) = ((((0 : Word) ||| (inp 500).zeroExtend 32 <<< 0) ||| (inp 501).zeroExtend 32 <<< 8) ||| (inp 502).zeroExtend 32 <<< 16) ||| (inp 503).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨500, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨501, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨502, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨503, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 13) :=
  shape19 (env (.m 1 (⟨500, [1]⟩ : Lin))) (env (.m 1 (⟨501, [1]⟩ : Lin))) (env (.m 1 (⟨502, [1]⟩ : Lin))) (env (.m 1 (⟨503, [1]⟩ : Lin))) (V (.W 7 0 13)) (V (.R 7 13)) ((inp 500)) ((inp 501)) ((inp 502)) ((inp 503)) h0 h1 h2 h3 h4 h5

theorem core15_1095 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨56, [1]⟩ : Lin)) = (inp 56).zeroExtend 32)
    (h1 : env (.m 1 (⟨57, [1]⟩ : Lin)) = (inp 57).zeroExtend 32)
    (h2 : env (.m 1 (⟨58, [1]⟩ : Lin)) = (inp 58).zeroExtend 32)
    (h3 : env (.m 1 (⟨59, [1]⟩ : Lin)) = (inp 59).zeroExtend 32)
    (h4 : V (.W 0 0 14) = bswap (V (.R 0 14)))
    (h5 : V (.R 0 14) = ((((0 : Word) ||| (inp 56).zeroExtend 32 <<< 0) ||| (inp 57).zeroExtend 32 <<< 8) ||| (inp 58).zeroExtend 32 <<< 16) ||| (inp 59).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 14) :=
  shape19 (env (.m 1 (⟨56, [1]⟩ : Lin))) (env (.m 1 (⟨57, [1]⟩ : Lin))) (env (.m 1 (⟨58, [1]⟩ : Lin))) (env (.m 1 (⟨59, [1]⟩ : Lin))) (V (.W 0 0 14)) (V (.R 0 14)) ((inp 56)) ((inp 57)) ((inp 58)) ((inp 59)) h0 h1 h2 h3 h4 h5

theorem core15_1094 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨56, [1]⟩ : Lin)) = (inp 56).zeroExtend 32)
    (h1 : env (.m 1 (⟨57, [1]⟩ : Lin)) = (inp 57).zeroExtend 32)
    (h2 : env (.m 1 (⟨58, [1]⟩ : Lin)) = (inp 58).zeroExtend 32)
    (h3 : env (.m 1 (⟨59, [1]⟩ : Lin)) = (inp 59).zeroExtend 32)
    (h4 : V (.W 0 0 14) = bswap (V (.R 0 14)))
    (h5 : V (.R 0 14) = ((((0 : Word) ||| (inp 56).zeroExtend 32 <<< 0) ||| (inp 57).zeroExtend 32 <<< 8) ||| (inp 58).zeroExtend 32 <<< 16) ||| (inp 59).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 14) :=
  shape19 (env (.m 1 (⟨56, [1]⟩ : Lin))) (env (.m 1 (⟨57, [1]⟩ : Lin))) (env (.m 1 (⟨58, [1]⟩ : Lin))) (env (.m 1 (⟨59, [1]⟩ : Lin))) (V (.W 0 0 14)) (V (.R 0 14)) ((inp 56)) ((inp 57)) ((inp 58)) ((inp 59)) h0 h1 h2 h3 h4 h5

theorem core15_1093 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨56, [1]⟩ : Lin)) = (inp 56).zeroExtend 32)
    (h1 : env (.m 1 (⟨57, [1]⟩ : Lin)) = (inp 57).zeroExtend 32)
    (h2 : env (.m 1 (⟨58, [1]⟩ : Lin)) = (inp 58).zeroExtend 32)
    (h3 : env (.m 1 (⟨59, [1]⟩ : Lin)) = (inp 59).zeroExtend 32)
    (h4 : V (.W 0 0 14) = bswap (V (.R 0 14)))
    (h5 : V (.R 0 14) = ((((0 : Word) ||| (inp 56).zeroExtend 32 <<< 0) ||| (inp 57).zeroExtend 32 <<< 8) ||| (inp 58).zeroExtend 32 <<< 16) ||| (inp 59).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 14) :=
  shape19 (env (.m 1 (⟨56, [1]⟩ : Lin))) (env (.m 1 (⟨57, [1]⟩ : Lin))) (env (.m 1 (⟨58, [1]⟩ : Lin))) (env (.m 1 (⟨59, [1]⟩ : Lin))) (V (.W 0 0 14)) (V (.R 0 14)) ((inp 56)) ((inp 57)) ((inp 58)) ((inp 59)) h0 h1 h2 h3 h4 h5

theorem core15_1092 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨56, [1]⟩ : Lin)) = (inp 56).zeroExtend 32)
    (h1 : env (.m 1 (⟨57, [1]⟩ : Lin)) = (inp 57).zeroExtend 32)
    (h2 : env (.m 1 (⟨58, [1]⟩ : Lin)) = (inp 58).zeroExtend 32)
    (h3 : env (.m 1 (⟨59, [1]⟩ : Lin)) = (inp 59).zeroExtend 32)
    (h4 : V (.W 0 0 14) = bswap (V (.R 0 14)))
    (h5 : V (.R 0 14) = ((((0 : Word) ||| (inp 56).zeroExtend 32 <<< 0) ||| (inp 57).zeroExtend 32 <<< 8) ||| (inp 58).zeroExtend 32 <<< 16) ||| (inp 59).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 14) :=
  shape19 (env (.m 1 (⟨56, [1]⟩ : Lin))) (env (.m 1 (⟨57, [1]⟩ : Lin))) (env (.m 1 (⟨58, [1]⟩ : Lin))) (env (.m 1 (⟨59, [1]⟩ : Lin))) (V (.W 0 0 14)) (V (.R 0 14)) ((inp 56)) ((inp 57)) ((inp 58)) ((inp 59)) h0 h1 h2 h3 h4 h5

theorem core15_1091 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨120, [1]⟩ : Lin)) = (inp 120).zeroExtend 32)
    (h1 : env (.m 1 (⟨121, [1]⟩ : Lin)) = (inp 121).zeroExtend 32)
    (h2 : env (.m 1 (⟨122, [1]⟩ : Lin)) = (inp 122).zeroExtend 32)
    (h3 : env (.m 1 (⟨123, [1]⟩ : Lin)) = (inp 123).zeroExtend 32)
    (h4 : V (.W 1 0 14) = bswap (V (.R 1 14)))
    (h5 : V (.R 1 14) = ((((0 : Word) ||| (inp 120).zeroExtend 32 <<< 0) ||| (inp 121).zeroExtend 32 <<< 8) ||| (inp 122).zeroExtend 32 <<< 16) ||| (inp 123).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 14) :=
  shape19 (env (.m 1 (⟨120, [1]⟩ : Lin))) (env (.m 1 (⟨121, [1]⟩ : Lin))) (env (.m 1 (⟨122, [1]⟩ : Lin))) (env (.m 1 (⟨123, [1]⟩ : Lin))) (V (.W 1 0 14)) (V (.R 1 14)) ((inp 120)) ((inp 121)) ((inp 122)) ((inp 123)) h0 h1 h2 h3 h4 h5

theorem core15_1090 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨120, [1]⟩ : Lin)) = (inp 120).zeroExtend 32)
    (h1 : env (.m 1 (⟨121, [1]⟩ : Lin)) = (inp 121).zeroExtend 32)
    (h2 : env (.m 1 (⟨122, [1]⟩ : Lin)) = (inp 122).zeroExtend 32)
    (h3 : env (.m 1 (⟨123, [1]⟩ : Lin)) = (inp 123).zeroExtend 32)
    (h4 : V (.W 1 0 14) = bswap (V (.R 1 14)))
    (h5 : V (.R 1 14) = ((((0 : Word) ||| (inp 120).zeroExtend 32 <<< 0) ||| (inp 121).zeroExtend 32 <<< 8) ||| (inp 122).zeroExtend 32 <<< 16) ||| (inp 123).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 14) :=
  shape19 (env (.m 1 (⟨120, [1]⟩ : Lin))) (env (.m 1 (⟨121, [1]⟩ : Lin))) (env (.m 1 (⟨122, [1]⟩ : Lin))) (env (.m 1 (⟨123, [1]⟩ : Lin))) (V (.W 1 0 14)) (V (.R 1 14)) ((inp 120)) ((inp 121)) ((inp 122)) ((inp 123)) h0 h1 h2 h3 h4 h5

theorem core15_1089 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨120, [1]⟩ : Lin)) = (inp 120).zeroExtend 32)
    (h1 : env (.m 1 (⟨121, [1]⟩ : Lin)) = (inp 121).zeroExtend 32)
    (h2 : env (.m 1 (⟨122, [1]⟩ : Lin)) = (inp 122).zeroExtend 32)
    (h3 : env (.m 1 (⟨123, [1]⟩ : Lin)) = (inp 123).zeroExtend 32)
    (h4 : V (.W 1 0 14) = bswap (V (.R 1 14)))
    (h5 : V (.R 1 14) = ((((0 : Word) ||| (inp 120).zeroExtend 32 <<< 0) ||| (inp 121).zeroExtend 32 <<< 8) ||| (inp 122).zeroExtend 32 <<< 16) ||| (inp 123).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 14) :=
  shape19 (env (.m 1 (⟨120, [1]⟩ : Lin))) (env (.m 1 (⟨121, [1]⟩ : Lin))) (env (.m 1 (⟨122, [1]⟩ : Lin))) (env (.m 1 (⟨123, [1]⟩ : Lin))) (V (.W 1 0 14)) (V (.R 1 14)) ((inp 120)) ((inp 121)) ((inp 122)) ((inp 123)) h0 h1 h2 h3 h4 h5

theorem core15_1088 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨120, [1]⟩ : Lin)) = (inp 120).zeroExtend 32)
    (h1 : env (.m 1 (⟨121, [1]⟩ : Lin)) = (inp 121).zeroExtend 32)
    (h2 : env (.m 1 (⟨122, [1]⟩ : Lin)) = (inp 122).zeroExtend 32)
    (h3 : env (.m 1 (⟨123, [1]⟩ : Lin)) = (inp 123).zeroExtend 32)
    (h4 : V (.W 1 0 14) = bswap (V (.R 1 14)))
    (h5 : V (.R 1 14) = ((((0 : Word) ||| (inp 120).zeroExtend 32 <<< 0) ||| (inp 121).zeroExtend 32 <<< 8) ||| (inp 122).zeroExtend 32 <<< 16) ||| (inp 123).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 14) :=
  shape19 (env (.m 1 (⟨120, [1]⟩ : Lin))) (env (.m 1 (⟨121, [1]⟩ : Lin))) (env (.m 1 (⟨122, [1]⟩ : Lin))) (env (.m 1 (⟨123, [1]⟩ : Lin))) (V (.W 1 0 14)) (V (.R 1 14)) ((inp 120)) ((inp 121)) ((inp 122)) ((inp 123)) h0 h1 h2 h3 h4 h5

theorem core15_1087 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨184, [1]⟩ : Lin)) = (inp 184).zeroExtend 32)
    (h1 : env (.m 1 (⟨185, [1]⟩ : Lin)) = (inp 185).zeroExtend 32)
    (h2 : env (.m 1 (⟨186, [1]⟩ : Lin)) = (inp 186).zeroExtend 32)
    (h3 : env (.m 1 (⟨187, [1]⟩ : Lin)) = (inp 187).zeroExtend 32)
    (h4 : V (.W 2 0 14) = bswap (V (.R 2 14)))
    (h5 : V (.R 2 14) = ((((0 : Word) ||| (inp 184).zeroExtend 32 <<< 0) ||| (inp 185).zeroExtend 32 <<< 8) ||| (inp 186).zeroExtend 32 <<< 16) ||| (inp 187).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 14) :=
  shape19 (env (.m 1 (⟨184, [1]⟩ : Lin))) (env (.m 1 (⟨185, [1]⟩ : Lin))) (env (.m 1 (⟨186, [1]⟩ : Lin))) (env (.m 1 (⟨187, [1]⟩ : Lin))) (V (.W 2 0 14)) (V (.R 2 14)) ((inp 184)) ((inp 185)) ((inp 186)) ((inp 187)) h0 h1 h2 h3 h4 h5

theorem core15_1086 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨184, [1]⟩ : Lin)) = (inp 184).zeroExtend 32)
    (h1 : env (.m 1 (⟨185, [1]⟩ : Lin)) = (inp 185).zeroExtend 32)
    (h2 : env (.m 1 (⟨186, [1]⟩ : Lin)) = (inp 186).zeroExtend 32)
    (h3 : env (.m 1 (⟨187, [1]⟩ : Lin)) = (inp 187).zeroExtend 32)
    (h4 : V (.W 2 0 14) = bswap (V (.R 2 14)))
    (h5 : V (.R 2 14) = ((((0 : Word) ||| (inp 184).zeroExtend 32 <<< 0) ||| (inp 185).zeroExtend 32 <<< 8) ||| (inp 186).zeroExtend 32 <<< 16) ||| (inp 187).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 14) :=
  shape19 (env (.m 1 (⟨184, [1]⟩ : Lin))) (env (.m 1 (⟨185, [1]⟩ : Lin))) (env (.m 1 (⟨186, [1]⟩ : Lin))) (env (.m 1 (⟨187, [1]⟩ : Lin))) (V (.W 2 0 14)) (V (.R 2 14)) ((inp 184)) ((inp 185)) ((inp 186)) ((inp 187)) h0 h1 h2 h3 h4 h5

theorem core15_1085 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨184, [1]⟩ : Lin)) = (inp 184).zeroExtend 32)
    (h1 : env (.m 1 (⟨185, [1]⟩ : Lin)) = (inp 185).zeroExtend 32)
    (h2 : env (.m 1 (⟨186, [1]⟩ : Lin)) = (inp 186).zeroExtend 32)
    (h3 : env (.m 1 (⟨187, [1]⟩ : Lin)) = (inp 187).zeroExtend 32)
    (h4 : V (.W 2 0 14) = bswap (V (.R 2 14)))
    (h5 : V (.R 2 14) = ((((0 : Word) ||| (inp 184).zeroExtend 32 <<< 0) ||| (inp 185).zeroExtend 32 <<< 8) ||| (inp 186).zeroExtend 32 <<< 16) ||| (inp 187).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 14) :=
  shape19 (env (.m 1 (⟨184, [1]⟩ : Lin))) (env (.m 1 (⟨185, [1]⟩ : Lin))) (env (.m 1 (⟨186, [1]⟩ : Lin))) (env (.m 1 (⟨187, [1]⟩ : Lin))) (V (.W 2 0 14)) (V (.R 2 14)) ((inp 184)) ((inp 185)) ((inp 186)) ((inp 187)) h0 h1 h2 h3 h4 h5

theorem core15_1084 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨184, [1]⟩ : Lin)) = (inp 184).zeroExtend 32)
    (h1 : env (.m 1 (⟨185, [1]⟩ : Lin)) = (inp 185).zeroExtend 32)
    (h2 : env (.m 1 (⟨186, [1]⟩ : Lin)) = (inp 186).zeroExtend 32)
    (h3 : env (.m 1 (⟨187, [1]⟩ : Lin)) = (inp 187).zeroExtend 32)
    (h4 : V (.W 2 0 14) = bswap (V (.R 2 14)))
    (h5 : V (.R 2 14) = ((((0 : Word) ||| (inp 184).zeroExtend 32 <<< 0) ||| (inp 185).zeroExtend 32 <<< 8) ||| (inp 186).zeroExtend 32 <<< 16) ||| (inp 187).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 14) :=
  shape19 (env (.m 1 (⟨184, [1]⟩ : Lin))) (env (.m 1 (⟨185, [1]⟩ : Lin))) (env (.m 1 (⟨186, [1]⟩ : Lin))) (env (.m 1 (⟨187, [1]⟩ : Lin))) (V (.W 2 0 14)) (V (.R 2 14)) ((inp 184)) ((inp 185)) ((inp 186)) ((inp 187)) h0 h1 h2 h3 h4 h5

theorem core15_1083 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨248, [1]⟩ : Lin)) = (inp 248).zeroExtend 32)
    (h1 : env (.m 1 (⟨249, [1]⟩ : Lin)) = (inp 249).zeroExtend 32)
    (h2 : env (.m 1 (⟨250, [1]⟩ : Lin)) = (inp 250).zeroExtend 32)
    (h3 : env (.m 1 (⟨251, [1]⟩ : Lin)) = (inp 251).zeroExtend 32)
    (h4 : V (.W 3 0 14) = bswap (V (.R 3 14)))
    (h5 : V (.R 3 14) = ((((0 : Word) ||| (inp 248).zeroExtend 32 <<< 0) ||| (inp 249).zeroExtend 32 <<< 8) ||| (inp 250).zeroExtend 32 <<< 16) ||| (inp 251).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 14) :=
  shape19 (env (.m 1 (⟨248, [1]⟩ : Lin))) (env (.m 1 (⟨249, [1]⟩ : Lin))) (env (.m 1 (⟨250, [1]⟩ : Lin))) (env (.m 1 (⟨251, [1]⟩ : Lin))) (V (.W 3 0 14)) (V (.R 3 14)) ((inp 248)) ((inp 249)) ((inp 250)) ((inp 251)) h0 h1 h2 h3 h4 h5

theorem core15_1082 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨248, [1]⟩ : Lin)) = (inp 248).zeroExtend 32)
    (h1 : env (.m 1 (⟨249, [1]⟩ : Lin)) = (inp 249).zeroExtend 32)
    (h2 : env (.m 1 (⟨250, [1]⟩ : Lin)) = (inp 250).zeroExtend 32)
    (h3 : env (.m 1 (⟨251, [1]⟩ : Lin)) = (inp 251).zeroExtend 32)
    (h4 : V (.W 3 0 14) = bswap (V (.R 3 14)))
    (h5 : V (.R 3 14) = ((((0 : Word) ||| (inp 248).zeroExtend 32 <<< 0) ||| (inp 249).zeroExtend 32 <<< 8) ||| (inp 250).zeroExtend 32 <<< 16) ||| (inp 251).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 14) :=
  shape19 (env (.m 1 (⟨248, [1]⟩ : Lin))) (env (.m 1 (⟨249, [1]⟩ : Lin))) (env (.m 1 (⟨250, [1]⟩ : Lin))) (env (.m 1 (⟨251, [1]⟩ : Lin))) (V (.W 3 0 14)) (V (.R 3 14)) ((inp 248)) ((inp 249)) ((inp 250)) ((inp 251)) h0 h1 h2 h3 h4 h5

theorem core15_1081 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨248, [1]⟩ : Lin)) = (inp 248).zeroExtend 32)
    (h1 : env (.m 1 (⟨249, [1]⟩ : Lin)) = (inp 249).zeroExtend 32)
    (h2 : env (.m 1 (⟨250, [1]⟩ : Lin)) = (inp 250).zeroExtend 32)
    (h3 : env (.m 1 (⟨251, [1]⟩ : Lin)) = (inp 251).zeroExtend 32)
    (h4 : V (.W 3 0 14) = bswap (V (.R 3 14)))
    (h5 : V (.R 3 14) = ((((0 : Word) ||| (inp 248).zeroExtend 32 <<< 0) ||| (inp 249).zeroExtend 32 <<< 8) ||| (inp 250).zeroExtend 32 <<< 16) ||| (inp 251).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 14) :=
  shape19 (env (.m 1 (⟨248, [1]⟩ : Lin))) (env (.m 1 (⟨249, [1]⟩ : Lin))) (env (.m 1 (⟨250, [1]⟩ : Lin))) (env (.m 1 (⟨251, [1]⟩ : Lin))) (V (.W 3 0 14)) (V (.R 3 14)) ((inp 248)) ((inp 249)) ((inp 250)) ((inp 251)) h0 h1 h2 h3 h4 h5

theorem core15_1080 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨248, [1]⟩ : Lin)) = (inp 248).zeroExtend 32)
    (h1 : env (.m 1 (⟨249, [1]⟩ : Lin)) = (inp 249).zeroExtend 32)
    (h2 : env (.m 1 (⟨250, [1]⟩ : Lin)) = (inp 250).zeroExtend 32)
    (h3 : env (.m 1 (⟨251, [1]⟩ : Lin)) = (inp 251).zeroExtend 32)
    (h4 : V (.W 3 0 14) = bswap (V (.R 3 14)))
    (h5 : V (.R 3 14) = ((((0 : Word) ||| (inp 248).zeroExtend 32 <<< 0) ||| (inp 249).zeroExtend 32 <<< 8) ||| (inp 250).zeroExtend 32 <<< 16) ||| (inp 251).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 14) :=
  shape19 (env (.m 1 (⟨248, [1]⟩ : Lin))) (env (.m 1 (⟨249, [1]⟩ : Lin))) (env (.m 1 (⟨250, [1]⟩ : Lin))) (env (.m 1 (⟨251, [1]⟩ : Lin))) (V (.W 3 0 14)) (V (.R 3 14)) ((inp 248)) ((inp 249)) ((inp 250)) ((inp 251)) h0 h1 h2 h3 h4 h5

theorem core15_1079 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨312, [1]⟩ : Lin)) = (inp 312).zeroExtend 32)
    (h1 : env (.m 1 (⟨313, [1]⟩ : Lin)) = (inp 313).zeroExtend 32)
    (h2 : env (.m 1 (⟨314, [1]⟩ : Lin)) = (inp 314).zeroExtend 32)
    (h3 : env (.m 1 (⟨315, [1]⟩ : Lin)) = (inp 315).zeroExtend 32)
    (h4 : V (.W 4 0 14) = bswap (V (.R 4 14)))
    (h5 : V (.R 4 14) = ((((0 : Word) ||| (inp 312).zeroExtend 32 <<< 0) ||| (inp 313).zeroExtend 32 <<< 8) ||| (inp 314).zeroExtend 32 <<< 16) ||| (inp 315).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 14) :=
  shape19 (env (.m 1 (⟨312, [1]⟩ : Lin))) (env (.m 1 (⟨313, [1]⟩ : Lin))) (env (.m 1 (⟨314, [1]⟩ : Lin))) (env (.m 1 (⟨315, [1]⟩ : Lin))) (V (.W 4 0 14)) (V (.R 4 14)) ((inp 312)) ((inp 313)) ((inp 314)) ((inp 315)) h0 h1 h2 h3 h4 h5

theorem core15_1078 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨312, [1]⟩ : Lin)) = (inp 312).zeroExtend 32)
    (h1 : env (.m 1 (⟨313, [1]⟩ : Lin)) = (inp 313).zeroExtend 32)
    (h2 : env (.m 1 (⟨314, [1]⟩ : Lin)) = (inp 314).zeroExtend 32)
    (h3 : env (.m 1 (⟨315, [1]⟩ : Lin)) = (inp 315).zeroExtend 32)
    (h4 : V (.W 4 0 14) = bswap (V (.R 4 14)))
    (h5 : V (.R 4 14) = ((((0 : Word) ||| (inp 312).zeroExtend 32 <<< 0) ||| (inp 313).zeroExtend 32 <<< 8) ||| (inp 314).zeroExtend 32 <<< 16) ||| (inp 315).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 14) :=
  shape19 (env (.m 1 (⟨312, [1]⟩ : Lin))) (env (.m 1 (⟨313, [1]⟩ : Lin))) (env (.m 1 (⟨314, [1]⟩ : Lin))) (env (.m 1 (⟨315, [1]⟩ : Lin))) (V (.W 4 0 14)) (V (.R 4 14)) ((inp 312)) ((inp 313)) ((inp 314)) ((inp 315)) h0 h1 h2 h3 h4 h5

theorem core15_1077 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨312, [1]⟩ : Lin)) = (inp 312).zeroExtend 32)
    (h1 : env (.m 1 (⟨313, [1]⟩ : Lin)) = (inp 313).zeroExtend 32)
    (h2 : env (.m 1 (⟨314, [1]⟩ : Lin)) = (inp 314).zeroExtend 32)
    (h3 : env (.m 1 (⟨315, [1]⟩ : Lin)) = (inp 315).zeroExtend 32)
    (h4 : V (.W 4 0 14) = bswap (V (.R 4 14)))
    (h5 : V (.R 4 14) = ((((0 : Word) ||| (inp 312).zeroExtend 32 <<< 0) ||| (inp 313).zeroExtend 32 <<< 8) ||| (inp 314).zeroExtend 32 <<< 16) ||| (inp 315).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 14) :=
  shape19 (env (.m 1 (⟨312, [1]⟩ : Lin))) (env (.m 1 (⟨313, [1]⟩ : Lin))) (env (.m 1 (⟨314, [1]⟩ : Lin))) (env (.m 1 (⟨315, [1]⟩ : Lin))) (V (.W 4 0 14)) (V (.R 4 14)) ((inp 312)) ((inp 313)) ((inp 314)) ((inp 315)) h0 h1 h2 h3 h4 h5

theorem core15_1076 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨312, [1]⟩ : Lin)) = (inp 312).zeroExtend 32)
    (h1 : env (.m 1 (⟨313, [1]⟩ : Lin)) = (inp 313).zeroExtend 32)
    (h2 : env (.m 1 (⟨314, [1]⟩ : Lin)) = (inp 314).zeroExtend 32)
    (h3 : env (.m 1 (⟨315, [1]⟩ : Lin)) = (inp 315).zeroExtend 32)
    (h4 : V (.W 4 0 14) = bswap (V (.R 4 14)))
    (h5 : V (.R 4 14) = ((((0 : Word) ||| (inp 312).zeroExtend 32 <<< 0) ||| (inp 313).zeroExtend 32 <<< 8) ||| (inp 314).zeroExtend 32 <<< 16) ||| (inp 315).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨312, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨313, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨314, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨315, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 14) :=
  shape19 (env (.m 1 (⟨312, [1]⟩ : Lin))) (env (.m 1 (⟨313, [1]⟩ : Lin))) (env (.m 1 (⟨314, [1]⟩ : Lin))) (env (.m 1 (⟨315, [1]⟩ : Lin))) (V (.W 4 0 14)) (V (.R 4 14)) ((inp 312)) ((inp 313)) ((inp 314)) ((inp 315)) h0 h1 h2 h3 h4 h5

theorem core15_1075 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨376, [1]⟩ : Lin)) = (inp 376).zeroExtend 32)
    (h1 : env (.m 1 (⟨377, [1]⟩ : Lin)) = (inp 377).zeroExtend 32)
    (h2 : env (.m 1 (⟨378, [1]⟩ : Lin)) = (inp 378).zeroExtend 32)
    (h3 : env (.m 1 (⟨379, [1]⟩ : Lin)) = (inp 379).zeroExtend 32)
    (h4 : V (.W 5 0 14) = bswap (V (.R 5 14)))
    (h5 : V (.R 5 14) = ((((0 : Word) ||| (inp 376).zeroExtend 32 <<< 0) ||| (inp 377).zeroExtend 32 <<< 8) ||| (inp 378).zeroExtend 32 <<< 16) ||| (inp 379).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 14) :=
  shape19 (env (.m 1 (⟨376, [1]⟩ : Lin))) (env (.m 1 (⟨377, [1]⟩ : Lin))) (env (.m 1 (⟨378, [1]⟩ : Lin))) (env (.m 1 (⟨379, [1]⟩ : Lin))) (V (.W 5 0 14)) (V (.R 5 14)) ((inp 376)) ((inp 377)) ((inp 378)) ((inp 379)) h0 h1 h2 h3 h4 h5

theorem core15_1074 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨376, [1]⟩ : Lin)) = (inp 376).zeroExtend 32)
    (h1 : env (.m 1 (⟨377, [1]⟩ : Lin)) = (inp 377).zeroExtend 32)
    (h2 : env (.m 1 (⟨378, [1]⟩ : Lin)) = (inp 378).zeroExtend 32)
    (h3 : env (.m 1 (⟨379, [1]⟩ : Lin)) = (inp 379).zeroExtend 32)
    (h4 : V (.W 5 0 14) = bswap (V (.R 5 14)))
    (h5 : V (.R 5 14) = ((((0 : Word) ||| (inp 376).zeroExtend 32 <<< 0) ||| (inp 377).zeroExtend 32 <<< 8) ||| (inp 378).zeroExtend 32 <<< 16) ||| (inp 379).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 14) :=
  shape19 (env (.m 1 (⟨376, [1]⟩ : Lin))) (env (.m 1 (⟨377, [1]⟩ : Lin))) (env (.m 1 (⟨378, [1]⟩ : Lin))) (env (.m 1 (⟨379, [1]⟩ : Lin))) (V (.W 5 0 14)) (V (.R 5 14)) ((inp 376)) ((inp 377)) ((inp 378)) ((inp 379)) h0 h1 h2 h3 h4 h5

theorem core15_1073 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨376, [1]⟩ : Lin)) = (inp 376).zeroExtend 32)
    (h1 : env (.m 1 (⟨377, [1]⟩ : Lin)) = (inp 377).zeroExtend 32)
    (h2 : env (.m 1 (⟨378, [1]⟩ : Lin)) = (inp 378).zeroExtend 32)
    (h3 : env (.m 1 (⟨379, [1]⟩ : Lin)) = (inp 379).zeroExtend 32)
    (h4 : V (.W 5 0 14) = bswap (V (.R 5 14)))
    (h5 : V (.R 5 14) = ((((0 : Word) ||| (inp 376).zeroExtend 32 <<< 0) ||| (inp 377).zeroExtend 32 <<< 8) ||| (inp 378).zeroExtend 32 <<< 16) ||| (inp 379).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 14) :=
  shape19 (env (.m 1 (⟨376, [1]⟩ : Lin))) (env (.m 1 (⟨377, [1]⟩ : Lin))) (env (.m 1 (⟨378, [1]⟩ : Lin))) (env (.m 1 (⟨379, [1]⟩ : Lin))) (V (.W 5 0 14)) (V (.R 5 14)) ((inp 376)) ((inp 377)) ((inp 378)) ((inp 379)) h0 h1 h2 h3 h4 h5

theorem core15_1072 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨376, [1]⟩ : Lin)) = (inp 376).zeroExtend 32)
    (h1 : env (.m 1 (⟨377, [1]⟩ : Lin)) = (inp 377).zeroExtend 32)
    (h2 : env (.m 1 (⟨378, [1]⟩ : Lin)) = (inp 378).zeroExtend 32)
    (h3 : env (.m 1 (⟨379, [1]⟩ : Lin)) = (inp 379).zeroExtend 32)
    (h4 : V (.W 5 0 14) = bswap (V (.R 5 14)))
    (h5 : V (.R 5 14) = ((((0 : Word) ||| (inp 376).zeroExtend 32 <<< 0) ||| (inp 377).zeroExtend 32 <<< 8) ||| (inp 378).zeroExtend 32 <<< 16) ||| (inp 379).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨376, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨377, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨378, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨379, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 14) :=
  shape19 (env (.m 1 (⟨376, [1]⟩ : Lin))) (env (.m 1 (⟨377, [1]⟩ : Lin))) (env (.m 1 (⟨378, [1]⟩ : Lin))) (env (.m 1 (⟨379, [1]⟩ : Lin))) (V (.W 5 0 14)) (V (.R 5 14)) ((inp 376)) ((inp 377)) ((inp 378)) ((inp 379)) h0 h1 h2 h3 h4 h5

theorem core15_1071 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨440, [1]⟩ : Lin)) = (inp 440).zeroExtend 32)
    (h1 : env (.m 1 (⟨441, [1]⟩ : Lin)) = (inp 441).zeroExtend 32)
    (h2 : env (.m 1 (⟨442, [1]⟩ : Lin)) = (inp 442).zeroExtend 32)
    (h3 : env (.m 1 (⟨443, [1]⟩ : Lin)) = (inp 443).zeroExtend 32)
    (h4 : V (.W 6 0 14) = bswap (V (.R 6 14)))
    (h5 : V (.R 6 14) = ((((0 : Word) ||| (inp 440).zeroExtend 32 <<< 0) ||| (inp 441).zeroExtend 32 <<< 8) ||| (inp 442).zeroExtend 32 <<< 16) ||| (inp 443).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 14) :=
  shape19 (env (.m 1 (⟨440, [1]⟩ : Lin))) (env (.m 1 (⟨441, [1]⟩ : Lin))) (env (.m 1 (⟨442, [1]⟩ : Lin))) (env (.m 1 (⟨443, [1]⟩ : Lin))) (V (.W 6 0 14)) (V (.R 6 14)) ((inp 440)) ((inp 441)) ((inp 442)) ((inp 443)) h0 h1 h2 h3 h4 h5

theorem core15_1070 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨440, [1]⟩ : Lin)) = (inp 440).zeroExtend 32)
    (h1 : env (.m 1 (⟨441, [1]⟩ : Lin)) = (inp 441).zeroExtend 32)
    (h2 : env (.m 1 (⟨442, [1]⟩ : Lin)) = (inp 442).zeroExtend 32)
    (h3 : env (.m 1 (⟨443, [1]⟩ : Lin)) = (inp 443).zeroExtend 32)
    (h4 : V (.W 6 0 14) = bswap (V (.R 6 14)))
    (h5 : V (.R 6 14) = ((((0 : Word) ||| (inp 440).zeroExtend 32 <<< 0) ||| (inp 441).zeroExtend 32 <<< 8) ||| (inp 442).zeroExtend 32 <<< 16) ||| (inp 443).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 14) :=
  shape19 (env (.m 1 (⟨440, [1]⟩ : Lin))) (env (.m 1 (⟨441, [1]⟩ : Lin))) (env (.m 1 (⟨442, [1]⟩ : Lin))) (env (.m 1 (⟨443, [1]⟩ : Lin))) (V (.W 6 0 14)) (V (.R 6 14)) ((inp 440)) ((inp 441)) ((inp 442)) ((inp 443)) h0 h1 h2 h3 h4 h5

theorem core15_1069 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨440, [1]⟩ : Lin)) = (inp 440).zeroExtend 32)
    (h1 : env (.m 1 (⟨441, [1]⟩ : Lin)) = (inp 441).zeroExtend 32)
    (h2 : env (.m 1 (⟨442, [1]⟩ : Lin)) = (inp 442).zeroExtend 32)
    (h3 : env (.m 1 (⟨443, [1]⟩ : Lin)) = (inp 443).zeroExtend 32)
    (h4 : V (.W 6 0 14) = bswap (V (.R 6 14)))
    (h5 : V (.R 6 14) = ((((0 : Word) ||| (inp 440).zeroExtend 32 <<< 0) ||| (inp 441).zeroExtend 32 <<< 8) ||| (inp 442).zeroExtend 32 <<< 16) ||| (inp 443).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 14) :=
  shape19 (env (.m 1 (⟨440, [1]⟩ : Lin))) (env (.m 1 (⟨441, [1]⟩ : Lin))) (env (.m 1 (⟨442, [1]⟩ : Lin))) (env (.m 1 (⟨443, [1]⟩ : Lin))) (V (.W 6 0 14)) (V (.R 6 14)) ((inp 440)) ((inp 441)) ((inp 442)) ((inp 443)) h0 h1 h2 h3 h4 h5

theorem core15_1068 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨440, [1]⟩ : Lin)) = (inp 440).zeroExtend 32)
    (h1 : env (.m 1 (⟨441, [1]⟩ : Lin)) = (inp 441).zeroExtend 32)
    (h2 : env (.m 1 (⟨442, [1]⟩ : Lin)) = (inp 442).zeroExtend 32)
    (h3 : env (.m 1 (⟨443, [1]⟩ : Lin)) = (inp 443).zeroExtend 32)
    (h4 : V (.W 6 0 14) = bswap (V (.R 6 14)))
    (h5 : V (.R 6 14) = ((((0 : Word) ||| (inp 440).zeroExtend 32 <<< 0) ||| (inp 441).zeroExtend 32 <<< 8) ||| (inp 442).zeroExtend 32 <<< 16) ||| (inp 443).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨440, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨441, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨442, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨443, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 14) :=
  shape19 (env (.m 1 (⟨440, [1]⟩ : Lin))) (env (.m 1 (⟨441, [1]⟩ : Lin))) (env (.m 1 (⟨442, [1]⟩ : Lin))) (env (.m 1 (⟨443, [1]⟩ : Lin))) (V (.W 6 0 14)) (V (.R 6 14)) ((inp 440)) ((inp 441)) ((inp 442)) ((inp 443)) h0 h1 h2 h3 h4 h5

theorem core15_1067 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨504, [1]⟩ : Lin)) = (inp 504).zeroExtend 32)
    (h1 : env (.m 1 (⟨505, [1]⟩ : Lin)) = (inp 505).zeroExtend 32)
    (h2 : env (.m 1 (⟨506, [1]⟩ : Lin)) = (inp 506).zeroExtend 32)
    (h3 : env (.m 1 (⟨507, [1]⟩ : Lin)) = (inp 507).zeroExtend 32)
    (h4 : V (.W 7 0 14) = bswap (V (.R 7 14)))
    (h5 : V (.R 7 14) = ((((0 : Word) ||| (inp 504).zeroExtend 32 <<< 0) ||| (inp 505).zeroExtend 32 <<< 8) ||| (inp 506).zeroExtend 32 <<< 16) ||| (inp 507).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 14) :=
  shape19 (env (.m 1 (⟨504, [1]⟩ : Lin))) (env (.m 1 (⟨505, [1]⟩ : Lin))) (env (.m 1 (⟨506, [1]⟩ : Lin))) (env (.m 1 (⟨507, [1]⟩ : Lin))) (V (.W 7 0 14)) (V (.R 7 14)) ((inp 504)) ((inp 505)) ((inp 506)) ((inp 507)) h0 h1 h2 h3 h4 h5

theorem core15_1066 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨504, [1]⟩ : Lin)) = (inp 504).zeroExtend 32)
    (h1 : env (.m 1 (⟨505, [1]⟩ : Lin)) = (inp 505).zeroExtend 32)
    (h2 : env (.m 1 (⟨506, [1]⟩ : Lin)) = (inp 506).zeroExtend 32)
    (h3 : env (.m 1 (⟨507, [1]⟩ : Lin)) = (inp 507).zeroExtend 32)
    (h4 : V (.W 7 0 14) = bswap (V (.R 7 14)))
    (h5 : V (.R 7 14) = ((((0 : Word) ||| (inp 504).zeroExtend 32 <<< 0) ||| (inp 505).zeroExtend 32 <<< 8) ||| (inp 506).zeroExtend 32 <<< 16) ||| (inp 507).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 14) :=
  shape19 (env (.m 1 (⟨504, [1]⟩ : Lin))) (env (.m 1 (⟨505, [1]⟩ : Lin))) (env (.m 1 (⟨506, [1]⟩ : Lin))) (env (.m 1 (⟨507, [1]⟩ : Lin))) (V (.W 7 0 14)) (V (.R 7 14)) ((inp 504)) ((inp 505)) ((inp 506)) ((inp 507)) h0 h1 h2 h3 h4 h5

theorem core15_1065 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨504, [1]⟩ : Lin)) = (inp 504).zeroExtend 32)
    (h1 : env (.m 1 (⟨505, [1]⟩ : Lin)) = (inp 505).zeroExtend 32)
    (h2 : env (.m 1 (⟨506, [1]⟩ : Lin)) = (inp 506).zeroExtend 32)
    (h3 : env (.m 1 (⟨507, [1]⟩ : Lin)) = (inp 507).zeroExtend 32)
    (h4 : V (.W 7 0 14) = bswap (V (.R 7 14)))
    (h5 : V (.R 7 14) = ((((0 : Word) ||| (inp 504).zeroExtend 32 <<< 0) ||| (inp 505).zeroExtend 32 <<< 8) ||| (inp 506).zeroExtend 32 <<< 16) ||| (inp 507).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 14) :=
  shape19 (env (.m 1 (⟨504, [1]⟩ : Lin))) (env (.m 1 (⟨505, [1]⟩ : Lin))) (env (.m 1 (⟨506, [1]⟩ : Lin))) (env (.m 1 (⟨507, [1]⟩ : Lin))) (V (.W 7 0 14)) (V (.R 7 14)) ((inp 504)) ((inp 505)) ((inp 506)) ((inp 507)) h0 h1 h2 h3 h4 h5

theorem core15_1064 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨504, [1]⟩ : Lin)) = (inp 504).zeroExtend 32)
    (h1 : env (.m 1 (⟨505, [1]⟩ : Lin)) = (inp 505).zeroExtend 32)
    (h2 : env (.m 1 (⟨506, [1]⟩ : Lin)) = (inp 506).zeroExtend 32)
    (h3 : env (.m 1 (⟨507, [1]⟩ : Lin)) = (inp 507).zeroExtend 32)
    (h4 : V (.W 7 0 14) = bswap (V (.R 7 14)))
    (h5 : V (.R 7 14) = ((((0 : Word) ||| (inp 504).zeroExtend 32 <<< 0) ||| (inp 505).zeroExtend 32 <<< 8) ||| (inp 506).zeroExtend 32 <<< 16) ||| (inp 507).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨504, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨505, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨506, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨507, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 14) :=
  shape19 (env (.m 1 (⟨504, [1]⟩ : Lin))) (env (.m 1 (⟨505, [1]⟩ : Lin))) (env (.m 1 (⟨506, [1]⟩ : Lin))) (env (.m 1 (⟨507, [1]⟩ : Lin))) (V (.W 7 0 14)) (V (.R 7 14)) ((inp 504)) ((inp 505)) ((inp 506)) ((inp 507)) h0 h1 h2 h3 h4 h5

theorem core15_1063 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨60, [1]⟩ : Lin)) = (inp 60).zeroExtend 32)
    (h1 : env (.m 1 (⟨61, [1]⟩ : Lin)) = (inp 61).zeroExtend 32)
    (h2 : env (.m 1 (⟨62, [1]⟩ : Lin)) = (inp 62).zeroExtend 32)
    (h3 : env (.m 1 (⟨63, [1]⟩ : Lin)) = (inp 63).zeroExtend 32)
    (h4 : V (.W 0 0 15) = bswap (V (.R 0 15)))
    (h5 : V (.R 0 15) = ((((0 : Word) ||| (inp 60).zeroExtend 32 <<< 0) ||| (inp 61).zeroExtend 32 <<< 8) ||| (inp 62).zeroExtend 32 <<< 16) ||| (inp 63).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 15) :=
  shape19 (env (.m 1 (⟨60, [1]⟩ : Lin))) (env (.m 1 (⟨61, [1]⟩ : Lin))) (env (.m 1 (⟨62, [1]⟩ : Lin))) (env (.m 1 (⟨63, [1]⟩ : Lin))) (V (.W 0 0 15)) (V (.R 0 15)) ((inp 60)) ((inp 61)) ((inp 62)) ((inp 63)) h0 h1 h2 h3 h4 h5

theorem core15_1062 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨60, [1]⟩ : Lin)) = (inp 60).zeroExtend 32)
    (h1 : env (.m 1 (⟨61, [1]⟩ : Lin)) = (inp 61).zeroExtend 32)
    (h2 : env (.m 1 (⟨62, [1]⟩ : Lin)) = (inp 62).zeroExtend 32)
    (h3 : env (.m 1 (⟨63, [1]⟩ : Lin)) = (inp 63).zeroExtend 32)
    (h4 : V (.W 0 0 15) = bswap (V (.R 0 15)))
    (h5 : V (.R 0 15) = ((((0 : Word) ||| (inp 60).zeroExtend 32 <<< 0) ||| (inp 61).zeroExtend 32 <<< 8) ||| (inp 62).zeroExtend 32 <<< 16) ||| (inp 63).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 15) :=
  shape19 (env (.m 1 (⟨60, [1]⟩ : Lin))) (env (.m 1 (⟨61, [1]⟩ : Lin))) (env (.m 1 (⟨62, [1]⟩ : Lin))) (env (.m 1 (⟨63, [1]⟩ : Lin))) (V (.W 0 0 15)) (V (.R 0 15)) ((inp 60)) ((inp 61)) ((inp 62)) ((inp 63)) h0 h1 h2 h3 h4 h5

theorem core15_1061 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨60, [1]⟩ : Lin)) = (inp 60).zeroExtend 32)
    (h1 : env (.m 1 (⟨61, [1]⟩ : Lin)) = (inp 61).zeroExtend 32)
    (h2 : env (.m 1 (⟨62, [1]⟩ : Lin)) = (inp 62).zeroExtend 32)
    (h3 : env (.m 1 (⟨63, [1]⟩ : Lin)) = (inp 63).zeroExtend 32)
    (h4 : V (.W 0 0 15) = bswap (V (.R 0 15)))
    (h5 : V (.R 0 15) = ((((0 : Word) ||| (inp 60).zeroExtend 32 <<< 0) ||| (inp 61).zeroExtend 32 <<< 8) ||| (inp 62).zeroExtend 32 <<< 16) ||| (inp 63).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 15) :=
  shape19 (env (.m 1 (⟨60, [1]⟩ : Lin))) (env (.m 1 (⟨61, [1]⟩ : Lin))) (env (.m 1 (⟨62, [1]⟩ : Lin))) (env (.m 1 (⟨63, [1]⟩ : Lin))) (V (.W 0 0 15)) (V (.R 0 15)) ((inp 60)) ((inp 61)) ((inp 62)) ((inp 63)) h0 h1 h2 h3 h4 h5

theorem core15_1060 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨60, [1]⟩ : Lin)) = (inp 60).zeroExtend 32)
    (h1 : env (.m 1 (⟨61, [1]⟩ : Lin)) = (inp 61).zeroExtend 32)
    (h2 : env (.m 1 (⟨62, [1]⟩ : Lin)) = (inp 62).zeroExtend 32)
    (h3 : env (.m 1 (⟨63, [1]⟩ : Lin)) = (inp 63).zeroExtend 32)
    (h4 : V (.W 0 0 15) = bswap (V (.R 0 15)))
    (h5 : V (.R 0 15) = ((((0 : Word) ||| (inp 60).zeroExtend 32 <<< 0) ||| (inp 61).zeroExtend 32 <<< 8) ||| (inp 62).zeroExtend 32 <<< 16) ||| (inp 63).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 15) :=
  shape19 (env (.m 1 (⟨60, [1]⟩ : Lin))) (env (.m 1 (⟨61, [1]⟩ : Lin))) (env (.m 1 (⟨62, [1]⟩ : Lin))) (env (.m 1 (⟨63, [1]⟩ : Lin))) (V (.W 0 0 15)) (V (.R 0 15)) ((inp 60)) ((inp 61)) ((inp 62)) ((inp 63)) h0 h1 h2 h3 h4 h5

theorem core15_1059 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨124, [1]⟩ : Lin)) = (inp 124).zeroExtend 32)
    (h1 : env (.m 1 (⟨125, [1]⟩ : Lin)) = (inp 125).zeroExtend 32)
    (h2 : env (.m 1 (⟨126, [1]⟩ : Lin)) = (inp 126).zeroExtend 32)
    (h3 : env (.m 1 (⟨127, [1]⟩ : Lin)) = (inp 127).zeroExtend 32)
    (h4 : V (.W 1 0 15) = bswap (V (.R 1 15)))
    (h5 : V (.R 1 15) = ((((0 : Word) ||| (inp 124).zeroExtend 32 <<< 0) ||| (inp 125).zeroExtend 32 <<< 8) ||| (inp 126).zeroExtend 32 <<< 16) ||| (inp 127).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 15) :=
  shape19 (env (.m 1 (⟨124, [1]⟩ : Lin))) (env (.m 1 (⟨125, [1]⟩ : Lin))) (env (.m 1 (⟨126, [1]⟩ : Lin))) (env (.m 1 (⟨127, [1]⟩ : Lin))) (V (.W 1 0 15)) (V (.R 1 15)) ((inp 124)) ((inp 125)) ((inp 126)) ((inp 127)) h0 h1 h2 h3 h4 h5

theorem core15_1058 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨124, [1]⟩ : Lin)) = (inp 124).zeroExtend 32)
    (h1 : env (.m 1 (⟨125, [1]⟩ : Lin)) = (inp 125).zeroExtend 32)
    (h2 : env (.m 1 (⟨126, [1]⟩ : Lin)) = (inp 126).zeroExtend 32)
    (h3 : env (.m 1 (⟨127, [1]⟩ : Lin)) = (inp 127).zeroExtend 32)
    (h4 : V (.W 1 0 15) = bswap (V (.R 1 15)))
    (h5 : V (.R 1 15) = ((((0 : Word) ||| (inp 124).zeroExtend 32 <<< 0) ||| (inp 125).zeroExtend 32 <<< 8) ||| (inp 126).zeroExtend 32 <<< 16) ||| (inp 127).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 15) :=
  shape19 (env (.m 1 (⟨124, [1]⟩ : Lin))) (env (.m 1 (⟨125, [1]⟩ : Lin))) (env (.m 1 (⟨126, [1]⟩ : Lin))) (env (.m 1 (⟨127, [1]⟩ : Lin))) (V (.W 1 0 15)) (V (.R 1 15)) ((inp 124)) ((inp 125)) ((inp 126)) ((inp 127)) h0 h1 h2 h3 h4 h5

theorem core15_1057 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨124, [1]⟩ : Lin)) = (inp 124).zeroExtend 32)
    (h1 : env (.m 1 (⟨125, [1]⟩ : Lin)) = (inp 125).zeroExtend 32)
    (h2 : env (.m 1 (⟨126, [1]⟩ : Lin)) = (inp 126).zeroExtend 32)
    (h3 : env (.m 1 (⟨127, [1]⟩ : Lin)) = (inp 127).zeroExtend 32)
    (h4 : V (.W 1 0 15) = bswap (V (.R 1 15)))
    (h5 : V (.R 1 15) = ((((0 : Word) ||| (inp 124).zeroExtend 32 <<< 0) ||| (inp 125).zeroExtend 32 <<< 8) ||| (inp 126).zeroExtend 32 <<< 16) ||| (inp 127).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 15) :=
  shape19 (env (.m 1 (⟨124, [1]⟩ : Lin))) (env (.m 1 (⟨125, [1]⟩ : Lin))) (env (.m 1 (⟨126, [1]⟩ : Lin))) (env (.m 1 (⟨127, [1]⟩ : Lin))) (V (.W 1 0 15)) (V (.R 1 15)) ((inp 124)) ((inp 125)) ((inp 126)) ((inp 127)) h0 h1 h2 h3 h4 h5

theorem core15_1056 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨124, [1]⟩ : Lin)) = (inp 124).zeroExtend 32)
    (h1 : env (.m 1 (⟨125, [1]⟩ : Lin)) = (inp 125).zeroExtend 32)
    (h2 : env (.m 1 (⟨126, [1]⟩ : Lin)) = (inp 126).zeroExtend 32)
    (h3 : env (.m 1 (⟨127, [1]⟩ : Lin)) = (inp 127).zeroExtend 32)
    (h4 : V (.W 1 0 15) = bswap (V (.R 1 15)))
    (h5 : V (.R 1 15) = ((((0 : Word) ||| (inp 124).zeroExtend 32 <<< 0) ||| (inp 125).zeroExtend 32 <<< 8) ||| (inp 126).zeroExtend 32 <<< 16) ||| (inp 127).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 15) :=
  shape19 (env (.m 1 (⟨124, [1]⟩ : Lin))) (env (.m 1 (⟨125, [1]⟩ : Lin))) (env (.m 1 (⟨126, [1]⟩ : Lin))) (env (.m 1 (⟨127, [1]⟩ : Lin))) (V (.W 1 0 15)) (V (.R 1 15)) ((inp 124)) ((inp 125)) ((inp 126)) ((inp 127)) h0 h1 h2 h3 h4 h5

theorem core15_1055 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨188, [1]⟩ : Lin)) = (inp 188).zeroExtend 32)
    (h1 : env (.m 1 (⟨189, [1]⟩ : Lin)) = (inp 189).zeroExtend 32)
    (h2 : env (.m 1 (⟨190, [1]⟩ : Lin)) = (inp 190).zeroExtend 32)
    (h3 : env (.m 1 (⟨191, [1]⟩ : Lin)) = (inp 191).zeroExtend 32)
    (h4 : V (.W 2 0 15) = bswap (V (.R 2 15)))
    (h5 : V (.R 2 15) = ((((0 : Word) ||| (inp 188).zeroExtend 32 <<< 0) ||| (inp 189).zeroExtend 32 <<< 8) ||| (inp 190).zeroExtend 32 <<< 16) ||| (inp 191).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 15) :=
  shape19 (env (.m 1 (⟨188, [1]⟩ : Lin))) (env (.m 1 (⟨189, [1]⟩ : Lin))) (env (.m 1 (⟨190, [1]⟩ : Lin))) (env (.m 1 (⟨191, [1]⟩ : Lin))) (V (.W 2 0 15)) (V (.R 2 15)) ((inp 188)) ((inp 189)) ((inp 190)) ((inp 191)) h0 h1 h2 h3 h4 h5

theorem core15_1054 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨188, [1]⟩ : Lin)) = (inp 188).zeroExtend 32)
    (h1 : env (.m 1 (⟨189, [1]⟩ : Lin)) = (inp 189).zeroExtend 32)
    (h2 : env (.m 1 (⟨190, [1]⟩ : Lin)) = (inp 190).zeroExtend 32)
    (h3 : env (.m 1 (⟨191, [1]⟩ : Lin)) = (inp 191).zeroExtend 32)
    (h4 : V (.W 2 0 15) = bswap (V (.R 2 15)))
    (h5 : V (.R 2 15) = ((((0 : Word) ||| (inp 188).zeroExtend 32 <<< 0) ||| (inp 189).zeroExtend 32 <<< 8) ||| (inp 190).zeroExtend 32 <<< 16) ||| (inp 191).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 15) :=
  shape19 (env (.m 1 (⟨188, [1]⟩ : Lin))) (env (.m 1 (⟨189, [1]⟩ : Lin))) (env (.m 1 (⟨190, [1]⟩ : Lin))) (env (.m 1 (⟨191, [1]⟩ : Lin))) (V (.W 2 0 15)) (V (.R 2 15)) ((inp 188)) ((inp 189)) ((inp 190)) ((inp 191)) h0 h1 h2 h3 h4 h5

theorem core15_1053 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨188, [1]⟩ : Lin)) = (inp 188).zeroExtend 32)
    (h1 : env (.m 1 (⟨189, [1]⟩ : Lin)) = (inp 189).zeroExtend 32)
    (h2 : env (.m 1 (⟨190, [1]⟩ : Lin)) = (inp 190).zeroExtend 32)
    (h3 : env (.m 1 (⟨191, [1]⟩ : Lin)) = (inp 191).zeroExtend 32)
    (h4 : V (.W 2 0 15) = bswap (V (.R 2 15)))
    (h5 : V (.R 2 15) = ((((0 : Word) ||| (inp 188).zeroExtend 32 <<< 0) ||| (inp 189).zeroExtend 32 <<< 8) ||| (inp 190).zeroExtend 32 <<< 16) ||| (inp 191).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 15) :=
  shape19 (env (.m 1 (⟨188, [1]⟩ : Lin))) (env (.m 1 (⟨189, [1]⟩ : Lin))) (env (.m 1 (⟨190, [1]⟩ : Lin))) (env (.m 1 (⟨191, [1]⟩ : Lin))) (V (.W 2 0 15)) (V (.R 2 15)) ((inp 188)) ((inp 189)) ((inp 190)) ((inp 191)) h0 h1 h2 h3 h4 h5

theorem core15_1052 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨188, [1]⟩ : Lin)) = (inp 188).zeroExtend 32)
    (h1 : env (.m 1 (⟨189, [1]⟩ : Lin)) = (inp 189).zeroExtend 32)
    (h2 : env (.m 1 (⟨190, [1]⟩ : Lin)) = (inp 190).zeroExtend 32)
    (h3 : env (.m 1 (⟨191, [1]⟩ : Lin)) = (inp 191).zeroExtend 32)
    (h4 : V (.W 2 0 15) = bswap (V (.R 2 15)))
    (h5 : V (.R 2 15) = ((((0 : Word) ||| (inp 188).zeroExtend 32 <<< 0) ||| (inp 189).zeroExtend 32 <<< 8) ||| (inp 190).zeroExtend 32 <<< 16) ||| (inp 191).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 15) :=
  shape19 (env (.m 1 (⟨188, [1]⟩ : Lin))) (env (.m 1 (⟨189, [1]⟩ : Lin))) (env (.m 1 (⟨190, [1]⟩ : Lin))) (env (.m 1 (⟨191, [1]⟩ : Lin))) (V (.W 2 0 15)) (V (.R 2 15)) ((inp 188)) ((inp 189)) ((inp 190)) ((inp 191)) h0 h1 h2 h3 h4 h5

theorem core15_1051 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨252, [1]⟩ : Lin)) = (inp 252).zeroExtend 32)
    (h1 : env (.m 1 (⟨253, [1]⟩ : Lin)) = (inp 253).zeroExtend 32)
    (h2 : env (.m 1 (⟨254, [1]⟩ : Lin)) = (inp 254).zeroExtend 32)
    (h3 : env (.m 1 (⟨255, [1]⟩ : Lin)) = (inp 255).zeroExtend 32)
    (h4 : V (.W 3 0 15) = bswap (V (.R 3 15)))
    (h5 : V (.R 3 15) = ((((0 : Word) ||| (inp 252).zeroExtend 32 <<< 0) ||| (inp 253).zeroExtend 32 <<< 8) ||| (inp 254).zeroExtend 32 <<< 16) ||| (inp 255).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 15) :=
  shape19 (env (.m 1 (⟨252, [1]⟩ : Lin))) (env (.m 1 (⟨253, [1]⟩ : Lin))) (env (.m 1 (⟨254, [1]⟩ : Lin))) (env (.m 1 (⟨255, [1]⟩ : Lin))) (V (.W 3 0 15)) (V (.R 3 15)) ((inp 252)) ((inp 253)) ((inp 254)) ((inp 255)) h0 h1 h2 h3 h4 h5

theorem core15_1050 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨252, [1]⟩ : Lin)) = (inp 252).zeroExtend 32)
    (h1 : env (.m 1 (⟨253, [1]⟩ : Lin)) = (inp 253).zeroExtend 32)
    (h2 : env (.m 1 (⟨254, [1]⟩ : Lin)) = (inp 254).zeroExtend 32)
    (h3 : env (.m 1 (⟨255, [1]⟩ : Lin)) = (inp 255).zeroExtend 32)
    (h4 : V (.W 3 0 15) = bswap (V (.R 3 15)))
    (h5 : V (.R 3 15) = ((((0 : Word) ||| (inp 252).zeroExtend 32 <<< 0) ||| (inp 253).zeroExtend 32 <<< 8) ||| (inp 254).zeroExtend 32 <<< 16) ||| (inp 255).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 15) :=
  shape19 (env (.m 1 (⟨252, [1]⟩ : Lin))) (env (.m 1 (⟨253, [1]⟩ : Lin))) (env (.m 1 (⟨254, [1]⟩ : Lin))) (env (.m 1 (⟨255, [1]⟩ : Lin))) (V (.W 3 0 15)) (V (.R 3 15)) ((inp 252)) ((inp 253)) ((inp 254)) ((inp 255)) h0 h1 h2 h3 h4 h5

theorem core15_1049 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨252, [1]⟩ : Lin)) = (inp 252).zeroExtend 32)
    (h1 : env (.m 1 (⟨253, [1]⟩ : Lin)) = (inp 253).zeroExtend 32)
    (h2 : env (.m 1 (⟨254, [1]⟩ : Lin)) = (inp 254).zeroExtend 32)
    (h3 : env (.m 1 (⟨255, [1]⟩ : Lin)) = (inp 255).zeroExtend 32)
    (h4 : V (.W 3 0 15) = bswap (V (.R 3 15)))
    (h5 : V (.R 3 15) = ((((0 : Word) ||| (inp 252).zeroExtend 32 <<< 0) ||| (inp 253).zeroExtend 32 <<< 8) ||| (inp 254).zeroExtend 32 <<< 16) ||| (inp 255).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 15) :=
  shape19 (env (.m 1 (⟨252, [1]⟩ : Lin))) (env (.m 1 (⟨253, [1]⟩ : Lin))) (env (.m 1 (⟨254, [1]⟩ : Lin))) (env (.m 1 (⟨255, [1]⟩ : Lin))) (V (.W 3 0 15)) (V (.R 3 15)) ((inp 252)) ((inp 253)) ((inp 254)) ((inp 255)) h0 h1 h2 h3 h4 h5

theorem core15_1048 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨252, [1]⟩ : Lin)) = (inp 252).zeroExtend 32)
    (h1 : env (.m 1 (⟨253, [1]⟩ : Lin)) = (inp 253).zeroExtend 32)
    (h2 : env (.m 1 (⟨254, [1]⟩ : Lin)) = (inp 254).zeroExtend 32)
    (h3 : env (.m 1 (⟨255, [1]⟩ : Lin)) = (inp 255).zeroExtend 32)
    (h4 : V (.W 3 0 15) = bswap (V (.R 3 15)))
    (h5 : V (.R 3 15) = ((((0 : Word) ||| (inp 252).zeroExtend 32 <<< 0) ||| (inp 253).zeroExtend 32 <<< 8) ||| (inp 254).zeroExtend 32 <<< 16) ||| (inp 255).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 15) :=
  shape19 (env (.m 1 (⟨252, [1]⟩ : Lin))) (env (.m 1 (⟨253, [1]⟩ : Lin))) (env (.m 1 (⟨254, [1]⟩ : Lin))) (env (.m 1 (⟨255, [1]⟩ : Lin))) (V (.W 3 0 15)) (V (.R 3 15)) ((inp 252)) ((inp 253)) ((inp 254)) ((inp 255)) h0 h1 h2 h3 h4 h5

theorem core15_1047 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨316, [1]⟩ : Lin)) = (inp 316).zeroExtend 32)
    (h1 : env (.m 1 (⟨317, [1]⟩ : Lin)) = (inp 317).zeroExtend 32)
    (h2 : env (.m 1 (⟨318, [1]⟩ : Lin)) = (inp 318).zeroExtend 32)
    (h3 : env (.m 1 (⟨319, [1]⟩ : Lin)) = (inp 319).zeroExtend 32)
    (h4 : V (.W 4 0 15) = bswap (V (.R 4 15)))
    (h5 : V (.R 4 15) = ((((0 : Word) ||| (inp 316).zeroExtend 32 <<< 0) ||| (inp 317).zeroExtend 32 <<< 8) ||| (inp 318).zeroExtend 32 <<< 16) ||| (inp 319).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 15) :=
  shape19 (env (.m 1 (⟨316, [1]⟩ : Lin))) (env (.m 1 (⟨317, [1]⟩ : Lin))) (env (.m 1 (⟨318, [1]⟩ : Lin))) (env (.m 1 (⟨319, [1]⟩ : Lin))) (V (.W 4 0 15)) (V (.R 4 15)) ((inp 316)) ((inp 317)) ((inp 318)) ((inp 319)) h0 h1 h2 h3 h4 h5

theorem core15_1046 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨316, [1]⟩ : Lin)) = (inp 316).zeroExtend 32)
    (h1 : env (.m 1 (⟨317, [1]⟩ : Lin)) = (inp 317).zeroExtend 32)
    (h2 : env (.m 1 (⟨318, [1]⟩ : Lin)) = (inp 318).zeroExtend 32)
    (h3 : env (.m 1 (⟨319, [1]⟩ : Lin)) = (inp 319).zeroExtend 32)
    (h4 : V (.W 4 0 15) = bswap (V (.R 4 15)))
    (h5 : V (.R 4 15) = ((((0 : Word) ||| (inp 316).zeroExtend 32 <<< 0) ||| (inp 317).zeroExtend 32 <<< 8) ||| (inp 318).zeroExtend 32 <<< 16) ||| (inp 319).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 15) :=
  shape19 (env (.m 1 (⟨316, [1]⟩ : Lin))) (env (.m 1 (⟨317, [1]⟩ : Lin))) (env (.m 1 (⟨318, [1]⟩ : Lin))) (env (.m 1 (⟨319, [1]⟩ : Lin))) (V (.W 4 0 15)) (V (.R 4 15)) ((inp 316)) ((inp 317)) ((inp 318)) ((inp 319)) h0 h1 h2 h3 h4 h5

theorem core15_1045 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨316, [1]⟩ : Lin)) = (inp 316).zeroExtend 32)
    (h1 : env (.m 1 (⟨317, [1]⟩ : Lin)) = (inp 317).zeroExtend 32)
    (h2 : env (.m 1 (⟨318, [1]⟩ : Lin)) = (inp 318).zeroExtend 32)
    (h3 : env (.m 1 (⟨319, [1]⟩ : Lin)) = (inp 319).zeroExtend 32)
    (h4 : V (.W 4 0 15) = bswap (V (.R 4 15)))
    (h5 : V (.R 4 15) = ((((0 : Word) ||| (inp 316).zeroExtend 32 <<< 0) ||| (inp 317).zeroExtend 32 <<< 8) ||| (inp 318).zeroExtend 32 <<< 16) ||| (inp 319).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 15) :=
  shape19 (env (.m 1 (⟨316, [1]⟩ : Lin))) (env (.m 1 (⟨317, [1]⟩ : Lin))) (env (.m 1 (⟨318, [1]⟩ : Lin))) (env (.m 1 (⟨319, [1]⟩ : Lin))) (V (.W 4 0 15)) (V (.R 4 15)) ((inp 316)) ((inp 317)) ((inp 318)) ((inp 319)) h0 h1 h2 h3 h4 h5

theorem core15_1044 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨316, [1]⟩ : Lin)) = (inp 316).zeroExtend 32)
    (h1 : env (.m 1 (⟨317, [1]⟩ : Lin)) = (inp 317).zeroExtend 32)
    (h2 : env (.m 1 (⟨318, [1]⟩ : Lin)) = (inp 318).zeroExtend 32)
    (h3 : env (.m 1 (⟨319, [1]⟩ : Lin)) = (inp 319).zeroExtend 32)
    (h4 : V (.W 4 0 15) = bswap (V (.R 4 15)))
    (h5 : V (.R 4 15) = ((((0 : Word) ||| (inp 316).zeroExtend 32 <<< 0) ||| (inp 317).zeroExtend 32 <<< 8) ||| (inp 318).zeroExtend 32 <<< 16) ||| (inp 319).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨316, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨317, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨318, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨319, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 15) :=
  shape19 (env (.m 1 (⟨316, [1]⟩ : Lin))) (env (.m 1 (⟨317, [1]⟩ : Lin))) (env (.m 1 (⟨318, [1]⟩ : Lin))) (env (.m 1 (⟨319, [1]⟩ : Lin))) (V (.W 4 0 15)) (V (.R 4 15)) ((inp 316)) ((inp 317)) ((inp 318)) ((inp 319)) h0 h1 h2 h3 h4 h5

theorem core15_1043 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨380, [1]⟩ : Lin)) = (inp 380).zeroExtend 32)
    (h1 : env (.m 1 (⟨381, [1]⟩ : Lin)) = (inp 381).zeroExtend 32)
    (h2 : env (.m 1 (⟨382, [1]⟩ : Lin)) = (inp 382).zeroExtend 32)
    (h3 : env (.m 1 (⟨383, [1]⟩ : Lin)) = (inp 383).zeroExtend 32)
    (h4 : V (.W 5 0 15) = bswap (V (.R 5 15)))
    (h5 : V (.R 5 15) = ((((0 : Word) ||| (inp 380).zeroExtend 32 <<< 0) ||| (inp 381).zeroExtend 32 <<< 8) ||| (inp 382).zeroExtend 32 <<< 16) ||| (inp 383).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 15) :=
  shape19 (env (.m 1 (⟨380, [1]⟩ : Lin))) (env (.m 1 (⟨381, [1]⟩ : Lin))) (env (.m 1 (⟨382, [1]⟩ : Lin))) (env (.m 1 (⟨383, [1]⟩ : Lin))) (V (.W 5 0 15)) (V (.R 5 15)) ((inp 380)) ((inp 381)) ((inp 382)) ((inp 383)) h0 h1 h2 h3 h4 h5

theorem core15_1042 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨380, [1]⟩ : Lin)) = (inp 380).zeroExtend 32)
    (h1 : env (.m 1 (⟨381, [1]⟩ : Lin)) = (inp 381).zeroExtend 32)
    (h2 : env (.m 1 (⟨382, [1]⟩ : Lin)) = (inp 382).zeroExtend 32)
    (h3 : env (.m 1 (⟨383, [1]⟩ : Lin)) = (inp 383).zeroExtend 32)
    (h4 : V (.W 5 0 15) = bswap (V (.R 5 15)))
    (h5 : V (.R 5 15) = ((((0 : Word) ||| (inp 380).zeroExtend 32 <<< 0) ||| (inp 381).zeroExtend 32 <<< 8) ||| (inp 382).zeroExtend 32 <<< 16) ||| (inp 383).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 15) :=
  shape19 (env (.m 1 (⟨380, [1]⟩ : Lin))) (env (.m 1 (⟨381, [1]⟩ : Lin))) (env (.m 1 (⟨382, [1]⟩ : Lin))) (env (.m 1 (⟨383, [1]⟩ : Lin))) (V (.W 5 0 15)) (V (.R 5 15)) ((inp 380)) ((inp 381)) ((inp 382)) ((inp 383)) h0 h1 h2 h3 h4 h5

theorem core15_1041 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨380, [1]⟩ : Lin)) = (inp 380).zeroExtend 32)
    (h1 : env (.m 1 (⟨381, [1]⟩ : Lin)) = (inp 381).zeroExtend 32)
    (h2 : env (.m 1 (⟨382, [1]⟩ : Lin)) = (inp 382).zeroExtend 32)
    (h3 : env (.m 1 (⟨383, [1]⟩ : Lin)) = (inp 383).zeroExtend 32)
    (h4 : V (.W 5 0 15) = bswap (V (.R 5 15)))
    (h5 : V (.R 5 15) = ((((0 : Word) ||| (inp 380).zeroExtend 32 <<< 0) ||| (inp 381).zeroExtend 32 <<< 8) ||| (inp 382).zeroExtend 32 <<< 16) ||| (inp 383).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 15) :=
  shape19 (env (.m 1 (⟨380, [1]⟩ : Lin))) (env (.m 1 (⟨381, [1]⟩ : Lin))) (env (.m 1 (⟨382, [1]⟩ : Lin))) (env (.m 1 (⟨383, [1]⟩ : Lin))) (V (.W 5 0 15)) (V (.R 5 15)) ((inp 380)) ((inp 381)) ((inp 382)) ((inp 383)) h0 h1 h2 h3 h4 h5

theorem core15_1040 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨380, [1]⟩ : Lin)) = (inp 380).zeroExtend 32)
    (h1 : env (.m 1 (⟨381, [1]⟩ : Lin)) = (inp 381).zeroExtend 32)
    (h2 : env (.m 1 (⟨382, [1]⟩ : Lin)) = (inp 382).zeroExtend 32)
    (h3 : env (.m 1 (⟨383, [1]⟩ : Lin)) = (inp 383).zeroExtend 32)
    (h4 : V (.W 5 0 15) = bswap (V (.R 5 15)))
    (h5 : V (.R 5 15) = ((((0 : Word) ||| (inp 380).zeroExtend 32 <<< 0) ||| (inp 381).zeroExtend 32 <<< 8) ||| (inp 382).zeroExtend 32 <<< 16) ||| (inp 383).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨380, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨381, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨382, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨383, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 15) :=
  shape19 (env (.m 1 (⟨380, [1]⟩ : Lin))) (env (.m 1 (⟨381, [1]⟩ : Lin))) (env (.m 1 (⟨382, [1]⟩ : Lin))) (env (.m 1 (⟨383, [1]⟩ : Lin))) (V (.W 5 0 15)) (V (.R 5 15)) ((inp 380)) ((inp 381)) ((inp 382)) ((inp 383)) h0 h1 h2 h3 h4 h5

theorem core15_1039 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨444, [1]⟩ : Lin)) = (inp 444).zeroExtend 32)
    (h1 : env (.m 1 (⟨445, [1]⟩ : Lin)) = (inp 445).zeroExtend 32)
    (h2 : env (.m 1 (⟨446, [1]⟩ : Lin)) = (inp 446).zeroExtend 32)
    (h3 : env (.m 1 (⟨447, [1]⟩ : Lin)) = (inp 447).zeroExtend 32)
    (h4 : V (.W 6 0 15) = bswap (V (.R 6 15)))
    (h5 : V (.R 6 15) = ((((0 : Word) ||| (inp 444).zeroExtend 32 <<< 0) ||| (inp 445).zeroExtend 32 <<< 8) ||| (inp 446).zeroExtend 32 <<< 16) ||| (inp 447).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 15) :=
  shape19 (env (.m 1 (⟨444, [1]⟩ : Lin))) (env (.m 1 (⟨445, [1]⟩ : Lin))) (env (.m 1 (⟨446, [1]⟩ : Lin))) (env (.m 1 (⟨447, [1]⟩ : Lin))) (V (.W 6 0 15)) (V (.R 6 15)) ((inp 444)) ((inp 445)) ((inp 446)) ((inp 447)) h0 h1 h2 h3 h4 h5

theorem core15_1038 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨444, [1]⟩ : Lin)) = (inp 444).zeroExtend 32)
    (h1 : env (.m 1 (⟨445, [1]⟩ : Lin)) = (inp 445).zeroExtend 32)
    (h2 : env (.m 1 (⟨446, [1]⟩ : Lin)) = (inp 446).zeroExtend 32)
    (h3 : env (.m 1 (⟨447, [1]⟩ : Lin)) = (inp 447).zeroExtend 32)
    (h4 : V (.W 6 0 15) = bswap (V (.R 6 15)))
    (h5 : V (.R 6 15) = ((((0 : Word) ||| (inp 444).zeroExtend 32 <<< 0) ||| (inp 445).zeroExtend 32 <<< 8) ||| (inp 446).zeroExtend 32 <<< 16) ||| (inp 447).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 15) :=
  shape19 (env (.m 1 (⟨444, [1]⟩ : Lin))) (env (.m 1 (⟨445, [1]⟩ : Lin))) (env (.m 1 (⟨446, [1]⟩ : Lin))) (env (.m 1 (⟨447, [1]⟩ : Lin))) (V (.W 6 0 15)) (V (.R 6 15)) ((inp 444)) ((inp 445)) ((inp 446)) ((inp 447)) h0 h1 h2 h3 h4 h5

theorem core15_1037 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨444, [1]⟩ : Lin)) = (inp 444).zeroExtend 32)
    (h1 : env (.m 1 (⟨445, [1]⟩ : Lin)) = (inp 445).zeroExtend 32)
    (h2 : env (.m 1 (⟨446, [1]⟩ : Lin)) = (inp 446).zeroExtend 32)
    (h3 : env (.m 1 (⟨447, [1]⟩ : Lin)) = (inp 447).zeroExtend 32)
    (h4 : V (.W 6 0 15) = bswap (V (.R 6 15)))
    (h5 : V (.R 6 15) = ((((0 : Word) ||| (inp 444).zeroExtend 32 <<< 0) ||| (inp 445).zeroExtend 32 <<< 8) ||| (inp 446).zeroExtend 32 <<< 16) ||| (inp 447).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 15) :=
  shape19 (env (.m 1 (⟨444, [1]⟩ : Lin))) (env (.m 1 (⟨445, [1]⟩ : Lin))) (env (.m 1 (⟨446, [1]⟩ : Lin))) (env (.m 1 (⟨447, [1]⟩ : Lin))) (V (.W 6 0 15)) (V (.R 6 15)) ((inp 444)) ((inp 445)) ((inp 446)) ((inp 447)) h0 h1 h2 h3 h4 h5

theorem core15_1036 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨444, [1]⟩ : Lin)) = (inp 444).zeroExtend 32)
    (h1 : env (.m 1 (⟨445, [1]⟩ : Lin)) = (inp 445).zeroExtend 32)
    (h2 : env (.m 1 (⟨446, [1]⟩ : Lin)) = (inp 446).zeroExtend 32)
    (h3 : env (.m 1 (⟨447, [1]⟩ : Lin)) = (inp 447).zeroExtend 32)
    (h4 : V (.W 6 0 15) = bswap (V (.R 6 15)))
    (h5 : V (.R 6 15) = ((((0 : Word) ||| (inp 444).zeroExtend 32 <<< 0) ||| (inp 445).zeroExtend 32 <<< 8) ||| (inp 446).zeroExtend 32 <<< 16) ||| (inp 447).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨444, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨445, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨446, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨447, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 15) :=
  shape19 (env (.m 1 (⟨444, [1]⟩ : Lin))) (env (.m 1 (⟨445, [1]⟩ : Lin))) (env (.m 1 (⟨446, [1]⟩ : Lin))) (env (.m 1 (⟨447, [1]⟩ : Lin))) (V (.W 6 0 15)) (V (.R 6 15)) ((inp 444)) ((inp 445)) ((inp 446)) ((inp 447)) h0 h1 h2 h3 h4 h5

theorem core15_1035 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨508, [1]⟩ : Lin)) = (inp 508).zeroExtend 32)
    (h1 : env (.m 1 (⟨509, [1]⟩ : Lin)) = (inp 509).zeroExtend 32)
    (h2 : env (.m 1 (⟨510, [1]⟩ : Lin)) = (inp 510).zeroExtend 32)
    (h3 : env (.m 1 (⟨511, [1]⟩ : Lin)) = (inp 511).zeroExtend 32)
    (h4 : V (.W 7 0 15) = bswap (V (.R 7 15)))
    (h5 : V (.R 7 15) = ((((0 : Word) ||| (inp 508).zeroExtend 32 <<< 0) ||| (inp 509).zeroExtend 32 <<< 8) ||| (inp 510).zeroExtend 32 <<< 16) ||| (inp 511).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 15) :=
  shape19 (env (.m 1 (⟨508, [1]⟩ : Lin))) (env (.m 1 (⟨509, [1]⟩ : Lin))) (env (.m 1 (⟨510, [1]⟩ : Lin))) (env (.m 1 (⟨511, [1]⟩ : Lin))) (V (.W 7 0 15)) (V (.R 7 15)) ((inp 508)) ((inp 509)) ((inp 510)) ((inp 511)) h0 h1 h2 h3 h4 h5

theorem core15_1034 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨508, [1]⟩ : Lin)) = (inp 508).zeroExtend 32)
    (h1 : env (.m 1 (⟨509, [1]⟩ : Lin)) = (inp 509).zeroExtend 32)
    (h2 : env (.m 1 (⟨510, [1]⟩ : Lin)) = (inp 510).zeroExtend 32)
    (h3 : env (.m 1 (⟨511, [1]⟩ : Lin)) = (inp 511).zeroExtend 32)
    (h4 : V (.W 7 0 15) = bswap (V (.R 7 15)))
    (h5 : V (.R 7 15) = ((((0 : Word) ||| (inp 508).zeroExtend 32 <<< 0) ||| (inp 509).zeroExtend 32 <<< 8) ||| (inp 510).zeroExtend 32 <<< 16) ||| (inp 511).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 15) :=
  shape19 (env (.m 1 (⟨508, [1]⟩ : Lin))) (env (.m 1 (⟨509, [1]⟩ : Lin))) (env (.m 1 (⟨510, [1]⟩ : Lin))) (env (.m 1 (⟨511, [1]⟩ : Lin))) (V (.W 7 0 15)) (V (.R 7 15)) ((inp 508)) ((inp 509)) ((inp 510)) ((inp 511)) h0 h1 h2 h3 h4 h5

theorem core15_1033 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨508, [1]⟩ : Lin)) = (inp 508).zeroExtend 32)
    (h1 : env (.m 1 (⟨509, [1]⟩ : Lin)) = (inp 509).zeroExtend 32)
    (h2 : env (.m 1 (⟨510, [1]⟩ : Lin)) = (inp 510).zeroExtend 32)
    (h3 : env (.m 1 (⟨511, [1]⟩ : Lin)) = (inp 511).zeroExtend 32)
    (h4 : V (.W 7 0 15) = bswap (V (.R 7 15)))
    (h5 : V (.R 7 15) = ((((0 : Word) ||| (inp 508).zeroExtend 32 <<< 0) ||| (inp 509).zeroExtend 32 <<< 8) ||| (inp 510).zeroExtend 32 <<< 16) ||| (inp 511).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 15) :=
  shape19 (env (.m 1 (⟨508, [1]⟩ : Lin))) (env (.m 1 (⟨509, [1]⟩ : Lin))) (env (.m 1 (⟨510, [1]⟩ : Lin))) (env (.m 1 (⟨511, [1]⟩ : Lin))) (V (.W 7 0 15)) (V (.R 7 15)) ((inp 508)) ((inp 509)) ((inp 510)) ((inp 511)) h0 h1 h2 h3 h4 h5

theorem core15_1032 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨508, [1]⟩ : Lin)) = (inp 508).zeroExtend 32)
    (h1 : env (.m 1 (⟨509, [1]⟩ : Lin)) = (inp 509).zeroExtend 32)
    (h2 : env (.m 1 (⟨510, [1]⟩ : Lin)) = (inp 510).zeroExtend 32)
    (h3 : env (.m 1 (⟨511, [1]⟩ : Lin)) = (inp 511).zeroExtend 32)
    (h4 : V (.W 7 0 15) = bswap (V (.R 7 15)))
    (h5 : V (.R 7 15) = ((((0 : Word) ||| (inp 508).zeroExtend 32 <<< 0) ||| (inp 509).zeroExtend 32 <<< 8) ||| (inp 510).zeroExtend 32 <<< 16) ||| (inp 511).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨508, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨509, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨510, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨511, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 15) :=
  shape19 (env (.m 1 (⟨508, [1]⟩ : Lin))) (env (.m 1 (⟨509, [1]⟩ : Lin))) (env (.m 1 (⟨510, [1]⟩ : Lin))) (env (.m 1 (⟨511, [1]⟩ : Lin))) (V (.W 7 0 15)) (V (.R 7 15)) ((inp 508)) ((inp 509)) ((inp 510)) ((inp 511)) h0 h1 h2 h3 h4 h5

theorem core15_1031 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape19 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core15_1030 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape19 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core15_1029 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape19 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core15_1028 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape19 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core15_1027 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape19 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core15_1026 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape19 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core15_1025 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape19 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core15_1024 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape19 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core15_1023 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape19 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core15_1022 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape19 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core15_1021 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape19 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core15_1020 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape19 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core15_1019 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape19 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core15_1018 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape19 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core15_1017 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape19 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core15_1016 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape19 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core15_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨288, [1]⟩ : Lin)) = (inp 288).zeroExtend 32)
    (h1 : env (.m 1 (⟨289, [1]⟩ : Lin)) = (inp 289).zeroExtend 32)
    (h2 : env (.m 1 (⟨290, [1]⟩ : Lin)) = (inp 290).zeroExtend 32)
    (h3 : env (.m 1 (⟨291, [1]⟩ : Lin)) = (inp 291).zeroExtend 32)
    (h4 : V (.W 4 0 8) = bswap (V (.R 4 8)))
    (h5 : V (.R 4 8) = ((((0 : Word) ||| (inp 288).zeroExtend 32 <<< 0) ||| (inp 289).zeroExtend 32 <<< 8) ||| (inp 290).zeroExtend 32 <<< 16) ||| (inp 291).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 8) :=
  shape19 (env (.m 1 (⟨288, [1]⟩ : Lin))) (env (.m 1 (⟨289, [1]⟩ : Lin))) (env (.m 1 (⟨290, [1]⟩ : Lin))) (env (.m 1 (⟨291, [1]⟩ : Lin))) (V (.W 4 0 8)) (V (.R 4 8)) ((inp 288)) ((inp 289)) ((inp 290)) ((inp 291)) h0 h1 h2 h3 h4 h5

theorem core15_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨288, [1]⟩ : Lin)) = (inp 288).zeroExtend 32)
    (h1 : env (.m 1 (⟨289, [1]⟩ : Lin)) = (inp 289).zeroExtend 32)
    (h2 : env (.m 1 (⟨290, [1]⟩ : Lin)) = (inp 290).zeroExtend 32)
    (h3 : env (.m 1 (⟨291, [1]⟩ : Lin)) = (inp 291).zeroExtend 32)
    (h4 : V (.W 4 0 8) = bswap (V (.R 4 8)))
    (h5 : V (.R 4 8) = ((((0 : Word) ||| (inp 288).zeroExtend 32 <<< 0) ||| (inp 289).zeroExtend 32 <<< 8) ||| (inp 290).zeroExtend 32 <<< 16) ||| (inp 291).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 8) :=
  shape19 (env (.m 1 (⟨288, [1]⟩ : Lin))) (env (.m 1 (⟨289, [1]⟩ : Lin))) (env (.m 1 (⟨290, [1]⟩ : Lin))) (env (.m 1 (⟨291, [1]⟩ : Lin))) (V (.W 4 0 8)) (V (.R 4 8)) ((inp 288)) ((inp 289)) ((inp 290)) ((inp 291)) h0 h1 h2 h3 h4 h5

theorem core15_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨288, [1]⟩ : Lin)) = (inp 288).zeroExtend 32)
    (h1 : env (.m 1 (⟨289, [1]⟩ : Lin)) = (inp 289).zeroExtend 32)
    (h2 : env (.m 1 (⟨290, [1]⟩ : Lin)) = (inp 290).zeroExtend 32)
    (h3 : env (.m 1 (⟨291, [1]⟩ : Lin)) = (inp 291).zeroExtend 32)
    (h4 : V (.W 4 0 8) = bswap (V (.R 4 8)))
    (h5 : V (.R 4 8) = ((((0 : Word) ||| (inp 288).zeroExtend 32 <<< 0) ||| (inp 289).zeroExtend 32 <<< 8) ||| (inp 290).zeroExtend 32 <<< 16) ||| (inp 291).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 8) :=
  shape19 (env (.m 1 (⟨288, [1]⟩ : Lin))) (env (.m 1 (⟨289, [1]⟩ : Lin))) (env (.m 1 (⟨290, [1]⟩ : Lin))) (env (.m 1 (⟨291, [1]⟩ : Lin))) (V (.W 4 0 8)) (V (.R 4 8)) ((inp 288)) ((inp 289)) ((inp 290)) ((inp 291)) h0 h1 h2 h3 h4 h5

theorem core15_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨288, [1]⟩ : Lin)) = (inp 288).zeroExtend 32)
    (h1 : env (.m 1 (⟨289, [1]⟩ : Lin)) = (inp 289).zeroExtend 32)
    (h2 : env (.m 1 (⟨290, [1]⟩ : Lin)) = (inp 290).zeroExtend 32)
    (h3 : env (.m 1 (⟨291, [1]⟩ : Lin)) = (inp 291).zeroExtend 32)
    (h4 : V (.W 4 0 8) = bswap (V (.R 4 8)))
    (h5 : V (.R 4 8) = ((((0 : Word) ||| (inp 288).zeroExtend 32 <<< 0) ||| (inp 289).zeroExtend 32 <<< 8) ||| (inp 290).zeroExtend 32 <<< 16) ||| (inp 291).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 8) :=
  shape19 (env (.m 1 (⟨288, [1]⟩ : Lin))) (env (.m 1 (⟨289, [1]⟩ : Lin))) (env (.m 1 (⟨290, [1]⟩ : Lin))) (env (.m 1 (⟨291, [1]⟩ : Lin))) (V (.W 4 0 8)) (V (.R 4 8)) ((inp 288)) ((inp 289)) ((inp 290)) ((inp 291)) h0 h1 h2 h3 h4 h5

theorem core15_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨352, [1]⟩ : Lin)) = (inp 352).zeroExtend 32)
    (h1 : env (.m 1 (⟨353, [1]⟩ : Lin)) = (inp 353).zeroExtend 32)
    (h2 : env (.m 1 (⟨354, [1]⟩ : Lin)) = (inp 354).zeroExtend 32)
    (h3 : env (.m 1 (⟨355, [1]⟩ : Lin)) = (inp 355).zeroExtend 32)
    (h4 : V (.W 5 0 8) = bswap (V (.R 5 8)))
    (h5 : V (.R 5 8) = ((((0 : Word) ||| (inp 352).zeroExtend 32 <<< 0) ||| (inp 353).zeroExtend 32 <<< 8) ||| (inp 354).zeroExtend 32 <<< 16) ||| (inp 355).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 8) :=
  shape19 (env (.m 1 (⟨352, [1]⟩ : Lin))) (env (.m 1 (⟨353, [1]⟩ : Lin))) (env (.m 1 (⟨354, [1]⟩ : Lin))) (env (.m 1 (⟨355, [1]⟩ : Lin))) (V (.W 5 0 8)) (V (.R 5 8)) ((inp 352)) ((inp 353)) ((inp 354)) ((inp 355)) h0 h1 h2 h3 h4 h5

theorem core15_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨352, [1]⟩ : Lin)) = (inp 352).zeroExtend 32)
    (h1 : env (.m 1 (⟨353, [1]⟩ : Lin)) = (inp 353).zeroExtend 32)
    (h2 : env (.m 1 (⟨354, [1]⟩ : Lin)) = (inp 354).zeroExtend 32)
    (h3 : env (.m 1 (⟨355, [1]⟩ : Lin)) = (inp 355).zeroExtend 32)
    (h4 : V (.W 5 0 8) = bswap (V (.R 5 8)))
    (h5 : V (.R 5 8) = ((((0 : Word) ||| (inp 352).zeroExtend 32 <<< 0) ||| (inp 353).zeroExtend 32 <<< 8) ||| (inp 354).zeroExtend 32 <<< 16) ||| (inp 355).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 8) :=
  shape19 (env (.m 1 (⟨352, [1]⟩ : Lin))) (env (.m 1 (⟨353, [1]⟩ : Lin))) (env (.m 1 (⟨354, [1]⟩ : Lin))) (env (.m 1 (⟨355, [1]⟩ : Lin))) (V (.W 5 0 8)) (V (.R 5 8)) ((inp 352)) ((inp 353)) ((inp 354)) ((inp 355)) h0 h1 h2 h3 h4 h5

theorem core15_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨352, [1]⟩ : Lin)) = (inp 352).zeroExtend 32)
    (h1 : env (.m 1 (⟨353, [1]⟩ : Lin)) = (inp 353).zeroExtend 32)
    (h2 : env (.m 1 (⟨354, [1]⟩ : Lin)) = (inp 354).zeroExtend 32)
    (h3 : env (.m 1 (⟨355, [1]⟩ : Lin)) = (inp 355).zeroExtend 32)
    (h4 : V (.W 5 0 8) = bswap (V (.R 5 8)))
    (h5 : V (.R 5 8) = ((((0 : Word) ||| (inp 352).zeroExtend 32 <<< 0) ||| (inp 353).zeroExtend 32 <<< 8) ||| (inp 354).zeroExtend 32 <<< 16) ||| (inp 355).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 8) :=
  shape19 (env (.m 1 (⟨352, [1]⟩ : Lin))) (env (.m 1 (⟨353, [1]⟩ : Lin))) (env (.m 1 (⟨354, [1]⟩ : Lin))) (env (.m 1 (⟨355, [1]⟩ : Lin))) (V (.W 5 0 8)) (V (.R 5 8)) ((inp 352)) ((inp 353)) ((inp 354)) ((inp 355)) h0 h1 h2 h3 h4 h5

theorem core15_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨352, [1]⟩ : Lin)) = (inp 352).zeroExtend 32)
    (h1 : env (.m 1 (⟨353, [1]⟩ : Lin)) = (inp 353).zeroExtend 32)
    (h2 : env (.m 1 (⟨354, [1]⟩ : Lin)) = (inp 354).zeroExtend 32)
    (h3 : env (.m 1 (⟨355, [1]⟩ : Lin)) = (inp 355).zeroExtend 32)
    (h4 : V (.W 5 0 8) = bswap (V (.R 5 8)))
    (h5 : V (.R 5 8) = ((((0 : Word) ||| (inp 352).zeroExtend 32 <<< 0) ||| (inp 353).zeroExtend 32 <<< 8) ||| (inp 354).zeroExtend 32 <<< 16) ||| (inp 355).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 8) :=
  shape19 (env (.m 1 (⟨352, [1]⟩ : Lin))) (env (.m 1 (⟨353, [1]⟩ : Lin))) (env (.m 1 (⟨354, [1]⟩ : Lin))) (env (.m 1 (⟨355, [1]⟩ : Lin))) (V (.W 5 0 8)) (V (.R 5 8)) ((inp 352)) ((inp 353)) ((inp 354)) ((inp 355)) h0 h1 h2 h3 h4 h5

theorem core15_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨416, [1]⟩ : Lin)) = (inp 416).zeroExtend 32)
    (h1 : env (.m 1 (⟨417, [1]⟩ : Lin)) = (inp 417).zeroExtend 32)
    (h2 : env (.m 1 (⟨418, [1]⟩ : Lin)) = (inp 418).zeroExtend 32)
    (h3 : env (.m 1 (⟨419, [1]⟩ : Lin)) = (inp 419).zeroExtend 32)
    (h4 : V (.W 6 0 8) = bswap (V (.R 6 8)))
    (h5 : V (.R 6 8) = ((((0 : Word) ||| (inp 416).zeroExtend 32 <<< 0) ||| (inp 417).zeroExtend 32 <<< 8) ||| (inp 418).zeroExtend 32 <<< 16) ||| (inp 419).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 8) :=
  shape19 (env (.m 1 (⟨416, [1]⟩ : Lin))) (env (.m 1 (⟨417, [1]⟩ : Lin))) (env (.m 1 (⟨418, [1]⟩ : Lin))) (env (.m 1 (⟨419, [1]⟩ : Lin))) (V (.W 6 0 8)) (V (.R 6 8)) ((inp 416)) ((inp 417)) ((inp 418)) ((inp 419)) h0 h1 h2 h3 h4 h5

theorem core15_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨416, [1]⟩ : Lin)) = (inp 416).zeroExtend 32)
    (h1 : env (.m 1 (⟨417, [1]⟩ : Lin)) = (inp 417).zeroExtend 32)
    (h2 : env (.m 1 (⟨418, [1]⟩ : Lin)) = (inp 418).zeroExtend 32)
    (h3 : env (.m 1 (⟨419, [1]⟩ : Lin)) = (inp 419).zeroExtend 32)
    (h4 : V (.W 6 0 8) = bswap (V (.R 6 8)))
    (h5 : V (.R 6 8) = ((((0 : Word) ||| (inp 416).zeroExtend 32 <<< 0) ||| (inp 417).zeroExtend 32 <<< 8) ||| (inp 418).zeroExtend 32 <<< 16) ||| (inp 419).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 8) :=
  shape19 (env (.m 1 (⟨416, [1]⟩ : Lin))) (env (.m 1 (⟨417, [1]⟩ : Lin))) (env (.m 1 (⟨418, [1]⟩ : Lin))) (env (.m 1 (⟨419, [1]⟩ : Lin))) (V (.W 6 0 8)) (V (.R 6 8)) ((inp 416)) ((inp 417)) ((inp 418)) ((inp 419)) h0 h1 h2 h3 h4 h5

theorem core15_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨416, [1]⟩ : Lin)) = (inp 416).zeroExtend 32)
    (h1 : env (.m 1 (⟨417, [1]⟩ : Lin)) = (inp 417).zeroExtend 32)
    (h2 : env (.m 1 (⟨418, [1]⟩ : Lin)) = (inp 418).zeroExtend 32)
    (h3 : env (.m 1 (⟨419, [1]⟩ : Lin)) = (inp 419).zeroExtend 32)
    (h4 : V (.W 6 0 8) = bswap (V (.R 6 8)))
    (h5 : V (.R 6 8) = ((((0 : Word) ||| (inp 416).zeroExtend 32 <<< 0) ||| (inp 417).zeroExtend 32 <<< 8) ||| (inp 418).zeroExtend 32 <<< 16) ||| (inp 419).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 8) :=
  shape19 (env (.m 1 (⟨416, [1]⟩ : Lin))) (env (.m 1 (⟨417, [1]⟩ : Lin))) (env (.m 1 (⟨418, [1]⟩ : Lin))) (env (.m 1 (⟨419, [1]⟩ : Lin))) (V (.W 6 0 8)) (V (.R 6 8)) ((inp 416)) ((inp 417)) ((inp 418)) ((inp 419)) h0 h1 h2 h3 h4 h5

theorem core15_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨416, [1]⟩ : Lin)) = (inp 416).zeroExtend 32)
    (h1 : env (.m 1 (⟨417, [1]⟩ : Lin)) = (inp 417).zeroExtend 32)
    (h2 : env (.m 1 (⟨418, [1]⟩ : Lin)) = (inp 418).zeroExtend 32)
    (h3 : env (.m 1 (⟨419, [1]⟩ : Lin)) = (inp 419).zeroExtend 32)
    (h4 : V (.W 6 0 8) = bswap (V (.R 6 8)))
    (h5 : V (.R 6 8) = ((((0 : Word) ||| (inp 416).zeroExtend 32 <<< 0) ||| (inp 417).zeroExtend 32 <<< 8) ||| (inp 418).zeroExtend 32 <<< 16) ||| (inp 419).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 8) :=
  shape19 (env (.m 1 (⟨416, [1]⟩ : Lin))) (env (.m 1 (⟨417, [1]⟩ : Lin))) (env (.m 1 (⟨418, [1]⟩ : Lin))) (env (.m 1 (⟨419, [1]⟩ : Lin))) (V (.W 6 0 8)) (V (.R 6 8)) ((inp 416)) ((inp 417)) ((inp 418)) ((inp 419)) h0 h1 h2 h3 h4 h5

theorem core15_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨480, [1]⟩ : Lin)) = (inp 480).zeroExtend 32)
    (h1 : env (.m 1 (⟨481, [1]⟩ : Lin)) = (inp 481).zeroExtend 32)
    (h2 : env (.m 1 (⟨482, [1]⟩ : Lin)) = (inp 482).zeroExtend 32)
    (h3 : env (.m 1 (⟨483, [1]⟩ : Lin)) = (inp 483).zeroExtend 32)
    (h4 : V (.W 7 0 8) = bswap (V (.R 7 8)))
    (h5 : V (.R 7 8) = ((((0 : Word) ||| (inp 480).zeroExtend 32 <<< 0) ||| (inp 481).zeroExtend 32 <<< 8) ||| (inp 482).zeroExtend 32 <<< 16) ||| (inp 483).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 8) :=
  shape19 (env (.m 1 (⟨480, [1]⟩ : Lin))) (env (.m 1 (⟨481, [1]⟩ : Lin))) (env (.m 1 (⟨482, [1]⟩ : Lin))) (env (.m 1 (⟨483, [1]⟩ : Lin))) (V (.W 7 0 8)) (V (.R 7 8)) ((inp 480)) ((inp 481)) ((inp 482)) ((inp 483)) h0 h1 h2 h3 h4 h5

theorem core15_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨480, [1]⟩ : Lin)) = (inp 480).zeroExtend 32)
    (h1 : env (.m 1 (⟨481, [1]⟩ : Lin)) = (inp 481).zeroExtend 32)
    (h2 : env (.m 1 (⟨482, [1]⟩ : Lin)) = (inp 482).zeroExtend 32)
    (h3 : env (.m 1 (⟨483, [1]⟩ : Lin)) = (inp 483).zeroExtend 32)
    (h4 : V (.W 7 0 8) = bswap (V (.R 7 8)))
    (h5 : V (.R 7 8) = ((((0 : Word) ||| (inp 480).zeroExtend 32 <<< 0) ||| (inp 481).zeroExtend 32 <<< 8) ||| (inp 482).zeroExtend 32 <<< 16) ||| (inp 483).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 8) :=
  shape19 (env (.m 1 (⟨480, [1]⟩ : Lin))) (env (.m 1 (⟨481, [1]⟩ : Lin))) (env (.m 1 (⟨482, [1]⟩ : Lin))) (env (.m 1 (⟨483, [1]⟩ : Lin))) (V (.W 7 0 8)) (V (.R 7 8)) ((inp 480)) ((inp 481)) ((inp 482)) ((inp 483)) h0 h1 h2 h3 h4 h5

theorem core15_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨480, [1]⟩ : Lin)) = (inp 480).zeroExtend 32)
    (h1 : env (.m 1 (⟨481, [1]⟩ : Lin)) = (inp 481).zeroExtend 32)
    (h2 : env (.m 1 (⟨482, [1]⟩ : Lin)) = (inp 482).zeroExtend 32)
    (h3 : env (.m 1 (⟨483, [1]⟩ : Lin)) = (inp 483).zeroExtend 32)
    (h4 : V (.W 7 0 8) = bswap (V (.R 7 8)))
    (h5 : V (.R 7 8) = ((((0 : Word) ||| (inp 480).zeroExtend 32 <<< 0) ||| (inp 481).zeroExtend 32 <<< 8) ||| (inp 482).zeroExtend 32 <<< 16) ||| (inp 483).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 8) :=
  shape19 (env (.m 1 (⟨480, [1]⟩ : Lin))) (env (.m 1 (⟨481, [1]⟩ : Lin))) (env (.m 1 (⟨482, [1]⟩ : Lin))) (env (.m 1 (⟨483, [1]⟩ : Lin))) (V (.W 7 0 8)) (V (.R 7 8)) ((inp 480)) ((inp 481)) ((inp 482)) ((inp 483)) h0 h1 h2 h3 h4 h5

theorem core15_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨480, [1]⟩ : Lin)) = (inp 480).zeroExtend 32)
    (h1 : env (.m 1 (⟨481, [1]⟩ : Lin)) = (inp 481).zeroExtend 32)
    (h2 : env (.m 1 (⟨482, [1]⟩ : Lin)) = (inp 482).zeroExtend 32)
    (h3 : env (.m 1 (⟨483, [1]⟩ : Lin)) = (inp 483).zeroExtend 32)
    (h4 : V (.W 7 0 8) = bswap (V (.R 7 8)))
    (h5 : V (.R 7 8) = ((((0 : Word) ||| (inp 480).zeroExtend 32 <<< 0) ||| (inp 481).zeroExtend 32 <<< 8) ||| (inp 482).zeroExtend 32 <<< 16) ||| (inp 483).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 8) :=
  shape19 (env (.m 1 (⟨480, [1]⟩ : Lin))) (env (.m 1 (⟨481, [1]⟩ : Lin))) (env (.m 1 (⟨482, [1]⟩ : Lin))) (env (.m 1 (⟨483, [1]⟩ : Lin))) (V (.W 7 0 8)) (V (.R 7 8)) ((inp 480)) ((inp 481)) ((inp 482)) ((inp 483)) h0 h1 h2 h3 h4 h5

theorem core15_283 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨492, [1]⟩ : Lin)) = (inp 492).zeroExtend 32)
    (h1 : env (.m 1 (⟨493, [1]⟩ : Lin)) = (inp 493).zeroExtend 32)
    (h2 : env (.m 1 (⟨494, [1]⟩ : Lin)) = (inp 494).zeroExtend 32)
    (h3 : env (.m 1 (⟨495, [1]⟩ : Lin)) = (inp 495).zeroExtend 32)
    (h4 : V (.W 7 0 11) = bswap (V (.R 7 11)))
    (h5 : V (.R 7 11) = ((((0 : Word) ||| (inp 492).zeroExtend 32 <<< 0) ||| (inp 493).zeroExtend 32 <<< 8) ||| (inp 494).zeroExtend 32 <<< 16) ||| (inp 495).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨492, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨493, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨494, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨495, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨492, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨493, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨494, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨495, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨492, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨493, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨494, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨495, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨492, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨493, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨494, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨495, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 11) :=
  shape19 (env (.m 1 (⟨492, [1]⟩ : Lin))) (env (.m 1 (⟨493, [1]⟩ : Lin))) (env (.m 1 (⟨494, [1]⟩ : Lin))) (env (.m 1 (⟨495, [1]⟩ : Lin))) (V (.W 7 0 11)) (V (.R 7 11)) ((inp 492)) ((inp 493)) ((inp 494)) ((inp 495)) h0 h1 h2 h3 h4 h5

theorem core15_282 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨428, [1]⟩ : Lin)) = (inp 428).zeroExtend 32)
    (h1 : env (.m 1 (⟨429, [1]⟩ : Lin)) = (inp 429).zeroExtend 32)
    (h2 : env (.m 1 (⟨430, [1]⟩ : Lin)) = (inp 430).zeroExtend 32)
    (h3 : env (.m 1 (⟨431, [1]⟩ : Lin)) = (inp 431).zeroExtend 32)
    (h4 : V (.W 6 0 11) = bswap (V (.R 6 11)))
    (h5 : V (.R 6 11) = ((((0 : Word) ||| (inp 428).zeroExtend 32 <<< 0) ||| (inp 429).zeroExtend 32 <<< 8) ||| (inp 430).zeroExtend 32 <<< 16) ||| (inp 431).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨428, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨429, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨430, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨431, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨428, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨429, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨430, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨431, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨428, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨429, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨430, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨431, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨428, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨429, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨430, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨431, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 11) :=
  shape19 (env (.m 1 (⟨428, [1]⟩ : Lin))) (env (.m 1 (⟨429, [1]⟩ : Lin))) (env (.m 1 (⟨430, [1]⟩ : Lin))) (env (.m 1 (⟨431, [1]⟩ : Lin))) (V (.W 6 0 11)) (V (.R 6 11)) ((inp 428)) ((inp 429)) ((inp 430)) ((inp 431)) h0 h1 h2 h3 h4 h5

theorem core15_281 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨364, [1]⟩ : Lin)) = (inp 364).zeroExtend 32)
    (h1 : env (.m 1 (⟨365, [1]⟩ : Lin)) = (inp 365).zeroExtend 32)
    (h2 : env (.m 1 (⟨366, [1]⟩ : Lin)) = (inp 366).zeroExtend 32)
    (h3 : env (.m 1 (⟨367, [1]⟩ : Lin)) = (inp 367).zeroExtend 32)
    (h4 : V (.W 5 0 11) = bswap (V (.R 5 11)))
    (h5 : V (.R 5 11) = ((((0 : Word) ||| (inp 364).zeroExtend 32 <<< 0) ||| (inp 365).zeroExtend 32 <<< 8) ||| (inp 366).zeroExtend 32 <<< 16) ||| (inp 367).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨364, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨365, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨366, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨367, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨364, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨365, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨366, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨367, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨364, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨365, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨366, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨367, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨364, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨365, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨366, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨367, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 11) :=
  shape19 (env (.m 1 (⟨364, [1]⟩ : Lin))) (env (.m 1 (⟨365, [1]⟩ : Lin))) (env (.m 1 (⟨366, [1]⟩ : Lin))) (env (.m 1 (⟨367, [1]⟩ : Lin))) (V (.W 5 0 11)) (V (.R 5 11)) ((inp 364)) ((inp 365)) ((inp 366)) ((inp 367)) h0 h1 h2 h3 h4 h5

theorem core15_280 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨300, [1]⟩ : Lin)) = (inp 300).zeroExtend 32)
    (h1 : env (.m 1 (⟨301, [1]⟩ : Lin)) = (inp 301).zeroExtend 32)
    (h2 : env (.m 1 (⟨302, [1]⟩ : Lin)) = (inp 302).zeroExtend 32)
    (h3 : env (.m 1 (⟨303, [1]⟩ : Lin)) = (inp 303).zeroExtend 32)
    (h4 : V (.W 4 0 11) = bswap (V (.R 4 11)))
    (h5 : V (.R 4 11) = ((((0 : Word) ||| (inp 300).zeroExtend 32 <<< 0) ||| (inp 301).zeroExtend 32 <<< 8) ||| (inp 302).zeroExtend 32 <<< 16) ||| (inp 303).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨300, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨301, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨302, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨303, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨300, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨301, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨302, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨303, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨300, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨301, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨302, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨303, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨300, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨301, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨302, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨303, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 11) :=
  shape19 (env (.m 1 (⟨300, [1]⟩ : Lin))) (env (.m 1 (⟨301, [1]⟩ : Lin))) (env (.m 1 (⟨302, [1]⟩ : Lin))) (env (.m 1 (⟨303, [1]⟩ : Lin))) (V (.W 4 0 11)) (V (.R 4 11)) ((inp 300)) ((inp 301)) ((inp 302)) ((inp 303)) h0 h1 h2 h3 h4 h5

theorem core15_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨236, [1]⟩ : Lin)) = (inp 236).zeroExtend 32)
    (h1 : env (.m 1 (⟨237, [1]⟩ : Lin)) = (inp 237).zeroExtend 32)
    (h2 : env (.m 1 (⟨238, [1]⟩ : Lin)) = (inp 238).zeroExtend 32)
    (h3 : env (.m 1 (⟨239, [1]⟩ : Lin)) = (inp 239).zeroExtend 32)
    (h4 : V (.W 3 0 11) = bswap (V (.R 3 11)))
    (h5 : V (.R 3 11) = ((((0 : Word) ||| (inp 236).zeroExtend 32 <<< 0) ||| (inp 237).zeroExtend 32 <<< 8) ||| (inp 238).zeroExtend 32 <<< 16) ||| (inp 239).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 11) :=
  shape19 (env (.m 1 (⟨236, [1]⟩ : Lin))) (env (.m 1 (⟨237, [1]⟩ : Lin))) (env (.m 1 (⟨238, [1]⟩ : Lin))) (env (.m 1 (⟨239, [1]⟩ : Lin))) (V (.W 3 0 11)) (V (.R 3 11)) ((inp 236)) ((inp 237)) ((inp 238)) ((inp 239)) h0 h1 h2 h3 h4 h5

theorem core15_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨172, [1]⟩ : Lin)) = (inp 172).zeroExtend 32)
    (h1 : env (.m 1 (⟨173, [1]⟩ : Lin)) = (inp 173).zeroExtend 32)
    (h2 : env (.m 1 (⟨174, [1]⟩ : Lin)) = (inp 174).zeroExtend 32)
    (h3 : env (.m 1 (⟨175, [1]⟩ : Lin)) = (inp 175).zeroExtend 32)
    (h4 : V (.W 2 0 11) = bswap (V (.R 2 11)))
    (h5 : V (.R 2 11) = ((((0 : Word) ||| (inp 172).zeroExtend 32 <<< 0) ||| (inp 173).zeroExtend 32 <<< 8) ||| (inp 174).zeroExtend 32 <<< 16) ||| (inp 175).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 11) :=
  shape19 (env (.m 1 (⟨172, [1]⟩ : Lin))) (env (.m 1 (⟨173, [1]⟩ : Lin))) (env (.m 1 (⟨174, [1]⟩ : Lin))) (env (.m 1 (⟨175, [1]⟩ : Lin))) (V (.W 2 0 11)) (V (.R 2 11)) ((inp 172)) ((inp 173)) ((inp 174)) ((inp 175)) h0 h1 h2 h3 h4 h5

theorem core15_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨108, [1]⟩ : Lin)) = (inp 108).zeroExtend 32)
    (h1 : env (.m 1 (⟨109, [1]⟩ : Lin)) = (inp 109).zeroExtend 32)
    (h2 : env (.m 1 (⟨110, [1]⟩ : Lin)) = (inp 110).zeroExtend 32)
    (h3 : env (.m 1 (⟨111, [1]⟩ : Lin)) = (inp 111).zeroExtend 32)
    (h4 : V (.W 1 0 11) = bswap (V (.R 1 11)))
    (h5 : V (.R 1 11) = ((((0 : Word) ||| (inp 108).zeroExtend 32 <<< 0) ||| (inp 109).zeroExtend 32 <<< 8) ||| (inp 110).zeroExtend 32 <<< 16) ||| (inp 111).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 11) :=
  shape19 (env (.m 1 (⟨108, [1]⟩ : Lin))) (env (.m 1 (⟨109, [1]⟩ : Lin))) (env (.m 1 (⟨110, [1]⟩ : Lin))) (env (.m 1 (⟨111, [1]⟩ : Lin))) (V (.W 1 0 11)) (V (.R 1 11)) ((inp 108)) ((inp 109)) ((inp 110)) ((inp 111)) h0 h1 h2 h3 h4 h5

theorem core15_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨44, [1]⟩ : Lin)) = (inp 44).zeroExtend 32)
    (h1 : env (.m 1 (⟨45, [1]⟩ : Lin)) = (inp 45).zeroExtend 32)
    (h2 : env (.m 1 (⟨46, [1]⟩ : Lin)) = (inp 46).zeroExtend 32)
    (h3 : env (.m 1 (⟨47, [1]⟩ : Lin)) = (inp 47).zeroExtend 32)
    (h4 : V (.W 0 0 11) = bswap (V (.R 0 11)))
    (h5 : V (.R 0 11) = ((((0 : Word) ||| (inp 44).zeroExtend 32 <<< 0) ||| (inp 45).zeroExtend 32 <<< 8) ||| (inp 46).zeroExtend 32 <<< 16) ||| (inp 47).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 11) :=
  shape19 (env (.m 1 (⟨44, [1]⟩ : Lin))) (env (.m 1 (⟨45, [1]⟩ : Lin))) (env (.m 1 (⟨46, [1]⟩ : Lin))) (env (.m 1 (⟨47, [1]⟩ : Lin))) (V (.W 0 0 11)) (V (.R 0 11)) ((inp 44)) ((inp 45)) ((inp 46)) ((inp 47)) h0 h1 h2 h3 h4 h5

theorem core15_267 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨488, [1]⟩ : Lin)) = (inp 488).zeroExtend 32)
    (h1 : env (.m 1 (⟨489, [1]⟩ : Lin)) = (inp 489).zeroExtend 32)
    (h2 : env (.m 1 (⟨490, [1]⟩ : Lin)) = (inp 490).zeroExtend 32)
    (h3 : env (.m 1 (⟨491, [1]⟩ : Lin)) = (inp 491).zeroExtend 32)
    (h4 : V (.W 7 0 10) = bswap (V (.R 7 10)))
    (h5 : V (.R 7 10) = ((((0 : Word) ||| (inp 488).zeroExtend 32 <<< 0) ||| (inp 489).zeroExtend 32 <<< 8) ||| (inp 490).zeroExtend 32 <<< 16) ||| (inp 491).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨488, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨489, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨490, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨491, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨488, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨489, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨490, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨491, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨488, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨489, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨490, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨491, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨488, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨489, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨490, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨491, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 10) :=
  shape19 (env (.m 1 (⟨488, [1]⟩ : Lin))) (env (.m 1 (⟨489, [1]⟩ : Lin))) (env (.m 1 (⟨490, [1]⟩ : Lin))) (env (.m 1 (⟨491, [1]⟩ : Lin))) (V (.W 7 0 10)) (V (.R 7 10)) ((inp 488)) ((inp 489)) ((inp 490)) ((inp 491)) h0 h1 h2 h3 h4 h5

theorem core15_266 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨424, [1]⟩ : Lin)) = (inp 424).zeroExtend 32)
    (h1 : env (.m 1 (⟨425, [1]⟩ : Lin)) = (inp 425).zeroExtend 32)
    (h2 : env (.m 1 (⟨426, [1]⟩ : Lin)) = (inp 426).zeroExtend 32)
    (h3 : env (.m 1 (⟨427, [1]⟩ : Lin)) = (inp 427).zeroExtend 32)
    (h4 : V (.W 6 0 10) = bswap (V (.R 6 10)))
    (h5 : V (.R 6 10) = ((((0 : Word) ||| (inp 424).zeroExtend 32 <<< 0) ||| (inp 425).zeroExtend 32 <<< 8) ||| (inp 426).zeroExtend 32 <<< 16) ||| (inp 427).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨424, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨425, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨426, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨427, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨424, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨425, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨426, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨427, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨424, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨425, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨426, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨427, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨424, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨425, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨426, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨427, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 10) :=
  shape19 (env (.m 1 (⟨424, [1]⟩ : Lin))) (env (.m 1 (⟨425, [1]⟩ : Lin))) (env (.m 1 (⟨426, [1]⟩ : Lin))) (env (.m 1 (⟨427, [1]⟩ : Lin))) (V (.W 6 0 10)) (V (.R 6 10)) ((inp 424)) ((inp 425)) ((inp 426)) ((inp 427)) h0 h1 h2 h3 h4 h5

theorem core15_265 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨360, [1]⟩ : Lin)) = (inp 360).zeroExtend 32)
    (h1 : env (.m 1 (⟨361, [1]⟩ : Lin)) = (inp 361).zeroExtend 32)
    (h2 : env (.m 1 (⟨362, [1]⟩ : Lin)) = (inp 362).zeroExtend 32)
    (h3 : env (.m 1 (⟨363, [1]⟩ : Lin)) = (inp 363).zeroExtend 32)
    (h4 : V (.W 5 0 10) = bswap (V (.R 5 10)))
    (h5 : V (.R 5 10) = ((((0 : Word) ||| (inp 360).zeroExtend 32 <<< 0) ||| (inp 361).zeroExtend 32 <<< 8) ||| (inp 362).zeroExtend 32 <<< 16) ||| (inp 363).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨360, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨361, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨362, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨363, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨360, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨361, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨362, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨363, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨360, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨361, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨362, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨363, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨360, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨361, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨362, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨363, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 10) :=
  shape19 (env (.m 1 (⟨360, [1]⟩ : Lin))) (env (.m 1 (⟨361, [1]⟩ : Lin))) (env (.m 1 (⟨362, [1]⟩ : Lin))) (env (.m 1 (⟨363, [1]⟩ : Lin))) (V (.W 5 0 10)) (V (.R 5 10)) ((inp 360)) ((inp 361)) ((inp 362)) ((inp 363)) h0 h1 h2 h3 h4 h5

theorem core15_264 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨296, [1]⟩ : Lin)) = (inp 296).zeroExtend 32)
    (h1 : env (.m 1 (⟨297, [1]⟩ : Lin)) = (inp 297).zeroExtend 32)
    (h2 : env (.m 1 (⟨298, [1]⟩ : Lin)) = (inp 298).zeroExtend 32)
    (h3 : env (.m 1 (⟨299, [1]⟩ : Lin)) = (inp 299).zeroExtend 32)
    (h4 : V (.W 4 0 10) = bswap (V (.R 4 10)))
    (h5 : V (.R 4 10) = ((((0 : Word) ||| (inp 296).zeroExtend 32 <<< 0) ||| (inp 297).zeroExtend 32 <<< 8) ||| (inp 298).zeroExtend 32 <<< 16) ||| (inp 299).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨296, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨297, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨298, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨299, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨296, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨297, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨298, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨299, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨296, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨297, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨298, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨299, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨296, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨297, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨298, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨299, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 10) :=
  shape19 (env (.m 1 (⟨296, [1]⟩ : Lin))) (env (.m 1 (⟨297, [1]⟩ : Lin))) (env (.m 1 (⟨298, [1]⟩ : Lin))) (env (.m 1 (⟨299, [1]⟩ : Lin))) (V (.W 4 0 10)) (V (.R 4 10)) ((inp 296)) ((inp 297)) ((inp 298)) ((inp 299)) h0 h1 h2 h3 h4 h5

theorem core15_263 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨232, [1]⟩ : Lin)) = (inp 232).zeroExtend 32)
    (h1 : env (.m 1 (⟨233, [1]⟩ : Lin)) = (inp 233).zeroExtend 32)
    (h2 : env (.m 1 (⟨234, [1]⟩ : Lin)) = (inp 234).zeroExtend 32)
    (h3 : env (.m 1 (⟨235, [1]⟩ : Lin)) = (inp 235).zeroExtend 32)
    (h4 : V (.W 3 0 10) = bswap (V (.R 3 10)))
    (h5 : V (.R 3 10) = ((((0 : Word) ||| (inp 232).zeroExtend 32 <<< 0) ||| (inp 233).zeroExtend 32 <<< 8) ||| (inp 234).zeroExtend 32 <<< 16) ||| (inp 235).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 10) :=
  shape19 (env (.m 1 (⟨232, [1]⟩ : Lin))) (env (.m 1 (⟨233, [1]⟩ : Lin))) (env (.m 1 (⟨234, [1]⟩ : Lin))) (env (.m 1 (⟨235, [1]⟩ : Lin))) (V (.W 3 0 10)) (V (.R 3 10)) ((inp 232)) ((inp 233)) ((inp 234)) ((inp 235)) h0 h1 h2 h3 h4 h5

theorem core15_262 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨168, [1]⟩ : Lin)) = (inp 168).zeroExtend 32)
    (h1 : env (.m 1 (⟨169, [1]⟩ : Lin)) = (inp 169).zeroExtend 32)
    (h2 : env (.m 1 (⟨170, [1]⟩ : Lin)) = (inp 170).zeroExtend 32)
    (h3 : env (.m 1 (⟨171, [1]⟩ : Lin)) = (inp 171).zeroExtend 32)
    (h4 : V (.W 2 0 10) = bswap (V (.R 2 10)))
    (h5 : V (.R 2 10) = ((((0 : Word) ||| (inp 168).zeroExtend 32 <<< 0) ||| (inp 169).zeroExtend 32 <<< 8) ||| (inp 170).zeroExtend 32 <<< 16) ||| (inp 171).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 10) :=
  shape19 (env (.m 1 (⟨168, [1]⟩ : Lin))) (env (.m 1 (⟨169, [1]⟩ : Lin))) (env (.m 1 (⟨170, [1]⟩ : Lin))) (env (.m 1 (⟨171, [1]⟩ : Lin))) (V (.W 2 0 10)) (V (.R 2 10)) ((inp 168)) ((inp 169)) ((inp 170)) ((inp 171)) h0 h1 h2 h3 h4 h5

theorem core15_261 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨104, [1]⟩ : Lin)) = (inp 104).zeroExtend 32)
    (h1 : env (.m 1 (⟨105, [1]⟩ : Lin)) = (inp 105).zeroExtend 32)
    (h2 : env (.m 1 (⟨106, [1]⟩ : Lin)) = (inp 106).zeroExtend 32)
    (h3 : env (.m 1 (⟨107, [1]⟩ : Lin)) = (inp 107).zeroExtend 32)
    (h4 : V (.W 1 0 10) = bswap (V (.R 1 10)))
    (h5 : V (.R 1 10) = ((((0 : Word) ||| (inp 104).zeroExtend 32 <<< 0) ||| (inp 105).zeroExtend 32 <<< 8) ||| (inp 106).zeroExtend 32 <<< 16) ||| (inp 107).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 10) :=
  shape19 (env (.m 1 (⟨104, [1]⟩ : Lin))) (env (.m 1 (⟨105, [1]⟩ : Lin))) (env (.m 1 (⟨106, [1]⟩ : Lin))) (env (.m 1 (⟨107, [1]⟩ : Lin))) (V (.W 1 0 10)) (V (.R 1 10)) ((inp 104)) ((inp 105)) ((inp 106)) ((inp 107)) h0 h1 h2 h3 h4 h5

theorem core15_260 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨40, [1]⟩ : Lin)) = (inp 40).zeroExtend 32)
    (h1 : env (.m 1 (⟨41, [1]⟩ : Lin)) = (inp 41).zeroExtend 32)
    (h2 : env (.m 1 (⟨42, [1]⟩ : Lin)) = (inp 42).zeroExtend 32)
    (h3 : env (.m 1 (⟨43, [1]⟩ : Lin)) = (inp 43).zeroExtend 32)
    (h4 : V (.W 0 0 10) = bswap (V (.R 0 10)))
    (h5 : V (.R 0 10) = ((((0 : Word) ||| (inp 40).zeroExtend 32 <<< 0) ||| (inp 41).zeroExtend 32 <<< 8) ||| (inp 42).zeroExtend 32 <<< 16) ||| (inp 43).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 10) :=
  shape19 (env (.m 1 (⟨40, [1]⟩ : Lin))) (env (.m 1 (⟨41, [1]⟩ : Lin))) (env (.m 1 (⟨42, [1]⟩ : Lin))) (env (.m 1 (⟨43, [1]⟩ : Lin))) (V (.W 0 0 10)) (V (.R 0 10)) ((inp 40)) ((inp 41)) ((inp 42)) ((inp 43)) h0 h1 h2 h3 h4 h5

theorem core15_251 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨484, [1]⟩ : Lin)) = (inp 484).zeroExtend 32)
    (h1 : env (.m 1 (⟨485, [1]⟩ : Lin)) = (inp 485).zeroExtend 32)
    (h2 : env (.m 1 (⟨486, [1]⟩ : Lin)) = (inp 486).zeroExtend 32)
    (h3 : env (.m 1 (⟨487, [1]⟩ : Lin)) = (inp 487).zeroExtend 32)
    (h4 : V (.W 7 0 9) = bswap (V (.R 7 9)))
    (h5 : V (.R 7 9) = ((((0 : Word) ||| (inp 484).zeroExtend 32 <<< 0) ||| (inp 485).zeroExtend 32 <<< 8) ||| (inp 486).zeroExtend 32 <<< 16) ||| (inp 487).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨484, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨485, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨486, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨487, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨484, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨485, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨486, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨487, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨484, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨485, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨486, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨487, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨484, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨485, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨486, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨487, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 7 0 9) :=
  shape19 (env (.m 1 (⟨484, [1]⟩ : Lin))) (env (.m 1 (⟨485, [1]⟩ : Lin))) (env (.m 1 (⟨486, [1]⟩ : Lin))) (env (.m 1 (⟨487, [1]⟩ : Lin))) (V (.W 7 0 9)) (V (.R 7 9)) ((inp 484)) ((inp 485)) ((inp 486)) ((inp 487)) h0 h1 h2 h3 h4 h5

theorem core15_250 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨420, [1]⟩ : Lin)) = (inp 420).zeroExtend 32)
    (h1 : env (.m 1 (⟨421, [1]⟩ : Lin)) = (inp 421).zeroExtend 32)
    (h2 : env (.m 1 (⟨422, [1]⟩ : Lin)) = (inp 422).zeroExtend 32)
    (h3 : env (.m 1 (⟨423, [1]⟩ : Lin)) = (inp 423).zeroExtend 32)
    (h4 : V (.W 6 0 9) = bswap (V (.R 6 9)))
    (h5 : V (.R 6 9) = ((((0 : Word) ||| (inp 420).zeroExtend 32 <<< 0) ||| (inp 421).zeroExtend 32 <<< 8) ||| (inp 422).zeroExtend 32 <<< 16) ||| (inp 423).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨420, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨421, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨422, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨423, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨420, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨421, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨422, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨423, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨420, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨421, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨422, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨423, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨420, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨421, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨422, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨423, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 6 0 9) :=
  shape19 (env (.m 1 (⟨420, [1]⟩ : Lin))) (env (.m 1 (⟨421, [1]⟩ : Lin))) (env (.m 1 (⟨422, [1]⟩ : Lin))) (env (.m 1 (⟨423, [1]⟩ : Lin))) (V (.W 6 0 9)) (V (.R 6 9)) ((inp 420)) ((inp 421)) ((inp 422)) ((inp 423)) h0 h1 h2 h3 h4 h5

theorem core15_249 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨356, [1]⟩ : Lin)) = (inp 356).zeroExtend 32)
    (h1 : env (.m 1 (⟨357, [1]⟩ : Lin)) = (inp 357).zeroExtend 32)
    (h2 : env (.m 1 (⟨358, [1]⟩ : Lin)) = (inp 358).zeroExtend 32)
    (h3 : env (.m 1 (⟨359, [1]⟩ : Lin)) = (inp 359).zeroExtend 32)
    (h4 : V (.W 5 0 9) = bswap (V (.R 5 9)))
    (h5 : V (.R 5 9) = ((((0 : Word) ||| (inp 356).zeroExtend 32 <<< 0) ||| (inp 357).zeroExtend 32 <<< 8) ||| (inp 358).zeroExtend 32 <<< 16) ||| (inp 359).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨356, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨357, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨358, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨359, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨356, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨357, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨358, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨359, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨356, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨357, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨358, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨359, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨356, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨357, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨358, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨359, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 5 0 9) :=
  shape19 (env (.m 1 (⟨356, [1]⟩ : Lin))) (env (.m 1 (⟨357, [1]⟩ : Lin))) (env (.m 1 (⟨358, [1]⟩ : Lin))) (env (.m 1 (⟨359, [1]⟩ : Lin))) (V (.W 5 0 9)) (V (.R 5 9)) ((inp 356)) ((inp 357)) ((inp 358)) ((inp 359)) h0 h1 h2 h3 h4 h5

theorem core15_248 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨292, [1]⟩ : Lin)) = (inp 292).zeroExtend 32)
    (h1 : env (.m 1 (⟨293, [1]⟩ : Lin)) = (inp 293).zeroExtend 32)
    (h2 : env (.m 1 (⟨294, [1]⟩ : Lin)) = (inp 294).zeroExtend 32)
    (h3 : env (.m 1 (⟨295, [1]⟩ : Lin)) = (inp 295).zeroExtend 32)
    (h4 : V (.W 4 0 9) = bswap (V (.R 4 9)))
    (h5 : V (.R 4 9) = ((((0 : Word) ||| (inp 292).zeroExtend 32 <<< 0) ||| (inp 293).zeroExtend 32 <<< 8) ||| (inp 294).zeroExtend 32 <<< 16) ||| (inp 295).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨292, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨293, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨294, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨295, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨292, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨293, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨294, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨295, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨292, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨293, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨294, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨295, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨292, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨293, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨294, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨295, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 4 0 9) :=
  shape19 (env (.m 1 (⟨292, [1]⟩ : Lin))) (env (.m 1 (⟨293, [1]⟩ : Lin))) (env (.m 1 (⟨294, [1]⟩ : Lin))) (env (.m 1 (⟨295, [1]⟩ : Lin))) (V (.W 4 0 9)) (V (.R 4 9)) ((inp 292)) ((inp 293)) ((inp 294)) ((inp 295)) h0 h1 h2 h3 h4 h5

theorem core15_247 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨228, [1]⟩ : Lin)) = (inp 228).zeroExtend 32)
    (h1 : env (.m 1 (⟨229, [1]⟩ : Lin)) = (inp 229).zeroExtend 32)
    (h2 : env (.m 1 (⟨230, [1]⟩ : Lin)) = (inp 230).zeroExtend 32)
    (h3 : env (.m 1 (⟨231, [1]⟩ : Lin)) = (inp 231).zeroExtend 32)
    (h4 : V (.W 3 0 9) = bswap (V (.R 3 9)))
    (h5 : V (.R 3 9) = ((((0 : Word) ||| (inp 228).zeroExtend 32 <<< 0) ||| (inp 229).zeroExtend 32 <<< 8) ||| (inp 230).zeroExtend 32 <<< 16) ||| (inp 231).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 9) :=
  shape19 (env (.m 1 (⟨228, [1]⟩ : Lin))) (env (.m 1 (⟨229, [1]⟩ : Lin))) (env (.m 1 (⟨230, [1]⟩ : Lin))) (env (.m 1 (⟨231, [1]⟩ : Lin))) (V (.W 3 0 9)) (V (.R 3 9)) ((inp 228)) ((inp 229)) ((inp 230)) ((inp 231)) h0 h1 h2 h3 h4 h5

theorem core15_246 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨164, [1]⟩ : Lin)) = (inp 164).zeroExtend 32)
    (h1 : env (.m 1 (⟨165, [1]⟩ : Lin)) = (inp 165).zeroExtend 32)
    (h2 : env (.m 1 (⟨166, [1]⟩ : Lin)) = (inp 166).zeroExtend 32)
    (h3 : env (.m 1 (⟨167, [1]⟩ : Lin)) = (inp 167).zeroExtend 32)
    (h4 : V (.W 2 0 9) = bswap (V (.R 2 9)))
    (h5 : V (.R 2 9) = ((((0 : Word) ||| (inp 164).zeroExtend 32 <<< 0) ||| (inp 165).zeroExtend 32 <<< 8) ||| (inp 166).zeroExtend 32 <<< 16) ||| (inp 167).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 9) :=
  shape19 (env (.m 1 (⟨164, [1]⟩ : Lin))) (env (.m 1 (⟨165, [1]⟩ : Lin))) (env (.m 1 (⟨166, [1]⟩ : Lin))) (env (.m 1 (⟨167, [1]⟩ : Lin))) (V (.W 2 0 9)) (V (.R 2 9)) ((inp 164)) ((inp 165)) ((inp 166)) ((inp 167)) h0 h1 h2 h3 h4 h5

theorem core15_245 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨100, [1]⟩ : Lin)) = (inp 100).zeroExtend 32)
    (h1 : env (.m 1 (⟨101, [1]⟩ : Lin)) = (inp 101).zeroExtend 32)
    (h2 : env (.m 1 (⟨102, [1]⟩ : Lin)) = (inp 102).zeroExtend 32)
    (h3 : env (.m 1 (⟨103, [1]⟩ : Lin)) = (inp 103).zeroExtend 32)
    (h4 : V (.W 1 0 9) = bswap (V (.R 1 9)))
    (h5 : V (.R 1 9) = ((((0 : Word) ||| (inp 100).zeroExtend 32 <<< 0) ||| (inp 101).zeroExtend 32 <<< 8) ||| (inp 102).zeroExtend 32 <<< 16) ||| (inp 103).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 9) :=
  shape19 (env (.m 1 (⟨100, [1]⟩ : Lin))) (env (.m 1 (⟨101, [1]⟩ : Lin))) (env (.m 1 (⟨102, [1]⟩ : Lin))) (env (.m 1 (⟨103, [1]⟩ : Lin))) (V (.W 1 0 9)) (V (.R 1 9)) ((inp 100)) ((inp 101)) ((inp 102)) ((inp 103)) h0 h1 h2 h3 h4 h5

theorem core15_244 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨36, [1]⟩ : Lin)) = (inp 36).zeroExtend 32)
    (h1 : env (.m 1 (⟨37, [1]⟩ : Lin)) = (inp 37).zeroExtend 32)
    (h2 : env (.m 1 (⟨38, [1]⟩ : Lin)) = (inp 38).zeroExtend 32)
    (h3 : env (.m 1 (⟨39, [1]⟩ : Lin)) = (inp 39).zeroExtend 32)
    (h4 : V (.W 0 0 9) = bswap (V (.R 0 9)))
    (h5 : V (.R 0 9) = ((((0 : Word) ||| (inp 36).zeroExtend 32 <<< 0) ||| (inp 37).zeroExtend 32 <<< 8) ||| (inp 38).zeroExtend 32 <<< 16) ||| (inp 39).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 9) :=
  shape19 (env (.m 1 (⟨36, [1]⟩ : Lin))) (env (.m 1 (⟨37, [1]⟩ : Lin))) (env (.m 1 (⟨38, [1]⟩ : Lin))) (env (.m 1 (⟨39, [1]⟩ : Lin))) (V (.W 0 0 9)) (V (.R 0 9)) ((inp 36)) ((inp 37)) ((inp 38)) ((inp 39)) h0 h1 h2 h3 h4 h5

theorem core15_219 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 219) = V (.E 7 0 (5)))
    (h1 : env (.n 187) = V (.E 7 0 (7)))
    (h2 : env (.n 203) = V (.E 7 0 (6)))
    (h3 : env (.n 171) = V (.E 7 0 (8)))
    (h4 : env (.n 107) = V (.A 7 0 (8)))
    (h5 : env (.n 139) = V (.A 7 0 (6)))
    (h6 : env (.n 123) = V (.A 7 0 (7)))
    (h7 : env (.m 1 (⟨480, [1]⟩ : Lin)) = (inp 480).zeroExtend 32)
    (h8 : env (.m 1 (⟨481, [1]⟩ : Lin)) = (inp 481).zeroExtend 32)
    (h9 : env (.m 1 (⟨482, [1]⟩ : Lin)) = (inp 482).zeroExtend 32)
    (h10 : env (.m 1 (⟨483, [1]⟩ : Lin)) = (inp 483).zeroExtend 32)
    (h11 : V (.A 7 0 (9)) = (V (.E 7 0 (5)) + Sigma1 (V (.E 7 0 (8))) + Ch (V (.E 7 0 (8))) (V (.E 7 0 (7))) (V (.E 7 0 (6))) + V (.KW 7 0 8)) + (Sigma0 (V (.A 7 0 (8))) + Maj (V (.A 7 0 (8))) (V (.A 7 0 (7))) (V (.A 7 0 (6)))))
    (h12 : V (.KW 7 0 8) = 3624381080#32 + V (.W 7 0 8))
    (h13 : V (.W 7 0 8) = bswap (V (.R 7 8)))
    (h14 : V (.R 7 8) = ((((0 : Word) ||| (inp 480).zeroExtend 32 <<< 0) ||| (inp 481).zeroExtend 32 <<< 8) ||| (inp 482).zeroExtend 32 <<< 16) ||| (inp 483).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 219)) (.xor (.and (.xor (.var (.n 187)) (.var (.n 203))) (.var (.n 171))) (.var (.n 203)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 171)) 5) (.shl (.var (.n 171)) 27)) (.var (.n 171))) 6) (.shl (.xor (.or (.shr (.var (.n 171)) 5) (.shl (.var (.n 171)) 27)) (.var (.n 171))) 26)) (.or (.shr (.var (.n 171)) 25) (.shl (.var (.n 171)) 7)))) (.or (.and (.var (.n 107)) (.var (.n 139))) (.and (.xor (.var (.n 107)) (.var (.n 139))) (.var (.n 123))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 107)) 11) (.shl (.var (.n 107)) 21)) (.var (.n 107))) 2) (.shl (.xor (.or (.shr (.var (.n 107)) 11) (.shl (.var (.n 107)) 21)) (.var (.n 107))) 30)) (.or (.shr (.var (.n 107)) 22) (.shl (.var (.n 107)) 10)))) = V (.A 7 0 (9)) :=
  shape20 (env (.n 219)) (env (.n 187)) (env (.n 203)) (env (.n 171)) (env (.m 1 (⟨480, [1]⟩ : Lin))) (env (.m 1 (⟨481, [1]⟩ : Lin))) (env (.m 1 (⟨482, [1]⟩ : Lin))) (env (.m 1 (⟨483, [1]⟩ : Lin))) (env (.n 107)) (env (.n 139)) (env (.n 123)) (V (.E 7 0 (5))) (V (.E 7 0 (7))) (V (.E 7 0 (6))) (V (.E 7 0 (8))) (V (.A 7 0 (8))) (V (.A 7 0 (6))) (V (.A 7 0 (7))) (V (.A 7 0 (9))) (V (.KW 7 0 8)) (V (.W 7 0 8)) (V (.R 7 8)) ((inp 480)) ((inp 481)) ((inp 482)) ((inp 483)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_218 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 218) = V (.E 6 0 (5)))
    (h1 : env (.n 186) = V (.E 6 0 (7)))
    (h2 : env (.n 202) = V (.E 6 0 (6)))
    (h3 : env (.n 170) = V (.E 6 0 (8)))
    (h4 : env (.n 106) = V (.A 6 0 (8)))
    (h5 : env (.n 138) = V (.A 6 0 (6)))
    (h6 : env (.n 122) = V (.A 6 0 (7)))
    (h7 : env (.m 1 (⟨416, [1]⟩ : Lin)) = (inp 416).zeroExtend 32)
    (h8 : env (.m 1 (⟨417, [1]⟩ : Lin)) = (inp 417).zeroExtend 32)
    (h9 : env (.m 1 (⟨418, [1]⟩ : Lin)) = (inp 418).zeroExtend 32)
    (h10 : env (.m 1 (⟨419, [1]⟩ : Lin)) = (inp 419).zeroExtend 32)
    (h11 : V (.A 6 0 (9)) = (V (.E 6 0 (5)) + Sigma1 (V (.E 6 0 (8))) + Ch (V (.E 6 0 (8))) (V (.E 6 0 (7))) (V (.E 6 0 (6))) + V (.KW 6 0 8)) + (Sigma0 (V (.A 6 0 (8))) + Maj (V (.A 6 0 (8))) (V (.A 6 0 (7))) (V (.A 6 0 (6)))))
    (h12 : V (.KW 6 0 8) = 3624381080#32 + V (.W 6 0 8))
    (h13 : V (.W 6 0 8) = bswap (V (.R 6 8)))
    (h14 : V (.R 6 8) = ((((0 : Word) ||| (inp 416).zeroExtend 32 <<< 0) ||| (inp 417).zeroExtend 32 <<< 8) ||| (inp 418).zeroExtend 32 <<< 16) ||| (inp 419).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 218)) (.xor (.and (.xor (.var (.n 186)) (.var (.n 202))) (.var (.n 170))) (.var (.n 202)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 170)) 5) (.shl (.var (.n 170)) 27)) (.var (.n 170))) 6) (.shl (.xor (.or (.shr (.var (.n 170)) 5) (.shl (.var (.n 170)) 27)) (.var (.n 170))) 26)) (.or (.shr (.var (.n 170)) 25) (.shl (.var (.n 170)) 7)))) (.or (.and (.var (.n 106)) (.var (.n 138))) (.and (.xor (.var (.n 106)) (.var (.n 138))) (.var (.n 122))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 106)) 11) (.shl (.var (.n 106)) 21)) (.var (.n 106))) 2) (.shl (.xor (.or (.shr (.var (.n 106)) 11) (.shl (.var (.n 106)) 21)) (.var (.n 106))) 30)) (.or (.shr (.var (.n 106)) 22) (.shl (.var (.n 106)) 10)))) = V (.A 6 0 (9)) :=
  shape20 (env (.n 218)) (env (.n 186)) (env (.n 202)) (env (.n 170)) (env (.m 1 (⟨416, [1]⟩ : Lin))) (env (.m 1 (⟨417, [1]⟩ : Lin))) (env (.m 1 (⟨418, [1]⟩ : Lin))) (env (.m 1 (⟨419, [1]⟩ : Lin))) (env (.n 106)) (env (.n 138)) (env (.n 122)) (V (.E 6 0 (5))) (V (.E 6 0 (7))) (V (.E 6 0 (6))) (V (.E 6 0 (8))) (V (.A 6 0 (8))) (V (.A 6 0 (6))) (V (.A 6 0 (7))) (V (.A 6 0 (9))) (V (.KW 6 0 8)) (V (.W 6 0 8)) (V (.R 6 8)) ((inp 416)) ((inp 417)) ((inp 418)) ((inp 419)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_217 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 217) = V (.E 5 0 (5)))
    (h1 : env (.n 185) = V (.E 5 0 (7)))
    (h2 : env (.n 201) = V (.E 5 0 (6)))
    (h3 : env (.n 169) = V (.E 5 0 (8)))
    (h4 : env (.n 105) = V (.A 5 0 (8)))
    (h5 : env (.n 137) = V (.A 5 0 (6)))
    (h6 : env (.n 121) = V (.A 5 0 (7)))
    (h7 : env (.m 1 (⟨352, [1]⟩ : Lin)) = (inp 352).zeroExtend 32)
    (h8 : env (.m 1 (⟨353, [1]⟩ : Lin)) = (inp 353).zeroExtend 32)
    (h9 : env (.m 1 (⟨354, [1]⟩ : Lin)) = (inp 354).zeroExtend 32)
    (h10 : env (.m 1 (⟨355, [1]⟩ : Lin)) = (inp 355).zeroExtend 32)
    (h11 : V (.A 5 0 (9)) = (V (.E 5 0 (5)) + Sigma1 (V (.E 5 0 (8))) + Ch (V (.E 5 0 (8))) (V (.E 5 0 (7))) (V (.E 5 0 (6))) + V (.KW 5 0 8)) + (Sigma0 (V (.A 5 0 (8))) + Maj (V (.A 5 0 (8))) (V (.A 5 0 (7))) (V (.A 5 0 (6)))))
    (h12 : V (.KW 5 0 8) = 3624381080#32 + V (.W 5 0 8))
    (h13 : V (.W 5 0 8) = bswap (V (.R 5 8)))
    (h14 : V (.R 5 8) = ((((0 : Word) ||| (inp 352).zeroExtend 32 <<< 0) ||| (inp 353).zeroExtend 32 <<< 8) ||| (inp 354).zeroExtend 32 <<< 16) ||| (inp 355).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 217)) (.xor (.and (.xor (.var (.n 185)) (.var (.n 201))) (.var (.n 169))) (.var (.n 201)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 169)) 5) (.shl (.var (.n 169)) 27)) (.var (.n 169))) 6) (.shl (.xor (.or (.shr (.var (.n 169)) 5) (.shl (.var (.n 169)) 27)) (.var (.n 169))) 26)) (.or (.shr (.var (.n 169)) 25) (.shl (.var (.n 169)) 7)))) (.or (.and (.var (.n 105)) (.var (.n 137))) (.and (.xor (.var (.n 105)) (.var (.n 137))) (.var (.n 121))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 105)) 11) (.shl (.var (.n 105)) 21)) (.var (.n 105))) 2) (.shl (.xor (.or (.shr (.var (.n 105)) 11) (.shl (.var (.n 105)) 21)) (.var (.n 105))) 30)) (.or (.shr (.var (.n 105)) 22) (.shl (.var (.n 105)) 10)))) = V (.A 5 0 (9)) :=
  shape20 (env (.n 217)) (env (.n 185)) (env (.n 201)) (env (.n 169)) (env (.m 1 (⟨352, [1]⟩ : Lin))) (env (.m 1 (⟨353, [1]⟩ : Lin))) (env (.m 1 (⟨354, [1]⟩ : Lin))) (env (.m 1 (⟨355, [1]⟩ : Lin))) (env (.n 105)) (env (.n 137)) (env (.n 121)) (V (.E 5 0 (5))) (V (.E 5 0 (7))) (V (.E 5 0 (6))) (V (.E 5 0 (8))) (V (.A 5 0 (8))) (V (.A 5 0 (6))) (V (.A 5 0 (7))) (V (.A 5 0 (9))) (V (.KW 5 0 8)) (V (.W 5 0 8)) (V (.R 5 8)) ((inp 352)) ((inp 353)) ((inp 354)) ((inp 355)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_216 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 216) = V (.E 4 0 (5)))
    (h1 : env (.n 184) = V (.E 4 0 (7)))
    (h2 : env (.n 200) = V (.E 4 0 (6)))
    (h3 : env (.n 168) = V (.E 4 0 (8)))
    (h4 : env (.n 104) = V (.A 4 0 (8)))
    (h5 : env (.n 136) = V (.A 4 0 (6)))
    (h6 : env (.n 120) = V (.A 4 0 (7)))
    (h7 : env (.m 1 (⟨288, [1]⟩ : Lin)) = (inp 288).zeroExtend 32)
    (h8 : env (.m 1 (⟨289, [1]⟩ : Lin)) = (inp 289).zeroExtend 32)
    (h9 : env (.m 1 (⟨290, [1]⟩ : Lin)) = (inp 290).zeroExtend 32)
    (h10 : env (.m 1 (⟨291, [1]⟩ : Lin)) = (inp 291).zeroExtend 32)
    (h11 : V (.A 4 0 (9)) = (V (.E 4 0 (5)) + Sigma1 (V (.E 4 0 (8))) + Ch (V (.E 4 0 (8))) (V (.E 4 0 (7))) (V (.E 4 0 (6))) + V (.KW 4 0 8)) + (Sigma0 (V (.A 4 0 (8))) + Maj (V (.A 4 0 (8))) (V (.A 4 0 (7))) (V (.A 4 0 (6)))))
    (h12 : V (.KW 4 0 8) = 3624381080#32 + V (.W 4 0 8))
    (h13 : V (.W 4 0 8) = bswap (V (.R 4 8)))
    (h14 : V (.R 4 8) = ((((0 : Word) ||| (inp 288).zeroExtend 32 <<< 0) ||| (inp 289).zeroExtend 32 <<< 8) ||| (inp 290).zeroExtend 32 <<< 16) ||| (inp 291).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 216)) (.xor (.and (.xor (.var (.n 184)) (.var (.n 200))) (.var (.n 168))) (.var (.n 200)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 168)) 5) (.shl (.var (.n 168)) 27)) (.var (.n 168))) 6) (.shl (.xor (.or (.shr (.var (.n 168)) 5) (.shl (.var (.n 168)) 27)) (.var (.n 168))) 26)) (.or (.shr (.var (.n 168)) 25) (.shl (.var (.n 168)) 7)))) (.or (.and (.var (.n 104)) (.var (.n 136))) (.and (.xor (.var (.n 104)) (.var (.n 136))) (.var (.n 120))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 104)) 11) (.shl (.var (.n 104)) 21)) (.var (.n 104))) 2) (.shl (.xor (.or (.shr (.var (.n 104)) 11) (.shl (.var (.n 104)) 21)) (.var (.n 104))) 30)) (.or (.shr (.var (.n 104)) 22) (.shl (.var (.n 104)) 10)))) = V (.A 4 0 (9)) :=
  shape20 (env (.n 216)) (env (.n 184)) (env (.n 200)) (env (.n 168)) (env (.m 1 (⟨288, [1]⟩ : Lin))) (env (.m 1 (⟨289, [1]⟩ : Lin))) (env (.m 1 (⟨290, [1]⟩ : Lin))) (env (.m 1 (⟨291, [1]⟩ : Lin))) (env (.n 104)) (env (.n 136)) (env (.n 120)) (V (.E 4 0 (5))) (V (.E 4 0 (7))) (V (.E 4 0 (6))) (V (.E 4 0 (8))) (V (.A 4 0 (8))) (V (.A 4 0 (6))) (V (.A 4 0 (7))) (V (.A 4 0 (9))) (V (.KW 4 0 8)) (V (.W 4 0 8)) (V (.R 4 8)) ((inp 288)) ((inp 289)) ((inp 290)) ((inp 291)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 215) = V (.E 3 0 (5)))
    (h1 : env (.n 183) = V (.E 3 0 (7)))
    (h2 : env (.n 199) = V (.E 3 0 (6)))
    (h3 : env (.n 167) = V (.E 3 0 (8)))
    (h4 : env (.n 103) = V (.A 3 0 (8)))
    (h5 : env (.n 135) = V (.A 3 0 (6)))
    (h6 : env (.n 119) = V (.A 3 0 (7)))
    (h7 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h8 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h9 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h10 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h11 : V (.A 3 0 (9)) = (V (.E 3 0 (5)) + Sigma1 (V (.E 3 0 (8))) + Ch (V (.E 3 0 (8))) (V (.E 3 0 (7))) (V (.E 3 0 (6))) + V (.KW 3 0 8)) + (Sigma0 (V (.A 3 0 (8))) + Maj (V (.A 3 0 (8))) (V (.A 3 0 (7))) (V (.A 3 0 (6)))))
    (h12 : V (.KW 3 0 8) = 3624381080#32 + V (.W 3 0 8))
    (h13 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h14 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 215)) (.xor (.and (.xor (.var (.n 183)) (.var (.n 199))) (.var (.n 167))) (.var (.n 199)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 167)) 5) (.shl (.var (.n 167)) 27)) (.var (.n 167))) 6) (.shl (.xor (.or (.shr (.var (.n 167)) 5) (.shl (.var (.n 167)) 27)) (.var (.n 167))) 26)) (.or (.shr (.var (.n 167)) 25) (.shl (.var (.n 167)) 7)))) (.or (.and (.var (.n 103)) (.var (.n 135))) (.and (.xor (.var (.n 103)) (.var (.n 135))) (.var (.n 119))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 11) (.shl (.var (.n 103)) 21)) (.var (.n 103))) 2) (.shl (.xor (.or (.shr (.var (.n 103)) 11) (.shl (.var (.n 103)) 21)) (.var (.n 103))) 30)) (.or (.shr (.var (.n 103)) 22) (.shl (.var (.n 103)) 10)))) = V (.A 3 0 (9)) :=
  shape20 (env (.n 215)) (env (.n 183)) (env (.n 199)) (env (.n 167)) (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (env (.n 103)) (env (.n 135)) (env (.n 119)) (V (.E 3 0 (5))) (V (.E 3 0 (7))) (V (.E 3 0 (6))) (V (.E 3 0 (8))) (V (.A 3 0 (8))) (V (.A 3 0 (6))) (V (.A 3 0 (7))) (V (.A 3 0 (9))) (V (.KW 3 0 8)) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.E 2 0 (5)))
    (h1 : env (.n 182) = V (.E 2 0 (7)))
    (h2 : env (.n 198) = V (.E 2 0 (6)))
    (h3 : env (.n 166) = V (.E 2 0 (8)))
    (h4 : env (.n 102) = V (.A 2 0 (8)))
    (h5 : env (.n 134) = V (.A 2 0 (6)))
    (h6 : env (.n 118) = V (.A 2 0 (7)))
    (h7 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h8 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h9 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h10 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h11 : V (.A 2 0 (9)) = (V (.E 2 0 (5)) + Sigma1 (V (.E 2 0 (8))) + Ch (V (.E 2 0 (8))) (V (.E 2 0 (7))) (V (.E 2 0 (6))) + V (.KW 2 0 8)) + (Sigma0 (V (.A 2 0 (8))) + Maj (V (.A 2 0 (8))) (V (.A 2 0 (7))) (V (.A 2 0 (6)))))
    (h12 : V (.KW 2 0 8) = 3624381080#32 + V (.W 2 0 8))
    (h13 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h14 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 214)) (.xor (.and (.xor (.var (.n 182)) (.var (.n 198))) (.var (.n 166))) (.var (.n 198)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 166)) 5) (.shl (.var (.n 166)) 27)) (.var (.n 166))) 6) (.shl (.xor (.or (.shr (.var (.n 166)) 5) (.shl (.var (.n 166)) 27)) (.var (.n 166))) 26)) (.or (.shr (.var (.n 166)) 25) (.shl (.var (.n 166)) 7)))) (.or (.and (.var (.n 102)) (.var (.n 134))) (.and (.xor (.var (.n 102)) (.var (.n 134))) (.var (.n 118))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 11) (.shl (.var (.n 102)) 21)) (.var (.n 102))) 2) (.shl (.xor (.or (.shr (.var (.n 102)) 11) (.shl (.var (.n 102)) 21)) (.var (.n 102))) 30)) (.or (.shr (.var (.n 102)) 22) (.shl (.var (.n 102)) 10)))) = V (.A 2 0 (9)) :=
  shape20 (env (.n 214)) (env (.n 182)) (env (.n 198)) (env (.n 166)) (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (env (.n 102)) (env (.n 134)) (env (.n 118)) (V (.E 2 0 (5))) (V (.E 2 0 (7))) (V (.E 2 0 (6))) (V (.E 2 0 (8))) (V (.A 2 0 (8))) (V (.A 2 0 (6))) (V (.A 2 0 (7))) (V (.A 2 0 (9))) (V (.KW 2 0 8)) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 213) = V (.E 1 0 (5)))
    (h1 : env (.n 181) = V (.E 1 0 (7)))
    (h2 : env (.n 197) = V (.E 1 0 (6)))
    (h3 : env (.n 165) = V (.E 1 0 (8)))
    (h4 : env (.n 101) = V (.A 1 0 (8)))
    (h5 : env (.n 133) = V (.A 1 0 (6)))
    (h6 : env (.n 117) = V (.A 1 0 (7)))
    (h7 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h8 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h9 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h10 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h11 : V (.A 1 0 (9)) = (V (.E 1 0 (5)) + Sigma1 (V (.E 1 0 (8))) + Ch (V (.E 1 0 (8))) (V (.E 1 0 (7))) (V (.E 1 0 (6))) + V (.KW 1 0 8)) + (Sigma0 (V (.A 1 0 (8))) + Maj (V (.A 1 0 (8))) (V (.A 1 0 (7))) (V (.A 1 0 (6)))))
    (h12 : V (.KW 1 0 8) = 3624381080#32 + V (.W 1 0 8))
    (h13 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h14 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 213)) (.xor (.and (.xor (.var (.n 181)) (.var (.n 197))) (.var (.n 165))) (.var (.n 197)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 165)) 5) (.shl (.var (.n 165)) 27)) (.var (.n 165))) 6) (.shl (.xor (.or (.shr (.var (.n 165)) 5) (.shl (.var (.n 165)) 27)) (.var (.n 165))) 26)) (.or (.shr (.var (.n 165)) 25) (.shl (.var (.n 165)) 7)))) (.or (.and (.var (.n 101)) (.var (.n 133))) (.and (.xor (.var (.n 101)) (.var (.n 133))) (.var (.n 117))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 11) (.shl (.var (.n 101)) 21)) (.var (.n 101))) 2) (.shl (.xor (.or (.shr (.var (.n 101)) 11) (.shl (.var (.n 101)) 21)) (.var (.n 101))) 30)) (.or (.shr (.var (.n 101)) 22) (.shl (.var (.n 101)) 10)))) = V (.A 1 0 (9)) :=
  shape20 (env (.n 213)) (env (.n 181)) (env (.n 197)) (env (.n 165)) (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (env (.n 101)) (env (.n 133)) (env (.n 117)) (V (.E 1 0 (5))) (V (.E 1 0 (7))) (V (.E 1 0 (6))) (V (.E 1 0 (8))) (V (.A 1 0 (8))) (V (.A 1 0 (6))) (V (.A 1 0 (7))) (V (.A 1 0 (9))) (V (.KW 1 0 8)) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.E 0 0 (5)))
    (h1 : env (.n 180) = V (.E 0 0 (7)))
    (h2 : env (.n 196) = V (.E 0 0 (6)))
    (h3 : env (.n 164) = V (.E 0 0 (8)))
    (h4 : env (.n 100) = V (.A 0 0 (8)))
    (h5 : env (.n 132) = V (.A 0 0 (6)))
    (h6 : env (.n 116) = V (.A 0 0 (7)))
    (h7 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h8 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h9 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h10 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h11 : V (.A 0 0 (9)) = (V (.E 0 0 (5)) + Sigma1 (V (.E 0 0 (8))) + Ch (V (.E 0 0 (8))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) + V (.KW 0 0 8)) + (Sigma0 (V (.A 0 0 (8))) + Maj (V (.A 0 0 (8))) (V (.A 0 0 (7))) (V (.A 0 0 (6)))))
    (h12 : V (.KW 0 0 8) = 3624381080#32 + V (.W 0 0 8))
    (h13 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h14 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 212)) (.xor (.and (.xor (.var (.n 180)) (.var (.n 196))) (.var (.n 164))) (.var (.n 196)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 164)) 5) (.shl (.var (.n 164)) 27)) (.var (.n 164))) 6) (.shl (.xor (.or (.shr (.var (.n 164)) 5) (.shl (.var (.n 164)) 27)) (.var (.n 164))) 26)) (.or (.shr (.var (.n 164)) 25) (.shl (.var (.n 164)) 7)))) (.or (.and (.var (.n 100)) (.var (.n 132))) (.and (.xor (.var (.n 100)) (.var (.n 132))) (.var (.n 116))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 11) (.shl (.var (.n 100)) 21)) (.var (.n 100))) 2) (.shl (.xor (.or (.shr (.var (.n 100)) 11) (.shl (.var (.n 100)) 21)) (.var (.n 100))) 30)) (.or (.shr (.var (.n 100)) 22) (.shl (.var (.n 100)) 10)))) = V (.A 0 0 (9)) :=
  shape20 (env (.n 212)) (env (.n 180)) (env (.n 196)) (env (.n 164)) (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (env (.n 100)) (env (.n 132)) (env (.n 116)) (V (.E 0 0 (5))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) (V (.E 0 0 (8))) (V (.A 0 0 (8))) (V (.A 0 0 (6))) (V (.A 0 0 (7))) (V (.A 0 0 (9))) (V (.KW 0 0 8)) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_155 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 155) = V (.A 7 0 (5)))
    (h1 : env (.n 219) = V (.E 7 0 (5)))
    (h2 : env (.n 187) = V (.E 7 0 (7)))
    (h3 : env (.n 203) = V (.E 7 0 (6)))
    (h4 : env (.n 171) = V (.E 7 0 (8)))
    (h5 : env (.m 1 (⟨480, [1]⟩ : Lin)) = (inp 480).zeroExtend 32)
    (h6 : env (.m 1 (⟨481, [1]⟩ : Lin)) = (inp 481).zeroExtend 32)
    (h7 : env (.m 1 (⟨482, [1]⟩ : Lin)) = (inp 482).zeroExtend 32)
    (h8 : env (.m 1 (⟨483, [1]⟩ : Lin)) = (inp 483).zeroExtend 32)
    (h9 : V (.E 7 0 (9)) = V (.A 7 0 (5)) + (V (.E 7 0 (5)) + Sigma1 (V (.E 7 0 (8))) + Ch (V (.E 7 0 (8))) (V (.E 7 0 (7))) (V (.E 7 0 (6))) + V (.KW 7 0 8)))
    (h10 : V (.KW 7 0 8) = 3624381080#32 + V (.W 7 0 8))
    (h11 : V (.W 7 0 8) = bswap (V (.R 7 8)))
    (h12 : V (.R 7 8) = ((((0 : Word) ||| (inp 480).zeroExtend 32 <<< 0) ||| (inp 481).zeroExtend 32 <<< 8) ||| (inp 482).zeroExtend 32 <<< 16) ||| (inp 483).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 155)) (.add (.add (.add (.var (.n 219)) (.xor (.and (.xor (.var (.n 187)) (.var (.n 203))) (.var (.n 171))) (.var (.n 203)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨480, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨481, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨482, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨483, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 171)) 5) (.shl (.var (.n 171)) 27)) (.var (.n 171))) 6) (.shl (.xor (.or (.shr (.var (.n 171)) 5) (.shl (.var (.n 171)) 27)) (.var (.n 171))) 26)) (.or (.shr (.var (.n 171)) 25) (.shl (.var (.n 171)) 7))))) = V (.E 7 0 (9)) :=
  shape21 (env (.n 155)) (env (.n 219)) (env (.n 187)) (env (.n 203)) (env (.n 171)) (env (.m 1 (⟨480, [1]⟩ : Lin))) (env (.m 1 (⟨481, [1]⟩ : Lin))) (env (.m 1 (⟨482, [1]⟩ : Lin))) (env (.m 1 (⟨483, [1]⟩ : Lin))) (V (.A 7 0 (5))) (V (.E 7 0 (5))) (V (.E 7 0 (7))) (V (.E 7 0 (6))) (V (.E 7 0 (8))) (V (.E 7 0 (9))) (V (.KW 7 0 8)) (V (.W 7 0 8)) (V (.R 7 8)) ((inp 480)) ((inp 481)) ((inp 482)) ((inp 483)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_154 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 154) = V (.A 6 0 (5)))
    (h1 : env (.n 218) = V (.E 6 0 (5)))
    (h2 : env (.n 186) = V (.E 6 0 (7)))
    (h3 : env (.n 202) = V (.E 6 0 (6)))
    (h4 : env (.n 170) = V (.E 6 0 (8)))
    (h5 : env (.m 1 (⟨416, [1]⟩ : Lin)) = (inp 416).zeroExtend 32)
    (h6 : env (.m 1 (⟨417, [1]⟩ : Lin)) = (inp 417).zeroExtend 32)
    (h7 : env (.m 1 (⟨418, [1]⟩ : Lin)) = (inp 418).zeroExtend 32)
    (h8 : env (.m 1 (⟨419, [1]⟩ : Lin)) = (inp 419).zeroExtend 32)
    (h9 : V (.E 6 0 (9)) = V (.A 6 0 (5)) + (V (.E 6 0 (5)) + Sigma1 (V (.E 6 0 (8))) + Ch (V (.E 6 0 (8))) (V (.E 6 0 (7))) (V (.E 6 0 (6))) + V (.KW 6 0 8)))
    (h10 : V (.KW 6 0 8) = 3624381080#32 + V (.W 6 0 8))
    (h11 : V (.W 6 0 8) = bswap (V (.R 6 8)))
    (h12 : V (.R 6 8) = ((((0 : Word) ||| (inp 416).zeroExtend 32 <<< 0) ||| (inp 417).zeroExtend 32 <<< 8) ||| (inp 418).zeroExtend 32 <<< 16) ||| (inp 419).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 154)) (.add (.add (.add (.var (.n 218)) (.xor (.and (.xor (.var (.n 186)) (.var (.n 202))) (.var (.n 170))) (.var (.n 202)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨416, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨417, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨418, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨419, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 170)) 5) (.shl (.var (.n 170)) 27)) (.var (.n 170))) 6) (.shl (.xor (.or (.shr (.var (.n 170)) 5) (.shl (.var (.n 170)) 27)) (.var (.n 170))) 26)) (.or (.shr (.var (.n 170)) 25) (.shl (.var (.n 170)) 7))))) = V (.E 6 0 (9)) :=
  shape21 (env (.n 154)) (env (.n 218)) (env (.n 186)) (env (.n 202)) (env (.n 170)) (env (.m 1 (⟨416, [1]⟩ : Lin))) (env (.m 1 (⟨417, [1]⟩ : Lin))) (env (.m 1 (⟨418, [1]⟩ : Lin))) (env (.m 1 (⟨419, [1]⟩ : Lin))) (V (.A 6 0 (5))) (V (.E 6 0 (5))) (V (.E 6 0 (7))) (V (.E 6 0 (6))) (V (.E 6 0 (8))) (V (.E 6 0 (9))) (V (.KW 6 0 8)) (V (.W 6 0 8)) (V (.R 6 8)) ((inp 416)) ((inp 417)) ((inp 418)) ((inp 419)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_153 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 153) = V (.A 5 0 (5)))
    (h1 : env (.n 217) = V (.E 5 0 (5)))
    (h2 : env (.n 185) = V (.E 5 0 (7)))
    (h3 : env (.n 201) = V (.E 5 0 (6)))
    (h4 : env (.n 169) = V (.E 5 0 (8)))
    (h5 : env (.m 1 (⟨352, [1]⟩ : Lin)) = (inp 352).zeroExtend 32)
    (h6 : env (.m 1 (⟨353, [1]⟩ : Lin)) = (inp 353).zeroExtend 32)
    (h7 : env (.m 1 (⟨354, [1]⟩ : Lin)) = (inp 354).zeroExtend 32)
    (h8 : env (.m 1 (⟨355, [1]⟩ : Lin)) = (inp 355).zeroExtend 32)
    (h9 : V (.E 5 0 (9)) = V (.A 5 0 (5)) + (V (.E 5 0 (5)) + Sigma1 (V (.E 5 0 (8))) + Ch (V (.E 5 0 (8))) (V (.E 5 0 (7))) (V (.E 5 0 (6))) + V (.KW 5 0 8)))
    (h10 : V (.KW 5 0 8) = 3624381080#32 + V (.W 5 0 8))
    (h11 : V (.W 5 0 8) = bswap (V (.R 5 8)))
    (h12 : V (.R 5 8) = ((((0 : Word) ||| (inp 352).zeroExtend 32 <<< 0) ||| (inp 353).zeroExtend 32 <<< 8) ||| (inp 354).zeroExtend 32 <<< 16) ||| (inp 355).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 153)) (.add (.add (.add (.var (.n 217)) (.xor (.and (.xor (.var (.n 185)) (.var (.n 201))) (.var (.n 169))) (.var (.n 201)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨352, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨353, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨354, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨355, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 169)) 5) (.shl (.var (.n 169)) 27)) (.var (.n 169))) 6) (.shl (.xor (.or (.shr (.var (.n 169)) 5) (.shl (.var (.n 169)) 27)) (.var (.n 169))) 26)) (.or (.shr (.var (.n 169)) 25) (.shl (.var (.n 169)) 7))))) = V (.E 5 0 (9)) :=
  shape21 (env (.n 153)) (env (.n 217)) (env (.n 185)) (env (.n 201)) (env (.n 169)) (env (.m 1 (⟨352, [1]⟩ : Lin))) (env (.m 1 (⟨353, [1]⟩ : Lin))) (env (.m 1 (⟨354, [1]⟩ : Lin))) (env (.m 1 (⟨355, [1]⟩ : Lin))) (V (.A 5 0 (5))) (V (.E 5 0 (5))) (V (.E 5 0 (7))) (V (.E 5 0 (6))) (V (.E 5 0 (8))) (V (.E 5 0 (9))) (V (.KW 5 0 8)) (V (.W 5 0 8)) (V (.R 5 8)) ((inp 352)) ((inp 353)) ((inp 354)) ((inp 355)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_152 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 152) = V (.A 4 0 (5)))
    (h1 : env (.n 216) = V (.E 4 0 (5)))
    (h2 : env (.n 184) = V (.E 4 0 (7)))
    (h3 : env (.n 200) = V (.E 4 0 (6)))
    (h4 : env (.n 168) = V (.E 4 0 (8)))
    (h5 : env (.m 1 (⟨288, [1]⟩ : Lin)) = (inp 288).zeroExtend 32)
    (h6 : env (.m 1 (⟨289, [1]⟩ : Lin)) = (inp 289).zeroExtend 32)
    (h7 : env (.m 1 (⟨290, [1]⟩ : Lin)) = (inp 290).zeroExtend 32)
    (h8 : env (.m 1 (⟨291, [1]⟩ : Lin)) = (inp 291).zeroExtend 32)
    (h9 : V (.E 4 0 (9)) = V (.A 4 0 (5)) + (V (.E 4 0 (5)) + Sigma1 (V (.E 4 0 (8))) + Ch (V (.E 4 0 (8))) (V (.E 4 0 (7))) (V (.E 4 0 (6))) + V (.KW 4 0 8)))
    (h10 : V (.KW 4 0 8) = 3624381080#32 + V (.W 4 0 8))
    (h11 : V (.W 4 0 8) = bswap (V (.R 4 8)))
    (h12 : V (.R 4 8) = ((((0 : Word) ||| (inp 288).zeroExtend 32 <<< 0) ||| (inp 289).zeroExtend 32 <<< 8) ||| (inp 290).zeroExtend 32 <<< 16) ||| (inp 291).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 152)) (.add (.add (.add (.var (.n 216)) (.xor (.and (.xor (.var (.n 184)) (.var (.n 200))) (.var (.n 168))) (.var (.n 200)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨288, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨289, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨290, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨291, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 168)) 5) (.shl (.var (.n 168)) 27)) (.var (.n 168))) 6) (.shl (.xor (.or (.shr (.var (.n 168)) 5) (.shl (.var (.n 168)) 27)) (.var (.n 168))) 26)) (.or (.shr (.var (.n 168)) 25) (.shl (.var (.n 168)) 7))))) = V (.E 4 0 (9)) :=
  shape21 (env (.n 152)) (env (.n 216)) (env (.n 184)) (env (.n 200)) (env (.n 168)) (env (.m 1 (⟨288, [1]⟩ : Lin))) (env (.m 1 (⟨289, [1]⟩ : Lin))) (env (.m 1 (⟨290, [1]⟩ : Lin))) (env (.m 1 (⟨291, [1]⟩ : Lin))) (V (.A 4 0 (5))) (V (.E 4 0 (5))) (V (.E 4 0 (7))) (V (.E 4 0 (6))) (V (.E 4 0 (8))) (V (.E 4 0 (9))) (V (.KW 4 0 8)) (V (.W 4 0 8)) (V (.R 4 8)) ((inp 288)) ((inp 289)) ((inp 290)) ((inp 291)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.A 3 0 (5)))
    (h1 : env (.n 215) = V (.E 3 0 (5)))
    (h2 : env (.n 183) = V (.E 3 0 (7)))
    (h3 : env (.n 199) = V (.E 3 0 (6)))
    (h4 : env (.n 167) = V (.E 3 0 (8)))
    (h5 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h6 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h7 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h8 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h9 : V (.E 3 0 (9)) = V (.A 3 0 (5)) + (V (.E 3 0 (5)) + Sigma1 (V (.E 3 0 (8))) + Ch (V (.E 3 0 (8))) (V (.E 3 0 (7))) (V (.E 3 0 (6))) + V (.KW 3 0 8)))
    (h10 : V (.KW 3 0 8) = 3624381080#32 + V (.W 3 0 8))
    (h11 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h12 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 151)) (.add (.add (.add (.var (.n 215)) (.xor (.and (.xor (.var (.n 183)) (.var (.n 199))) (.var (.n 167))) (.var (.n 199)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 167)) 5) (.shl (.var (.n 167)) 27)) (.var (.n 167))) 6) (.shl (.xor (.or (.shr (.var (.n 167)) 5) (.shl (.var (.n 167)) 27)) (.var (.n 167))) 26)) (.or (.shr (.var (.n 167)) 25) (.shl (.var (.n 167)) 7))))) = V (.E 3 0 (9)) :=
  shape21 (env (.n 151)) (env (.n 215)) (env (.n 183)) (env (.n 199)) (env (.n 167)) (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.A 3 0 (5))) (V (.E 3 0 (5))) (V (.E 3 0 (7))) (V (.E 3 0 (6))) (V (.E 3 0 (8))) (V (.E 3 0 (9))) (V (.KW 3 0 8)) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.A 2 0 (5)))
    (h1 : env (.n 214) = V (.E 2 0 (5)))
    (h2 : env (.n 182) = V (.E 2 0 (7)))
    (h3 : env (.n 198) = V (.E 2 0 (6)))
    (h4 : env (.n 166) = V (.E 2 0 (8)))
    (h5 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h6 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h7 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h8 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h9 : V (.E 2 0 (9)) = V (.A 2 0 (5)) + (V (.E 2 0 (5)) + Sigma1 (V (.E 2 0 (8))) + Ch (V (.E 2 0 (8))) (V (.E 2 0 (7))) (V (.E 2 0 (6))) + V (.KW 2 0 8)))
    (h10 : V (.KW 2 0 8) = 3624381080#32 + V (.W 2 0 8))
    (h11 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h12 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 150)) (.add (.add (.add (.var (.n 214)) (.xor (.and (.xor (.var (.n 182)) (.var (.n 198))) (.var (.n 166))) (.var (.n 198)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 166)) 5) (.shl (.var (.n 166)) 27)) (.var (.n 166))) 6) (.shl (.xor (.or (.shr (.var (.n 166)) 5) (.shl (.var (.n 166)) 27)) (.var (.n 166))) 26)) (.or (.shr (.var (.n 166)) 25) (.shl (.var (.n 166)) 7))))) = V (.E 2 0 (9)) :=
  shape21 (env (.n 150)) (env (.n 214)) (env (.n 182)) (env (.n 198)) (env (.n 166)) (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.A 2 0 (5))) (V (.E 2 0 (5))) (V (.E 2 0 (7))) (V (.E 2 0 (6))) (V (.E 2 0 (8))) (V (.E 2 0 (9))) (V (.KW 2 0 8)) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.A 1 0 (5)))
    (h1 : env (.n 213) = V (.E 1 0 (5)))
    (h2 : env (.n 181) = V (.E 1 0 (7)))
    (h3 : env (.n 197) = V (.E 1 0 (6)))
    (h4 : env (.n 165) = V (.E 1 0 (8)))
    (h5 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h6 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h7 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h8 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h9 : V (.E 1 0 (9)) = V (.A 1 0 (5)) + (V (.E 1 0 (5)) + Sigma1 (V (.E 1 0 (8))) + Ch (V (.E 1 0 (8))) (V (.E 1 0 (7))) (V (.E 1 0 (6))) + V (.KW 1 0 8)))
    (h10 : V (.KW 1 0 8) = 3624381080#32 + V (.W 1 0 8))
    (h11 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h12 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 149)) (.add (.add (.add (.var (.n 213)) (.xor (.and (.xor (.var (.n 181)) (.var (.n 197))) (.var (.n 165))) (.var (.n 197)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 165)) 5) (.shl (.var (.n 165)) 27)) (.var (.n 165))) 6) (.shl (.xor (.or (.shr (.var (.n 165)) 5) (.shl (.var (.n 165)) 27)) (.var (.n 165))) 26)) (.or (.shr (.var (.n 165)) 25) (.shl (.var (.n 165)) 7))))) = V (.E 1 0 (9)) :=
  shape21 (env (.n 149)) (env (.n 213)) (env (.n 181)) (env (.n 197)) (env (.n 165)) (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.A 1 0 (5))) (V (.E 1 0 (5))) (V (.E 1 0 (7))) (V (.E 1 0 (6))) (V (.E 1 0 (8))) (V (.E 1 0 (9))) (V (.KW 1 0 8)) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.A 0 0 (5)))
    (h1 : env (.n 212) = V (.E 0 0 (5)))
    (h2 : env (.n 180) = V (.E 0 0 (7)))
    (h3 : env (.n 196) = V (.E 0 0 (6)))
    (h4 : env (.n 164) = V (.E 0 0 (8)))
    (h5 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h6 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h7 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h8 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h9 : V (.E 0 0 (9)) = V (.A 0 0 (5)) + (V (.E 0 0 (5)) + Sigma1 (V (.E 0 0 (8))) + Ch (V (.E 0 0 (8))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) + V (.KW 0 0 8)))
    (h10 : V (.KW 0 0 8) = 3624381080#32 + V (.W 0 0 8))
    (h11 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h12 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 148)) (.add (.add (.add (.var (.n 212)) (.xor (.and (.xor (.var (.n 180)) (.var (.n 196))) (.var (.n 164))) (.var (.n 196)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 3624381080))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 164)) 5) (.shl (.var (.n 164)) 27)) (.var (.n 164))) 6) (.shl (.xor (.or (.shr (.var (.n 164)) 5) (.shl (.var (.n 164)) 27)) (.var (.n 164))) 26)) (.or (.shr (.var (.n 164)) 25) (.shl (.var (.n 164)) 7))))) = V (.E 0 0 (9)) :=
  shape21 (env (.n 148)) (env (.n 212)) (env (.n 180)) (env (.n 196)) (env (.n 164)) (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.A 0 0 (5))) (V (.E 0 0 (5))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) (V (.E 0 0 (8))) (V (.E 0 0 (9))) (V (.KW 0 0 8)) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem step15 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L15) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 86 K15)) L16 := by
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
  exact invC_of_trees inp env _ T15 L16 (slice_trees_mem prog 4 _ _ 86 K15 K16 T15 slice15 env)
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
      (And.intro ⟨rfl, core15_1159 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1158 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1157 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1156 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1155 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1154 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1153 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1152 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1151 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1150 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1149 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1148 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1147 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1146 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1145 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1144 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1143 (qv inp) inp env (hm 304 (by decide)) (hm 305 (by decide)) (hm 306 (by decide)) (hm 307 (by decide)) (qW_R inp 4 12 (by decide)) (qR inp 4 12)⟩
      (And.intro ⟨rfl, core15_1142 (qv inp) inp env (hm 304 (by decide)) (hm 305 (by decide)) (hm 306 (by decide)) (hm 307 (by decide)) (qW_R inp 4 12 (by decide)) (qR inp 4 12)⟩
      (And.intro ⟨rfl, core15_1141 (qv inp) inp env (hm 304 (by decide)) (hm 305 (by decide)) (hm 306 (by decide)) (hm 307 (by decide)) (qW_R inp 4 12 (by decide)) (qR inp 4 12)⟩
      (And.intro ⟨rfl, core15_1140 (qv inp) inp env (hm 304 (by decide)) (hm 305 (by decide)) (hm 306 (by decide)) (hm 307 (by decide)) (qW_R inp 4 12 (by decide)) (qR inp 4 12)⟩
      (And.intro ⟨rfl, core15_1139 (qv inp) inp env (hm 368 (by decide)) (hm 369 (by decide)) (hm 370 (by decide)) (hm 371 (by decide)) (qW_R inp 5 12 (by decide)) (qR inp 5 12)⟩
      (And.intro ⟨rfl, core15_1138 (qv inp) inp env (hm 368 (by decide)) (hm 369 (by decide)) (hm 370 (by decide)) (hm 371 (by decide)) (qW_R inp 5 12 (by decide)) (qR inp 5 12)⟩
      (And.intro ⟨rfl, core15_1137 (qv inp) inp env (hm 368 (by decide)) (hm 369 (by decide)) (hm 370 (by decide)) (hm 371 (by decide)) (qW_R inp 5 12 (by decide)) (qR inp 5 12)⟩
      (And.intro ⟨rfl, core15_1136 (qv inp) inp env (hm 368 (by decide)) (hm 369 (by decide)) (hm 370 (by decide)) (hm 371 (by decide)) (qW_R inp 5 12 (by decide)) (qR inp 5 12)⟩
      (And.intro ⟨rfl, core15_1135 (qv inp) inp env (hm 432 (by decide)) (hm 433 (by decide)) (hm 434 (by decide)) (hm 435 (by decide)) (qW_R inp 6 12 (by decide)) (qR inp 6 12)⟩
      (And.intro ⟨rfl, core15_1134 (qv inp) inp env (hm 432 (by decide)) (hm 433 (by decide)) (hm 434 (by decide)) (hm 435 (by decide)) (qW_R inp 6 12 (by decide)) (qR inp 6 12)⟩
      (And.intro ⟨rfl, core15_1133 (qv inp) inp env (hm 432 (by decide)) (hm 433 (by decide)) (hm 434 (by decide)) (hm 435 (by decide)) (qW_R inp 6 12 (by decide)) (qR inp 6 12)⟩
      (And.intro ⟨rfl, core15_1132 (qv inp) inp env (hm 432 (by decide)) (hm 433 (by decide)) (hm 434 (by decide)) (hm 435 (by decide)) (qW_R inp 6 12 (by decide)) (qR inp 6 12)⟩
      (And.intro ⟨rfl, core15_1131 (qv inp) inp env (hm 496 (by decide)) (hm 497 (by decide)) (hm 498 (by decide)) (hm 499 (by decide)) (qW_R inp 7 12 (by decide)) (qR inp 7 12)⟩
      (And.intro ⟨rfl, core15_1130 (qv inp) inp env (hm 496 (by decide)) (hm 497 (by decide)) (hm 498 (by decide)) (hm 499 (by decide)) (qW_R inp 7 12 (by decide)) (qR inp 7 12)⟩
      (And.intro ⟨rfl, core15_1129 (qv inp) inp env (hm 496 (by decide)) (hm 497 (by decide)) (hm 498 (by decide)) (hm 499 (by decide)) (qW_R inp 7 12 (by decide)) (qR inp 7 12)⟩
      (And.intro ⟨rfl, core15_1128 (qv inp) inp env (hm 496 (by decide)) (hm 497 (by decide)) (hm 498 (by decide)) (hm 499 (by decide)) (qW_R inp 7 12 (by decide)) (qR inp 7 12)⟩
      (And.intro ⟨rfl, core15_1127 (qv inp) inp env (hm 52 (by decide)) (hm 53 (by decide)) (hm 54 (by decide)) (hm 55 (by decide)) (qW_R inp 0 13 (by decide)) (qR inp 0 13)⟩
      (And.intro ⟨rfl, core15_1126 (qv inp) inp env (hm 52 (by decide)) (hm 53 (by decide)) (hm 54 (by decide)) (hm 55 (by decide)) (qW_R inp 0 13 (by decide)) (qR inp 0 13)⟩
      (And.intro ⟨rfl, core15_1125 (qv inp) inp env (hm 52 (by decide)) (hm 53 (by decide)) (hm 54 (by decide)) (hm 55 (by decide)) (qW_R inp 0 13 (by decide)) (qR inp 0 13)⟩
      (And.intro ⟨rfl, core15_1124 (qv inp) inp env (hm 52 (by decide)) (hm 53 (by decide)) (hm 54 (by decide)) (hm 55 (by decide)) (qW_R inp 0 13 (by decide)) (qR inp 0 13)⟩
      (And.intro ⟨rfl, core15_1123 (qv inp) inp env (hm 116 (by decide)) (hm 117 (by decide)) (hm 118 (by decide)) (hm 119 (by decide)) (qW_R inp 1 13 (by decide)) (qR inp 1 13)⟩
      (And.intro ⟨rfl, core15_1122 (qv inp) inp env (hm 116 (by decide)) (hm 117 (by decide)) (hm 118 (by decide)) (hm 119 (by decide)) (qW_R inp 1 13 (by decide)) (qR inp 1 13)⟩
      (And.intro ⟨rfl, core15_1121 (qv inp) inp env (hm 116 (by decide)) (hm 117 (by decide)) (hm 118 (by decide)) (hm 119 (by decide)) (qW_R inp 1 13 (by decide)) (qR inp 1 13)⟩
      (And.intro ⟨rfl, core15_1120 (qv inp) inp env (hm 116 (by decide)) (hm 117 (by decide)) (hm 118 (by decide)) (hm 119 (by decide)) (qW_R inp 1 13 (by decide)) (qR inp 1 13)⟩
      (And.intro ⟨rfl, core15_1119 (qv inp) inp env (hm 180 (by decide)) (hm 181 (by decide)) (hm 182 (by decide)) (hm 183 (by decide)) (qW_R inp 2 13 (by decide)) (qR inp 2 13)⟩
      (And.intro ⟨rfl, core15_1118 (qv inp) inp env (hm 180 (by decide)) (hm 181 (by decide)) (hm 182 (by decide)) (hm 183 (by decide)) (qW_R inp 2 13 (by decide)) (qR inp 2 13)⟩
      (And.intro ⟨rfl, core15_1117 (qv inp) inp env (hm 180 (by decide)) (hm 181 (by decide)) (hm 182 (by decide)) (hm 183 (by decide)) (qW_R inp 2 13 (by decide)) (qR inp 2 13)⟩
      (And.intro ⟨rfl, core15_1116 (qv inp) inp env (hm 180 (by decide)) (hm 181 (by decide)) (hm 182 (by decide)) (hm 183 (by decide)) (qW_R inp 2 13 (by decide)) (qR inp 2 13)⟩
      (And.intro ⟨rfl, core15_1115 (qv inp) inp env (hm 244 (by decide)) (hm 245 (by decide)) (hm 246 (by decide)) (hm 247 (by decide)) (qW_R inp 3 13 (by decide)) (qR inp 3 13)⟩
      (And.intro ⟨rfl, core15_1114 (qv inp) inp env (hm 244 (by decide)) (hm 245 (by decide)) (hm 246 (by decide)) (hm 247 (by decide)) (qW_R inp 3 13 (by decide)) (qR inp 3 13)⟩
      (And.intro ⟨rfl, core15_1113 (qv inp) inp env (hm 244 (by decide)) (hm 245 (by decide)) (hm 246 (by decide)) (hm 247 (by decide)) (qW_R inp 3 13 (by decide)) (qR inp 3 13)⟩
      (And.intro ⟨rfl, core15_1112 (qv inp) inp env (hm 244 (by decide)) (hm 245 (by decide)) (hm 246 (by decide)) (hm 247 (by decide)) (qW_R inp 3 13 (by decide)) (qR inp 3 13)⟩
      (And.intro ⟨rfl, core15_1111 (qv inp) inp env (hm 308 (by decide)) (hm 309 (by decide)) (hm 310 (by decide)) (hm 311 (by decide)) (qW_R inp 4 13 (by decide)) (qR inp 4 13)⟩
      (And.intro ⟨rfl, core15_1110 (qv inp) inp env (hm 308 (by decide)) (hm 309 (by decide)) (hm 310 (by decide)) (hm 311 (by decide)) (qW_R inp 4 13 (by decide)) (qR inp 4 13)⟩
      (And.intro ⟨rfl, core15_1109 (qv inp) inp env (hm 308 (by decide)) (hm 309 (by decide)) (hm 310 (by decide)) (hm 311 (by decide)) (qW_R inp 4 13 (by decide)) (qR inp 4 13)⟩
      (And.intro ⟨rfl, core15_1108 (qv inp) inp env (hm 308 (by decide)) (hm 309 (by decide)) (hm 310 (by decide)) (hm 311 (by decide)) (qW_R inp 4 13 (by decide)) (qR inp 4 13)⟩
      (And.intro ⟨rfl, core15_1107 (qv inp) inp env (hm 372 (by decide)) (hm 373 (by decide)) (hm 374 (by decide)) (hm 375 (by decide)) (qW_R inp 5 13 (by decide)) (qR inp 5 13)⟩
      (And.intro ⟨rfl, core15_1106 (qv inp) inp env (hm 372 (by decide)) (hm 373 (by decide)) (hm 374 (by decide)) (hm 375 (by decide)) (qW_R inp 5 13 (by decide)) (qR inp 5 13)⟩
      (And.intro ⟨rfl, core15_1105 (qv inp) inp env (hm 372 (by decide)) (hm 373 (by decide)) (hm 374 (by decide)) (hm 375 (by decide)) (qW_R inp 5 13 (by decide)) (qR inp 5 13)⟩
      (And.intro ⟨rfl, core15_1104 (qv inp) inp env (hm 372 (by decide)) (hm 373 (by decide)) (hm 374 (by decide)) (hm 375 (by decide)) (qW_R inp 5 13 (by decide)) (qR inp 5 13)⟩
      (And.intro ⟨rfl, core15_1103 (qv inp) inp env (hm 436 (by decide)) (hm 437 (by decide)) (hm 438 (by decide)) (hm 439 (by decide)) (qW_R inp 6 13 (by decide)) (qR inp 6 13)⟩
      (And.intro ⟨rfl, core15_1102 (qv inp) inp env (hm 436 (by decide)) (hm 437 (by decide)) (hm 438 (by decide)) (hm 439 (by decide)) (qW_R inp 6 13 (by decide)) (qR inp 6 13)⟩
      (And.intro ⟨rfl, core15_1101 (qv inp) inp env (hm 436 (by decide)) (hm 437 (by decide)) (hm 438 (by decide)) (hm 439 (by decide)) (qW_R inp 6 13 (by decide)) (qR inp 6 13)⟩
      (And.intro ⟨rfl, core15_1100 (qv inp) inp env (hm 436 (by decide)) (hm 437 (by decide)) (hm 438 (by decide)) (hm 439 (by decide)) (qW_R inp 6 13 (by decide)) (qR inp 6 13)⟩
      (And.intro ⟨rfl, core15_1099 (qv inp) inp env (hm 500 (by decide)) (hm 501 (by decide)) (hm 502 (by decide)) (hm 503 (by decide)) (qW_R inp 7 13 (by decide)) (qR inp 7 13)⟩
      (And.intro ⟨rfl, core15_1098 (qv inp) inp env (hm 500 (by decide)) (hm 501 (by decide)) (hm 502 (by decide)) (hm 503 (by decide)) (qW_R inp 7 13 (by decide)) (qR inp 7 13)⟩
      (And.intro ⟨rfl, core15_1097 (qv inp) inp env (hm 500 (by decide)) (hm 501 (by decide)) (hm 502 (by decide)) (hm 503 (by decide)) (qW_R inp 7 13 (by decide)) (qR inp 7 13)⟩
      (And.intro ⟨rfl, core15_1096 (qv inp) inp env (hm 500 (by decide)) (hm 501 (by decide)) (hm 502 (by decide)) (hm 503 (by decide)) (qW_R inp 7 13 (by decide)) (qR inp 7 13)⟩
      (And.intro ⟨rfl, core15_1095 (qv inp) inp env (hm 56 (by decide)) (hm 57 (by decide)) (hm 58 (by decide)) (hm 59 (by decide)) (qW_R inp 0 14 (by decide)) (qR inp 0 14)⟩
      (And.intro ⟨rfl, core15_1094 (qv inp) inp env (hm 56 (by decide)) (hm 57 (by decide)) (hm 58 (by decide)) (hm 59 (by decide)) (qW_R inp 0 14 (by decide)) (qR inp 0 14)⟩
      (And.intro ⟨rfl, core15_1093 (qv inp) inp env (hm 56 (by decide)) (hm 57 (by decide)) (hm 58 (by decide)) (hm 59 (by decide)) (qW_R inp 0 14 (by decide)) (qR inp 0 14)⟩
      (And.intro ⟨rfl, core15_1092 (qv inp) inp env (hm 56 (by decide)) (hm 57 (by decide)) (hm 58 (by decide)) (hm 59 (by decide)) (qW_R inp 0 14 (by decide)) (qR inp 0 14)⟩
      (And.intro ⟨rfl, core15_1091 (qv inp) inp env (hm 120 (by decide)) (hm 121 (by decide)) (hm 122 (by decide)) (hm 123 (by decide)) (qW_R inp 1 14 (by decide)) (qR inp 1 14)⟩
      (And.intro ⟨rfl, core15_1090 (qv inp) inp env (hm 120 (by decide)) (hm 121 (by decide)) (hm 122 (by decide)) (hm 123 (by decide)) (qW_R inp 1 14 (by decide)) (qR inp 1 14)⟩
      (And.intro ⟨rfl, core15_1089 (qv inp) inp env (hm 120 (by decide)) (hm 121 (by decide)) (hm 122 (by decide)) (hm 123 (by decide)) (qW_R inp 1 14 (by decide)) (qR inp 1 14)⟩
      (And.intro ⟨rfl, core15_1088 (qv inp) inp env (hm 120 (by decide)) (hm 121 (by decide)) (hm 122 (by decide)) (hm 123 (by decide)) (qW_R inp 1 14 (by decide)) (qR inp 1 14)⟩
      (And.intro ⟨rfl, core15_1087 (qv inp) inp env (hm 184 (by decide)) (hm 185 (by decide)) (hm 186 (by decide)) (hm 187 (by decide)) (qW_R inp 2 14 (by decide)) (qR inp 2 14)⟩
      (And.intro ⟨rfl, core15_1086 (qv inp) inp env (hm 184 (by decide)) (hm 185 (by decide)) (hm 186 (by decide)) (hm 187 (by decide)) (qW_R inp 2 14 (by decide)) (qR inp 2 14)⟩
      (And.intro ⟨rfl, core15_1085 (qv inp) inp env (hm 184 (by decide)) (hm 185 (by decide)) (hm 186 (by decide)) (hm 187 (by decide)) (qW_R inp 2 14 (by decide)) (qR inp 2 14)⟩
      (And.intro ⟨rfl, core15_1084 (qv inp) inp env (hm 184 (by decide)) (hm 185 (by decide)) (hm 186 (by decide)) (hm 187 (by decide)) (qW_R inp 2 14 (by decide)) (qR inp 2 14)⟩
      (And.intro ⟨rfl, core15_1083 (qv inp) inp env (hm 248 (by decide)) (hm 249 (by decide)) (hm 250 (by decide)) (hm 251 (by decide)) (qW_R inp 3 14 (by decide)) (qR inp 3 14)⟩
      (And.intro ⟨rfl, core15_1082 (qv inp) inp env (hm 248 (by decide)) (hm 249 (by decide)) (hm 250 (by decide)) (hm 251 (by decide)) (qW_R inp 3 14 (by decide)) (qR inp 3 14)⟩
      (And.intro ⟨rfl, core15_1081 (qv inp) inp env (hm 248 (by decide)) (hm 249 (by decide)) (hm 250 (by decide)) (hm 251 (by decide)) (qW_R inp 3 14 (by decide)) (qR inp 3 14)⟩
      (And.intro ⟨rfl, core15_1080 (qv inp) inp env (hm 248 (by decide)) (hm 249 (by decide)) (hm 250 (by decide)) (hm 251 (by decide)) (qW_R inp 3 14 (by decide)) (qR inp 3 14)⟩
      (And.intro ⟨rfl, core15_1079 (qv inp) inp env (hm 312 (by decide)) (hm 313 (by decide)) (hm 314 (by decide)) (hm 315 (by decide)) (qW_R inp 4 14 (by decide)) (qR inp 4 14)⟩
      (And.intro ⟨rfl, core15_1078 (qv inp) inp env (hm 312 (by decide)) (hm 313 (by decide)) (hm 314 (by decide)) (hm 315 (by decide)) (qW_R inp 4 14 (by decide)) (qR inp 4 14)⟩
      (And.intro ⟨rfl, core15_1077 (qv inp) inp env (hm 312 (by decide)) (hm 313 (by decide)) (hm 314 (by decide)) (hm 315 (by decide)) (qW_R inp 4 14 (by decide)) (qR inp 4 14)⟩
      (And.intro ⟨rfl, core15_1076 (qv inp) inp env (hm 312 (by decide)) (hm 313 (by decide)) (hm 314 (by decide)) (hm 315 (by decide)) (qW_R inp 4 14 (by decide)) (qR inp 4 14)⟩
      (And.intro ⟨rfl, core15_1075 (qv inp) inp env (hm 376 (by decide)) (hm 377 (by decide)) (hm 378 (by decide)) (hm 379 (by decide)) (qW_R inp 5 14 (by decide)) (qR inp 5 14)⟩
      (And.intro ⟨rfl, core15_1074 (qv inp) inp env (hm 376 (by decide)) (hm 377 (by decide)) (hm 378 (by decide)) (hm 379 (by decide)) (qW_R inp 5 14 (by decide)) (qR inp 5 14)⟩
      (And.intro ⟨rfl, core15_1073 (qv inp) inp env (hm 376 (by decide)) (hm 377 (by decide)) (hm 378 (by decide)) (hm 379 (by decide)) (qW_R inp 5 14 (by decide)) (qR inp 5 14)⟩
      (And.intro ⟨rfl, core15_1072 (qv inp) inp env (hm 376 (by decide)) (hm 377 (by decide)) (hm 378 (by decide)) (hm 379 (by decide)) (qW_R inp 5 14 (by decide)) (qR inp 5 14)⟩
      (And.intro ⟨rfl, core15_1071 (qv inp) inp env (hm 440 (by decide)) (hm 441 (by decide)) (hm 442 (by decide)) (hm 443 (by decide)) (qW_R inp 6 14 (by decide)) (qR inp 6 14)⟩
      (And.intro ⟨rfl, core15_1070 (qv inp) inp env (hm 440 (by decide)) (hm 441 (by decide)) (hm 442 (by decide)) (hm 443 (by decide)) (qW_R inp 6 14 (by decide)) (qR inp 6 14)⟩
      (And.intro ⟨rfl, core15_1069 (qv inp) inp env (hm 440 (by decide)) (hm 441 (by decide)) (hm 442 (by decide)) (hm 443 (by decide)) (qW_R inp 6 14 (by decide)) (qR inp 6 14)⟩
      (And.intro ⟨rfl, core15_1068 (qv inp) inp env (hm 440 (by decide)) (hm 441 (by decide)) (hm 442 (by decide)) (hm 443 (by decide)) (qW_R inp 6 14 (by decide)) (qR inp 6 14)⟩
      (And.intro ⟨rfl, core15_1067 (qv inp) inp env (hm 504 (by decide)) (hm 505 (by decide)) (hm 506 (by decide)) (hm 507 (by decide)) (qW_R inp 7 14 (by decide)) (qR inp 7 14)⟩
      (And.intro ⟨rfl, core15_1066 (qv inp) inp env (hm 504 (by decide)) (hm 505 (by decide)) (hm 506 (by decide)) (hm 507 (by decide)) (qW_R inp 7 14 (by decide)) (qR inp 7 14)⟩
      (And.intro ⟨rfl, core15_1065 (qv inp) inp env (hm 504 (by decide)) (hm 505 (by decide)) (hm 506 (by decide)) (hm 507 (by decide)) (qW_R inp 7 14 (by decide)) (qR inp 7 14)⟩
      (And.intro ⟨rfl, core15_1064 (qv inp) inp env (hm 504 (by decide)) (hm 505 (by decide)) (hm 506 (by decide)) (hm 507 (by decide)) (qW_R inp 7 14 (by decide)) (qR inp 7 14)⟩
      (And.intro ⟨rfl, core15_1063 (qv inp) inp env (hm 60 (by decide)) (hm 61 (by decide)) (hm 62 (by decide)) (hm 63 (by decide)) (qW_R inp 0 15 (by decide)) (qR inp 0 15)⟩
      (And.intro ⟨rfl, core15_1062 (qv inp) inp env (hm 60 (by decide)) (hm 61 (by decide)) (hm 62 (by decide)) (hm 63 (by decide)) (qW_R inp 0 15 (by decide)) (qR inp 0 15)⟩
      (And.intro ⟨rfl, core15_1061 (qv inp) inp env (hm 60 (by decide)) (hm 61 (by decide)) (hm 62 (by decide)) (hm 63 (by decide)) (qW_R inp 0 15 (by decide)) (qR inp 0 15)⟩
      (And.intro ⟨rfl, core15_1060 (qv inp) inp env (hm 60 (by decide)) (hm 61 (by decide)) (hm 62 (by decide)) (hm 63 (by decide)) (qW_R inp 0 15 (by decide)) (qR inp 0 15)⟩
      (And.intro ⟨rfl, core15_1059 (qv inp) inp env (hm 124 (by decide)) (hm 125 (by decide)) (hm 126 (by decide)) (hm 127 (by decide)) (qW_R inp 1 15 (by decide)) (qR inp 1 15)⟩
      (And.intro ⟨rfl, core15_1058 (qv inp) inp env (hm 124 (by decide)) (hm 125 (by decide)) (hm 126 (by decide)) (hm 127 (by decide)) (qW_R inp 1 15 (by decide)) (qR inp 1 15)⟩
      (And.intro ⟨rfl, core15_1057 (qv inp) inp env (hm 124 (by decide)) (hm 125 (by decide)) (hm 126 (by decide)) (hm 127 (by decide)) (qW_R inp 1 15 (by decide)) (qR inp 1 15)⟩
      (And.intro ⟨rfl, core15_1056 (qv inp) inp env (hm 124 (by decide)) (hm 125 (by decide)) (hm 126 (by decide)) (hm 127 (by decide)) (qW_R inp 1 15 (by decide)) (qR inp 1 15)⟩
      (And.intro ⟨rfl, core15_1055 (qv inp) inp env (hm 188 (by decide)) (hm 189 (by decide)) (hm 190 (by decide)) (hm 191 (by decide)) (qW_R inp 2 15 (by decide)) (qR inp 2 15)⟩
      (And.intro ⟨rfl, core15_1054 (qv inp) inp env (hm 188 (by decide)) (hm 189 (by decide)) (hm 190 (by decide)) (hm 191 (by decide)) (qW_R inp 2 15 (by decide)) (qR inp 2 15)⟩
      (And.intro ⟨rfl, core15_1053 (qv inp) inp env (hm 188 (by decide)) (hm 189 (by decide)) (hm 190 (by decide)) (hm 191 (by decide)) (qW_R inp 2 15 (by decide)) (qR inp 2 15)⟩
      (And.intro ⟨rfl, core15_1052 (qv inp) inp env (hm 188 (by decide)) (hm 189 (by decide)) (hm 190 (by decide)) (hm 191 (by decide)) (qW_R inp 2 15 (by decide)) (qR inp 2 15)⟩
      (And.intro ⟨rfl, core15_1051 (qv inp) inp env (hm 252 (by decide)) (hm 253 (by decide)) (hm 254 (by decide)) (hm 255 (by decide)) (qW_R inp 3 15 (by decide)) (qR inp 3 15)⟩
      (And.intro ⟨rfl, core15_1050 (qv inp) inp env (hm 252 (by decide)) (hm 253 (by decide)) (hm 254 (by decide)) (hm 255 (by decide)) (qW_R inp 3 15 (by decide)) (qR inp 3 15)⟩
      (And.intro ⟨rfl, core15_1049 (qv inp) inp env (hm 252 (by decide)) (hm 253 (by decide)) (hm 254 (by decide)) (hm 255 (by decide)) (qW_R inp 3 15 (by decide)) (qR inp 3 15)⟩
      (And.intro ⟨rfl, core15_1048 (qv inp) inp env (hm 252 (by decide)) (hm 253 (by decide)) (hm 254 (by decide)) (hm 255 (by decide)) (qW_R inp 3 15 (by decide)) (qR inp 3 15)⟩
      (And.intro ⟨rfl, core15_1047 (qv inp) inp env (hm 316 (by decide)) (hm 317 (by decide)) (hm 318 (by decide)) (hm 319 (by decide)) (qW_R inp 4 15 (by decide)) (qR inp 4 15)⟩
      (And.intro ⟨rfl, core15_1046 (qv inp) inp env (hm 316 (by decide)) (hm 317 (by decide)) (hm 318 (by decide)) (hm 319 (by decide)) (qW_R inp 4 15 (by decide)) (qR inp 4 15)⟩
      (And.intro ⟨rfl, core15_1045 (qv inp) inp env (hm 316 (by decide)) (hm 317 (by decide)) (hm 318 (by decide)) (hm 319 (by decide)) (qW_R inp 4 15 (by decide)) (qR inp 4 15)⟩
      (And.intro ⟨rfl, core15_1044 (qv inp) inp env (hm 316 (by decide)) (hm 317 (by decide)) (hm 318 (by decide)) (hm 319 (by decide)) (qW_R inp 4 15 (by decide)) (qR inp 4 15)⟩
      (And.intro ⟨rfl, core15_1043 (qv inp) inp env (hm 380 (by decide)) (hm 381 (by decide)) (hm 382 (by decide)) (hm 383 (by decide)) (qW_R inp 5 15 (by decide)) (qR inp 5 15)⟩
      (And.intro ⟨rfl, core15_1042 (qv inp) inp env (hm 380 (by decide)) (hm 381 (by decide)) (hm 382 (by decide)) (hm 383 (by decide)) (qW_R inp 5 15 (by decide)) (qR inp 5 15)⟩
      (And.intro ⟨rfl, core15_1041 (qv inp) inp env (hm 380 (by decide)) (hm 381 (by decide)) (hm 382 (by decide)) (hm 383 (by decide)) (qW_R inp 5 15 (by decide)) (qR inp 5 15)⟩
      (And.intro ⟨rfl, core15_1040 (qv inp) inp env (hm 380 (by decide)) (hm 381 (by decide)) (hm 382 (by decide)) (hm 383 (by decide)) (qW_R inp 5 15 (by decide)) (qR inp 5 15)⟩
      (And.intro ⟨rfl, core15_1039 (qv inp) inp env (hm 444 (by decide)) (hm 445 (by decide)) (hm 446 (by decide)) (hm 447 (by decide)) (qW_R inp 6 15 (by decide)) (qR inp 6 15)⟩
      (And.intro ⟨rfl, core15_1038 (qv inp) inp env (hm 444 (by decide)) (hm 445 (by decide)) (hm 446 (by decide)) (hm 447 (by decide)) (qW_R inp 6 15 (by decide)) (qR inp 6 15)⟩
      (And.intro ⟨rfl, core15_1037 (qv inp) inp env (hm 444 (by decide)) (hm 445 (by decide)) (hm 446 (by decide)) (hm 447 (by decide)) (qW_R inp 6 15 (by decide)) (qR inp 6 15)⟩
      (And.intro ⟨rfl, core15_1036 (qv inp) inp env (hm 444 (by decide)) (hm 445 (by decide)) (hm 446 (by decide)) (hm 447 (by decide)) (qW_R inp 6 15 (by decide)) (qR inp 6 15)⟩
      (And.intro ⟨rfl, core15_1035 (qv inp) inp env (hm 508 (by decide)) (hm 509 (by decide)) (hm 510 (by decide)) (hm 511 (by decide)) (qW_R inp 7 15 (by decide)) (qR inp 7 15)⟩
      (And.intro ⟨rfl, core15_1034 (qv inp) inp env (hm 508 (by decide)) (hm 509 (by decide)) (hm 510 (by decide)) (hm 511 (by decide)) (qW_R inp 7 15 (by decide)) (qR inp 7 15)⟩
      (And.intro ⟨rfl, core15_1033 (qv inp) inp env (hm 508 (by decide)) (hm 509 (by decide)) (hm 510 (by decide)) (hm 511 (by decide)) (qW_R inp 7 15 (by decide)) (qR inp 7 15)⟩
      (And.intro ⟨rfl, core15_1032 (qv inp) inp env (hm 508 (by decide)) (hm 509 (by decide)) (hm 510 (by decide)) (hm 511 (by decide)) (qW_R inp 7 15 (by decide)) (qR inp 7 15)⟩
      (And.intro ⟨rfl, core15_1031 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core15_1030 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core15_1029 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core15_1028 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core15_1027 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core15_1026 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core15_1025 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core15_1024 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core15_1023 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core15_1022 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core15_1021 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core15_1020 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core15_1019 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core15_1018 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core15_1017 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core15_1016 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core15_1015 (qv inp) inp env (hm 288 (by decide)) (hm 289 (by decide)) (hm 290 (by decide)) (hm 291 (by decide)) (qW_R inp 4 8 (by decide)) (qR inp 4 8)⟩
      (And.intro ⟨rfl, core15_1014 (qv inp) inp env (hm 288 (by decide)) (hm 289 (by decide)) (hm 290 (by decide)) (hm 291 (by decide)) (qW_R inp 4 8 (by decide)) (qR inp 4 8)⟩
      (And.intro ⟨rfl, core15_1013 (qv inp) inp env (hm 288 (by decide)) (hm 289 (by decide)) (hm 290 (by decide)) (hm 291 (by decide)) (qW_R inp 4 8 (by decide)) (qR inp 4 8)⟩
      (And.intro ⟨rfl, core15_1012 (qv inp) inp env (hm 288 (by decide)) (hm 289 (by decide)) (hm 290 (by decide)) (hm 291 (by decide)) (qW_R inp 4 8 (by decide)) (qR inp 4 8)⟩
      (And.intro ⟨rfl, core15_1011 (qv inp) inp env (hm 352 (by decide)) (hm 353 (by decide)) (hm 354 (by decide)) (hm 355 (by decide)) (qW_R inp 5 8 (by decide)) (qR inp 5 8)⟩
      (And.intro ⟨rfl, core15_1010 (qv inp) inp env (hm 352 (by decide)) (hm 353 (by decide)) (hm 354 (by decide)) (hm 355 (by decide)) (qW_R inp 5 8 (by decide)) (qR inp 5 8)⟩
      (And.intro ⟨rfl, core15_1009 (qv inp) inp env (hm 352 (by decide)) (hm 353 (by decide)) (hm 354 (by decide)) (hm 355 (by decide)) (qW_R inp 5 8 (by decide)) (qR inp 5 8)⟩
      (And.intro ⟨rfl, core15_1008 (qv inp) inp env (hm 352 (by decide)) (hm 353 (by decide)) (hm 354 (by decide)) (hm 355 (by decide)) (qW_R inp 5 8 (by decide)) (qR inp 5 8)⟩
      (And.intro ⟨rfl, core15_1007 (qv inp) inp env (hm 416 (by decide)) (hm 417 (by decide)) (hm 418 (by decide)) (hm 419 (by decide)) (qW_R inp 6 8 (by decide)) (qR inp 6 8)⟩
      (And.intro ⟨rfl, core15_1006 (qv inp) inp env (hm 416 (by decide)) (hm 417 (by decide)) (hm 418 (by decide)) (hm 419 (by decide)) (qW_R inp 6 8 (by decide)) (qR inp 6 8)⟩
      (And.intro ⟨rfl, core15_1005 (qv inp) inp env (hm 416 (by decide)) (hm 417 (by decide)) (hm 418 (by decide)) (hm 419 (by decide)) (qW_R inp 6 8 (by decide)) (qR inp 6 8)⟩
      (And.intro ⟨rfl, core15_1004 (qv inp) inp env (hm 416 (by decide)) (hm 417 (by decide)) (hm 418 (by decide)) (hm 419 (by decide)) (qW_R inp 6 8 (by decide)) (qR inp 6 8)⟩
      (And.intro ⟨rfl, core15_1003 (qv inp) inp env (hm 480 (by decide)) (hm 481 (by decide)) (hm 482 (by decide)) (hm 483 (by decide)) (qW_R inp 7 8 (by decide)) (qR inp 7 8)⟩
      (And.intro ⟨rfl, core15_1002 (qv inp) inp env (hm 480 (by decide)) (hm 481 (by decide)) (hm 482 (by decide)) (hm 483 (by decide)) (qW_R inp 7 8 (by decide)) (qR inp 7 8)⟩
      (And.intro ⟨rfl, core15_1001 (qv inp) inp env (hm 480 (by decide)) (hm 481 (by decide)) (hm 482 (by decide)) (hm 483 (by decide)) (qW_R inp 7 8 (by decide)) (qR inp 7 8)⟩
      (And.intro ⟨rfl, core15_1000 (qv inp) inp env (hm 480 (by decide)) (hm 481 (by decide)) (hm 482 (by decide)) (hm 483 (by decide)) (qW_R inp 7 8 (by decide)) (qR inp 7 8)⟩
      (And.intro ⟨rfl, core15_283 (qv inp) inp env (hm 492 (by decide)) (hm 493 (by decide)) (hm 494 (by decide)) (hm 495 (by decide)) (qW_R inp 7 11 (by decide)) (qR inp 7 11)⟩
      (And.intro ⟨rfl, core15_282 (qv inp) inp env (hm 428 (by decide)) (hm 429 (by decide)) (hm 430 (by decide)) (hm 431 (by decide)) (qW_R inp 6 11 (by decide)) (qR inp 6 11)⟩
      (And.intro ⟨rfl, core15_281 (qv inp) inp env (hm 364 (by decide)) (hm 365 (by decide)) (hm 366 (by decide)) (hm 367 (by decide)) (qW_R inp 5 11 (by decide)) (qR inp 5 11)⟩
      (And.intro ⟨rfl, core15_280 (qv inp) inp env (hm 300 (by decide)) (hm 301 (by decide)) (hm 302 (by decide)) (hm 303 (by decide)) (qW_R inp 4 11 (by decide)) (qR inp 4 11)⟩
      (And.intro ⟨rfl, core15_279 (qv inp) inp env (hm 236 (by decide)) (hm 237 (by decide)) (hm 238 (by decide)) (hm 239 (by decide)) (qW_R inp 3 11 (by decide)) (qR inp 3 11)⟩
      (And.intro ⟨rfl, core15_278 (qv inp) inp env (hm 172 (by decide)) (hm 173 (by decide)) (hm 174 (by decide)) (hm 175 (by decide)) (qW_R inp 2 11 (by decide)) (qR inp 2 11)⟩
      (And.intro ⟨rfl, core15_277 (qv inp) inp env (hm 108 (by decide)) (hm 109 (by decide)) (hm 110 (by decide)) (hm 111 (by decide)) (qW_R inp 1 11 (by decide)) (qR inp 1 11)⟩
      (And.intro ⟨rfl, core15_276 (qv inp) inp env (hm 44 (by decide)) (hm 45 (by decide)) (hm 46 (by decide)) (hm 47 (by decide)) (qW_R inp 0 11 (by decide)) (qR inp 0 11)⟩
      (And.intro ⟨rfl, core15_267 (qv inp) inp env (hm 488 (by decide)) (hm 489 (by decide)) (hm 490 (by decide)) (hm 491 (by decide)) (qW_R inp 7 10 (by decide)) (qR inp 7 10)⟩
      (And.intro ⟨rfl, core15_266 (qv inp) inp env (hm 424 (by decide)) (hm 425 (by decide)) (hm 426 (by decide)) (hm 427 (by decide)) (qW_R inp 6 10 (by decide)) (qR inp 6 10)⟩
      (And.intro ⟨rfl, core15_265 (qv inp) inp env (hm 360 (by decide)) (hm 361 (by decide)) (hm 362 (by decide)) (hm 363 (by decide)) (qW_R inp 5 10 (by decide)) (qR inp 5 10)⟩
      (And.intro ⟨rfl, core15_264 (qv inp) inp env (hm 296 (by decide)) (hm 297 (by decide)) (hm 298 (by decide)) (hm 299 (by decide)) (qW_R inp 4 10 (by decide)) (qR inp 4 10)⟩
      (And.intro ⟨rfl, core15_263 (qv inp) inp env (hm 232 (by decide)) (hm 233 (by decide)) (hm 234 (by decide)) (hm 235 (by decide)) (qW_R inp 3 10 (by decide)) (qR inp 3 10)⟩
      (And.intro ⟨rfl, core15_262 (qv inp) inp env (hm 168 (by decide)) (hm 169 (by decide)) (hm 170 (by decide)) (hm 171 (by decide)) (qW_R inp 2 10 (by decide)) (qR inp 2 10)⟩
      (And.intro ⟨rfl, core15_261 (qv inp) inp env (hm 104 (by decide)) (hm 105 (by decide)) (hm 106 (by decide)) (hm 107 (by decide)) (qW_R inp 1 10 (by decide)) (qR inp 1 10)⟩
      (And.intro ⟨rfl, core15_260 (qv inp) inp env (hm 40 (by decide)) (hm 41 (by decide)) (hm 42 (by decide)) (hm 43 (by decide)) (qW_R inp 0 10 (by decide)) (qR inp 0 10)⟩
      (And.intro ⟨rfl, core15_251 (qv inp) inp env (hm 484 (by decide)) (hm 485 (by decide)) (hm 486 (by decide)) (hm 487 (by decide)) (qW_R inp 7 9 (by decide)) (qR inp 7 9)⟩
      (And.intro ⟨rfl, core15_250 (qv inp) inp env (hm 420 (by decide)) (hm 421 (by decide)) (hm 422 (by decide)) (hm 423 (by decide)) (qW_R inp 6 9 (by decide)) (qR inp 6 9)⟩
      (And.intro ⟨rfl, core15_249 (qv inp) inp env (hm 356 (by decide)) (hm 357 (by decide)) (hm 358 (by decide)) (hm 359 (by decide)) (qW_R inp 5 9 (by decide)) (qR inp 5 9)⟩
      (And.intro ⟨rfl, core15_248 (qv inp) inp env (hm 292 (by decide)) (hm 293 (by decide)) (hm 294 (by decide)) (hm 295 (by decide)) (qW_R inp 4 9 (by decide)) (qR inp 4 9)⟩
      (And.intro ⟨rfl, core15_247 (qv inp) inp env (hm 228 (by decide)) (hm 229 (by decide)) (hm 230 (by decide)) (hm 231 (by decide)) (qW_R inp 3 9 (by decide)) (qR inp 3 9)⟩
      (And.intro ⟨rfl, core15_246 (qv inp) inp env (hm 164 (by decide)) (hm 165 (by decide)) (hm 166 (by decide)) (hm 167 (by decide)) (qW_R inp 2 9 (by decide)) (qR inp 2 9)⟩
      (And.intro ⟨rfl, core15_245 (qv inp) inp env (hm 100 (by decide)) (hm 101 (by decide)) (hm 102 (by decide)) (hm 103 (by decide)) (qW_R inp 1 9 (by decide)) (qR inp 1 9)⟩
      (And.intro ⟨rfl, core15_244 (qv inp) inp env (hm 36 (by decide)) (hm 37 (by decide)) (hm 38 (by decide)) (hm 39 (by decide)) (qW_R inp 0 9 (by decide)) (qR inp 0 9)⟩
      (And.intro ⟨rfl, core15_219 (qv inp) inp env h384 h400 h392 h408 h440 h424 h432 (hm 480 (by decide)) (hm 481 (by decide)) (hm 482 (by decide)) (hm 483 (by decide)) (qA_succI inp 7 0 (8) (by decide)) ((qKW inp 7 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 7 8 (by decide)) (qR inp 7 8)⟩
      (And.intro ⟨rfl, core15_218 (qv inp) inp env h385 h401 h393 h409 h441 h425 h433 (hm 416 (by decide)) (hm 417 (by decide)) (hm 418 (by decide)) (hm 419 (by decide)) (qA_succI inp 6 0 (8) (by decide)) ((qKW inp 6 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 6 8 (by decide)) (qR inp 6 8)⟩
      (And.intro ⟨rfl, core15_217 (qv inp) inp env h386 h402 h394 h410 h442 h426 h434 (hm 352 (by decide)) (hm 353 (by decide)) (hm 354 (by decide)) (hm 355 (by decide)) (qA_succI inp 5 0 (8) (by decide)) ((qKW inp 5 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 5 8 (by decide)) (qR inp 5 8)⟩
      (And.intro ⟨rfl, core15_216 (qv inp) inp env h387 h403 h395 h411 h443 h427 h435 (hm 288 (by decide)) (hm 289 (by decide)) (hm 290 (by decide)) (hm 291 (by decide)) (qA_succI inp 4 0 (8) (by decide)) ((qKW inp 4 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 4 8 (by decide)) (qR inp 4 8)⟩
      (And.intro ⟨rfl, core15_215 (qv inp) inp env h388 h404 h396 h412 h444 h428 h436 (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qA_succI inp 3 0 (8) (by decide)) ((qKW inp 3 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core15_214 (qv inp) inp env h389 h405 h397 h413 h445 h429 h437 (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qA_succI inp 2 0 (8) (by decide)) ((qKW inp 2 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core15_213 (qv inp) inp env h390 h406 h398 h414 h446 h430 h438 (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qA_succI inp 1 0 (8) (by decide)) ((qKW inp 1 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core15_212 (qv inp) inp env h391 h407 h399 h415 h447 h431 h439 (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qA_succI inp 0 0 (8) (by decide)) ((qKW inp 0 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
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
      (And.intro ⟨rfl, core15_155 (qv inp) inp env h416 h384 h400 h392 h408 (hm 480 (by decide)) (hm 481 (by decide)) (hm 482 (by decide)) (hm 483 (by decide)) (qE_succI inp 7 0 (8) (by decide)) ((qKW inp 7 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 7 8 (by decide)) (qR inp 7 8)⟩
      (And.intro ⟨rfl, core15_154 (qv inp) inp env h417 h385 h401 h393 h409 (hm 416 (by decide)) (hm 417 (by decide)) (hm 418 (by decide)) (hm 419 (by decide)) (qE_succI inp 6 0 (8) (by decide)) ((qKW inp 6 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 6 8 (by decide)) (qR inp 6 8)⟩
      (And.intro ⟨rfl, core15_153 (qv inp) inp env h418 h386 h402 h394 h410 (hm 352 (by decide)) (hm 353 (by decide)) (hm 354 (by decide)) (hm 355 (by decide)) (qE_succI inp 5 0 (8) (by decide)) ((qKW inp 5 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 5 8 (by decide)) (qR inp 5 8)⟩
      (And.intro ⟨rfl, core15_152 (qv inp) inp env h419 h387 h403 h395 h411 (hm 288 (by decide)) (hm 289 (by decide)) (hm 290 (by decide)) (hm 291 (by decide)) (qE_succI inp 4 0 (8) (by decide)) ((qKW inp 4 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 4 8 (by decide)) (qR inp 4 8)⟩
      (And.intro ⟨rfl, core15_151 (qv inp) inp env h420 h388 h404 h396 h412 (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qE_succI inp 3 0 (8) (by decide)) ((qKW inp 3 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core15_150 (qv inp) inp env h421 h389 h405 h397 h413 (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qE_succI inp 2 0 (8) (by decide)) ((qKW inp 2 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core15_149 (qv inp) inp env h422 h390 h406 h398 h414 (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qE_succI inp 1 0 (8) (by decide)) ((qKW inp 1 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core15_148 (qv inp) inp env h423 h391 h407 h399 h415 (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qE_succI inp 0 0 (8) (by decide)) ((qKW inp 0 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
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
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
