import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D15
import Hashtree.Gen.WinAvxX4P.D14

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice15 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 55 K15 K16 T15 = true := by
  decide +kernel

theorem core15_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape0 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape0 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape0 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h1 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h2 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h3 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h4 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h5 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 12) :=
  shape0 (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5

theorem core15_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape0 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape0 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape0 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h1 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h2 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h3 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h4 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h5 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 12) :=
  shape0 (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5

theorem core15_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape0 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape0 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape0 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h1 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h2 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h3 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h4 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h5 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 12) :=
  shape0 (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5

theorem core15_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape0 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape0 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape0 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h1 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h2 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h3 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h4 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h5 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 12) :=
  shape0 (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5

theorem core15_311 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨244, [1]⟩ : Lin)) = (inp 244).zeroExtend 32)
    (h1 : env (.m 1 (⟨245, [1]⟩ : Lin)) = (inp 245).zeroExtend 32)
    (h2 : env (.m 1 (⟨246, [1]⟩ : Lin)) = (inp 246).zeroExtend 32)
    (h3 : env (.m 1 (⟨247, [1]⟩ : Lin)) = (inp 247).zeroExtend 32)
    (h4 : V (.W 3 0 13) = bswap (V (.R 3 13)))
    (h5 : V (.R 3 13) = ((((0 : Word) ||| (inp 244).zeroExtend 32 <<< 0) ||| (inp 245).zeroExtend 32 <<< 8) ||| (inp 246).zeroExtend 32 <<< 16) ||| (inp 247).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨244, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨245, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨246, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨247, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 13) :=
  shape0 (env (.m 1 (⟨244, [1]⟩ : Lin))) (env (.m 1 (⟨245, [1]⟩ : Lin))) (env (.m 1 (⟨246, [1]⟩ : Lin))) (env (.m 1 (⟨247, [1]⟩ : Lin))) (V (.W 3 0 13)) (V (.R 3 13)) ((inp 244)) ((inp 245)) ((inp 246)) ((inp 247)) h0 h1 h2 h3 h4 h5

theorem core15_310 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨180, [1]⟩ : Lin)) = (inp 180).zeroExtend 32)
    (h1 : env (.m 1 (⟨181, [1]⟩ : Lin)) = (inp 181).zeroExtend 32)
    (h2 : env (.m 1 (⟨182, [1]⟩ : Lin)) = (inp 182).zeroExtend 32)
    (h3 : env (.m 1 (⟨183, [1]⟩ : Lin)) = (inp 183).zeroExtend 32)
    (h4 : V (.W 2 0 13) = bswap (V (.R 2 13)))
    (h5 : V (.R 2 13) = ((((0 : Word) ||| (inp 180).zeroExtend 32 <<< 0) ||| (inp 181).zeroExtend 32 <<< 8) ||| (inp 182).zeroExtend 32 <<< 16) ||| (inp 183).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨180, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨181, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨182, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨183, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 13) :=
  shape0 (env (.m 1 (⟨180, [1]⟩ : Lin))) (env (.m 1 (⟨181, [1]⟩ : Lin))) (env (.m 1 (⟨182, [1]⟩ : Lin))) (env (.m 1 (⟨183, [1]⟩ : Lin))) (V (.W 2 0 13)) (V (.R 2 13)) ((inp 180)) ((inp 181)) ((inp 182)) ((inp 183)) h0 h1 h2 h3 h4 h5

theorem core15_309 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨116, [1]⟩ : Lin)) = (inp 116).zeroExtend 32)
    (h1 : env (.m 1 (⟨117, [1]⟩ : Lin)) = (inp 117).zeroExtend 32)
    (h2 : env (.m 1 (⟨118, [1]⟩ : Lin)) = (inp 118).zeroExtend 32)
    (h3 : env (.m 1 (⟨119, [1]⟩ : Lin)) = (inp 119).zeroExtend 32)
    (h4 : V (.W 1 0 13) = bswap (V (.R 1 13)))
    (h5 : V (.R 1 13) = ((((0 : Word) ||| (inp 116).zeroExtend 32 <<< 0) ||| (inp 117).zeroExtend 32 <<< 8) ||| (inp 118).zeroExtend 32 <<< 16) ||| (inp 119).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨116, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨117, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨118, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨119, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 13) :=
  shape0 (env (.m 1 (⟨116, [1]⟩ : Lin))) (env (.m 1 (⟨117, [1]⟩ : Lin))) (env (.m 1 (⟨118, [1]⟩ : Lin))) (env (.m 1 (⟨119, [1]⟩ : Lin))) (V (.W 1 0 13)) (V (.R 1 13)) ((inp 116)) ((inp 117)) ((inp 118)) ((inp 119)) h0 h1 h2 h3 h4 h5

theorem core15_308 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨52, [1]⟩ : Lin)) = (inp 52).zeroExtend 32)
    (h1 : env (.m 1 (⟨53, [1]⟩ : Lin)) = (inp 53).zeroExtend 32)
    (h2 : env (.m 1 (⟨54, [1]⟩ : Lin)) = (inp 54).zeroExtend 32)
    (h3 : env (.m 1 (⟨55, [1]⟩ : Lin)) = (inp 55).zeroExtend 32)
    (h4 : V (.W 0 0 13) = bswap (V (.R 0 13)))
    (h5 : V (.R 0 13) = ((((0 : Word) ||| (inp 52).zeroExtend 32 <<< 0) ||| (inp 53).zeroExtend 32 <<< 8) ||| (inp 54).zeroExtend 32 <<< 16) ||| (inp 55).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨52, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨53, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨54, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨55, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 13) :=
  shape0 (env (.m 1 (⟨52, [1]⟩ : Lin))) (env (.m 1 (⟨53, [1]⟩ : Lin))) (env (.m 1 (⟨54, [1]⟩ : Lin))) (env (.m 1 (⟨55, [1]⟩ : Lin))) (V (.W 0 0 13)) (V (.R 0 13)) ((inp 52)) ((inp 53)) ((inp 54)) ((inp 55)) h0 h1 h2 h3 h4 h5

theorem core15_295 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨248, [1]⟩ : Lin)) = (inp 248).zeroExtend 32)
    (h1 : env (.m 1 (⟨249, [1]⟩ : Lin)) = (inp 249).zeroExtend 32)
    (h2 : env (.m 1 (⟨250, [1]⟩ : Lin)) = (inp 250).zeroExtend 32)
    (h3 : env (.m 1 (⟨251, [1]⟩ : Lin)) = (inp 251).zeroExtend 32)
    (h4 : V (.W 3 0 14) = bswap (V (.R 3 14)))
    (h5 : V (.R 3 14) = ((((0 : Word) ||| (inp 248).zeroExtend 32 <<< 0) ||| (inp 249).zeroExtend 32 <<< 8) ||| (inp 250).zeroExtend 32 <<< 16) ||| (inp 251).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨248, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨249, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨250, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨251, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 14) :=
  shape0 (env (.m 1 (⟨248, [1]⟩ : Lin))) (env (.m 1 (⟨249, [1]⟩ : Lin))) (env (.m 1 (⟨250, [1]⟩ : Lin))) (env (.m 1 (⟨251, [1]⟩ : Lin))) (V (.W 3 0 14)) (V (.R 3 14)) ((inp 248)) ((inp 249)) ((inp 250)) ((inp 251)) h0 h1 h2 h3 h4 h5

theorem core15_294 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨184, [1]⟩ : Lin)) = (inp 184).zeroExtend 32)
    (h1 : env (.m 1 (⟨185, [1]⟩ : Lin)) = (inp 185).zeroExtend 32)
    (h2 : env (.m 1 (⟨186, [1]⟩ : Lin)) = (inp 186).zeroExtend 32)
    (h3 : env (.m 1 (⟨187, [1]⟩ : Lin)) = (inp 187).zeroExtend 32)
    (h4 : V (.W 2 0 14) = bswap (V (.R 2 14)))
    (h5 : V (.R 2 14) = ((((0 : Word) ||| (inp 184).zeroExtend 32 <<< 0) ||| (inp 185).zeroExtend 32 <<< 8) ||| (inp 186).zeroExtend 32 <<< 16) ||| (inp 187).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨184, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨185, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨186, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨187, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 14) :=
  shape0 (env (.m 1 (⟨184, [1]⟩ : Lin))) (env (.m 1 (⟨185, [1]⟩ : Lin))) (env (.m 1 (⟨186, [1]⟩ : Lin))) (env (.m 1 (⟨187, [1]⟩ : Lin))) (V (.W 2 0 14)) (V (.R 2 14)) ((inp 184)) ((inp 185)) ((inp 186)) ((inp 187)) h0 h1 h2 h3 h4 h5

theorem core15_293 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨120, [1]⟩ : Lin)) = (inp 120).zeroExtend 32)
    (h1 : env (.m 1 (⟨121, [1]⟩ : Lin)) = (inp 121).zeroExtend 32)
    (h2 : env (.m 1 (⟨122, [1]⟩ : Lin)) = (inp 122).zeroExtend 32)
    (h3 : env (.m 1 (⟨123, [1]⟩ : Lin)) = (inp 123).zeroExtend 32)
    (h4 : V (.W 1 0 14) = bswap (V (.R 1 14)))
    (h5 : V (.R 1 14) = ((((0 : Word) ||| (inp 120).zeroExtend 32 <<< 0) ||| (inp 121).zeroExtend 32 <<< 8) ||| (inp 122).zeroExtend 32 <<< 16) ||| (inp 123).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨120, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨121, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨122, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨123, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 14) :=
  shape0 (env (.m 1 (⟨120, [1]⟩ : Lin))) (env (.m 1 (⟨121, [1]⟩ : Lin))) (env (.m 1 (⟨122, [1]⟩ : Lin))) (env (.m 1 (⟨123, [1]⟩ : Lin))) (V (.W 1 0 14)) (V (.R 1 14)) ((inp 120)) ((inp 121)) ((inp 122)) ((inp 123)) h0 h1 h2 h3 h4 h5

theorem core15_292 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨56, [1]⟩ : Lin)) = (inp 56).zeroExtend 32)
    (h1 : env (.m 1 (⟨57, [1]⟩ : Lin)) = (inp 57).zeroExtend 32)
    (h2 : env (.m 1 (⟨58, [1]⟩ : Lin)) = (inp 58).zeroExtend 32)
    (h3 : env (.m 1 (⟨59, [1]⟩ : Lin)) = (inp 59).zeroExtend 32)
    (h4 : V (.W 0 0 14) = bswap (V (.R 0 14)))
    (h5 : V (.R 0 14) = ((((0 : Word) ||| (inp 56).zeroExtend 32 <<< 0) ||| (inp 57).zeroExtend 32 <<< 8) ||| (inp 58).zeroExtend 32 <<< 16) ||| (inp 59).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨56, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨57, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨58, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨59, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 14) :=
  shape0 (env (.m 1 (⟨56, [1]⟩ : Lin))) (env (.m 1 (⟨57, [1]⟩ : Lin))) (env (.m 1 (⟨58, [1]⟩ : Lin))) (env (.m 1 (⟨59, [1]⟩ : Lin))) (V (.W 0 0 14)) (V (.R 0 14)) ((inp 56)) ((inp 57)) ((inp 58)) ((inp 59)) h0 h1 h2 h3 h4 h5

theorem core15_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨252, [1]⟩ : Lin)) = (inp 252).zeroExtend 32)
    (h1 : env (.m 1 (⟨253, [1]⟩ : Lin)) = (inp 253).zeroExtend 32)
    (h2 : env (.m 1 (⟨254, [1]⟩ : Lin)) = (inp 254).zeroExtend 32)
    (h3 : env (.m 1 (⟨255, [1]⟩ : Lin)) = (inp 255).zeroExtend 32)
    (h4 : V (.W 3 0 15) = bswap (V (.R 3 15)))
    (h5 : V (.R 3 15) = ((((0 : Word) ||| (inp 252).zeroExtend 32 <<< 0) ||| (inp 253).zeroExtend 32 <<< 8) ||| (inp 254).zeroExtend 32 <<< 16) ||| (inp 255).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨252, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨253, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨254, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨255, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 15) :=
  shape0 (env (.m 1 (⟨252, [1]⟩ : Lin))) (env (.m 1 (⟨253, [1]⟩ : Lin))) (env (.m 1 (⟨254, [1]⟩ : Lin))) (env (.m 1 (⟨255, [1]⟩ : Lin))) (V (.W 3 0 15)) (V (.R 3 15)) ((inp 252)) ((inp 253)) ((inp 254)) ((inp 255)) h0 h1 h2 h3 h4 h5

theorem core15_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨188, [1]⟩ : Lin)) = (inp 188).zeroExtend 32)
    (h1 : env (.m 1 (⟨189, [1]⟩ : Lin)) = (inp 189).zeroExtend 32)
    (h2 : env (.m 1 (⟨190, [1]⟩ : Lin)) = (inp 190).zeroExtend 32)
    (h3 : env (.m 1 (⟨191, [1]⟩ : Lin)) = (inp 191).zeroExtend 32)
    (h4 : V (.W 2 0 15) = bswap (V (.R 2 15)))
    (h5 : V (.R 2 15) = ((((0 : Word) ||| (inp 188).zeroExtend 32 <<< 0) ||| (inp 189).zeroExtend 32 <<< 8) ||| (inp 190).zeroExtend 32 <<< 16) ||| (inp 191).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨188, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨189, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨190, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨191, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 15) :=
  shape0 (env (.m 1 (⟨188, [1]⟩ : Lin))) (env (.m 1 (⟨189, [1]⟩ : Lin))) (env (.m 1 (⟨190, [1]⟩ : Lin))) (env (.m 1 (⟨191, [1]⟩ : Lin))) (V (.W 2 0 15)) (V (.R 2 15)) ((inp 188)) ((inp 189)) ((inp 190)) ((inp 191)) h0 h1 h2 h3 h4 h5

theorem core15_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨124, [1]⟩ : Lin)) = (inp 124).zeroExtend 32)
    (h1 : env (.m 1 (⟨125, [1]⟩ : Lin)) = (inp 125).zeroExtend 32)
    (h2 : env (.m 1 (⟨126, [1]⟩ : Lin)) = (inp 126).zeroExtend 32)
    (h3 : env (.m 1 (⟨127, [1]⟩ : Lin)) = (inp 127).zeroExtend 32)
    (h4 : V (.W 1 0 15) = bswap (V (.R 1 15)))
    (h5 : V (.R 1 15) = ((((0 : Word) ||| (inp 124).zeroExtend 32 <<< 0) ||| (inp 125).zeroExtend 32 <<< 8) ||| (inp 126).zeroExtend 32 <<< 16) ||| (inp 127).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨124, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨125, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨126, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨127, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 15) :=
  shape0 (env (.m 1 (⟨124, [1]⟩ : Lin))) (env (.m 1 (⟨125, [1]⟩ : Lin))) (env (.m 1 (⟨126, [1]⟩ : Lin))) (env (.m 1 (⟨127, [1]⟩ : Lin))) (V (.W 1 0 15)) (V (.R 1 15)) ((inp 124)) ((inp 125)) ((inp 126)) ((inp 127)) h0 h1 h2 h3 h4 h5

theorem core15_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨60, [1]⟩ : Lin)) = (inp 60).zeroExtend 32)
    (h1 : env (.m 1 (⟨61, [1]⟩ : Lin)) = (inp 61).zeroExtend 32)
    (h2 : env (.m 1 (⟨62, [1]⟩ : Lin)) = (inp 62).zeroExtend 32)
    (h3 : env (.m 1 (⟨63, [1]⟩ : Lin)) = (inp 63).zeroExtend 32)
    (h4 : V (.W 0 0 15) = bswap (V (.R 0 15)))
    (h5 : V (.R 0 15) = ((((0 : Word) ||| (inp 60).zeroExtend 32 <<< 0) ||| (inp 61).zeroExtend 32 <<< 8) ||| (inp 62).zeroExtend 32 <<< 16) ||| (inp 63).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨60, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨61, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨62, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨63, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 15) :=
  shape0 (env (.m 1 (⟨60, [1]⟩ : Lin))) (env (.m 1 (⟨61, [1]⟩ : Lin))) (env (.m 1 (⟨62, [1]⟩ : Lin))) (env (.m 1 (⟨63, [1]⟩ : Lin))) (V (.W 0 0 15)) (V (.R 0 15)) ((inp 60)) ((inp 61)) ((inp 62)) ((inp 63)) h0 h1 h2 h3 h4 h5

theorem core15_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 215) = V (.A 3 0 (9)))
    (h1 : env (.n 151) = V (.E 3 0 (9)))
    (h2 : env (.n 119) = V (.E 3 0 (11)))
    (h3 : env (.n 135) = V (.E 3 0 (10)))
    (h4 : env (.n 103) = V (.E 3 0 (12)))
    (h5 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h6 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h7 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h8 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h9 : V (.E 3 0 (13)) = V (.A 3 0 (9)) + (V (.E 3 0 (9)) + Sigma1 (V (.E 3 0 (12))) + Ch (V (.E 3 0 (12))) (V (.E 3 0 (11))) (V (.E 3 0 (10))) + V (.KW 3 0 12)))
    (h10 : V (.KW 3 0 12) = 1925078388#32 + V (.W 3 0 12))
    (h11 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h12 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 215)) (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7))))) = V (.E 3 0 (13)) :=
  shape25 (env (.n 215)) (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (V (.A 3 0 (9))) (V (.E 3 0 (9))) (V (.E 3 0 (11))) (V (.E 3 0 (10))) (V (.E 3 0 (12))) (V (.E 3 0 (13))) (V (.KW 3 0 12)) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.A 2 0 (9)))
    (h1 : env (.n 150) = V (.E 2 0 (9)))
    (h2 : env (.n 118) = V (.E 2 0 (11)))
    (h3 : env (.n 134) = V (.E 2 0 (10)))
    (h4 : env (.n 102) = V (.E 2 0 (12)))
    (h5 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h6 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h7 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h8 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h9 : V (.E 2 0 (13)) = V (.A 2 0 (9)) + (V (.E 2 0 (9)) + Sigma1 (V (.E 2 0 (12))) + Ch (V (.E 2 0 (12))) (V (.E 2 0 (11))) (V (.E 2 0 (10))) + V (.KW 2 0 12)))
    (h10 : V (.KW 2 0 12) = 1925078388#32 + V (.W 2 0 12))
    (h11 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h12 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 214)) (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7))))) = V (.E 2 0 (13)) :=
  shape25 (env (.n 214)) (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (V (.A 2 0 (9))) (V (.E 2 0 (9))) (V (.E 2 0 (11))) (V (.E 2 0 (10))) (V (.E 2 0 (12))) (V (.E 2 0 (13))) (V (.KW 2 0 12)) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 213) = V (.A 1 0 (9)))
    (h1 : env (.n 149) = V (.E 1 0 (9)))
    (h2 : env (.n 117) = V (.E 1 0 (11)))
    (h3 : env (.n 133) = V (.E 1 0 (10)))
    (h4 : env (.n 101) = V (.E 1 0 (12)))
    (h5 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h6 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h7 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h8 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h9 : V (.E 1 0 (13)) = V (.A 1 0 (9)) + (V (.E 1 0 (9)) + Sigma1 (V (.E 1 0 (12))) + Ch (V (.E 1 0 (12))) (V (.E 1 0 (11))) (V (.E 1 0 (10))) + V (.KW 1 0 12)))
    (h10 : V (.KW 1 0 12) = 1925078388#32 + V (.W 1 0 12))
    (h11 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h12 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 213)) (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7))))) = V (.E 1 0 (13)) :=
  shape25 (env (.n 213)) (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (V (.A 1 0 (9))) (V (.E 1 0 (9))) (V (.E 1 0 (11))) (V (.E 1 0 (10))) (V (.E 1 0 (12))) (V (.E 1 0 (13))) (V (.KW 1 0 12)) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.A 0 0 (9)))
    (h1 : env (.n 148) = V (.E 0 0 (9)))
    (h2 : env (.n 116) = V (.E 0 0 (11)))
    (h3 : env (.n 132) = V (.E 0 0 (10)))
    (h4 : env (.n 100) = V (.E 0 0 (12)))
    (h5 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h6 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h7 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h8 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h9 : V (.E 0 0 (13)) = V (.A 0 0 (9)) + (V (.E 0 0 (9)) + Sigma1 (V (.E 0 0 (12))) + Ch (V (.E 0 0 (12))) (V (.E 0 0 (11))) (V (.E 0 0 (10))) + V (.KW 0 0 12)))
    (h10 : V (.KW 0 0 12) = 1925078388#32 + V (.W 0 0 12))
    (h11 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h12 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 212)) (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7))))) = V (.E 0 0 (13)) :=
  shape25 (env (.n 212)) (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (V (.A 0 0 (9))) (V (.E 0 0 (9))) (V (.E 0 0 (11))) (V (.E 0 0 (10))) (V (.E 0 0 (12))) (V (.E 0 0 (13))) (V (.KW 0 0 12)) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core15_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (9)))
    (h1 : env (.n 119) = V (.E 3 0 (11)))
    (h2 : env (.n 135) = V (.E 3 0 (10)))
    (h3 : env (.n 103) = V (.E 3 0 (12)))
    (h4 : env (.n 167) = V (.A 3 0 (12)))
    (h5 : env (.n 199) = V (.A 3 0 (10)))
    (h6 : env (.n 183) = V (.A 3 0 (11)))
    (h7 : env (.m 1 (⟨240, [1]⟩ : Lin)) = (inp 240).zeroExtend 32)
    (h8 : env (.m 1 (⟨241, [1]⟩ : Lin)) = (inp 241).zeroExtend 32)
    (h9 : env (.m 1 (⟨242, [1]⟩ : Lin)) = (inp 242).zeroExtend 32)
    (h10 : env (.m 1 (⟨243, [1]⟩ : Lin)) = (inp 243).zeroExtend 32)
    (h11 : V (.A 3 0 (13)) = (V (.E 3 0 (9)) + Sigma1 (V (.E 3 0 (12))) + Ch (V (.E 3 0 (12))) (V (.E 3 0 (11))) (V (.E 3 0 (10))) + V (.KW 3 0 12)) + (Sigma0 (V (.A 3 0 (12))) + Maj (V (.A 3 0 (12))) (V (.A 3 0 (11))) (V (.A 3 0 (10)))))
    (h12 : V (.KW 3 0 12) = 1925078388#32 + V (.W 3 0 12))
    (h13 : V (.W 3 0 12) = bswap (V (.R 3 12)))
    (h14 : V (.R 3 12) = ((((0 : Word) ||| (inp 240).zeroExtend 32 <<< 0) ||| (inp 241).zeroExtend 32 <<< 8) ||| (inp 242).zeroExtend 32 <<< 16) ||| (inp 243).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨240, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨241, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨242, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨243, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7)))) (.or (.and (.var (.n 167)) (.var (.n 199))) (.and (.xor (.var (.n 167)) (.var (.n 199))) (.var (.n 183))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 2) (.shl (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 30)) (.or (.shr (.var (.n 167)) 22) (.shl (.var (.n 167)) 10)))) = V (.A 3 0 (13)) :=
  shape26 (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.m 1 (⟨240, [1]⟩ : Lin))) (env (.m 1 (⟨241, [1]⟩ : Lin))) (env (.m 1 (⟨242, [1]⟩ : Lin))) (env (.m 1 (⟨243, [1]⟩ : Lin))) (env (.n 167)) (env (.n 199)) (env (.n 183)) (V (.E 3 0 (9))) (V (.E 3 0 (11))) (V (.E 3 0 (10))) (V (.E 3 0 (12))) (V (.A 3 0 (12))) (V (.A 3 0 (10))) (V (.A 3 0 (11))) (V (.A 3 0 (13))) (V (.KW 3 0 12)) (V (.W 3 0 12)) (V (.R 3 12)) ((inp 240)) ((inp 241)) ((inp 242)) ((inp 243)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (9)))
    (h1 : env (.n 118) = V (.E 2 0 (11)))
    (h2 : env (.n 134) = V (.E 2 0 (10)))
    (h3 : env (.n 102) = V (.E 2 0 (12)))
    (h4 : env (.n 166) = V (.A 2 0 (12)))
    (h5 : env (.n 198) = V (.A 2 0 (10)))
    (h6 : env (.n 182) = V (.A 2 0 (11)))
    (h7 : env (.m 1 (⟨176, [1]⟩ : Lin)) = (inp 176).zeroExtend 32)
    (h8 : env (.m 1 (⟨177, [1]⟩ : Lin)) = (inp 177).zeroExtend 32)
    (h9 : env (.m 1 (⟨178, [1]⟩ : Lin)) = (inp 178).zeroExtend 32)
    (h10 : env (.m 1 (⟨179, [1]⟩ : Lin)) = (inp 179).zeroExtend 32)
    (h11 : V (.A 2 0 (13)) = (V (.E 2 0 (9)) + Sigma1 (V (.E 2 0 (12))) + Ch (V (.E 2 0 (12))) (V (.E 2 0 (11))) (V (.E 2 0 (10))) + V (.KW 2 0 12)) + (Sigma0 (V (.A 2 0 (12))) + Maj (V (.A 2 0 (12))) (V (.A 2 0 (11))) (V (.A 2 0 (10)))))
    (h12 : V (.KW 2 0 12) = 1925078388#32 + V (.W 2 0 12))
    (h13 : V (.W 2 0 12) = bswap (V (.R 2 12)))
    (h14 : V (.R 2 12) = ((((0 : Word) ||| (inp 176).zeroExtend 32 <<< 0) ||| (inp 177).zeroExtend 32 <<< 8) ||| (inp 178).zeroExtend 32 <<< 16) ||| (inp 179).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨176, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨177, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨178, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨179, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7)))) (.or (.and (.var (.n 166)) (.var (.n 198))) (.and (.xor (.var (.n 166)) (.var (.n 198))) (.var (.n 182))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 2) (.shl (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 30)) (.or (.shr (.var (.n 166)) 22) (.shl (.var (.n 166)) 10)))) = V (.A 2 0 (13)) :=
  shape26 (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.m 1 (⟨176, [1]⟩ : Lin))) (env (.m 1 (⟨177, [1]⟩ : Lin))) (env (.m 1 (⟨178, [1]⟩ : Lin))) (env (.m 1 (⟨179, [1]⟩ : Lin))) (env (.n 166)) (env (.n 198)) (env (.n 182)) (V (.E 2 0 (9))) (V (.E 2 0 (11))) (V (.E 2 0 (10))) (V (.E 2 0 (12))) (V (.A 2 0 (12))) (V (.A 2 0 (10))) (V (.A 2 0 (11))) (V (.A 2 0 (13))) (V (.KW 2 0 12)) (V (.W 2 0 12)) (V (.R 2 12)) ((inp 176)) ((inp 177)) ((inp 178)) ((inp 179)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (9)))
    (h1 : env (.n 117) = V (.E 1 0 (11)))
    (h2 : env (.n 133) = V (.E 1 0 (10)))
    (h3 : env (.n 101) = V (.E 1 0 (12)))
    (h4 : env (.n 165) = V (.A 1 0 (12)))
    (h5 : env (.n 197) = V (.A 1 0 (10)))
    (h6 : env (.n 181) = V (.A 1 0 (11)))
    (h7 : env (.m 1 (⟨112, [1]⟩ : Lin)) = (inp 112).zeroExtend 32)
    (h8 : env (.m 1 (⟨113, [1]⟩ : Lin)) = (inp 113).zeroExtend 32)
    (h9 : env (.m 1 (⟨114, [1]⟩ : Lin)) = (inp 114).zeroExtend 32)
    (h10 : env (.m 1 (⟨115, [1]⟩ : Lin)) = (inp 115).zeroExtend 32)
    (h11 : V (.A 1 0 (13)) = (V (.E 1 0 (9)) + Sigma1 (V (.E 1 0 (12))) + Ch (V (.E 1 0 (12))) (V (.E 1 0 (11))) (V (.E 1 0 (10))) + V (.KW 1 0 12)) + (Sigma0 (V (.A 1 0 (12))) + Maj (V (.A 1 0 (12))) (V (.A 1 0 (11))) (V (.A 1 0 (10)))))
    (h12 : V (.KW 1 0 12) = 1925078388#32 + V (.W 1 0 12))
    (h13 : V (.W 1 0 12) = bswap (V (.R 1 12)))
    (h14 : V (.R 1 12) = ((((0 : Word) ||| (inp 112).zeroExtend 32 <<< 0) ||| (inp 113).zeroExtend 32 <<< 8) ||| (inp 114).zeroExtend 32 <<< 16) ||| (inp 115).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨112, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨113, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨114, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨115, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7)))) (.or (.and (.var (.n 165)) (.var (.n 197))) (.and (.xor (.var (.n 165)) (.var (.n 197))) (.var (.n 181))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 2) (.shl (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 30)) (.or (.shr (.var (.n 165)) 22) (.shl (.var (.n 165)) 10)))) = V (.A 1 0 (13)) :=
  shape26 (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.m 1 (⟨112, [1]⟩ : Lin))) (env (.m 1 (⟨113, [1]⟩ : Lin))) (env (.m 1 (⟨114, [1]⟩ : Lin))) (env (.m 1 (⟨115, [1]⟩ : Lin))) (env (.n 165)) (env (.n 197)) (env (.n 181)) (V (.E 1 0 (9))) (V (.E 1 0 (11))) (V (.E 1 0 (10))) (V (.E 1 0 (12))) (V (.A 1 0 (12))) (V (.A 1 0 (10))) (V (.A 1 0 (11))) (V (.A 1 0 (13))) (V (.KW 1 0 12)) (V (.W 1 0 12)) (V (.R 1 12)) ((inp 112)) ((inp 113)) ((inp 114)) ((inp 115)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core15_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (9)))
    (h1 : env (.n 116) = V (.E 0 0 (11)))
    (h2 : env (.n 132) = V (.E 0 0 (10)))
    (h3 : env (.n 100) = V (.E 0 0 (12)))
    (h4 : env (.n 164) = V (.A 0 0 (12)))
    (h5 : env (.n 196) = V (.A 0 0 (10)))
    (h6 : env (.n 180) = V (.A 0 0 (11)))
    (h7 : env (.m 1 (⟨48, [1]⟩ : Lin)) = (inp 48).zeroExtend 32)
    (h8 : env (.m 1 (⟨49, [1]⟩ : Lin)) = (inp 49).zeroExtend 32)
    (h9 : env (.m 1 (⟨50, [1]⟩ : Lin)) = (inp 50).zeroExtend 32)
    (h10 : env (.m 1 (⟨51, [1]⟩ : Lin)) = (inp 51).zeroExtend 32)
    (h11 : V (.A 0 0 (13)) = (V (.E 0 0 (9)) + Sigma1 (V (.E 0 0 (12))) + Ch (V (.E 0 0 (12))) (V (.E 0 0 (11))) (V (.E 0 0 (10))) + V (.KW 0 0 12)) + (Sigma0 (V (.A 0 0 (12))) + Maj (V (.A 0 0 (12))) (V (.A 0 0 (11))) (V (.A 0 0 (10)))))
    (h12 : V (.KW 0 0 12) = 1925078388#32 + V (.W 0 0 12))
    (h13 : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (h14 : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨48, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨49, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨50, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨51, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1925078388))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7)))) (.or (.and (.var (.n 164)) (.var (.n 196))) (.and (.xor (.var (.n 164)) (.var (.n 196))) (.var (.n 180))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 2) (.shl (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 30)) (.or (.shr (.var (.n 164)) 22) (.shl (.var (.n 164)) 10)))) = V (.A 0 0 (13)) :=
  shape26 (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.m 1 (⟨48, [1]⟩ : Lin))) (env (.m 1 (⟨49, [1]⟩ : Lin))) (env (.m 1 (⟨50, [1]⟩ : Lin))) (env (.m 1 (⟨51, [1]⟩ : Lin))) (env (.n 164)) (env (.n 196)) (env (.n 180)) (V (.E 0 0 (9))) (V (.E 0 0 (11))) (V (.E 0 0 (10))) (V (.E 0 0 (12))) (V (.A 0 0 (12))) (V (.A 0 0 (10))) (V (.A 0 0 (11))) (V (.A 0 0 (13))) (V (.KW 0 0 12)) (V (.W 0 0 12)) (V (.R 0 12)) ((inp 48)) ((inp 49)) ((inp 50)) ((inp 51)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem step15 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L15) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 55 K15)) L16 := by
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
  exact invC_of_trees inp env _ T15 L16 (slice_trees_mem prog 4 _ _ 55 K15 K16 T15 slice15 env)
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
      (And.intro ⟨rfl, core15_1015 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1014 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1013 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1012 (qv inp) inp env (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
      (And.intro ⟨rfl, core15_1011 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1010 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1009 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1008 (qv inp) inp env (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_1007 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1006 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1005 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1004 (qv inp) inp env (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_1003 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1002 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1001 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_1000 (qv inp) inp env (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_311 (qv inp) inp env (hm 244 (by decide)) (hm 245 (by decide)) (hm 246 (by decide)) (hm 247 (by decide)) (qW_R inp 3 13 (by decide)) (qR inp 3 13)⟩
      (And.intro ⟨rfl, core15_310 (qv inp) inp env (hm 180 (by decide)) (hm 181 (by decide)) (hm 182 (by decide)) (hm 183 (by decide)) (qW_R inp 2 13 (by decide)) (qR inp 2 13)⟩
      (And.intro ⟨rfl, core15_309 (qv inp) inp env (hm 116 (by decide)) (hm 117 (by decide)) (hm 118 (by decide)) (hm 119 (by decide)) (qW_R inp 1 13 (by decide)) (qR inp 1 13)⟩
      (And.intro ⟨rfl, core15_308 (qv inp) inp env (hm 52 (by decide)) (hm 53 (by decide)) (hm 54 (by decide)) (hm 55 (by decide)) (qW_R inp 0 13 (by decide)) (qR inp 0 13)⟩
      (And.intro ⟨rfl, core15_295 (qv inp) inp env (hm 248 (by decide)) (hm 249 (by decide)) (hm 250 (by decide)) (hm 251 (by decide)) (qW_R inp 3 14 (by decide)) (qR inp 3 14)⟩
      (And.intro ⟨rfl, core15_294 (qv inp) inp env (hm 184 (by decide)) (hm 185 (by decide)) (hm 186 (by decide)) (hm 187 (by decide)) (qW_R inp 2 14 (by decide)) (qR inp 2 14)⟩
      (And.intro ⟨rfl, core15_293 (qv inp) inp env (hm 120 (by decide)) (hm 121 (by decide)) (hm 122 (by decide)) (hm 123 (by decide)) (qW_R inp 1 14 (by decide)) (qR inp 1 14)⟩
      (And.intro ⟨rfl, core15_292 (qv inp) inp env (hm 56 (by decide)) (hm 57 (by decide)) (hm 58 (by decide)) (hm 59 (by decide)) (qW_R inp 0 14 (by decide)) (qR inp 0 14)⟩
      (And.intro ⟨rfl, core15_279 (qv inp) inp env (hm 252 (by decide)) (hm 253 (by decide)) (hm 254 (by decide)) (hm 255 (by decide)) (qW_R inp 3 15 (by decide)) (qR inp 3 15)⟩
      (And.intro ⟨rfl, core15_278 (qv inp) inp env (hm 188 (by decide)) (hm 189 (by decide)) (hm 190 (by decide)) (hm 191 (by decide)) (qW_R inp 2 15 (by decide)) (qR inp 2 15)⟩
      (And.intro ⟨rfl, core15_277 (qv inp) inp env (hm 124 (by decide)) (hm 125 (by decide)) (hm 126 (by decide)) (hm 127 (by decide)) (qW_R inp 1 15 (by decide)) (qR inp 1 15)⟩
      (And.intro ⟨rfl, core15_276 (qv inp) inp env (hm 60 (by decide)) (hm 61 (by decide)) (hm 62 (by decide)) (hm 63 (by decide)) (qW_R inp 0 15 (by decide)) (qR inp 0 15)⟩
      (And.intro ⟨rfl, core15_215 (qv inp) inp env h192 h208 h216 h212 h220 (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qE_succI inp 3 0 (12) (by decide)) ((qKW inp 3 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_214 (qv inp) inp env h193 h209 h217 h213 h221 (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qE_succI inp 2 0 (12) (by decide)) ((qKW inp 2 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_213 (qv inp) inp env h194 h210 h218 h214 h222 (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qE_succI inp 1 0 (12) (by decide)) ((qKW inp 1 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_212 (qv inp) inp env h195 h211 h219 h215 h223 (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qE_succI inp 0 0 (12) (by decide)) ((qKW inp 0 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
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
      (And.intro ⟨rfl, core15_151 (qv inp) inp env h208 h216 h212 h220 h204 h196 h200 (hm 240 (by decide)) (hm 241 (by decide)) (hm 242 (by decide)) (hm 243 (by decide)) (qA_succI inp 3 0 (12) (by decide)) ((qKW inp 3 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 3 12 (by decide)) (qR inp 3 12)⟩
      (And.intro ⟨rfl, core15_150 (qv inp) inp env h209 h217 h213 h221 h205 h197 h201 (hm 176 (by decide)) (hm 177 (by decide)) (hm 178 (by decide)) (hm 179 (by decide)) (qA_succI inp 2 0 (12) (by decide)) ((qKW inp 2 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 2 12 (by decide)) (qR inp 2 12)⟩
      (And.intro ⟨rfl, core15_149 (qv inp) inp env h210 h218 h214 h222 h206 h198 h202 (hm 112 (by decide)) (hm 113 (by decide)) (hm 114 (by decide)) (hm 115 (by decide)) (qA_succI inp 1 0 (12) (by decide)) ((qKW inp 1 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 1 12 (by decide)) (qR inp 1 12)⟩
      (And.intro ⟨rfl, core15_148 (qv inp) inp env h211 h219 h215 h223 h207 h199 h203 (hm 48 (by decide)) (hm 49 (by decide)) (hm 50 (by decide)) (hm 51 (by decide)) (qA_succI inp 0 0 (12) (by decide)) ((qKW inp 0 0 12).trans (by rw [show Spec.K 12 = 1925078388#32 from by decide])) (qW_R inp 0 12 (by decide)) (qR inp 0 12)⟩
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
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
