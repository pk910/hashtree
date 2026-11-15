import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D3
import Hashtree.Gen.WinAvxX4P.D2

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice3 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 58 K3 K4 T3 = true := by
  decide +kernel

theorem core3_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h5 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape0 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.W 0 0 0)) (V (.R 0 0)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4 h5

theorem core3_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h5 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape0 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.W 0 0 0)) (V (.R 0 0)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4 h5

theorem core3_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h5 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape0 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.W 0 0 0)) (V (.R 0 0)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4 h5

theorem core3_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h5 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 0) :=
  shape0 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.W 0 0 0)) (V (.R 0 0)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4 h5

theorem core3_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h5 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape0 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.W 1 0 0)) (V (.R 1 0)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4 h5

theorem core3_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h5 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape0 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.W 1 0 0)) (V (.R 1 0)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4 h5

theorem core3_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h5 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape0 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.W 1 0 0)) (V (.R 1 0)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4 h5

theorem core3_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h5 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 0) :=
  shape0 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.W 1 0 0)) (V (.R 1 0)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4 h5

theorem core3_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h5 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape0 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.W 2 0 0)) (V (.R 2 0)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4 h5

theorem core3_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h5 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape0 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.W 2 0 0)) (V (.R 2 0)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4 h5

theorem core3_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h5 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape0 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.W 2 0 0)) (V (.R 2 0)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4 h5

theorem core3_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h5 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 0) :=
  shape0 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.W 2 0 0)) (V (.R 2 0)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4 h5

theorem core3_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h5 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape0 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.W 3 0 0)) (V (.R 3 0)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4 h5

theorem core3_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h5 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape0 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.W 3 0 0)) (V (.R 3 0)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4 h5

theorem core3_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h5 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape0 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.W 3 0 0)) (V (.R 3 0)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4 h5

theorem core3_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h5 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 0) :=
  shape0 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.W 3 0 0)) (V (.R 3 0)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4 h5

theorem core3_311 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨196, [1]⟩ : Lin)) = (inp 196).zeroExtend 32)
    (h1 : env (.m 1 (⟨197, [1]⟩ : Lin)) = (inp 197).zeroExtend 32)
    (h2 : env (.m 1 (⟨198, [1]⟩ : Lin)) = (inp 198).zeroExtend 32)
    (h3 : env (.m 1 (⟨199, [1]⟩ : Lin)) = (inp 199).zeroExtend 32)
    (h4 : V (.W 3 0 1) = bswap (V (.R 3 1)))
    (h5 : V (.R 3 1) = ((((0 : Word) ||| (inp 196).zeroExtend 32 <<< 0) ||| (inp 197).zeroExtend 32 <<< 8) ||| (inp 198).zeroExtend 32 <<< 16) ||| (inp 199).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨196, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨197, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨198, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨199, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨196, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨197, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨198, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨199, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨196, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨197, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨198, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨199, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨196, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨197, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨198, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨199, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 1) :=
  shape0 (env (.m 1 (⟨196, [1]⟩ : Lin))) (env (.m 1 (⟨197, [1]⟩ : Lin))) (env (.m 1 (⟨198, [1]⟩ : Lin))) (env (.m 1 (⟨199, [1]⟩ : Lin))) (V (.W 3 0 1)) (V (.R 3 1)) ((inp 196)) ((inp 197)) ((inp 198)) ((inp 199)) h0 h1 h2 h3 h4 h5

theorem core3_310 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨132, [1]⟩ : Lin)) = (inp 132).zeroExtend 32)
    (h1 : env (.m 1 (⟨133, [1]⟩ : Lin)) = (inp 133).zeroExtend 32)
    (h2 : env (.m 1 (⟨134, [1]⟩ : Lin)) = (inp 134).zeroExtend 32)
    (h3 : env (.m 1 (⟨135, [1]⟩ : Lin)) = (inp 135).zeroExtend 32)
    (h4 : V (.W 2 0 1) = bswap (V (.R 2 1)))
    (h5 : V (.R 2 1) = ((((0 : Word) ||| (inp 132).zeroExtend 32 <<< 0) ||| (inp 133).zeroExtend 32 <<< 8) ||| (inp 134).zeroExtend 32 <<< 16) ||| (inp 135).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨132, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨133, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨134, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨135, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨132, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨133, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨134, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨135, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨132, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨133, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨134, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨135, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨132, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨133, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨134, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨135, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 1) :=
  shape0 (env (.m 1 (⟨132, [1]⟩ : Lin))) (env (.m 1 (⟨133, [1]⟩ : Lin))) (env (.m 1 (⟨134, [1]⟩ : Lin))) (env (.m 1 (⟨135, [1]⟩ : Lin))) (V (.W 2 0 1)) (V (.R 2 1)) ((inp 132)) ((inp 133)) ((inp 134)) ((inp 135)) h0 h1 h2 h3 h4 h5

theorem core3_309 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨68, [1]⟩ : Lin)) = (inp 68).zeroExtend 32)
    (h1 : env (.m 1 (⟨69, [1]⟩ : Lin)) = (inp 69).zeroExtend 32)
    (h2 : env (.m 1 (⟨70, [1]⟩ : Lin)) = (inp 70).zeroExtend 32)
    (h3 : env (.m 1 (⟨71, [1]⟩ : Lin)) = (inp 71).zeroExtend 32)
    (h4 : V (.W 1 0 1) = bswap (V (.R 1 1)))
    (h5 : V (.R 1 1) = ((((0 : Word) ||| (inp 68).zeroExtend 32 <<< 0) ||| (inp 69).zeroExtend 32 <<< 8) ||| (inp 70).zeroExtend 32 <<< 16) ||| (inp 71).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨68, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨69, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨70, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨71, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨68, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨69, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨70, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨71, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨68, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨69, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨70, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨71, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨68, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨69, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨70, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨71, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 1) :=
  shape0 (env (.m 1 (⟨68, [1]⟩ : Lin))) (env (.m 1 (⟨69, [1]⟩ : Lin))) (env (.m 1 (⟨70, [1]⟩ : Lin))) (env (.m 1 (⟨71, [1]⟩ : Lin))) (V (.W 1 0 1)) (V (.R 1 1)) ((inp 68)) ((inp 69)) ((inp 70)) ((inp 71)) h0 h1 h2 h3 h4 h5

theorem core3_308 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨4, [1]⟩ : Lin)) = (inp 4).zeroExtend 32)
    (h1 : env (.m 1 (⟨5, [1]⟩ : Lin)) = (inp 5).zeroExtend 32)
    (h2 : env (.m 1 (⟨6, [1]⟩ : Lin)) = (inp 6).zeroExtend 32)
    (h3 : env (.m 1 (⟨7, [1]⟩ : Lin)) = (inp 7).zeroExtend 32)
    (h4 : V (.W 0 0 1) = bswap (V (.R 0 1)))
    (h5 : V (.R 0 1) = ((((0 : Word) ||| (inp 4).zeroExtend 32 <<< 0) ||| (inp 5).zeroExtend 32 <<< 8) ||| (inp 6).zeroExtend 32 <<< 16) ||| (inp 7).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨4, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨5, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨6, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨7, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨4, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨5, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨6, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨7, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨4, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨5, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨6, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨7, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨4, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨5, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨6, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨7, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 1) :=
  shape0 (env (.m 1 (⟨4, [1]⟩ : Lin))) (env (.m 1 (⟨5, [1]⟩ : Lin))) (env (.m 1 (⟨6, [1]⟩ : Lin))) (env (.m 1 (⟨7, [1]⟩ : Lin))) (V (.W 0 0 1)) (V (.R 0 1)) ((inp 4)) ((inp 5)) ((inp 6)) ((inp 7)) h0 h1 h2 h3 h4 h5

theorem core3_295 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨200, [1]⟩ : Lin)) = (inp 200).zeroExtend 32)
    (h1 : env (.m 1 (⟨201, [1]⟩ : Lin)) = (inp 201).zeroExtend 32)
    (h2 : env (.m 1 (⟨202, [1]⟩ : Lin)) = (inp 202).zeroExtend 32)
    (h3 : env (.m 1 (⟨203, [1]⟩ : Lin)) = (inp 203).zeroExtend 32)
    (h4 : V (.W 3 0 2) = bswap (V (.R 3 2)))
    (h5 : V (.R 3 2) = ((((0 : Word) ||| (inp 200).zeroExtend 32 <<< 0) ||| (inp 201).zeroExtend 32 <<< 8) ||| (inp 202).zeroExtend 32 <<< 16) ||| (inp 203).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨200, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨201, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨202, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨203, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨200, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨201, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨202, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨203, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨200, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨201, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨202, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨203, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨200, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨201, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨202, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨203, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 2) :=
  shape0 (env (.m 1 (⟨200, [1]⟩ : Lin))) (env (.m 1 (⟨201, [1]⟩ : Lin))) (env (.m 1 (⟨202, [1]⟩ : Lin))) (env (.m 1 (⟨203, [1]⟩ : Lin))) (V (.W 3 0 2)) (V (.R 3 2)) ((inp 200)) ((inp 201)) ((inp 202)) ((inp 203)) h0 h1 h2 h3 h4 h5

theorem core3_294 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨136, [1]⟩ : Lin)) = (inp 136).zeroExtend 32)
    (h1 : env (.m 1 (⟨137, [1]⟩ : Lin)) = (inp 137).zeroExtend 32)
    (h2 : env (.m 1 (⟨138, [1]⟩ : Lin)) = (inp 138).zeroExtend 32)
    (h3 : env (.m 1 (⟨139, [1]⟩ : Lin)) = (inp 139).zeroExtend 32)
    (h4 : V (.W 2 0 2) = bswap (V (.R 2 2)))
    (h5 : V (.R 2 2) = ((((0 : Word) ||| (inp 136).zeroExtend 32 <<< 0) ||| (inp 137).zeroExtend 32 <<< 8) ||| (inp 138).zeroExtend 32 <<< 16) ||| (inp 139).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨136, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨137, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨138, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨139, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨136, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨137, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨138, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨139, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨136, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨137, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨138, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨139, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨136, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨137, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨138, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨139, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 2) :=
  shape0 (env (.m 1 (⟨136, [1]⟩ : Lin))) (env (.m 1 (⟨137, [1]⟩ : Lin))) (env (.m 1 (⟨138, [1]⟩ : Lin))) (env (.m 1 (⟨139, [1]⟩ : Lin))) (V (.W 2 0 2)) (V (.R 2 2)) ((inp 136)) ((inp 137)) ((inp 138)) ((inp 139)) h0 h1 h2 h3 h4 h5

theorem core3_293 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨72, [1]⟩ : Lin)) = (inp 72).zeroExtend 32)
    (h1 : env (.m 1 (⟨73, [1]⟩ : Lin)) = (inp 73).zeroExtend 32)
    (h2 : env (.m 1 (⟨74, [1]⟩ : Lin)) = (inp 74).zeroExtend 32)
    (h3 : env (.m 1 (⟨75, [1]⟩ : Lin)) = (inp 75).zeroExtend 32)
    (h4 : V (.W 1 0 2) = bswap (V (.R 1 2)))
    (h5 : V (.R 1 2) = ((((0 : Word) ||| (inp 72).zeroExtend 32 <<< 0) ||| (inp 73).zeroExtend 32 <<< 8) ||| (inp 74).zeroExtend 32 <<< 16) ||| (inp 75).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨72, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨73, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨74, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨75, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨72, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨73, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨74, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨75, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨72, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨73, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨74, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨75, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨72, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨73, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨74, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨75, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 2) :=
  shape0 (env (.m 1 (⟨72, [1]⟩ : Lin))) (env (.m 1 (⟨73, [1]⟩ : Lin))) (env (.m 1 (⟨74, [1]⟩ : Lin))) (env (.m 1 (⟨75, [1]⟩ : Lin))) (V (.W 1 0 2)) (V (.R 1 2)) ((inp 72)) ((inp 73)) ((inp 74)) ((inp 75)) h0 h1 h2 h3 h4 h5

theorem core3_292 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨8, [1]⟩ : Lin)) = (inp 8).zeroExtend 32)
    (h1 : env (.m 1 (⟨9, [1]⟩ : Lin)) = (inp 9).zeroExtend 32)
    (h2 : env (.m 1 (⟨10, [1]⟩ : Lin)) = (inp 10).zeroExtend 32)
    (h3 : env (.m 1 (⟨11, [1]⟩ : Lin)) = (inp 11).zeroExtend 32)
    (h4 : V (.W 0 0 2) = bswap (V (.R 0 2)))
    (h5 : V (.R 0 2) = ((((0 : Word) ||| (inp 8).zeroExtend 32 <<< 0) ||| (inp 9).zeroExtend 32 <<< 8) ||| (inp 10).zeroExtend 32 <<< 16) ||| (inp 11).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨8, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨9, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨10, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨11, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨8, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨9, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨10, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨11, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨8, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨9, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨10, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨11, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨8, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨9, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨10, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨11, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 2) :=
  shape0 (env (.m 1 (⟨8, [1]⟩ : Lin))) (env (.m 1 (⟨9, [1]⟩ : Lin))) (env (.m 1 (⟨10, [1]⟩ : Lin))) (env (.m 1 (⟨11, [1]⟩ : Lin))) (V (.W 0 0 2)) (V (.R 0 2)) ((inp 8)) ((inp 9)) ((inp 10)) ((inp 11)) h0 h1 h2 h3 h4 h5

theorem core3_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨204, [1]⟩ : Lin)) = (inp 204).zeroExtend 32)
    (h1 : env (.m 1 (⟨205, [1]⟩ : Lin)) = (inp 205).zeroExtend 32)
    (h2 : env (.m 1 (⟨206, [1]⟩ : Lin)) = (inp 206).zeroExtend 32)
    (h3 : env (.m 1 (⟨207, [1]⟩ : Lin)) = (inp 207).zeroExtend 32)
    (h4 : V (.W 3 0 3) = bswap (V (.R 3 3)))
    (h5 : V (.R 3 3) = ((((0 : Word) ||| (inp 204).zeroExtend 32 <<< 0) ||| (inp 205).zeroExtend 32 <<< 8) ||| (inp 206).zeroExtend 32 <<< 16) ||| (inp 207).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨204, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨205, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨206, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨207, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨204, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨205, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨206, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨207, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨204, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨205, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨206, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨207, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨204, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨205, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨206, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨207, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 3) :=
  shape0 (env (.m 1 (⟨204, [1]⟩ : Lin))) (env (.m 1 (⟨205, [1]⟩ : Lin))) (env (.m 1 (⟨206, [1]⟩ : Lin))) (env (.m 1 (⟨207, [1]⟩ : Lin))) (V (.W 3 0 3)) (V (.R 3 3)) ((inp 204)) ((inp 205)) ((inp 206)) ((inp 207)) h0 h1 h2 h3 h4 h5

theorem core3_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨140, [1]⟩ : Lin)) = (inp 140).zeroExtend 32)
    (h1 : env (.m 1 (⟨141, [1]⟩ : Lin)) = (inp 141).zeroExtend 32)
    (h2 : env (.m 1 (⟨142, [1]⟩ : Lin)) = (inp 142).zeroExtend 32)
    (h3 : env (.m 1 (⟨143, [1]⟩ : Lin)) = (inp 143).zeroExtend 32)
    (h4 : V (.W 2 0 3) = bswap (V (.R 2 3)))
    (h5 : V (.R 2 3) = ((((0 : Word) ||| (inp 140).zeroExtend 32 <<< 0) ||| (inp 141).zeroExtend 32 <<< 8) ||| (inp 142).zeroExtend 32 <<< 16) ||| (inp 143).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨140, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨141, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨142, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨143, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨140, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨141, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨142, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨143, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨140, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨141, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨142, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨143, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨140, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨141, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨142, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨143, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 3) :=
  shape0 (env (.m 1 (⟨140, [1]⟩ : Lin))) (env (.m 1 (⟨141, [1]⟩ : Lin))) (env (.m 1 (⟨142, [1]⟩ : Lin))) (env (.m 1 (⟨143, [1]⟩ : Lin))) (V (.W 2 0 3)) (V (.R 2 3)) ((inp 140)) ((inp 141)) ((inp 142)) ((inp 143)) h0 h1 h2 h3 h4 h5

theorem core3_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨76, [1]⟩ : Lin)) = (inp 76).zeroExtend 32)
    (h1 : env (.m 1 (⟨77, [1]⟩ : Lin)) = (inp 77).zeroExtend 32)
    (h2 : env (.m 1 (⟨78, [1]⟩ : Lin)) = (inp 78).zeroExtend 32)
    (h3 : env (.m 1 (⟨79, [1]⟩ : Lin)) = (inp 79).zeroExtend 32)
    (h4 : V (.W 1 0 3) = bswap (V (.R 1 3)))
    (h5 : V (.R 1 3) = ((((0 : Word) ||| (inp 76).zeroExtend 32 <<< 0) ||| (inp 77).zeroExtend 32 <<< 8) ||| (inp 78).zeroExtend 32 <<< 16) ||| (inp 79).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨76, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨77, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨78, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨79, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨76, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨77, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨78, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨79, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨76, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨77, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨78, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨79, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨76, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨77, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨78, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨79, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 3) :=
  shape0 (env (.m 1 (⟨76, [1]⟩ : Lin))) (env (.m 1 (⟨77, [1]⟩ : Lin))) (env (.m 1 (⟨78, [1]⟩ : Lin))) (env (.m 1 (⟨79, [1]⟩ : Lin))) (V (.W 1 0 3)) (V (.R 1 3)) ((inp 76)) ((inp 77)) ((inp 78)) ((inp 79)) h0 h1 h2 h3 h4 h5

theorem core3_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨12, [1]⟩ : Lin)) = (inp 12).zeroExtend 32)
    (h1 : env (.m 1 (⟨13, [1]⟩ : Lin)) = (inp 13).zeroExtend 32)
    (h2 : env (.m 1 (⟨14, [1]⟩ : Lin)) = (inp 14).zeroExtend 32)
    (h3 : env (.m 1 (⟨15, [1]⟩ : Lin)) = (inp 15).zeroExtend 32)
    (h4 : V (.W 0 0 3) = bswap (V (.R 0 3)))
    (h5 : V (.R 0 3) = ((((0 : Word) ||| (inp 12).zeroExtend 32 <<< 0) ||| (inp 13).zeroExtend 32 <<< 8) ||| (inp 14).zeroExtend 32 <<< 16) ||| (inp 15).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨12, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨13, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨14, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨15, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨12, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨13, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨14, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨15, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨12, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨13, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨14, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨15, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨12, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨13, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨14, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨15, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 3) :=
  shape0 (env (.m 1 (⟨12, [1]⟩ : Lin))) (env (.m 1 (⟨13, [1]⟩ : Lin))) (env (.m 1 (⟨14, [1]⟩ : Lin))) (env (.m 1 (⟨15, [1]⟩ : Lin))) (V (.W 0 0 3)) (V (.R 0 3)) ((inp 12)) ((inp 13)) ((inp 14)) ((inp 15)) h0 h1 h2 h3 h4 h5

theorem core3_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.A 3 0 (1)) = (V (.E 3 0 (-3)) + Sigma1 (V (.E 3 0 (0))) + Ch (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) + V (.KW 3 0 0)) + (Sigma0 (V (.A 3 0 (0))) + Maj (V (.A 3 0 (0))) (V (.A 3 0 (-1))) (V (.A 3 0 (-2)))))
    (h5 : V (.E 3 0 (-3)) = V (.H 3 0 7))
    (h6 : V (.H 3 0 7) = 1541459225#32)
    (h7 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h8 : V (.H 3 0 4) = 1359893119#32)
    (h9 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h10 : V (.H 3 0 5) = 2600822924#32)
    (h11 : V (.E 3 0 (-2)) = V (.H 3 0 6))
    (h12 : V (.H 3 0 6) = 528734635#32)
    (h13 : V (.KW 3 0 0) = 1116352408#32 + V (.W 3 0 0))
    (h14 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h15 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24)
    (h16 : V (.A 3 0 (0)) = V (.H 3 0 0))
    (h17 : V (.H 3 0 0) = 1779033703#32)
    (h18 : V (.A 3 0 (-1)) = V (.H 3 0 1))
    (h19 : V (.H 3 0 1) = 3144134277#32)
    (h20 : V (.A 3 0 (-2)) = V (.H 3 0 2))
    (h21 : V (.H 3 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 3 0 (1)) :=
  shape1 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.A 3 0 (1))) (V (.E 3 0 (-3))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) (V (.KW 3 0 0)) (V (.A 3 0 (0))) (V (.A 3 0 (-1))) (V (.A 3 0 (-2))) (V (.H 3 0 7)) (V (.H 3 0 4)) (V (.H 3 0 5)) (V (.H 3 0 6)) (V (.W 3 0 0)) (V (.R 3 0)) (V (.H 3 0 0)) (V (.H 3 0 1)) (V (.H 3 0 2)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21

theorem core3_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.A 2 0 (1)) = (V (.E 2 0 (-3)) + Sigma1 (V (.E 2 0 (0))) + Ch (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) + V (.KW 2 0 0)) + (Sigma0 (V (.A 2 0 (0))) + Maj (V (.A 2 0 (0))) (V (.A 2 0 (-1))) (V (.A 2 0 (-2)))))
    (h5 : V (.E 2 0 (-3)) = V (.H 2 0 7))
    (h6 : V (.H 2 0 7) = 1541459225#32)
    (h7 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h8 : V (.H 2 0 4) = 1359893119#32)
    (h9 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h10 : V (.H 2 0 5) = 2600822924#32)
    (h11 : V (.E 2 0 (-2)) = V (.H 2 0 6))
    (h12 : V (.H 2 0 6) = 528734635#32)
    (h13 : V (.KW 2 0 0) = 1116352408#32 + V (.W 2 0 0))
    (h14 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h15 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24)
    (h16 : V (.A 2 0 (0)) = V (.H 2 0 0))
    (h17 : V (.H 2 0 0) = 1779033703#32)
    (h18 : V (.A 2 0 (-1)) = V (.H 2 0 1))
    (h19 : V (.H 2 0 1) = 3144134277#32)
    (h20 : V (.A 2 0 (-2)) = V (.H 2 0 2))
    (h21 : V (.H 2 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 2 0 (1)) :=
  shape1 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.A 2 0 (1))) (V (.E 2 0 (-3))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) (V (.KW 2 0 0)) (V (.A 2 0 (0))) (V (.A 2 0 (-1))) (V (.A 2 0 (-2))) (V (.H 2 0 7)) (V (.H 2 0 4)) (V (.H 2 0 5)) (V (.H 2 0 6)) (V (.W 2 0 0)) (V (.R 2 0)) (V (.H 2 0 0)) (V (.H 2 0 1)) (V (.H 2 0 2)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21

theorem core3_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.A 1 0 (1)) = (V (.E 1 0 (-3)) + Sigma1 (V (.E 1 0 (0))) + Ch (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) + V (.KW 1 0 0)) + (Sigma0 (V (.A 1 0 (0))) + Maj (V (.A 1 0 (0))) (V (.A 1 0 (-1))) (V (.A 1 0 (-2)))))
    (h5 : V (.E 1 0 (-3)) = V (.H 1 0 7))
    (h6 : V (.H 1 0 7) = 1541459225#32)
    (h7 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h8 : V (.H 1 0 4) = 1359893119#32)
    (h9 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h10 : V (.H 1 0 5) = 2600822924#32)
    (h11 : V (.E 1 0 (-2)) = V (.H 1 0 6))
    (h12 : V (.H 1 0 6) = 528734635#32)
    (h13 : V (.KW 1 0 0) = 1116352408#32 + V (.W 1 0 0))
    (h14 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h15 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24)
    (h16 : V (.A 1 0 (0)) = V (.H 1 0 0))
    (h17 : V (.H 1 0 0) = 1779033703#32)
    (h18 : V (.A 1 0 (-1)) = V (.H 1 0 1))
    (h19 : V (.H 1 0 1) = 3144134277#32)
    (h20 : V (.A 1 0 (-2)) = V (.H 1 0 2))
    (h21 : V (.H 1 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 1 0 (1)) :=
  shape1 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.A 1 0 (1))) (V (.E 1 0 (-3))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) (V (.KW 1 0 0)) (V (.A 1 0 (0))) (V (.A 1 0 (-1))) (V (.A 1 0 (-2))) (V (.H 1 0 7)) (V (.H 1 0 4)) (V (.H 1 0 5)) (V (.H 1 0 6)) (V (.W 1 0 0)) (V (.R 1 0)) (V (.H 1 0 0)) (V (.H 1 0 1)) (V (.H 1 0 2)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21

theorem core3_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.A 0 0 (1)) = (V (.E 0 0 (-3)) + Sigma1 (V (.E 0 0 (0))) + Ch (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) + V (.KW 0 0 0)) + (Sigma0 (V (.A 0 0 (0))) + Maj (V (.A 0 0 (0))) (V (.A 0 0 (-1))) (V (.A 0 0 (-2)))))
    (h5 : V (.E 0 0 (-3)) = V (.H 0 0 7))
    (h6 : V (.H 0 0 7) = 1541459225#32)
    (h7 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h8 : V (.H 0 0 4) = 1359893119#32)
    (h9 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h10 : V (.H 0 0 5) = 2600822924#32)
    (h11 : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (h12 : V (.H 0 0 6) = 528734635#32)
    (h13 : V (.KW 0 0 0) = 1116352408#32 + V (.W 0 0 0))
    (h14 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h15 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24)
    (h16 : V (.A 0 0 (0)) = V (.H 0 0 0))
    (h17 : V (.H 0 0 0) = 1779033703#32)
    (h18 : V (.A 0 0 (-1)) = V (.H 0 0 1))
    (h19 : V (.H 0 0 1) = 3144134277#32)
    (h20 : V (.A 0 0 (-2)) = V (.H 0 0 2))
    (h21 : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835)) (.const 980412007)) (.const 3458249854)) = V (.A 0 0 (1)) :=
  shape1 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.A 0 0 (1))) (V (.E 0 0 (-3))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) (V (.KW 0 0 0)) (V (.A 0 0 (0))) (V (.A 0 0 (-1))) (V (.A 0 0 (-2))) (V (.H 0 0 7)) (V (.H 0 0 4)) (V (.H 0 0 5)) (V (.H 0 0 6)) (V (.W 0 0 0)) (V (.R 0 0)) (V (.H 0 0 0)) (V (.H 0 0 1)) (V (.H 0 0 2)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21

theorem core3_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.E 3 0 (1)) = V (.A 3 0 (-3)) + (V (.E 3 0 (-3)) + Sigma1 (V (.E 3 0 (0))) + Ch (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) + V (.KW 3 0 0)))
    (h5 : V (.A 3 0 (-3)) = V (.H 3 0 3))
    (h6 : V (.H 3 0 3) = 2773480762#32)
    (h7 : V (.E 3 0 (-3)) = V (.H 3 0 7))
    (h8 : V (.H 3 0 7) = 1541459225#32)
    (h9 : V (.E 3 0 (0)) = V (.H 3 0 4))
    (h10 : V (.H 3 0 4) = 1359893119#32)
    (h11 : V (.E 3 0 (-1)) = V (.H 3 0 5))
    (h12 : V (.H 3 0 5) = 2600822924#32)
    (h13 : V (.E 3 0 (-2)) = V (.H 3 0 6))
    (h14 : V (.H 3 0 6) = 528734635#32)
    (h15 : V (.KW 3 0 0) = 1116352408#32 + V (.W 3 0 0))
    (h16 : V (.W 3 0 0) = bswap (V (.R 3 0)))
    (h17 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 3 0 (1)) :=
  shape2 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.E 3 0 (1))) (V (.A 3 0 (-3))) (V (.E 3 0 (-3))) (V (.E 3 0 (0))) (V (.E 3 0 (-1))) (V (.E 3 0 (-2))) (V (.KW 3 0 0)) (V (.H 3 0 3)) (V (.H 3 0 7)) (V (.H 3 0 4)) (V (.H 3 0 5)) (V (.H 3 0 6)) (V (.W 3 0 0)) (V (.R 3 0)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core3_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.E 2 0 (1)) = V (.A 2 0 (-3)) + (V (.E 2 0 (-3)) + Sigma1 (V (.E 2 0 (0))) + Ch (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) + V (.KW 2 0 0)))
    (h5 : V (.A 2 0 (-3)) = V (.H 2 0 3))
    (h6 : V (.H 2 0 3) = 2773480762#32)
    (h7 : V (.E 2 0 (-3)) = V (.H 2 0 7))
    (h8 : V (.H 2 0 7) = 1541459225#32)
    (h9 : V (.E 2 0 (0)) = V (.H 2 0 4))
    (h10 : V (.H 2 0 4) = 1359893119#32)
    (h11 : V (.E 2 0 (-1)) = V (.H 2 0 5))
    (h12 : V (.H 2 0 5) = 2600822924#32)
    (h13 : V (.E 2 0 (-2)) = V (.H 2 0 6))
    (h14 : V (.H 2 0 6) = 528734635#32)
    (h15 : V (.KW 2 0 0) = 1116352408#32 + V (.W 2 0 0))
    (h16 : V (.W 2 0 0) = bswap (V (.R 2 0)))
    (h17 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 2 0 (1)) :=
  shape2 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.E 2 0 (1))) (V (.A 2 0 (-3))) (V (.E 2 0 (-3))) (V (.E 2 0 (0))) (V (.E 2 0 (-1))) (V (.E 2 0 (-2))) (V (.KW 2 0 0)) (V (.H 2 0 3)) (V (.H 2 0 7)) (V (.H 2 0 4)) (V (.H 2 0 5)) (V (.H 2 0 6)) (V (.W 2 0 0)) (V (.R 2 0)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core3_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.E 1 0 (1)) = V (.A 1 0 (-3)) + (V (.E 1 0 (-3)) + Sigma1 (V (.E 1 0 (0))) + Ch (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) + V (.KW 1 0 0)))
    (h5 : V (.A 1 0 (-3)) = V (.H 1 0 3))
    (h6 : V (.H 1 0 3) = 2773480762#32)
    (h7 : V (.E 1 0 (-3)) = V (.H 1 0 7))
    (h8 : V (.H 1 0 7) = 1541459225#32)
    (h9 : V (.E 1 0 (0)) = V (.H 1 0 4))
    (h10 : V (.H 1 0 4) = 1359893119#32)
    (h11 : V (.E 1 0 (-1)) = V (.H 1 0 5))
    (h12 : V (.H 1 0 5) = 2600822924#32)
    (h13 : V (.E 1 0 (-2)) = V (.H 1 0 6))
    (h14 : V (.H 1 0 6) = 528734635#32)
    (h15 : V (.KW 1 0 0) = 1116352408#32 + V (.W 1 0 0))
    (h16 : V (.W 1 0 0) = bswap (V (.R 1 0)))
    (h17 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 1 0 (1)) :=
  shape2 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.E 1 0 (1))) (V (.A 1 0 (-3))) (V (.E 1 0 (-3))) (V (.E 1 0 (0))) (V (.E 1 0 (-1))) (V (.E 1 0 (-2))) (V (.KW 1 0 0)) (V (.H 1 0 3)) (V (.H 1 0 7)) (V (.H 1 0 4)) (V (.H 1 0 5)) (V (.H 1 0 6)) (V (.W 1 0 0)) (V (.R 1 0)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem core3_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.E 0 0 (1)) = V (.A 0 0 (-3)) + (V (.E 0 0 (-3)) + Sigma1 (V (.E 0 0 (0))) + Ch (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) + V (.KW 0 0 0)))
    (h5 : V (.A 0 0 (-3)) = V (.H 0 0 3))
    (h6 : V (.H 0 0 3) = 2773480762#32)
    (h7 : V (.E 0 0 (-3)) = V (.H 0 0 7))
    (h8 : V (.H 0 0 7) = 1541459225#32)
    (h9 : V (.E 0 0 (0)) = V (.H 0 0 4))
    (h10 : V (.H 0 0 4) = 1359893119#32)
    (h11 : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (h12 : V (.H 0 0 5) = 2600822924#32)
    (h13 : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (h14 : V (.H 0 0 6) = 528734635#32)
    (h15 : V (.KW 0 0 0) = 1116352408#32 + V (.W 0 0 0))
    (h16 : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (h17 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24) :
    E.eval env (.add (.const 2773480762) (.add (.add (.const 2070320805) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 1116352408))) (.const 898049835))) = V (.E 0 0 (1)) :=
  shape2 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.E 0 0 (1))) (V (.A 0 0 (-3))) (V (.E 0 0 (-3))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) (V (.E 0 0 (-2))) (V (.KW 0 0 0)) (V (.H 0 0 3)) (V (.H 0 0 7)) (V (.H 0 0 4)) (V (.H 0 0 5)) (V (.H 0 0 6)) (V (.W 0 0 0)) (V (.R 0 0)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

theorem step3 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L3) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 58 K3)) L4 := by
  exact invC_of_trees inp env _ T3 L4 (slice_trees_mem prog 4 _ _ 58 K3 K4 T3 slice3 env)
      (And.intro ⟨rfl, core3_1015 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core3_1014 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core3_1013 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core3_1012 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core3_1011 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core3_1010 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core3_1009 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core3_1008 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core3_1007 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core3_1006 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core3_1005 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core3_1004 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core3_1003 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core3_1002 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core3_1001 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core3_1000 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core3_311 (qv inp) inp env (hm 196 (by decide)) (hm 197 (by decide)) (hm 198 (by decide)) (hm 199 (by decide)) (qW_R inp 3 1 (by decide)) (qR inp 3 1)⟩
      (And.intro ⟨rfl, core3_310 (qv inp) inp env (hm 132 (by decide)) (hm 133 (by decide)) (hm 134 (by decide)) (hm 135 (by decide)) (qW_R inp 2 1 (by decide)) (qR inp 2 1)⟩
      (And.intro ⟨rfl, core3_309 (qv inp) inp env (hm 68 (by decide)) (hm 69 (by decide)) (hm 70 (by decide)) (hm 71 (by decide)) (qW_R inp 1 1 (by decide)) (qR inp 1 1)⟩
      (And.intro ⟨rfl, core3_308 (qv inp) inp env (hm 4 (by decide)) (hm 5 (by decide)) (hm 6 (by decide)) (hm 7 (by decide)) (qW_R inp 0 1 (by decide)) (qR inp 0 1)⟩
      (And.intro ⟨rfl, core3_295 (qv inp) inp env (hm 200 (by decide)) (hm 201 (by decide)) (hm 202 (by decide)) (hm 203 (by decide)) (qW_R inp 3 2 (by decide)) (qR inp 3 2)⟩
      (And.intro ⟨rfl, core3_294 (qv inp) inp env (hm 136 (by decide)) (hm 137 (by decide)) (hm 138 (by decide)) (hm 139 (by decide)) (qW_R inp 2 2 (by decide)) (qR inp 2 2)⟩
      (And.intro ⟨rfl, core3_293 (qv inp) inp env (hm 72 (by decide)) (hm 73 (by decide)) (hm 74 (by decide)) (hm 75 (by decide)) (qW_R inp 1 2 (by decide)) (qR inp 1 2)⟩
      (And.intro ⟨rfl, core3_292 (qv inp) inp env (hm 8 (by decide)) (hm 9 (by decide)) (hm 10 (by decide)) (hm 11 (by decide)) (qW_R inp 0 2 (by decide)) (qR inp 0 2)⟩
      (And.intro ⟨rfl, core3_279 (qv inp) inp env (hm 204 (by decide)) (hm 205 (by decide)) (hm 206 (by decide)) (hm 207 (by decide)) (qW_R inp 3 3 (by decide)) (qR inp 3 3)⟩
      (And.intro ⟨rfl, core3_278 (qv inp) inp env (hm 140 (by decide)) (hm 141 (by decide)) (hm 142 (by decide)) (hm 143 (by decide)) (qW_R inp 2 3 (by decide)) (qR inp 2 3)⟩
      (And.intro ⟨rfl, core3_277 (qv inp) inp env (hm 76 (by decide)) (hm 77 (by decide)) (hm 78 (by decide)) (hm 79 (by decide)) (qW_R inp 1 3 (by decide)) (qR inp 1 3)⟩
      (And.intro ⟨rfl, core3_276 (qv inp) inp env (hm 12 (by decide)) (hm 13 (by decide)) (hm 14 (by decide)) (hm 15 (by decide)) (qW_R inp 0 3 (by decide)) (qR inp 0 3)⟩
      (And.intro ⟨rfl, core3_215 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qA_succI inp 3 0 (0) (by decide)) (qE_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 3 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 3 0 (by decide)) (qR inp 3 0) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core3_214 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qA_succI inp 2 0 (0) (by decide)) (qE_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 2 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 2 0 (by decide)) (qR inp 2 0) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core3_213 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qA_succI inp 1 0 (0) (by decide)) (qE_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 1 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 1 0 (by decide)) (qR inp 1 0) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core3_212 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qA_succI inp 0 0 (0) (by decide)) (qE_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 0 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 0 0 (by decide)) (qR inp 0 0) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core3_151 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qE_succI inp 3 0 (0) (by decide)) (qA_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 3 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core3_150 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qE_succI inp 2 0 (0) (by decide)) (qA_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 2 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core3_149 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qE_succI inp 1 0 (0) (by decide)) (qA_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 1 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core3_148 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qE_succI inp 0 0 (0) (by decide)) (qA_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 0 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      trivial))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
