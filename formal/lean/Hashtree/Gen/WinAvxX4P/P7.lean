import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D7
import Hashtree.Gen.WinAvxX4P.D6

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice7 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 55 K7 K8 T7 = true := by
  decide +kernel

theorem core7_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h1 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h2 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h3 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h4 : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (h5 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape0 (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.W 0 0 4)) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4 h5

theorem core7_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h1 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h2 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h3 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h4 : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (h5 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape0 (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.W 0 0 4)) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4 h5

theorem core7_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h1 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h2 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h3 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h4 : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (h5 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape0 (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.W 0 0 4)) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4 h5

theorem core7_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h1 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h2 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h3 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h4 : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (h5 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 4) :=
  shape0 (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.W 0 0 4)) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4 h5

theorem core7_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h1 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h2 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h3 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h4 : V (.W 1 0 4) = bswap (V (.R 1 4)))
    (h5 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape0 (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.W 1 0 4)) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4 h5

theorem core7_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h1 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h2 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h3 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h4 : V (.W 1 0 4) = bswap (V (.R 1 4)))
    (h5 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape0 (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.W 1 0 4)) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4 h5

theorem core7_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h1 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h2 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h3 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h4 : V (.W 1 0 4) = bswap (V (.R 1 4)))
    (h5 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape0 (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.W 1 0 4)) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4 h5

theorem core7_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h1 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h2 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h3 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h4 : V (.W 1 0 4) = bswap (V (.R 1 4)))
    (h5 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 4) :=
  shape0 (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.W 1 0 4)) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4 h5

theorem core7_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h1 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h2 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h3 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h4 : V (.W 2 0 4) = bswap (V (.R 2 4)))
    (h5 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape0 (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.W 2 0 4)) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4 h5

theorem core7_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h1 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h2 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h3 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h4 : V (.W 2 0 4) = bswap (V (.R 2 4)))
    (h5 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape0 (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.W 2 0 4)) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4 h5

theorem core7_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h1 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h2 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h3 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h4 : V (.W 2 0 4) = bswap (V (.R 2 4)))
    (h5 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape0 (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.W 2 0 4)) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4 h5

theorem core7_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h1 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h2 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h3 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h4 : V (.W 2 0 4) = bswap (V (.R 2 4)))
    (h5 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 4) :=
  shape0 (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.W 2 0 4)) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4 h5

theorem core7_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h1 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h2 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h3 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h4 : V (.W 3 0 4) = bswap (V (.R 3 4)))
    (h5 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape0 (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.W 3 0 4)) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4 h5

theorem core7_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h1 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h2 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h3 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h4 : V (.W 3 0 4) = bswap (V (.R 3 4)))
    (h5 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape0 (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.W 3 0 4)) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4 h5

theorem core7_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h1 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h2 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h3 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h4 : V (.W 3 0 4) = bswap (V (.R 3 4)))
    (h5 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape0 (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.W 3 0 4)) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4 h5

theorem core7_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h1 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h2 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h3 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h4 : V (.W 3 0 4) = bswap (V (.R 3 4)))
    (h5 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 4) :=
  shape0 (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.W 3 0 4)) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4 h5

theorem core7_311 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨212, [1]⟩ : Lin)) = (inp 212).zeroExtend 32)
    (h1 : env (.m 1 (⟨213, [1]⟩ : Lin)) = (inp 213).zeroExtend 32)
    (h2 : env (.m 1 (⟨214, [1]⟩ : Lin)) = (inp 214).zeroExtend 32)
    (h3 : env (.m 1 (⟨215, [1]⟩ : Lin)) = (inp 215).zeroExtend 32)
    (h4 : V (.W 3 0 5) = bswap (V (.R 3 5)))
    (h5 : V (.R 3 5) = ((((0 : Word) ||| (inp 212).zeroExtend 32 <<< 0) ||| (inp 213).zeroExtend 32 <<< 8) ||| (inp 214).zeroExtend 32 <<< 16) ||| (inp 215).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨212, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨213, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨214, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨215, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨212, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨213, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨214, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨215, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨212, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨213, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨214, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨215, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨212, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨213, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨214, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨215, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 5) :=
  shape0 (env (.m 1 (⟨212, [1]⟩ : Lin))) (env (.m 1 (⟨213, [1]⟩ : Lin))) (env (.m 1 (⟨214, [1]⟩ : Lin))) (env (.m 1 (⟨215, [1]⟩ : Lin))) (V (.W 3 0 5)) (V (.R 3 5)) ((inp 212)) ((inp 213)) ((inp 214)) ((inp 215)) h0 h1 h2 h3 h4 h5

theorem core7_310 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨148, [1]⟩ : Lin)) = (inp 148).zeroExtend 32)
    (h1 : env (.m 1 (⟨149, [1]⟩ : Lin)) = (inp 149).zeroExtend 32)
    (h2 : env (.m 1 (⟨150, [1]⟩ : Lin)) = (inp 150).zeroExtend 32)
    (h3 : env (.m 1 (⟨151, [1]⟩ : Lin)) = (inp 151).zeroExtend 32)
    (h4 : V (.W 2 0 5) = bswap (V (.R 2 5)))
    (h5 : V (.R 2 5) = ((((0 : Word) ||| (inp 148).zeroExtend 32 <<< 0) ||| (inp 149).zeroExtend 32 <<< 8) ||| (inp 150).zeroExtend 32 <<< 16) ||| (inp 151).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨148, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨149, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨150, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨151, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨148, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨149, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨150, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨151, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨148, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨149, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨150, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨151, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨148, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨149, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨150, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨151, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 5) :=
  shape0 (env (.m 1 (⟨148, [1]⟩ : Lin))) (env (.m 1 (⟨149, [1]⟩ : Lin))) (env (.m 1 (⟨150, [1]⟩ : Lin))) (env (.m 1 (⟨151, [1]⟩ : Lin))) (V (.W 2 0 5)) (V (.R 2 5)) ((inp 148)) ((inp 149)) ((inp 150)) ((inp 151)) h0 h1 h2 h3 h4 h5

theorem core7_309 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨84, [1]⟩ : Lin)) = (inp 84).zeroExtend 32)
    (h1 : env (.m 1 (⟨85, [1]⟩ : Lin)) = (inp 85).zeroExtend 32)
    (h2 : env (.m 1 (⟨86, [1]⟩ : Lin)) = (inp 86).zeroExtend 32)
    (h3 : env (.m 1 (⟨87, [1]⟩ : Lin)) = (inp 87).zeroExtend 32)
    (h4 : V (.W 1 0 5) = bswap (V (.R 1 5)))
    (h5 : V (.R 1 5) = ((((0 : Word) ||| (inp 84).zeroExtend 32 <<< 0) ||| (inp 85).zeroExtend 32 <<< 8) ||| (inp 86).zeroExtend 32 <<< 16) ||| (inp 87).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨84, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨85, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨86, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨87, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨84, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨85, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨86, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨87, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨84, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨85, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨86, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨87, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨84, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨85, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨86, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨87, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 5) :=
  shape0 (env (.m 1 (⟨84, [1]⟩ : Lin))) (env (.m 1 (⟨85, [1]⟩ : Lin))) (env (.m 1 (⟨86, [1]⟩ : Lin))) (env (.m 1 (⟨87, [1]⟩ : Lin))) (V (.W 1 0 5)) (V (.R 1 5)) ((inp 84)) ((inp 85)) ((inp 86)) ((inp 87)) h0 h1 h2 h3 h4 h5

theorem core7_308 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨20, [1]⟩ : Lin)) = (inp 20).zeroExtend 32)
    (h1 : env (.m 1 (⟨21, [1]⟩ : Lin)) = (inp 21).zeroExtend 32)
    (h2 : env (.m 1 (⟨22, [1]⟩ : Lin)) = (inp 22).zeroExtend 32)
    (h3 : env (.m 1 (⟨23, [1]⟩ : Lin)) = (inp 23).zeroExtend 32)
    (h4 : V (.W 0 0 5) = bswap (V (.R 0 5)))
    (h5 : V (.R 0 5) = ((((0 : Word) ||| (inp 20).zeroExtend 32 <<< 0) ||| (inp 21).zeroExtend 32 <<< 8) ||| (inp 22).zeroExtend 32 <<< 16) ||| (inp 23).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨20, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨21, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨22, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨23, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨20, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨21, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨22, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨23, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨20, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨21, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨22, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨23, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨20, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨21, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨22, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨23, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 5) :=
  shape0 (env (.m 1 (⟨20, [1]⟩ : Lin))) (env (.m 1 (⟨21, [1]⟩ : Lin))) (env (.m 1 (⟨22, [1]⟩ : Lin))) (env (.m 1 (⟨23, [1]⟩ : Lin))) (V (.W 0 0 5)) (V (.R 0 5)) ((inp 20)) ((inp 21)) ((inp 22)) ((inp 23)) h0 h1 h2 h3 h4 h5

theorem core7_295 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨216, [1]⟩ : Lin)) = (inp 216).zeroExtend 32)
    (h1 : env (.m 1 (⟨217, [1]⟩ : Lin)) = (inp 217).zeroExtend 32)
    (h2 : env (.m 1 (⟨218, [1]⟩ : Lin)) = (inp 218).zeroExtend 32)
    (h3 : env (.m 1 (⟨219, [1]⟩ : Lin)) = (inp 219).zeroExtend 32)
    (h4 : V (.W 3 0 6) = bswap (V (.R 3 6)))
    (h5 : V (.R 3 6) = ((((0 : Word) ||| (inp 216).zeroExtend 32 <<< 0) ||| (inp 217).zeroExtend 32 <<< 8) ||| (inp 218).zeroExtend 32 <<< 16) ||| (inp 219).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨216, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨217, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨218, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨219, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨216, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨217, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨218, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨219, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨216, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨217, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨218, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨219, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨216, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨217, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨218, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨219, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 6) :=
  shape0 (env (.m 1 (⟨216, [1]⟩ : Lin))) (env (.m 1 (⟨217, [1]⟩ : Lin))) (env (.m 1 (⟨218, [1]⟩ : Lin))) (env (.m 1 (⟨219, [1]⟩ : Lin))) (V (.W 3 0 6)) (V (.R 3 6)) ((inp 216)) ((inp 217)) ((inp 218)) ((inp 219)) h0 h1 h2 h3 h4 h5

theorem core7_294 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨152, [1]⟩ : Lin)) = (inp 152).zeroExtend 32)
    (h1 : env (.m 1 (⟨153, [1]⟩ : Lin)) = (inp 153).zeroExtend 32)
    (h2 : env (.m 1 (⟨154, [1]⟩ : Lin)) = (inp 154).zeroExtend 32)
    (h3 : env (.m 1 (⟨155, [1]⟩ : Lin)) = (inp 155).zeroExtend 32)
    (h4 : V (.W 2 0 6) = bswap (V (.R 2 6)))
    (h5 : V (.R 2 6) = ((((0 : Word) ||| (inp 152).zeroExtend 32 <<< 0) ||| (inp 153).zeroExtend 32 <<< 8) ||| (inp 154).zeroExtend 32 <<< 16) ||| (inp 155).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨152, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨153, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨154, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨155, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨152, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨153, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨154, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨155, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨152, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨153, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨154, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨155, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨152, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨153, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨154, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨155, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 6) :=
  shape0 (env (.m 1 (⟨152, [1]⟩ : Lin))) (env (.m 1 (⟨153, [1]⟩ : Lin))) (env (.m 1 (⟨154, [1]⟩ : Lin))) (env (.m 1 (⟨155, [1]⟩ : Lin))) (V (.W 2 0 6)) (V (.R 2 6)) ((inp 152)) ((inp 153)) ((inp 154)) ((inp 155)) h0 h1 h2 h3 h4 h5

theorem core7_293 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨88, [1]⟩ : Lin)) = (inp 88).zeroExtend 32)
    (h1 : env (.m 1 (⟨89, [1]⟩ : Lin)) = (inp 89).zeroExtend 32)
    (h2 : env (.m 1 (⟨90, [1]⟩ : Lin)) = (inp 90).zeroExtend 32)
    (h3 : env (.m 1 (⟨91, [1]⟩ : Lin)) = (inp 91).zeroExtend 32)
    (h4 : V (.W 1 0 6) = bswap (V (.R 1 6)))
    (h5 : V (.R 1 6) = ((((0 : Word) ||| (inp 88).zeroExtend 32 <<< 0) ||| (inp 89).zeroExtend 32 <<< 8) ||| (inp 90).zeroExtend 32 <<< 16) ||| (inp 91).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨88, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨89, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨90, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨91, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨88, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨89, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨90, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨91, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨88, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨89, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨90, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨91, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨88, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨89, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨90, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨91, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 6) :=
  shape0 (env (.m 1 (⟨88, [1]⟩ : Lin))) (env (.m 1 (⟨89, [1]⟩ : Lin))) (env (.m 1 (⟨90, [1]⟩ : Lin))) (env (.m 1 (⟨91, [1]⟩ : Lin))) (V (.W 1 0 6)) (V (.R 1 6)) ((inp 88)) ((inp 89)) ((inp 90)) ((inp 91)) h0 h1 h2 h3 h4 h5

theorem core7_292 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨24, [1]⟩ : Lin)) = (inp 24).zeroExtend 32)
    (h1 : env (.m 1 (⟨25, [1]⟩ : Lin)) = (inp 25).zeroExtend 32)
    (h2 : env (.m 1 (⟨26, [1]⟩ : Lin)) = (inp 26).zeroExtend 32)
    (h3 : env (.m 1 (⟨27, [1]⟩ : Lin)) = (inp 27).zeroExtend 32)
    (h4 : V (.W 0 0 6) = bswap (V (.R 0 6)))
    (h5 : V (.R 0 6) = ((((0 : Word) ||| (inp 24).zeroExtend 32 <<< 0) ||| (inp 25).zeroExtend 32 <<< 8) ||| (inp 26).zeroExtend 32 <<< 16) ||| (inp 27).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨24, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨25, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨26, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨27, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨24, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨25, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨26, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨27, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨24, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨25, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨26, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨27, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨24, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨25, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨26, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨27, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 6) :=
  shape0 (env (.m 1 (⟨24, [1]⟩ : Lin))) (env (.m 1 (⟨25, [1]⟩ : Lin))) (env (.m 1 (⟨26, [1]⟩ : Lin))) (env (.m 1 (⟨27, [1]⟩ : Lin))) (V (.W 0 0 6)) (V (.R 0 6)) ((inp 24)) ((inp 25)) ((inp 26)) ((inp 27)) h0 h1 h2 h3 h4 h5

theorem core7_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨220, [1]⟩ : Lin)) = (inp 220).zeroExtend 32)
    (h1 : env (.m 1 (⟨221, [1]⟩ : Lin)) = (inp 221).zeroExtend 32)
    (h2 : env (.m 1 (⟨222, [1]⟩ : Lin)) = (inp 222).zeroExtend 32)
    (h3 : env (.m 1 (⟨223, [1]⟩ : Lin)) = (inp 223).zeroExtend 32)
    (h4 : V (.W 3 0 7) = bswap (V (.R 3 7)))
    (h5 : V (.R 3 7) = ((((0 : Word) ||| (inp 220).zeroExtend 32 <<< 0) ||| (inp 221).zeroExtend 32 <<< 8) ||| (inp 222).zeroExtend 32 <<< 16) ||| (inp 223).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨220, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨221, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨222, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨223, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨220, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨221, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨222, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨223, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨220, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨221, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨222, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨223, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨220, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨221, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨222, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨223, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 7) :=
  shape0 (env (.m 1 (⟨220, [1]⟩ : Lin))) (env (.m 1 (⟨221, [1]⟩ : Lin))) (env (.m 1 (⟨222, [1]⟩ : Lin))) (env (.m 1 (⟨223, [1]⟩ : Lin))) (V (.W 3 0 7)) (V (.R 3 7)) ((inp 220)) ((inp 221)) ((inp 222)) ((inp 223)) h0 h1 h2 h3 h4 h5

theorem core7_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨156, [1]⟩ : Lin)) = (inp 156).zeroExtend 32)
    (h1 : env (.m 1 (⟨157, [1]⟩ : Lin)) = (inp 157).zeroExtend 32)
    (h2 : env (.m 1 (⟨158, [1]⟩ : Lin)) = (inp 158).zeroExtend 32)
    (h3 : env (.m 1 (⟨159, [1]⟩ : Lin)) = (inp 159).zeroExtend 32)
    (h4 : V (.W 2 0 7) = bswap (V (.R 2 7)))
    (h5 : V (.R 2 7) = ((((0 : Word) ||| (inp 156).zeroExtend 32 <<< 0) ||| (inp 157).zeroExtend 32 <<< 8) ||| (inp 158).zeroExtend 32 <<< 16) ||| (inp 159).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨156, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨157, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨158, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨159, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨156, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨157, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨158, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨159, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨156, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨157, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨158, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨159, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨156, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨157, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨158, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨159, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 7) :=
  shape0 (env (.m 1 (⟨156, [1]⟩ : Lin))) (env (.m 1 (⟨157, [1]⟩ : Lin))) (env (.m 1 (⟨158, [1]⟩ : Lin))) (env (.m 1 (⟨159, [1]⟩ : Lin))) (V (.W 2 0 7)) (V (.R 2 7)) ((inp 156)) ((inp 157)) ((inp 158)) ((inp 159)) h0 h1 h2 h3 h4 h5

theorem core7_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨92, [1]⟩ : Lin)) = (inp 92).zeroExtend 32)
    (h1 : env (.m 1 (⟨93, [1]⟩ : Lin)) = (inp 93).zeroExtend 32)
    (h2 : env (.m 1 (⟨94, [1]⟩ : Lin)) = (inp 94).zeroExtend 32)
    (h3 : env (.m 1 (⟨95, [1]⟩ : Lin)) = (inp 95).zeroExtend 32)
    (h4 : V (.W 1 0 7) = bswap (V (.R 1 7)))
    (h5 : V (.R 1 7) = ((((0 : Word) ||| (inp 92).zeroExtend 32 <<< 0) ||| (inp 93).zeroExtend 32 <<< 8) ||| (inp 94).zeroExtend 32 <<< 16) ||| (inp 95).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨92, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨93, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨94, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨95, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨92, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨93, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨94, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨95, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨92, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨93, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨94, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨95, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨92, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨93, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨94, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨95, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 7) :=
  shape0 (env (.m 1 (⟨92, [1]⟩ : Lin))) (env (.m 1 (⟨93, [1]⟩ : Lin))) (env (.m 1 (⟨94, [1]⟩ : Lin))) (env (.m 1 (⟨95, [1]⟩ : Lin))) (V (.W 1 0 7)) (V (.R 1 7)) ((inp 92)) ((inp 93)) ((inp 94)) ((inp 95)) h0 h1 h2 h3 h4 h5

theorem core7_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨28, [1]⟩ : Lin)) = (inp 28).zeroExtend 32)
    (h1 : env (.m 1 (⟨29, [1]⟩ : Lin)) = (inp 29).zeroExtend 32)
    (h2 : env (.m 1 (⟨30, [1]⟩ : Lin)) = (inp 30).zeroExtend 32)
    (h3 : env (.m 1 (⟨31, [1]⟩ : Lin)) = (inp 31).zeroExtend 32)
    (h4 : V (.W 0 0 7) = bswap (V (.R 0 7)))
    (h5 : V (.R 0 7) = ((((0 : Word) ||| (inp 28).zeroExtend 32 <<< 0) ||| (inp 29).zeroExtend 32 <<< 8) ||| (inp 30).zeroExtend 32 <<< 16) ||| (inp 31).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨28, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨29, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨30, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨31, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨28, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨29, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨30, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨31, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨28, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨29, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨30, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨31, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨28, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨29, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨30, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨31, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 7) :=
  shape0 (env (.m 1 (⟨28, [1]⟩ : Lin))) (env (.m 1 (⟨29, [1]⟩ : Lin))) (env (.m 1 (⟨30, [1]⟩ : Lin))) (env (.m 1 (⟨31, [1]⟩ : Lin))) (V (.W 0 0 7)) (V (.R 0 7)) ((inp 28)) ((inp 29)) ((inp 30)) ((inp 31)) h0 h1 h2 h3 h4 h5

theorem core7_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 215) = V (.A 3 0 (1)))
    (h1 : env (.n 151) = V (.E 3 0 (1)))
    (h2 : env (.n 119) = V (.E 3 0 (3)))
    (h3 : env (.n 135) = V (.E 3 0 (2)))
    (h4 : env (.n 103) = V (.E 3 0 (4)))
    (h5 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h6 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h7 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h8 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h9 : V (.E 3 0 (5)) = V (.A 3 0 (1)) + (V (.E 3 0 (1)) + Sigma1 (V (.E 3 0 (4))) + Ch (V (.E 3 0 (4))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) + V (.KW 3 0 4)))
    (h10 : V (.KW 3 0 4) = 961987163#32 + V (.W 3 0 4))
    (h11 : V (.W 3 0 4) = bswap (V (.R 3 4)))
    (h12 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 215)) (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7))))) = V (.E 3 0 (5)) :=
  shape9 (env (.n 215)) (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.A 3 0 (1))) (V (.E 3 0 (1))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) (V (.E 3 0 (4))) (V (.E 3 0 (5))) (V (.KW 3 0 4)) (V (.W 3 0 4)) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core7_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 214) = V (.A 2 0 (1)))
    (h1 : env (.n 150) = V (.E 2 0 (1)))
    (h2 : env (.n 118) = V (.E 2 0 (3)))
    (h3 : env (.n 134) = V (.E 2 0 (2)))
    (h4 : env (.n 102) = V (.E 2 0 (4)))
    (h5 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h6 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h7 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h8 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h9 : V (.E 2 0 (5)) = V (.A 2 0 (1)) + (V (.E 2 0 (1)) + Sigma1 (V (.E 2 0 (4))) + Ch (V (.E 2 0 (4))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) + V (.KW 2 0 4)))
    (h10 : V (.KW 2 0 4) = 961987163#32 + V (.W 2 0 4))
    (h11 : V (.W 2 0 4) = bswap (V (.R 2 4)))
    (h12 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 214)) (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7))))) = V (.E 2 0 (5)) :=
  shape9 (env (.n 214)) (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.A 2 0 (1))) (V (.E 2 0 (1))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) (V (.E 2 0 (4))) (V (.E 2 0 (5))) (V (.KW 2 0 4)) (V (.W 2 0 4)) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core7_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 213) = V (.A 1 0 (1)))
    (h1 : env (.n 149) = V (.E 1 0 (1)))
    (h2 : env (.n 117) = V (.E 1 0 (3)))
    (h3 : env (.n 133) = V (.E 1 0 (2)))
    (h4 : env (.n 101) = V (.E 1 0 (4)))
    (h5 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h6 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h7 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h8 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h9 : V (.E 1 0 (5)) = V (.A 1 0 (1)) + (V (.E 1 0 (1)) + Sigma1 (V (.E 1 0 (4))) + Ch (V (.E 1 0 (4))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) + V (.KW 1 0 4)))
    (h10 : V (.KW 1 0 4) = 961987163#32 + V (.W 1 0 4))
    (h11 : V (.W 1 0 4) = bswap (V (.R 1 4)))
    (h12 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 213)) (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7))))) = V (.E 1 0 (5)) :=
  shape9 (env (.n 213)) (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.A 1 0 (1))) (V (.E 1 0 (1))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) (V (.E 1 0 (4))) (V (.E 1 0 (5))) (V (.KW 1 0 4)) (V (.W 1 0 4)) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core7_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 212) = V (.A 0 0 (1)))
    (h1 : env (.n 148) = V (.E 0 0 (1)))
    (h2 : env (.n 116) = V (.E 0 0 (3)))
    (h3 : env (.n 132) = V (.E 0 0 (2)))
    (h4 : env (.n 100) = V (.E 0 0 (4)))
    (h5 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h6 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h7 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h8 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h9 : V (.E 0 0 (5)) = V (.A 0 0 (1)) + (V (.E 0 0 (1)) + Sigma1 (V (.E 0 0 (4))) + Ch (V (.E 0 0 (4))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) + V (.KW 0 0 4)))
    (h10 : V (.KW 0 0 4) = 961987163#32 + V (.W 0 0 4))
    (h11 : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (h12 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 212)) (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7))))) = V (.E 0 0 (5)) :=
  shape9 (env (.n 212)) (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.A 0 0 (1))) (V (.E 0 0 (1))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (4))) (V (.E 0 0 (5))) (V (.KW 0 0 4)) (V (.W 0 0 4)) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core7_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 151) = V (.E 3 0 (1)))
    (h1 : env (.n 119) = V (.E 3 0 (3)))
    (h2 : env (.n 135) = V (.E 3 0 (2)))
    (h3 : env (.n 103) = V (.E 3 0 (4)))
    (h4 : env (.n 167) = V (.A 3 0 (4)))
    (h5 : env (.n 199) = V (.A 3 0 (2)))
    (h6 : env (.n 183) = V (.A 3 0 (3)))
    (h7 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h8 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h9 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h10 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h11 : V (.A 3 0 (5)) = (V (.E 3 0 (1)) + Sigma1 (V (.E 3 0 (4))) + Ch (V (.E 3 0 (4))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) + V (.KW 3 0 4)) + (Sigma0 (V (.A 3 0 (4))) + Maj (V (.A 3 0 (4))) (V (.A 3 0 (3))) (V (.A 3 0 (2)))))
    (h12 : V (.KW 3 0 4) = 961987163#32 + V (.W 3 0 4))
    (h13 : V (.W 3 0 4) = bswap (V (.R 3 4)))
    (h14 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 151)) (.xor (.and (.xor (.var (.n 119)) (.var (.n 135))) (.var (.n 103))) (.var (.n 135)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 6) (.shl (.xor (.or (.shr (.var (.n 103)) 5) (.shl (.var (.n 103)) 27)) (.var (.n 103))) 26)) (.or (.shr (.var (.n 103)) 25) (.shl (.var (.n 103)) 7)))) (.or (.and (.var (.n 167)) (.var (.n 199))) (.and (.xor (.var (.n 167)) (.var (.n 199))) (.var (.n 183))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 2) (.shl (.xor (.or (.shr (.var (.n 167)) 11) (.shl (.var (.n 167)) 21)) (.var (.n 167))) 30)) (.or (.shr (.var (.n 167)) 22) (.shl (.var (.n 167)) 10)))) = V (.A 3 0 (5)) :=
  shape10 (env (.n 151)) (env (.n 119)) (env (.n 135)) (env (.n 103)) (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (env (.n 167)) (env (.n 199)) (env (.n 183)) (V (.E 3 0 (1))) (V (.E 3 0 (3))) (V (.E 3 0 (2))) (V (.E 3 0 (4))) (V (.A 3 0 (4))) (V (.A 3 0 (2))) (V (.A 3 0 (3))) (V (.A 3 0 (5))) (V (.KW 3 0 4)) (V (.W 3 0 4)) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core7_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 150) = V (.E 2 0 (1)))
    (h1 : env (.n 118) = V (.E 2 0 (3)))
    (h2 : env (.n 134) = V (.E 2 0 (2)))
    (h3 : env (.n 102) = V (.E 2 0 (4)))
    (h4 : env (.n 166) = V (.A 2 0 (4)))
    (h5 : env (.n 198) = V (.A 2 0 (2)))
    (h6 : env (.n 182) = V (.A 2 0 (3)))
    (h7 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h8 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h9 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h10 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h11 : V (.A 2 0 (5)) = (V (.E 2 0 (1)) + Sigma1 (V (.E 2 0 (4))) + Ch (V (.E 2 0 (4))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) + V (.KW 2 0 4)) + (Sigma0 (V (.A 2 0 (4))) + Maj (V (.A 2 0 (4))) (V (.A 2 0 (3))) (V (.A 2 0 (2)))))
    (h12 : V (.KW 2 0 4) = 961987163#32 + V (.W 2 0 4))
    (h13 : V (.W 2 0 4) = bswap (V (.R 2 4)))
    (h14 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 150)) (.xor (.and (.xor (.var (.n 118)) (.var (.n 134))) (.var (.n 102))) (.var (.n 134)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 6) (.shl (.xor (.or (.shr (.var (.n 102)) 5) (.shl (.var (.n 102)) 27)) (.var (.n 102))) 26)) (.or (.shr (.var (.n 102)) 25) (.shl (.var (.n 102)) 7)))) (.or (.and (.var (.n 166)) (.var (.n 198))) (.and (.xor (.var (.n 166)) (.var (.n 198))) (.var (.n 182))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 2) (.shl (.xor (.or (.shr (.var (.n 166)) 11) (.shl (.var (.n 166)) 21)) (.var (.n 166))) 30)) (.or (.shr (.var (.n 166)) 22) (.shl (.var (.n 166)) 10)))) = V (.A 2 0 (5)) :=
  shape10 (env (.n 150)) (env (.n 118)) (env (.n 134)) (env (.n 102)) (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (env (.n 166)) (env (.n 198)) (env (.n 182)) (V (.E 2 0 (1))) (V (.E 2 0 (3))) (V (.E 2 0 (2))) (V (.E 2 0 (4))) (V (.A 2 0 (4))) (V (.A 2 0 (2))) (V (.A 2 0 (3))) (V (.A 2 0 (5))) (V (.KW 2 0 4)) (V (.W 2 0 4)) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core7_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 149) = V (.E 1 0 (1)))
    (h1 : env (.n 117) = V (.E 1 0 (3)))
    (h2 : env (.n 133) = V (.E 1 0 (2)))
    (h3 : env (.n 101) = V (.E 1 0 (4)))
    (h4 : env (.n 165) = V (.A 1 0 (4)))
    (h5 : env (.n 197) = V (.A 1 0 (2)))
    (h6 : env (.n 181) = V (.A 1 0 (3)))
    (h7 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h8 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h9 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h10 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h11 : V (.A 1 0 (5)) = (V (.E 1 0 (1)) + Sigma1 (V (.E 1 0 (4))) + Ch (V (.E 1 0 (4))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) + V (.KW 1 0 4)) + (Sigma0 (V (.A 1 0 (4))) + Maj (V (.A 1 0 (4))) (V (.A 1 0 (3))) (V (.A 1 0 (2)))))
    (h12 : V (.KW 1 0 4) = 961987163#32 + V (.W 1 0 4))
    (h13 : V (.W 1 0 4) = bswap (V (.R 1 4)))
    (h14 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 149)) (.xor (.and (.xor (.var (.n 117)) (.var (.n 133))) (.var (.n 101))) (.var (.n 133)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 6) (.shl (.xor (.or (.shr (.var (.n 101)) 5) (.shl (.var (.n 101)) 27)) (.var (.n 101))) 26)) (.or (.shr (.var (.n 101)) 25) (.shl (.var (.n 101)) 7)))) (.or (.and (.var (.n 165)) (.var (.n 197))) (.and (.xor (.var (.n 165)) (.var (.n 197))) (.var (.n 181))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 2) (.shl (.xor (.or (.shr (.var (.n 165)) 11) (.shl (.var (.n 165)) 21)) (.var (.n 165))) 30)) (.or (.shr (.var (.n 165)) 22) (.shl (.var (.n 165)) 10)))) = V (.A 1 0 (5)) :=
  shape10 (env (.n 149)) (env (.n 117)) (env (.n 133)) (env (.n 101)) (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (env (.n 165)) (env (.n 197)) (env (.n 181)) (V (.E 1 0 (1))) (V (.E 1 0 (3))) (V (.E 1 0 (2))) (V (.E 1 0 (4))) (V (.A 1 0 (4))) (V (.A 1 0 (2))) (V (.A 1 0 (3))) (V (.A 1 0 (5))) (V (.KW 1 0 4)) (V (.W 1 0 4)) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core7_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 148) = V (.E 0 0 (1)))
    (h1 : env (.n 116) = V (.E 0 0 (3)))
    (h2 : env (.n 132) = V (.E 0 0 (2)))
    (h3 : env (.n 100) = V (.E 0 0 (4)))
    (h4 : env (.n 164) = V (.A 0 0 (4)))
    (h5 : env (.n 196) = V (.A 0 0 (2)))
    (h6 : env (.n 180) = V (.A 0 0 (3)))
    (h7 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h8 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h9 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h10 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h11 : V (.A 0 0 (5)) = (V (.E 0 0 (1)) + Sigma1 (V (.E 0 0 (4))) + Ch (V (.E 0 0 (4))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) + V (.KW 0 0 4)) + (Sigma0 (V (.A 0 0 (4))) + Maj (V (.A 0 0 (4))) (V (.A 0 0 (3))) (V (.A 0 0 (2)))))
    (h12 : V (.KW 0 0 4) = 961987163#32 + V (.W 0 0 4))
    (h13 : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (h14 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.add (.add (.add (.add (.add (.var (.n 148)) (.xor (.and (.xor (.var (.n 116)) (.var (.n 132))) (.var (.n 100))) (.var (.n 132)))) (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) (.const 961987163))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 6) (.shl (.xor (.or (.shr (.var (.n 100)) 5) (.shl (.var (.n 100)) 27)) (.var (.n 100))) 26)) (.or (.shr (.var (.n 100)) 25) (.shl (.var (.n 100)) 7)))) (.or (.and (.var (.n 164)) (.var (.n 196))) (.and (.xor (.var (.n 164)) (.var (.n 196))) (.var (.n 180))))) (.xor (.or (.shr (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 2) (.shl (.xor (.or (.shr (.var (.n 164)) 11) (.shl (.var (.n 164)) 21)) (.var (.n 164))) 30)) (.or (.shr (.var (.n 164)) 22) (.shl (.var (.n 164)) 10)))) = V (.A 0 0 (5)) :=
  shape10 (env (.n 148)) (env (.n 116)) (env (.n 132)) (env (.n 100)) (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (env (.n 164)) (env (.n 196)) (env (.n 180)) (V (.E 0 0 (1))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (4))) (V (.A 0 0 (4))) (V (.A 0 0 (2))) (V (.A 0 0 (3))) (V (.A 0 0 (5))) (V (.KW 0 0 4)) (V (.W 0 0 4)) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem step7 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L7) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 55 K7)) L8 := by
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
  exact invC_of_trees inp env _ T7 L8 (slice_trees_mem prog 4 _ _ 55 K7 K8 T7 slice7 env)
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
      (And.intro ⟨rfl, core7_1015 (qv inp) inp env (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qW_R inp 0 4 (by decide)) (qR inp 0 4)⟩
      (And.intro ⟨rfl, core7_1014 (qv inp) inp env (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qW_R inp 0 4 (by decide)) (qR inp 0 4)⟩
      (And.intro ⟨rfl, core7_1013 (qv inp) inp env (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qW_R inp 0 4 (by decide)) (qR inp 0 4)⟩
      (And.intro ⟨rfl, core7_1012 (qv inp) inp env (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qW_R inp 0 4 (by decide)) (qR inp 0 4)⟩
      (And.intro ⟨rfl, core7_1011 (qv inp) inp env (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qW_R inp 1 4 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core7_1010 (qv inp) inp env (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qW_R inp 1 4 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core7_1009 (qv inp) inp env (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qW_R inp 1 4 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core7_1008 (qv inp) inp env (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qW_R inp 1 4 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core7_1007 (qv inp) inp env (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qW_R inp 2 4 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core7_1006 (qv inp) inp env (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qW_R inp 2 4 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core7_1005 (qv inp) inp env (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qW_R inp 2 4 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core7_1004 (qv inp) inp env (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qW_R inp 2 4 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core7_1003 (qv inp) inp env (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qW_R inp 3 4 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core7_1002 (qv inp) inp env (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qW_R inp 3 4 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core7_1001 (qv inp) inp env (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qW_R inp 3 4 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core7_1000 (qv inp) inp env (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qW_R inp 3 4 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core7_311 (qv inp) inp env (hm 212 (by decide)) (hm 213 (by decide)) (hm 214 (by decide)) (hm 215 (by decide)) (qW_R inp 3 5 (by decide)) (qR inp 3 5)⟩
      (And.intro ⟨rfl, core7_310 (qv inp) inp env (hm 148 (by decide)) (hm 149 (by decide)) (hm 150 (by decide)) (hm 151 (by decide)) (qW_R inp 2 5 (by decide)) (qR inp 2 5)⟩
      (And.intro ⟨rfl, core7_309 (qv inp) inp env (hm 84 (by decide)) (hm 85 (by decide)) (hm 86 (by decide)) (hm 87 (by decide)) (qW_R inp 1 5 (by decide)) (qR inp 1 5)⟩
      (And.intro ⟨rfl, core7_308 (qv inp) inp env (hm 20 (by decide)) (hm 21 (by decide)) (hm 22 (by decide)) (hm 23 (by decide)) (qW_R inp 0 5 (by decide)) (qR inp 0 5)⟩
      (And.intro ⟨rfl, core7_295 (qv inp) inp env (hm 216 (by decide)) (hm 217 (by decide)) (hm 218 (by decide)) (hm 219 (by decide)) (qW_R inp 3 6 (by decide)) (qR inp 3 6)⟩
      (And.intro ⟨rfl, core7_294 (qv inp) inp env (hm 152 (by decide)) (hm 153 (by decide)) (hm 154 (by decide)) (hm 155 (by decide)) (qW_R inp 2 6 (by decide)) (qR inp 2 6)⟩
      (And.intro ⟨rfl, core7_293 (qv inp) inp env (hm 88 (by decide)) (hm 89 (by decide)) (hm 90 (by decide)) (hm 91 (by decide)) (qW_R inp 1 6 (by decide)) (qR inp 1 6)⟩
      (And.intro ⟨rfl, core7_292 (qv inp) inp env (hm 24 (by decide)) (hm 25 (by decide)) (hm 26 (by decide)) (hm 27 (by decide)) (qW_R inp 0 6 (by decide)) (qR inp 0 6)⟩
      (And.intro ⟨rfl, core7_279 (qv inp) inp env (hm 220 (by decide)) (hm 221 (by decide)) (hm 222 (by decide)) (hm 223 (by decide)) (qW_R inp 3 7 (by decide)) (qR inp 3 7)⟩
      (And.intro ⟨rfl, core7_278 (qv inp) inp env (hm 156 (by decide)) (hm 157 (by decide)) (hm 158 (by decide)) (hm 159 (by decide)) (qW_R inp 2 7 (by decide)) (qR inp 2 7)⟩
      (And.intro ⟨rfl, core7_277 (qv inp) inp env (hm 92 (by decide)) (hm 93 (by decide)) (hm 94 (by decide)) (hm 95 (by decide)) (qW_R inp 1 7 (by decide)) (qR inp 1 7)⟩
      (And.intro ⟨rfl, core7_276 (qv inp) inp env (hm 28 (by decide)) (hm 29 (by decide)) (hm 30 (by decide)) (hm 31 (by decide)) (qW_R inp 0 7 (by decide)) (qR inp 0 7)⟩
      (And.intro ⟨rfl, core7_215 (qv inp) inp env h64 h80 h88 h84 h92 (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qE_succI inp 3 0 (4) (by decide)) ((qKW inp 3 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 3 4 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core7_214 (qv inp) inp env h65 h81 h89 h85 h93 (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qE_succI inp 2 0 (4) (by decide)) ((qKW inp 2 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 2 4 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core7_213 (qv inp) inp env h66 h82 h90 h86 h94 (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qE_succI inp 1 0 (4) (by decide)) ((qKW inp 1 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 1 4 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core7_212 (qv inp) inp env h67 h83 h91 h87 h95 (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qE_succI inp 0 0 (4) (by decide)) ((qKW inp 0 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 0 4 (by decide)) (qR inp 0 4)⟩
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
      (And.intro ⟨rfl, core7_151 (qv inp) inp env h80 h88 h84 h92 h76 h68 h72 (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qA_succI inp 3 0 (4) (by decide)) ((qKW inp 3 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 3 4 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core7_150 (qv inp) inp env h81 h89 h85 h93 h77 h69 h73 (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qA_succI inp 2 0 (4) (by decide)) ((qKW inp 2 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 2 4 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core7_149 (qv inp) inp env h82 h90 h86 h94 h78 h70 h74 (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qA_succI inp 1 0 (4) (by decide)) ((qKW inp 1 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 1 4 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core7_148 (qv inp) inp env h83 h91 h87 h95 h79 h71 h75 (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qA_succI inp 0 0 (4) (by decide)) ((qKW inp 0 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])) (qW_R inp 0 4 (by decide)) (qR inp 0 4)⟩
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
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
