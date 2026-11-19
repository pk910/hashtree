import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D5
import Hashtree.Gen.WinAvx2X8P.D4

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice5 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K5 K6 T5 = true := by
  decide +kernel

theorem core5_347 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨236, [1]⟩ : Lin)) = (inp 236).zeroExtend 32)
    (h1 : env (.m 1 (⟨237, [1]⟩ : Lin)) = (inp 237).zeroExtend 32)
    (h2 : env (.m 1 (⟨238, [1]⟩ : Lin)) = (inp 238).zeroExtend 32)
    (h3 : env (.m 1 (⟨239, [1]⟩ : Lin)) = (inp 239).zeroExtend 32)
    (h4 : V (.R 3 11) = ((((0 : Word) ||| (inp 236).zeroExtend 32 <<< 0) ||| (inp 237).zeroExtend 32 <<< 8) ||| (inp 238).zeroExtend 32 <<< 16) ||| (inp 239).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 11) :=
  shape0 (env (.m 1 (⟨236, [1]⟩ : Lin))) (env (.m 1 (⟨237, [1]⟩ : Lin))) (env (.m 1 (⟨238, [1]⟩ : Lin))) (env (.m 1 (⟨239, [1]⟩ : Lin))) (V (.R 3 11)) ((inp 236)) ((inp 237)) ((inp 238)) ((inp 239)) h0 h1 h2 h3 h4

theorem core5_346 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨232, [1]⟩ : Lin)) = (inp 232).zeroExtend 32)
    (h1 : env (.m 1 (⟨233, [1]⟩ : Lin)) = (inp 233).zeroExtend 32)
    (h2 : env (.m 1 (⟨234, [1]⟩ : Lin)) = (inp 234).zeroExtend 32)
    (h3 : env (.m 1 (⟨235, [1]⟩ : Lin)) = (inp 235).zeroExtend 32)
    (h4 : V (.R 3 10) = ((((0 : Word) ||| (inp 232).zeroExtend 32 <<< 0) ||| (inp 233).zeroExtend 32 <<< 8) ||| (inp 234).zeroExtend 32 <<< 16) ||| (inp 235).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 10) :=
  shape0 (env (.m 1 (⟨232, [1]⟩ : Lin))) (env (.m 1 (⟨233, [1]⟩ : Lin))) (env (.m 1 (⟨234, [1]⟩ : Lin))) (env (.m 1 (⟨235, [1]⟩ : Lin))) (V (.R 3 10)) ((inp 232)) ((inp 233)) ((inp 234)) ((inp 235)) h0 h1 h2 h3 h4

theorem core5_345 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨228, [1]⟩ : Lin)) = (inp 228).zeroExtend 32)
    (h1 : env (.m 1 (⟨229, [1]⟩ : Lin)) = (inp 229).zeroExtend 32)
    (h2 : env (.m 1 (⟨230, [1]⟩ : Lin)) = (inp 230).zeroExtend 32)
    (h3 : env (.m 1 (⟨231, [1]⟩ : Lin)) = (inp 231).zeroExtend 32)
    (h4 : V (.R 3 9) = ((((0 : Word) ||| (inp 228).zeroExtend 32 <<< 0) ||| (inp 229).zeroExtend 32 <<< 8) ||| (inp 230).zeroExtend 32 <<< 16) ||| (inp 231).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 9) :=
  shape0 (env (.m 1 (⟨228, [1]⟩ : Lin))) (env (.m 1 (⟨229, [1]⟩ : Lin))) (env (.m 1 (⟨230, [1]⟩ : Lin))) (env (.m 1 (⟨231, [1]⟩ : Lin))) (V (.R 3 9)) ((inp 228)) ((inp 229)) ((inp 230)) ((inp 231)) h0 h1 h2 h3 h4

theorem core5_344 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 8) :=
  shape0 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4

theorem core5_343 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨220, [1]⟩ : Lin)) = (inp 220).zeroExtend 32)
    (h1 : env (.m 1 (⟨221, [1]⟩ : Lin)) = (inp 221).zeroExtend 32)
    (h2 : env (.m 1 (⟨222, [1]⟩ : Lin)) = (inp 222).zeroExtend 32)
    (h3 : env (.m 1 (⟨223, [1]⟩ : Lin)) = (inp 223).zeroExtend 32)
    (h4 : V (.R 3 7) = ((((0 : Word) ||| (inp 220).zeroExtend 32 <<< 0) ||| (inp 221).zeroExtend 32 <<< 8) ||| (inp 222).zeroExtend 32 <<< 16) ||| (inp 223).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨220, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨221, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨222, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨223, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 7) :=
  shape0 (env (.m 1 (⟨220, [1]⟩ : Lin))) (env (.m 1 (⟨221, [1]⟩ : Lin))) (env (.m 1 (⟨222, [1]⟩ : Lin))) (env (.m 1 (⟨223, [1]⟩ : Lin))) (V (.R 3 7)) ((inp 220)) ((inp 221)) ((inp 222)) ((inp 223)) h0 h1 h2 h3 h4

theorem core5_342 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨216, [1]⟩ : Lin)) = (inp 216).zeroExtend 32)
    (h1 : env (.m 1 (⟨217, [1]⟩ : Lin)) = (inp 217).zeroExtend 32)
    (h2 : env (.m 1 (⟨218, [1]⟩ : Lin)) = (inp 218).zeroExtend 32)
    (h3 : env (.m 1 (⟨219, [1]⟩ : Lin)) = (inp 219).zeroExtend 32)
    (h4 : V (.R 3 6) = ((((0 : Word) ||| (inp 216).zeroExtend 32 <<< 0) ||| (inp 217).zeroExtend 32 <<< 8) ||| (inp 218).zeroExtend 32 <<< 16) ||| (inp 219).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨216, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨217, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨218, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨219, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 6) :=
  shape0 (env (.m 1 (⟨216, [1]⟩ : Lin))) (env (.m 1 (⟨217, [1]⟩ : Lin))) (env (.m 1 (⟨218, [1]⟩ : Lin))) (env (.m 1 (⟨219, [1]⟩ : Lin))) (V (.R 3 6)) ((inp 216)) ((inp 217)) ((inp 218)) ((inp 219)) h0 h1 h2 h3 h4

theorem core5_341 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨212, [1]⟩ : Lin)) = (inp 212).zeroExtend 32)
    (h1 : env (.m 1 (⟨213, [1]⟩ : Lin)) = (inp 213).zeroExtend 32)
    (h2 : env (.m 1 (⟨214, [1]⟩ : Lin)) = (inp 214).zeroExtend 32)
    (h3 : env (.m 1 (⟨215, [1]⟩ : Lin)) = (inp 215).zeroExtend 32)
    (h4 : V (.R 3 5) = ((((0 : Word) ||| (inp 212).zeroExtend 32 <<< 0) ||| (inp 213).zeroExtend 32 <<< 8) ||| (inp 214).zeroExtend 32 <<< 16) ||| (inp 215).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨212, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨213, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨214, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨215, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 5) :=
  shape0 (env (.m 1 (⟨212, [1]⟩ : Lin))) (env (.m 1 (⟨213, [1]⟩ : Lin))) (env (.m 1 (⟨214, [1]⟩ : Lin))) (env (.m 1 (⟨215, [1]⟩ : Lin))) (V (.R 3 5)) ((inp 212)) ((inp 213)) ((inp 214)) ((inp 215)) h0 h1 h2 h3 h4

theorem core5_340 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h1 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h2 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h3 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h4 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 4) :=
  shape0 (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4

theorem core5_331 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨172, [1]⟩ : Lin)) = (inp 172).zeroExtend 32)
    (h1 : env (.m 1 (⟨173, [1]⟩ : Lin)) = (inp 173).zeroExtend 32)
    (h2 : env (.m 1 (⟨174, [1]⟩ : Lin)) = (inp 174).zeroExtend 32)
    (h3 : env (.m 1 (⟨175, [1]⟩ : Lin)) = (inp 175).zeroExtend 32)
    (h4 : V (.R 2 11) = ((((0 : Word) ||| (inp 172).zeroExtend 32 <<< 0) ||| (inp 173).zeroExtend 32 <<< 8) ||| (inp 174).zeroExtend 32 <<< 16) ||| (inp 175).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 11) :=
  shape0 (env (.m 1 (⟨172, [1]⟩ : Lin))) (env (.m 1 (⟨173, [1]⟩ : Lin))) (env (.m 1 (⟨174, [1]⟩ : Lin))) (env (.m 1 (⟨175, [1]⟩ : Lin))) (V (.R 2 11)) ((inp 172)) ((inp 173)) ((inp 174)) ((inp 175)) h0 h1 h2 h3 h4

theorem core5_330 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨168, [1]⟩ : Lin)) = (inp 168).zeroExtend 32)
    (h1 : env (.m 1 (⟨169, [1]⟩ : Lin)) = (inp 169).zeroExtend 32)
    (h2 : env (.m 1 (⟨170, [1]⟩ : Lin)) = (inp 170).zeroExtend 32)
    (h3 : env (.m 1 (⟨171, [1]⟩ : Lin)) = (inp 171).zeroExtend 32)
    (h4 : V (.R 2 10) = ((((0 : Word) ||| (inp 168).zeroExtend 32 <<< 0) ||| (inp 169).zeroExtend 32 <<< 8) ||| (inp 170).zeroExtend 32 <<< 16) ||| (inp 171).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 10) :=
  shape0 (env (.m 1 (⟨168, [1]⟩ : Lin))) (env (.m 1 (⟨169, [1]⟩ : Lin))) (env (.m 1 (⟨170, [1]⟩ : Lin))) (env (.m 1 (⟨171, [1]⟩ : Lin))) (V (.R 2 10)) ((inp 168)) ((inp 169)) ((inp 170)) ((inp 171)) h0 h1 h2 h3 h4

theorem core5_329 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨164, [1]⟩ : Lin)) = (inp 164).zeroExtend 32)
    (h1 : env (.m 1 (⟨165, [1]⟩ : Lin)) = (inp 165).zeroExtend 32)
    (h2 : env (.m 1 (⟨166, [1]⟩ : Lin)) = (inp 166).zeroExtend 32)
    (h3 : env (.m 1 (⟨167, [1]⟩ : Lin)) = (inp 167).zeroExtend 32)
    (h4 : V (.R 2 9) = ((((0 : Word) ||| (inp 164).zeroExtend 32 <<< 0) ||| (inp 165).zeroExtend 32 <<< 8) ||| (inp 166).zeroExtend 32 <<< 16) ||| (inp 167).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 9) :=
  shape0 (env (.m 1 (⟨164, [1]⟩ : Lin))) (env (.m 1 (⟨165, [1]⟩ : Lin))) (env (.m 1 (⟨166, [1]⟩ : Lin))) (env (.m 1 (⟨167, [1]⟩ : Lin))) (V (.R 2 9)) ((inp 164)) ((inp 165)) ((inp 166)) ((inp 167)) h0 h1 h2 h3 h4

theorem core5_328 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 8) :=
  shape0 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4

theorem core5_327 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨156, [1]⟩ : Lin)) = (inp 156).zeroExtend 32)
    (h1 : env (.m 1 (⟨157, [1]⟩ : Lin)) = (inp 157).zeroExtend 32)
    (h2 : env (.m 1 (⟨158, [1]⟩ : Lin)) = (inp 158).zeroExtend 32)
    (h3 : env (.m 1 (⟨159, [1]⟩ : Lin)) = (inp 159).zeroExtend 32)
    (h4 : V (.R 2 7) = ((((0 : Word) ||| (inp 156).zeroExtend 32 <<< 0) ||| (inp 157).zeroExtend 32 <<< 8) ||| (inp 158).zeroExtend 32 <<< 16) ||| (inp 159).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨156, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨157, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨158, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨159, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 7) :=
  shape0 (env (.m 1 (⟨156, [1]⟩ : Lin))) (env (.m 1 (⟨157, [1]⟩ : Lin))) (env (.m 1 (⟨158, [1]⟩ : Lin))) (env (.m 1 (⟨159, [1]⟩ : Lin))) (V (.R 2 7)) ((inp 156)) ((inp 157)) ((inp 158)) ((inp 159)) h0 h1 h2 h3 h4

theorem core5_326 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨152, [1]⟩ : Lin)) = (inp 152).zeroExtend 32)
    (h1 : env (.m 1 (⟨153, [1]⟩ : Lin)) = (inp 153).zeroExtend 32)
    (h2 : env (.m 1 (⟨154, [1]⟩ : Lin)) = (inp 154).zeroExtend 32)
    (h3 : env (.m 1 (⟨155, [1]⟩ : Lin)) = (inp 155).zeroExtend 32)
    (h4 : V (.R 2 6) = ((((0 : Word) ||| (inp 152).zeroExtend 32 <<< 0) ||| (inp 153).zeroExtend 32 <<< 8) ||| (inp 154).zeroExtend 32 <<< 16) ||| (inp 155).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨152, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨153, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨154, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨155, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 6) :=
  shape0 (env (.m 1 (⟨152, [1]⟩ : Lin))) (env (.m 1 (⟨153, [1]⟩ : Lin))) (env (.m 1 (⟨154, [1]⟩ : Lin))) (env (.m 1 (⟨155, [1]⟩ : Lin))) (V (.R 2 6)) ((inp 152)) ((inp 153)) ((inp 154)) ((inp 155)) h0 h1 h2 h3 h4

theorem core5_325 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨148, [1]⟩ : Lin)) = (inp 148).zeroExtend 32)
    (h1 : env (.m 1 (⟨149, [1]⟩ : Lin)) = (inp 149).zeroExtend 32)
    (h2 : env (.m 1 (⟨150, [1]⟩ : Lin)) = (inp 150).zeroExtend 32)
    (h3 : env (.m 1 (⟨151, [1]⟩ : Lin)) = (inp 151).zeroExtend 32)
    (h4 : V (.R 2 5) = ((((0 : Word) ||| (inp 148).zeroExtend 32 <<< 0) ||| (inp 149).zeroExtend 32 <<< 8) ||| (inp 150).zeroExtend 32 <<< 16) ||| (inp 151).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨148, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨149, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨150, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨151, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 5) :=
  shape0 (env (.m 1 (⟨148, [1]⟩ : Lin))) (env (.m 1 (⟨149, [1]⟩ : Lin))) (env (.m 1 (⟨150, [1]⟩ : Lin))) (env (.m 1 (⟨151, [1]⟩ : Lin))) (V (.R 2 5)) ((inp 148)) ((inp 149)) ((inp 150)) ((inp 151)) h0 h1 h2 h3 h4

theorem core5_324 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h1 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h2 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h3 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h4 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 4) :=
  shape0 (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4

theorem core5_315 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨348, [1]⟩ : Lin)) = (inp 348).zeroExtend 32)
    (h1 : env (.m 1 (⟨349, [1]⟩ : Lin)) = (inp 349).zeroExtend 32)
    (h2 : env (.m 1 (⟨350, [1]⟩ : Lin)) = (inp 350).zeroExtend 32)
    (h3 : env (.m 1 (⟨351, [1]⟩ : Lin)) = (inp 351).zeroExtend 32)
    (h4 : V (.R 5 7) = ((((0 : Word) ||| (inp 348).zeroExtend 32 <<< 0) ||| (inp 349).zeroExtend 32 <<< 8) ||| (inp 350).zeroExtend 32 <<< 16) ||| (inp 351).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨348, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨349, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨350, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨351, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 7) :=
  shape0 (env (.m 1 (⟨348, [1]⟩ : Lin))) (env (.m 1 (⟨349, [1]⟩ : Lin))) (env (.m 1 (⟨350, [1]⟩ : Lin))) (env (.m 1 (⟨351, [1]⟩ : Lin))) (V (.R 5 7)) ((inp 348)) ((inp 349)) ((inp 350)) ((inp 351)) h0 h1 h2 h3 h4

theorem core5_314 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨344, [1]⟩ : Lin)) = (inp 344).zeroExtend 32)
    (h1 : env (.m 1 (⟨345, [1]⟩ : Lin)) = (inp 345).zeroExtend 32)
    (h2 : env (.m 1 (⟨346, [1]⟩ : Lin)) = (inp 346).zeroExtend 32)
    (h3 : env (.m 1 (⟨347, [1]⟩ : Lin)) = (inp 347).zeroExtend 32)
    (h4 : V (.R 5 6) = ((((0 : Word) ||| (inp 344).zeroExtend 32 <<< 0) ||| (inp 345).zeroExtend 32 <<< 8) ||| (inp 346).zeroExtend 32 <<< 16) ||| (inp 347).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨344, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨345, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨346, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨347, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 6) :=
  shape0 (env (.m 1 (⟨344, [1]⟩ : Lin))) (env (.m 1 (⟨345, [1]⟩ : Lin))) (env (.m 1 (⟨346, [1]⟩ : Lin))) (env (.m 1 (⟨347, [1]⟩ : Lin))) (V (.R 5 6)) ((inp 344)) ((inp 345)) ((inp 346)) ((inp 347)) h0 h1 h2 h3 h4

theorem core5_313 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨340, [1]⟩ : Lin)) = (inp 340).zeroExtend 32)
    (h1 : env (.m 1 (⟨341, [1]⟩ : Lin)) = (inp 341).zeroExtend 32)
    (h2 : env (.m 1 (⟨342, [1]⟩ : Lin)) = (inp 342).zeroExtend 32)
    (h3 : env (.m 1 (⟨343, [1]⟩ : Lin)) = (inp 343).zeroExtend 32)
    (h4 : V (.R 5 5) = ((((0 : Word) ||| (inp 340).zeroExtend 32 <<< 0) ||| (inp 341).zeroExtend 32 <<< 8) ||| (inp 342).zeroExtend 32 <<< 16) ||| (inp 343).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨340, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨341, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨342, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨343, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 5) :=
  shape0 (env (.m 1 (⟨340, [1]⟩ : Lin))) (env (.m 1 (⟨341, [1]⟩ : Lin))) (env (.m 1 (⟨342, [1]⟩ : Lin))) (env (.m 1 (⟨343, [1]⟩ : Lin))) (V (.R 5 5)) ((inp 340)) ((inp 341)) ((inp 342)) ((inp 343)) h0 h1 h2 h3 h4

theorem core5_312 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨336, [1]⟩ : Lin)) = (inp 336).zeroExtend 32)
    (h1 : env (.m 1 (⟨337, [1]⟩ : Lin)) = (inp 337).zeroExtend 32)
    (h2 : env (.m 1 (⟨338, [1]⟩ : Lin)) = (inp 338).zeroExtend 32)
    (h3 : env (.m 1 (⟨339, [1]⟩ : Lin)) = (inp 339).zeroExtend 32)
    (h4 : V (.R 5 4) = ((((0 : Word) ||| (inp 336).zeroExtend 32 <<< 0) ||| (inp 337).zeroExtend 32 <<< 8) ||| (inp 338).zeroExtend 32 <<< 16) ||| (inp 339).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨336, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨337, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨338, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨339, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 4) :=
  shape0 (env (.m 1 (⟨336, [1]⟩ : Lin))) (env (.m 1 (⟨337, [1]⟩ : Lin))) (env (.m 1 (⟨338, [1]⟩ : Lin))) (env (.m 1 (⟨339, [1]⟩ : Lin))) (V (.R 5 4)) ((inp 336)) ((inp 337)) ((inp 338)) ((inp 339)) h0 h1 h2 h3 h4

theorem core5_299 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨284, [1]⟩ : Lin)) = (inp 284).zeroExtend 32)
    (h1 : env (.m 1 (⟨285, [1]⟩ : Lin)) = (inp 285).zeroExtend 32)
    (h2 : env (.m 1 (⟨286, [1]⟩ : Lin)) = (inp 286).zeroExtend 32)
    (h3 : env (.m 1 (⟨287, [1]⟩ : Lin)) = (inp 287).zeroExtend 32)
    (h4 : V (.R 4 7) = ((((0 : Word) ||| (inp 284).zeroExtend 32 <<< 0) ||| (inp 285).zeroExtend 32 <<< 8) ||| (inp 286).zeroExtend 32 <<< 16) ||| (inp 287).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨284, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨285, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨286, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨287, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 7) :=
  shape0 (env (.m 1 (⟨284, [1]⟩ : Lin))) (env (.m 1 (⟨285, [1]⟩ : Lin))) (env (.m 1 (⟨286, [1]⟩ : Lin))) (env (.m 1 (⟨287, [1]⟩ : Lin))) (V (.R 4 7)) ((inp 284)) ((inp 285)) ((inp 286)) ((inp 287)) h0 h1 h2 h3 h4

theorem core5_298 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨280, [1]⟩ : Lin)) = (inp 280).zeroExtend 32)
    (h1 : env (.m 1 (⟨281, [1]⟩ : Lin)) = (inp 281).zeroExtend 32)
    (h2 : env (.m 1 (⟨282, [1]⟩ : Lin)) = (inp 282).zeroExtend 32)
    (h3 : env (.m 1 (⟨283, [1]⟩ : Lin)) = (inp 283).zeroExtend 32)
    (h4 : V (.R 4 6) = ((((0 : Word) ||| (inp 280).zeroExtend 32 <<< 0) ||| (inp 281).zeroExtend 32 <<< 8) ||| (inp 282).zeroExtend 32 <<< 16) ||| (inp 283).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨280, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨281, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨282, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨283, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 6) :=
  shape0 (env (.m 1 (⟨280, [1]⟩ : Lin))) (env (.m 1 (⟨281, [1]⟩ : Lin))) (env (.m 1 (⟨282, [1]⟩ : Lin))) (env (.m 1 (⟨283, [1]⟩ : Lin))) (V (.R 4 6)) ((inp 280)) ((inp 281)) ((inp 282)) ((inp 283)) h0 h1 h2 h3 h4

theorem core5_297 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨276, [1]⟩ : Lin)) = (inp 276).zeroExtend 32)
    (h1 : env (.m 1 (⟨277, [1]⟩ : Lin)) = (inp 277).zeroExtend 32)
    (h2 : env (.m 1 (⟨278, [1]⟩ : Lin)) = (inp 278).zeroExtend 32)
    (h3 : env (.m 1 (⟨279, [1]⟩ : Lin)) = (inp 279).zeroExtend 32)
    (h4 : V (.R 4 5) = ((((0 : Word) ||| (inp 276).zeroExtend 32 <<< 0) ||| (inp 277).zeroExtend 32 <<< 8) ||| (inp 278).zeroExtend 32 <<< 16) ||| (inp 279).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨276, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨277, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨278, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨279, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 5) :=
  shape0 (env (.m 1 (⟨276, [1]⟩ : Lin))) (env (.m 1 (⟨277, [1]⟩ : Lin))) (env (.m 1 (⟨278, [1]⟩ : Lin))) (env (.m 1 (⟨279, [1]⟩ : Lin))) (V (.R 4 5)) ((inp 276)) ((inp 277)) ((inp 278)) ((inp 279)) h0 h1 h2 h3 h4

theorem core5_296 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨272, [1]⟩ : Lin)) = (inp 272).zeroExtend 32)
    (h1 : env (.m 1 (⟨273, [1]⟩ : Lin)) = (inp 273).zeroExtend 32)
    (h2 : env (.m 1 (⟨274, [1]⟩ : Lin)) = (inp 274).zeroExtend 32)
    (h3 : env (.m 1 (⟨275, [1]⟩ : Lin)) = (inp 275).zeroExtend 32)
    (h4 : V (.R 4 4) = ((((0 : Word) ||| (inp 272).zeroExtend 32 <<< 0) ||| (inp 273).zeroExtend 32 <<< 8) ||| (inp 274).zeroExtend 32 <<< 16) ||| (inp 275).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨272, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨273, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨274, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨275, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 4) :=
  shape0 (env (.m 1 (⟨272, [1]⟩ : Lin))) (env (.m 1 (⟨273, [1]⟩ : Lin))) (env (.m 1 (⟨274, [1]⟩ : Lin))) (env (.m 1 (⟨275, [1]⟩ : Lin))) (V (.R 4 4)) ((inp 272)) ((inp 273)) ((inp 274)) ((inp 275)) h0 h1 h2 h3 h4

theorem core5_283 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨460, [1]⟩ : Lin)) = (inp 460).zeroExtend 32)
    (h1 : env (.m 1 (⟨461, [1]⟩ : Lin)) = (inp 461).zeroExtend 32)
    (h2 : env (.m 1 (⟨462, [1]⟩ : Lin)) = (inp 462).zeroExtend 32)
    (h3 : env (.m 1 (⟨463, [1]⟩ : Lin)) = (inp 463).zeroExtend 32)
    (h4 : V (.R 7 3) = ((((0 : Word) ||| (inp 460).zeroExtend 32 <<< 0) ||| (inp 461).zeroExtend 32 <<< 8) ||| (inp 462).zeroExtend 32 <<< 16) ||| (inp 463).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨460, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨461, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨462, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨463, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 3) :=
  shape0 (env (.m 1 (⟨460, [1]⟩ : Lin))) (env (.m 1 (⟨461, [1]⟩ : Lin))) (env (.m 1 (⟨462, [1]⟩ : Lin))) (env (.m 1 (⟨463, [1]⟩ : Lin))) (V (.R 7 3)) ((inp 460)) ((inp 461)) ((inp 462)) ((inp 463)) h0 h1 h2 h3 h4

theorem core5_282 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨456, [1]⟩ : Lin)) = (inp 456).zeroExtend 32)
    (h1 : env (.m 1 (⟨457, [1]⟩ : Lin)) = (inp 457).zeroExtend 32)
    (h2 : env (.m 1 (⟨458, [1]⟩ : Lin)) = (inp 458).zeroExtend 32)
    (h3 : env (.m 1 (⟨459, [1]⟩ : Lin)) = (inp 459).zeroExtend 32)
    (h4 : V (.R 7 2) = ((((0 : Word) ||| (inp 456).zeroExtend 32 <<< 0) ||| (inp 457).zeroExtend 32 <<< 8) ||| (inp 458).zeroExtend 32 <<< 16) ||| (inp 459).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨456, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨457, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨458, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨459, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 2) :=
  shape0 (env (.m 1 (⟨456, [1]⟩ : Lin))) (env (.m 1 (⟨457, [1]⟩ : Lin))) (env (.m 1 (⟨458, [1]⟩ : Lin))) (env (.m 1 (⟨459, [1]⟩ : Lin))) (V (.R 7 2)) ((inp 456)) ((inp 457)) ((inp 458)) ((inp 459)) h0 h1 h2 h3 h4

theorem core5_281 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨452, [1]⟩ : Lin)) = (inp 452).zeroExtend 32)
    (h1 : env (.m 1 (⟨453, [1]⟩ : Lin)) = (inp 453).zeroExtend 32)
    (h2 : env (.m 1 (⟨454, [1]⟩ : Lin)) = (inp 454).zeroExtend 32)
    (h3 : env (.m 1 (⟨455, [1]⟩ : Lin)) = (inp 455).zeroExtend 32)
    (h4 : V (.R 7 1) = ((((0 : Word) ||| (inp 452).zeroExtend 32 <<< 0) ||| (inp 453).zeroExtend 32 <<< 8) ||| (inp 454).zeroExtend 32 <<< 16) ||| (inp 455).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨452, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨453, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨454, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨455, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 1) :=
  shape0 (env (.m 1 (⟨452, [1]⟩ : Lin))) (env (.m 1 (⟨453, [1]⟩ : Lin))) (env (.m 1 (⟨454, [1]⟩ : Lin))) (env (.m 1 (⟨455, [1]⟩ : Lin))) (V (.R 7 1)) ((inp 452)) ((inp 453)) ((inp 454)) ((inp 455)) h0 h1 h2 h3 h4

theorem core5_280 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨448, [1]⟩ : Lin)) = (inp 448).zeroExtend 32)
    (h1 : env (.m 1 (⟨449, [1]⟩ : Lin)) = (inp 449).zeroExtend 32)
    (h2 : env (.m 1 (⟨450, [1]⟩ : Lin)) = (inp 450).zeroExtend 32)
    (h3 : env (.m 1 (⟨451, [1]⟩ : Lin)) = (inp 451).zeroExtend 32)
    (h4 : V (.R 7 0) = ((((0 : Word) ||| (inp 448).zeroExtend 32 <<< 0) ||| (inp 449).zeroExtend 32 <<< 8) ||| (inp 450).zeroExtend 32 <<< 16) ||| (inp 451).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨448, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨449, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨450, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨451, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 0) :=
  shape0 (env (.m 1 (⟨448, [1]⟩ : Lin))) (env (.m 1 (⟨449, [1]⟩ : Lin))) (env (.m 1 (⟨450, [1]⟩ : Lin))) (env (.m 1 (⟨451, [1]⟩ : Lin))) (V (.R 7 0)) ((inp 448)) ((inp 449)) ((inp 450)) ((inp 451)) h0 h1 h2 h3 h4

theorem core5_267 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨396, [1]⟩ : Lin)) = (inp 396).zeroExtend 32)
    (h1 : env (.m 1 (⟨397, [1]⟩ : Lin)) = (inp 397).zeroExtend 32)
    (h2 : env (.m 1 (⟨398, [1]⟩ : Lin)) = (inp 398).zeroExtend 32)
    (h3 : env (.m 1 (⟨399, [1]⟩ : Lin)) = (inp 399).zeroExtend 32)
    (h4 : V (.R 6 3) = ((((0 : Word) ||| (inp 396).zeroExtend 32 <<< 0) ||| (inp 397).zeroExtend 32 <<< 8) ||| (inp 398).zeroExtend 32 <<< 16) ||| (inp 399).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨396, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨397, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨398, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨399, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 3) :=
  shape0 (env (.m 1 (⟨396, [1]⟩ : Lin))) (env (.m 1 (⟨397, [1]⟩ : Lin))) (env (.m 1 (⟨398, [1]⟩ : Lin))) (env (.m 1 (⟨399, [1]⟩ : Lin))) (V (.R 6 3)) ((inp 396)) ((inp 397)) ((inp 398)) ((inp 399)) h0 h1 h2 h3 h4

theorem core5_266 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨392, [1]⟩ : Lin)) = (inp 392).zeroExtend 32)
    (h1 : env (.m 1 (⟨393, [1]⟩ : Lin)) = (inp 393).zeroExtend 32)
    (h2 : env (.m 1 (⟨394, [1]⟩ : Lin)) = (inp 394).zeroExtend 32)
    (h3 : env (.m 1 (⟨395, [1]⟩ : Lin)) = (inp 395).zeroExtend 32)
    (h4 : V (.R 6 2) = ((((0 : Word) ||| (inp 392).zeroExtend 32 <<< 0) ||| (inp 393).zeroExtend 32 <<< 8) ||| (inp 394).zeroExtend 32 <<< 16) ||| (inp 395).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨392, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨393, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨394, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨395, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 2) :=
  shape0 (env (.m 1 (⟨392, [1]⟩ : Lin))) (env (.m 1 (⟨393, [1]⟩ : Lin))) (env (.m 1 (⟨394, [1]⟩ : Lin))) (env (.m 1 (⟨395, [1]⟩ : Lin))) (V (.R 6 2)) ((inp 392)) ((inp 393)) ((inp 394)) ((inp 395)) h0 h1 h2 h3 h4

theorem core5_265 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨388, [1]⟩ : Lin)) = (inp 388).zeroExtend 32)
    (h1 : env (.m 1 (⟨389, [1]⟩ : Lin)) = (inp 389).zeroExtend 32)
    (h2 : env (.m 1 (⟨390, [1]⟩ : Lin)) = (inp 390).zeroExtend 32)
    (h3 : env (.m 1 (⟨391, [1]⟩ : Lin)) = (inp 391).zeroExtend 32)
    (h4 : V (.R 6 1) = ((((0 : Word) ||| (inp 388).zeroExtend 32 <<< 0) ||| (inp 389).zeroExtend 32 <<< 8) ||| (inp 390).zeroExtend 32 <<< 16) ||| (inp 391).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨388, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨389, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨390, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨391, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 1) :=
  shape0 (env (.m 1 (⟨388, [1]⟩ : Lin))) (env (.m 1 (⟨389, [1]⟩ : Lin))) (env (.m 1 (⟨390, [1]⟩ : Lin))) (env (.m 1 (⟨391, [1]⟩ : Lin))) (V (.R 6 1)) ((inp 388)) ((inp 389)) ((inp 390)) ((inp 391)) h0 h1 h2 h3 h4

theorem core5_264 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨384, [1]⟩ : Lin)) = (inp 384).zeroExtend 32)
    (h1 : env (.m 1 (⟨385, [1]⟩ : Lin)) = (inp 385).zeroExtend 32)
    (h2 : env (.m 1 (⟨386, [1]⟩ : Lin)) = (inp 386).zeroExtend 32)
    (h3 : env (.m 1 (⟨387, [1]⟩ : Lin)) = (inp 387).zeroExtend 32)
    (h4 : V (.R 6 0) = ((((0 : Word) ||| (inp 384).zeroExtend 32 <<< 0) ||| (inp 385).zeroExtend 32 <<< 8) ||| (inp 386).zeroExtend 32 <<< 16) ||| (inp 387).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨384, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨385, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨386, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨387, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 0) :=
  shape0 (env (.m 1 (⟨384, [1]⟩ : Lin))) (env (.m 1 (⟨385, [1]⟩ : Lin))) (env (.m 1 (⟨386, [1]⟩ : Lin))) (env (.m 1 (⟨387, [1]⟩ : Lin))) (V (.R 6 0)) ((inp 384)) ((inp 385)) ((inp 386)) ((inp 387)) h0 h1 h2 h3 h4

theorem core5_251 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨332, [1]⟩ : Lin)) = (inp 332).zeroExtend 32)
    (h1 : env (.m 1 (⟨333, [1]⟩ : Lin)) = (inp 333).zeroExtend 32)
    (h2 : env (.m 1 (⟨334, [1]⟩ : Lin)) = (inp 334).zeroExtend 32)
    (h3 : env (.m 1 (⟨335, [1]⟩ : Lin)) = (inp 335).zeroExtend 32)
    (h4 : V (.R 5 3) = ((((0 : Word) ||| (inp 332).zeroExtend 32 <<< 0) ||| (inp 333).zeroExtend 32 <<< 8) ||| (inp 334).zeroExtend 32 <<< 16) ||| (inp 335).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨332, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨333, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨334, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨335, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 3) :=
  shape0 (env (.m 1 (⟨332, [1]⟩ : Lin))) (env (.m 1 (⟨333, [1]⟩ : Lin))) (env (.m 1 (⟨334, [1]⟩ : Lin))) (env (.m 1 (⟨335, [1]⟩ : Lin))) (V (.R 5 3)) ((inp 332)) ((inp 333)) ((inp 334)) ((inp 335)) h0 h1 h2 h3 h4

theorem core5_250 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨328, [1]⟩ : Lin)) = (inp 328).zeroExtend 32)
    (h1 : env (.m 1 (⟨329, [1]⟩ : Lin)) = (inp 329).zeroExtend 32)
    (h2 : env (.m 1 (⟨330, [1]⟩ : Lin)) = (inp 330).zeroExtend 32)
    (h3 : env (.m 1 (⟨331, [1]⟩ : Lin)) = (inp 331).zeroExtend 32)
    (h4 : V (.R 5 2) = ((((0 : Word) ||| (inp 328).zeroExtend 32 <<< 0) ||| (inp 329).zeroExtend 32 <<< 8) ||| (inp 330).zeroExtend 32 <<< 16) ||| (inp 331).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨328, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨329, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨330, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨331, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 2) :=
  shape0 (env (.m 1 (⟨328, [1]⟩ : Lin))) (env (.m 1 (⟨329, [1]⟩ : Lin))) (env (.m 1 (⟨330, [1]⟩ : Lin))) (env (.m 1 (⟨331, [1]⟩ : Lin))) (V (.R 5 2)) ((inp 328)) ((inp 329)) ((inp 330)) ((inp 331)) h0 h1 h2 h3 h4

theorem core5_249 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨324, [1]⟩ : Lin)) = (inp 324).zeroExtend 32)
    (h1 : env (.m 1 (⟨325, [1]⟩ : Lin)) = (inp 325).zeroExtend 32)
    (h2 : env (.m 1 (⟨326, [1]⟩ : Lin)) = (inp 326).zeroExtend 32)
    (h3 : env (.m 1 (⟨327, [1]⟩ : Lin)) = (inp 327).zeroExtend 32)
    (h4 : V (.R 5 1) = ((((0 : Word) ||| (inp 324).zeroExtend 32 <<< 0) ||| (inp 325).zeroExtend 32 <<< 8) ||| (inp 326).zeroExtend 32 <<< 16) ||| (inp 327).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨324, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨325, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨326, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨327, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 1) :=
  shape0 (env (.m 1 (⟨324, [1]⟩ : Lin))) (env (.m 1 (⟨325, [1]⟩ : Lin))) (env (.m 1 (⟨326, [1]⟩ : Lin))) (env (.m 1 (⟨327, [1]⟩ : Lin))) (V (.R 5 1)) ((inp 324)) ((inp 325)) ((inp 326)) ((inp 327)) h0 h1 h2 h3 h4

theorem core5_248 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨320, [1]⟩ : Lin)) = (inp 320).zeroExtend 32)
    (h1 : env (.m 1 (⟨321, [1]⟩ : Lin)) = (inp 321).zeroExtend 32)
    (h2 : env (.m 1 (⟨322, [1]⟩ : Lin)) = (inp 322).zeroExtend 32)
    (h3 : env (.m 1 (⟨323, [1]⟩ : Lin)) = (inp 323).zeroExtend 32)
    (h4 : V (.R 5 0) = ((((0 : Word) ||| (inp 320).zeroExtend 32 <<< 0) ||| (inp 321).zeroExtend 32 <<< 8) ||| (inp 322).zeroExtend 32 <<< 16) ||| (inp 323).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨320, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨321, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨322, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨323, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 5 0) :=
  shape0 (env (.m 1 (⟨320, [1]⟩ : Lin))) (env (.m 1 (⟨321, [1]⟩ : Lin))) (env (.m 1 (⟨322, [1]⟩ : Lin))) (env (.m 1 (⟨323, [1]⟩ : Lin))) (V (.R 5 0)) ((inp 320)) ((inp 321)) ((inp 322)) ((inp 323)) h0 h1 h2 h3 h4

theorem core5_235 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨268, [1]⟩ : Lin)) = (inp 268).zeroExtend 32)
    (h1 : env (.m 1 (⟨269, [1]⟩ : Lin)) = (inp 269).zeroExtend 32)
    (h2 : env (.m 1 (⟨270, [1]⟩ : Lin)) = (inp 270).zeroExtend 32)
    (h3 : env (.m 1 (⟨271, [1]⟩ : Lin)) = (inp 271).zeroExtend 32)
    (h4 : V (.R 4 3) = ((((0 : Word) ||| (inp 268).zeroExtend 32 <<< 0) ||| (inp 269).zeroExtend 32 <<< 8) ||| (inp 270).zeroExtend 32 <<< 16) ||| (inp 271).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨268, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨269, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨270, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨271, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 3) :=
  shape0 (env (.m 1 (⟨268, [1]⟩ : Lin))) (env (.m 1 (⟨269, [1]⟩ : Lin))) (env (.m 1 (⟨270, [1]⟩ : Lin))) (env (.m 1 (⟨271, [1]⟩ : Lin))) (V (.R 4 3)) ((inp 268)) ((inp 269)) ((inp 270)) ((inp 271)) h0 h1 h2 h3 h4

theorem core5_234 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨264, [1]⟩ : Lin)) = (inp 264).zeroExtend 32)
    (h1 : env (.m 1 (⟨265, [1]⟩ : Lin)) = (inp 265).zeroExtend 32)
    (h2 : env (.m 1 (⟨266, [1]⟩ : Lin)) = (inp 266).zeroExtend 32)
    (h3 : env (.m 1 (⟨267, [1]⟩ : Lin)) = (inp 267).zeroExtend 32)
    (h4 : V (.R 4 2) = ((((0 : Word) ||| (inp 264).zeroExtend 32 <<< 0) ||| (inp 265).zeroExtend 32 <<< 8) ||| (inp 266).zeroExtend 32 <<< 16) ||| (inp 267).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨264, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨265, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨266, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨267, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 2) :=
  shape0 (env (.m 1 (⟨264, [1]⟩ : Lin))) (env (.m 1 (⟨265, [1]⟩ : Lin))) (env (.m 1 (⟨266, [1]⟩ : Lin))) (env (.m 1 (⟨267, [1]⟩ : Lin))) (V (.R 4 2)) ((inp 264)) ((inp 265)) ((inp 266)) ((inp 267)) h0 h1 h2 h3 h4

theorem core5_233 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨260, [1]⟩ : Lin)) = (inp 260).zeroExtend 32)
    (h1 : env (.m 1 (⟨261, [1]⟩ : Lin)) = (inp 261).zeroExtend 32)
    (h2 : env (.m 1 (⟨262, [1]⟩ : Lin)) = (inp 262).zeroExtend 32)
    (h3 : env (.m 1 (⟨263, [1]⟩ : Lin)) = (inp 263).zeroExtend 32)
    (h4 : V (.R 4 1) = ((((0 : Word) ||| (inp 260).zeroExtend 32 <<< 0) ||| (inp 261).zeroExtend 32 <<< 8) ||| (inp 262).zeroExtend 32 <<< 16) ||| (inp 263).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨260, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨261, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨262, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨263, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 1) :=
  shape0 (env (.m 1 (⟨260, [1]⟩ : Lin))) (env (.m 1 (⟨261, [1]⟩ : Lin))) (env (.m 1 (⟨262, [1]⟩ : Lin))) (env (.m 1 (⟨263, [1]⟩ : Lin))) (V (.R 4 1)) ((inp 260)) ((inp 261)) ((inp 262)) ((inp 263)) h0 h1 h2 h3 h4

theorem core5_232 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨256, [1]⟩ : Lin)) = (inp 256).zeroExtend 32)
    (h1 : env (.m 1 (⟨257, [1]⟩ : Lin)) = (inp 257).zeroExtend 32)
    (h2 : env (.m 1 (⟨258, [1]⟩ : Lin)) = (inp 258).zeroExtend 32)
    (h3 : env (.m 1 (⟨259, [1]⟩ : Lin)) = (inp 259).zeroExtend 32)
    (h4 : V (.R 4 0) = ((((0 : Word) ||| (inp 256).zeroExtend 32 <<< 0) ||| (inp 257).zeroExtend 32 <<< 8) ||| (inp 258).zeroExtend 32 <<< 16) ||| (inp 259).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨256, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨257, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨258, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨259, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 4 0) :=
  shape0 (env (.m 1 (⟨256, [1]⟩ : Lin))) (env (.m 1 (⟨257, [1]⟩ : Lin))) (env (.m 1 (⟨258, [1]⟩ : Lin))) (env (.m 1 (⟨259, [1]⟩ : Lin))) (V (.R 4 0)) ((inp 256)) ((inp 257)) ((inp 258)) ((inp 259)) h0 h1 h2 h3 h4

theorem step5 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L5) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K5)) L6 := by
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
  exact invC_of_trees inp env _ T5 L6 (slice_trees_mem prog 4 _ _ 8 K5 K6 T5 slice5 env)
      (And.intro ⟨rfl, core5_347 (qv inp) inp env (hm 236 (by decide)) (hm 237 (by decide)) (hm 238 (by decide)) (hm 239 (by decide)) (qR inp 3 11)⟩
      (And.intro ⟨rfl, core5_346 (qv inp) inp env (hm 232 (by decide)) (hm 233 (by decide)) (hm 234 (by decide)) (hm 235 (by decide)) (qR inp 3 10)⟩
      (And.intro ⟨rfl, core5_345 (qv inp) inp env (hm 228 (by decide)) (hm 229 (by decide)) (hm 230 (by decide)) (hm 231 (by decide)) (qR inp 3 9)⟩
      (And.intro ⟨rfl, core5_344 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core5_343 (qv inp) inp env (hm 220 (by decide)) (hm 221 (by decide)) (hm 222 (by decide)) (hm 223 (by decide)) (qR inp 3 7)⟩
      (And.intro ⟨rfl, core5_342 (qv inp) inp env (hm 216 (by decide)) (hm 217 (by decide)) (hm 218 (by decide)) (hm 219 (by decide)) (qR inp 3 6)⟩
      (And.intro ⟨rfl, core5_341 (qv inp) inp env (hm 212 (by decide)) (hm 213 (by decide)) (hm 214 (by decide)) (hm 215 (by decide)) (qR inp 3 5)⟩
      (And.intro ⟨rfl, core5_340 (qv inp) inp env (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core5_331 (qv inp) inp env (hm 172 (by decide)) (hm 173 (by decide)) (hm 174 (by decide)) (hm 175 (by decide)) (qR inp 2 11)⟩
      (And.intro ⟨rfl, core5_330 (qv inp) inp env (hm 168 (by decide)) (hm 169 (by decide)) (hm 170 (by decide)) (hm 171 (by decide)) (qR inp 2 10)⟩
      (And.intro ⟨rfl, core5_329 (qv inp) inp env (hm 164 (by decide)) (hm 165 (by decide)) (hm 166 (by decide)) (hm 167 (by decide)) (qR inp 2 9)⟩
      (And.intro ⟨rfl, core5_328 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core5_327 (qv inp) inp env (hm 156 (by decide)) (hm 157 (by decide)) (hm 158 (by decide)) (hm 159 (by decide)) (qR inp 2 7)⟩
      (And.intro ⟨rfl, core5_326 (qv inp) inp env (hm 152 (by decide)) (hm 153 (by decide)) (hm 154 (by decide)) (hm 155 (by decide)) (qR inp 2 6)⟩
      (And.intro ⟨rfl, core5_325 (qv inp) inp env (hm 148 (by decide)) (hm 149 (by decide)) (hm 150 (by decide)) (hm 151 (by decide)) (qR inp 2 5)⟩
      (And.intro ⟨rfl, core5_324 (qv inp) inp env (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core5_315 (qv inp) inp env (hm 348 (by decide)) (hm 349 (by decide)) (hm 350 (by decide)) (hm 351 (by decide)) (qR inp 5 7)⟩
      (And.intro ⟨rfl, core5_314 (qv inp) inp env (hm 344 (by decide)) (hm 345 (by decide)) (hm 346 (by decide)) (hm 347 (by decide)) (qR inp 5 6)⟩
      (And.intro ⟨rfl, core5_313 (qv inp) inp env (hm 340 (by decide)) (hm 341 (by decide)) (hm 342 (by decide)) (hm 343 (by decide)) (qR inp 5 5)⟩
      (And.intro ⟨rfl, core5_312 (qv inp) inp env (hm 336 (by decide)) (hm 337 (by decide)) (hm 338 (by decide)) (hm 339 (by decide)) (qR inp 5 4)⟩
      (And.intro ⟨rfl, h4⟩
      (And.intro ⟨rfl, h5⟩
      (And.intro ⟨rfl, h6⟩
      (And.intro ⟨rfl, h7⟩
      (And.intro ⟨rfl, core5_299 (qv inp) inp env (hm 284 (by decide)) (hm 285 (by decide)) (hm 286 (by decide)) (hm 287 (by decide)) (qR inp 4 7)⟩
      (And.intro ⟨rfl, core5_298 (qv inp) inp env (hm 280 (by decide)) (hm 281 (by decide)) (hm 282 (by decide)) (hm 283 (by decide)) (qR inp 4 6)⟩
      (And.intro ⟨rfl, core5_297 (qv inp) inp env (hm 276 (by decide)) (hm 277 (by decide)) (hm 278 (by decide)) (hm 279 (by decide)) (qR inp 4 5)⟩
      (And.intro ⟨rfl, core5_296 (qv inp) inp env (hm 272 (by decide)) (hm 273 (by decide)) (hm 274 (by decide)) (hm 275 (by decide)) (qR inp 4 4)⟩
      (And.intro ⟨rfl, h12⟩
      (And.intro ⟨rfl, h13⟩
      (And.intro ⟨rfl, h14⟩
      (And.intro ⟨rfl, h15⟩
      (And.intro ⟨rfl, core5_283 (qv inp) inp env (hm 460 (by decide)) (hm 461 (by decide)) (hm 462 (by decide)) (hm 463 (by decide)) (qR inp 7 3)⟩
      (And.intro ⟨rfl, core5_282 (qv inp) inp env (hm 456 (by decide)) (hm 457 (by decide)) (hm 458 (by decide)) (hm 459 (by decide)) (qR inp 7 2)⟩
      (And.intro ⟨rfl, core5_281 (qv inp) inp env (hm 452 (by decide)) (hm 453 (by decide)) (hm 454 (by decide)) (hm 455 (by decide)) (qR inp 7 1)⟩
      (And.intro ⟨rfl, core5_280 (qv inp) inp env (hm 448 (by decide)) (hm 449 (by decide)) (hm 450 (by decide)) (hm 451 (by decide)) (qR inp 7 0)⟩
      (And.intro ⟨rfl, h20⟩
      (And.intro ⟨rfl, h21⟩
      (And.intro ⟨rfl, h22⟩
      (And.intro ⟨rfl, h23⟩
      (And.intro ⟨rfl, core5_267 (qv inp) inp env (hm 396 (by decide)) (hm 397 (by decide)) (hm 398 (by decide)) (hm 399 (by decide)) (qR inp 6 3)⟩
      (And.intro ⟨rfl, core5_266 (qv inp) inp env (hm 392 (by decide)) (hm 393 (by decide)) (hm 394 (by decide)) (hm 395 (by decide)) (qR inp 6 2)⟩
      (And.intro ⟨rfl, core5_265 (qv inp) inp env (hm 388 (by decide)) (hm 389 (by decide)) (hm 390 (by decide)) (hm 391 (by decide)) (qR inp 6 1)⟩
      (And.intro ⟨rfl, core5_264 (qv inp) inp env (hm 384 (by decide)) (hm 385 (by decide)) (hm 386 (by decide)) (hm 387 (by decide)) (qR inp 6 0)⟩
      (And.intro ⟨rfl, h28⟩
      (And.intro ⟨rfl, h29⟩
      (And.intro ⟨rfl, h30⟩
      (And.intro ⟨rfl, h31⟩
      (And.intro ⟨rfl, core5_251 (qv inp) inp env (hm 332 (by decide)) (hm 333 (by decide)) (hm 334 (by decide)) (hm 335 (by decide)) (qR inp 5 3)⟩
      (And.intro ⟨rfl, core5_250 (qv inp) inp env (hm 328 (by decide)) (hm 329 (by decide)) (hm 330 (by decide)) (hm 331 (by decide)) (qR inp 5 2)⟩
      (And.intro ⟨rfl, core5_249 (qv inp) inp env (hm 324 (by decide)) (hm 325 (by decide)) (hm 326 (by decide)) (hm 327 (by decide)) (qR inp 5 1)⟩
      (And.intro ⟨rfl, core5_248 (qv inp) inp env (hm 320 (by decide)) (hm 321 (by decide)) (hm 322 (by decide)) (hm 323 (by decide)) (qR inp 5 0)⟩
      (And.intro ⟨rfl, h36⟩
      (And.intro ⟨rfl, h37⟩
      (And.intro ⟨rfl, h38⟩
      (And.intro ⟨rfl, h39⟩
      (And.intro ⟨rfl, core5_235 (qv inp) inp env (hm 268 (by decide)) (hm 269 (by decide)) (hm 270 (by decide)) (hm 271 (by decide)) (qR inp 4 3)⟩
      (And.intro ⟨rfl, core5_234 (qv inp) inp env (hm 264 (by decide)) (hm 265 (by decide)) (hm 266 (by decide)) (hm 267 (by decide)) (qR inp 4 2)⟩
      (And.intro ⟨rfl, core5_233 (qv inp) inp env (hm 260 (by decide)) (hm 261 (by decide)) (hm 262 (by decide)) (hm 263 (by decide)) (qR inp 4 1)⟩
      (And.intro ⟨rfl, core5_232 (qv inp) inp env (hm 256 (by decide)) (hm 257 (by decide)) (hm 258 (by decide)) (hm 259 (by decide)) (qR inp 4 0)⟩
      (And.intro ⟨rfl, h44⟩
      (And.intro ⟨rfl, h45⟩
      (And.intro ⟨rfl, h46⟩
      (And.intro ⟨rfl, h47⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
