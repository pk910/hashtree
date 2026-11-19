import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D4
import Hashtree.Gen.WinAvx2X8P.D3

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice4 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K4 K5 T4 = true := by
  decide +kernel

theorem core4_315 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨108, [1]⟩ : Lin)) = (inp 108).zeroExtend 32)
    (h1 : env (.m 1 (⟨109, [1]⟩ : Lin)) = (inp 109).zeroExtend 32)
    (h2 : env (.m 1 (⟨110, [1]⟩ : Lin)) = (inp 110).zeroExtend 32)
    (h3 : env (.m 1 (⟨111, [1]⟩ : Lin)) = (inp 111).zeroExtend 32)
    (h4 : V (.R 1 11) = ((((0 : Word) ||| (inp 108).zeroExtend 32 <<< 0) ||| (inp 109).zeroExtend 32 <<< 8) ||| (inp 110).zeroExtend 32 <<< 16) ||| (inp 111).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 11) :=
  shape0 (env (.m 1 (⟨108, [1]⟩ : Lin))) (env (.m 1 (⟨109, [1]⟩ : Lin))) (env (.m 1 (⟨110, [1]⟩ : Lin))) (env (.m 1 (⟨111, [1]⟩ : Lin))) (V (.R 1 11)) ((inp 108)) ((inp 109)) ((inp 110)) ((inp 111)) h0 h1 h2 h3 h4

theorem core4_314 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨104, [1]⟩ : Lin)) = (inp 104).zeroExtend 32)
    (h1 : env (.m 1 (⟨105, [1]⟩ : Lin)) = (inp 105).zeroExtend 32)
    (h2 : env (.m 1 (⟨106, [1]⟩ : Lin)) = (inp 106).zeroExtend 32)
    (h3 : env (.m 1 (⟨107, [1]⟩ : Lin)) = (inp 107).zeroExtend 32)
    (h4 : V (.R 1 10) = ((((0 : Word) ||| (inp 104).zeroExtend 32 <<< 0) ||| (inp 105).zeroExtend 32 <<< 8) ||| (inp 106).zeroExtend 32 <<< 16) ||| (inp 107).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 10) :=
  shape0 (env (.m 1 (⟨104, [1]⟩ : Lin))) (env (.m 1 (⟨105, [1]⟩ : Lin))) (env (.m 1 (⟨106, [1]⟩ : Lin))) (env (.m 1 (⟨107, [1]⟩ : Lin))) (V (.R 1 10)) ((inp 104)) ((inp 105)) ((inp 106)) ((inp 107)) h0 h1 h2 h3 h4

theorem core4_313 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨100, [1]⟩ : Lin)) = (inp 100).zeroExtend 32)
    (h1 : env (.m 1 (⟨101, [1]⟩ : Lin)) = (inp 101).zeroExtend 32)
    (h2 : env (.m 1 (⟨102, [1]⟩ : Lin)) = (inp 102).zeroExtend 32)
    (h3 : env (.m 1 (⟨103, [1]⟩ : Lin)) = (inp 103).zeroExtend 32)
    (h4 : V (.R 1 9) = ((((0 : Word) ||| (inp 100).zeroExtend 32 <<< 0) ||| (inp 101).zeroExtend 32 <<< 8) ||| (inp 102).zeroExtend 32 <<< 16) ||| (inp 103).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 9) :=
  shape0 (env (.m 1 (⟨100, [1]⟩ : Lin))) (env (.m 1 (⟨101, [1]⟩ : Lin))) (env (.m 1 (⟨102, [1]⟩ : Lin))) (env (.m 1 (⟨103, [1]⟩ : Lin))) (V (.R 1 9)) ((inp 100)) ((inp 101)) ((inp 102)) ((inp 103)) h0 h1 h2 h3 h4

theorem core4_312 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 8) :=
  shape0 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4

theorem core4_311 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨92, [1]⟩ : Lin)) = (inp 92).zeroExtend 32)
    (h1 : env (.m 1 (⟨93, [1]⟩ : Lin)) = (inp 93).zeroExtend 32)
    (h2 : env (.m 1 (⟨94, [1]⟩ : Lin)) = (inp 94).zeroExtend 32)
    (h3 : env (.m 1 (⟨95, [1]⟩ : Lin)) = (inp 95).zeroExtend 32)
    (h4 : V (.R 1 7) = ((((0 : Word) ||| (inp 92).zeroExtend 32 <<< 0) ||| (inp 93).zeroExtend 32 <<< 8) ||| (inp 94).zeroExtend 32 <<< 16) ||| (inp 95).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨92, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨93, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨94, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨95, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 7) :=
  shape0 (env (.m 1 (⟨92, [1]⟩ : Lin))) (env (.m 1 (⟨93, [1]⟩ : Lin))) (env (.m 1 (⟨94, [1]⟩ : Lin))) (env (.m 1 (⟨95, [1]⟩ : Lin))) (V (.R 1 7)) ((inp 92)) ((inp 93)) ((inp 94)) ((inp 95)) h0 h1 h2 h3 h4

theorem core4_310 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨88, [1]⟩ : Lin)) = (inp 88).zeroExtend 32)
    (h1 : env (.m 1 (⟨89, [1]⟩ : Lin)) = (inp 89).zeroExtend 32)
    (h2 : env (.m 1 (⟨90, [1]⟩ : Lin)) = (inp 90).zeroExtend 32)
    (h3 : env (.m 1 (⟨91, [1]⟩ : Lin)) = (inp 91).zeroExtend 32)
    (h4 : V (.R 1 6) = ((((0 : Word) ||| (inp 88).zeroExtend 32 <<< 0) ||| (inp 89).zeroExtend 32 <<< 8) ||| (inp 90).zeroExtend 32 <<< 16) ||| (inp 91).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨88, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨89, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨90, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨91, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 6) :=
  shape0 (env (.m 1 (⟨88, [1]⟩ : Lin))) (env (.m 1 (⟨89, [1]⟩ : Lin))) (env (.m 1 (⟨90, [1]⟩ : Lin))) (env (.m 1 (⟨91, [1]⟩ : Lin))) (V (.R 1 6)) ((inp 88)) ((inp 89)) ((inp 90)) ((inp 91)) h0 h1 h2 h3 h4

theorem core4_309 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨84, [1]⟩ : Lin)) = (inp 84).zeroExtend 32)
    (h1 : env (.m 1 (⟨85, [1]⟩ : Lin)) = (inp 85).zeroExtend 32)
    (h2 : env (.m 1 (⟨86, [1]⟩ : Lin)) = (inp 86).zeroExtend 32)
    (h3 : env (.m 1 (⟨87, [1]⟩ : Lin)) = (inp 87).zeroExtend 32)
    (h4 : V (.R 1 5) = ((((0 : Word) ||| (inp 84).zeroExtend 32 <<< 0) ||| (inp 85).zeroExtend 32 <<< 8) ||| (inp 86).zeroExtend 32 <<< 16) ||| (inp 87).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨84, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨85, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨86, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨87, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 5) :=
  shape0 (env (.m 1 (⟨84, [1]⟩ : Lin))) (env (.m 1 (⟨85, [1]⟩ : Lin))) (env (.m 1 (⟨86, [1]⟩ : Lin))) (env (.m 1 (⟨87, [1]⟩ : Lin))) (V (.R 1 5)) ((inp 84)) ((inp 85)) ((inp 86)) ((inp 87)) h0 h1 h2 h3 h4

theorem core4_308 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h1 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h2 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h3 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h4 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 4) :=
  shape0 (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4

theorem core4_299 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨44, [1]⟩ : Lin)) = (inp 44).zeroExtend 32)
    (h1 : env (.m 1 (⟨45, [1]⟩ : Lin)) = (inp 45).zeroExtend 32)
    (h2 : env (.m 1 (⟨46, [1]⟩ : Lin)) = (inp 46).zeroExtend 32)
    (h3 : env (.m 1 (⟨47, [1]⟩ : Lin)) = (inp 47).zeroExtend 32)
    (h4 : V (.R 0 11) = ((((0 : Word) ||| (inp 44).zeroExtend 32 <<< 0) ||| (inp 45).zeroExtend 32 <<< 8) ||| (inp 46).zeroExtend 32 <<< 16) ||| (inp 47).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 11) :=
  shape0 (env (.m 1 (⟨44, [1]⟩ : Lin))) (env (.m 1 (⟨45, [1]⟩ : Lin))) (env (.m 1 (⟨46, [1]⟩ : Lin))) (env (.m 1 (⟨47, [1]⟩ : Lin))) (V (.R 0 11)) ((inp 44)) ((inp 45)) ((inp 46)) ((inp 47)) h0 h1 h2 h3 h4

theorem core4_298 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨40, [1]⟩ : Lin)) = (inp 40).zeroExtend 32)
    (h1 : env (.m 1 (⟨41, [1]⟩ : Lin)) = (inp 41).zeroExtend 32)
    (h2 : env (.m 1 (⟨42, [1]⟩ : Lin)) = (inp 42).zeroExtend 32)
    (h3 : env (.m 1 (⟨43, [1]⟩ : Lin)) = (inp 43).zeroExtend 32)
    (h4 : V (.R 0 10) = ((((0 : Word) ||| (inp 40).zeroExtend 32 <<< 0) ||| (inp 41).zeroExtend 32 <<< 8) ||| (inp 42).zeroExtend 32 <<< 16) ||| (inp 43).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 10) :=
  shape0 (env (.m 1 (⟨40, [1]⟩ : Lin))) (env (.m 1 (⟨41, [1]⟩ : Lin))) (env (.m 1 (⟨42, [1]⟩ : Lin))) (env (.m 1 (⟨43, [1]⟩ : Lin))) (V (.R 0 10)) ((inp 40)) ((inp 41)) ((inp 42)) ((inp 43)) h0 h1 h2 h3 h4

theorem core4_297 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨36, [1]⟩ : Lin)) = (inp 36).zeroExtend 32)
    (h1 : env (.m 1 (⟨37, [1]⟩ : Lin)) = (inp 37).zeroExtend 32)
    (h2 : env (.m 1 (⟨38, [1]⟩ : Lin)) = (inp 38).zeroExtend 32)
    (h3 : env (.m 1 (⟨39, [1]⟩ : Lin)) = (inp 39).zeroExtend 32)
    (h4 : V (.R 0 9) = ((((0 : Word) ||| (inp 36).zeroExtend 32 <<< 0) ||| (inp 37).zeroExtend 32 <<< 8) ||| (inp 38).zeroExtend 32 <<< 16) ||| (inp 39).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 9) :=
  shape0 (env (.m 1 (⟨36, [1]⟩ : Lin))) (env (.m 1 (⟨37, [1]⟩ : Lin))) (env (.m 1 (⟨38, [1]⟩ : Lin))) (env (.m 1 (⟨39, [1]⟩ : Lin))) (V (.R 0 9)) ((inp 36)) ((inp 37)) ((inp 38)) ((inp 39)) h0 h1 h2 h3 h4

theorem core4_296 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 8) :=
  shape0 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4

theorem core4_295 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨28, [1]⟩ : Lin)) = (inp 28).zeroExtend 32)
    (h1 : env (.m 1 (⟨29, [1]⟩ : Lin)) = (inp 29).zeroExtend 32)
    (h2 : env (.m 1 (⟨30, [1]⟩ : Lin)) = (inp 30).zeroExtend 32)
    (h3 : env (.m 1 (⟨31, [1]⟩ : Lin)) = (inp 31).zeroExtend 32)
    (h4 : V (.R 0 7) = ((((0 : Word) ||| (inp 28).zeroExtend 32 <<< 0) ||| (inp 29).zeroExtend 32 <<< 8) ||| (inp 30).zeroExtend 32 <<< 16) ||| (inp 31).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨28, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨29, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨30, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨31, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 7) :=
  shape0 (env (.m 1 (⟨28, [1]⟩ : Lin))) (env (.m 1 (⟨29, [1]⟩ : Lin))) (env (.m 1 (⟨30, [1]⟩ : Lin))) (env (.m 1 (⟨31, [1]⟩ : Lin))) (V (.R 0 7)) ((inp 28)) ((inp 29)) ((inp 30)) ((inp 31)) h0 h1 h2 h3 h4

theorem core4_294 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨24, [1]⟩ : Lin)) = (inp 24).zeroExtend 32)
    (h1 : env (.m 1 (⟨25, [1]⟩ : Lin)) = (inp 25).zeroExtend 32)
    (h2 : env (.m 1 (⟨26, [1]⟩ : Lin)) = (inp 26).zeroExtend 32)
    (h3 : env (.m 1 (⟨27, [1]⟩ : Lin)) = (inp 27).zeroExtend 32)
    (h4 : V (.R 0 6) = ((((0 : Word) ||| (inp 24).zeroExtend 32 <<< 0) ||| (inp 25).zeroExtend 32 <<< 8) ||| (inp 26).zeroExtend 32 <<< 16) ||| (inp 27).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨24, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨25, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨26, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨27, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 6) :=
  shape0 (env (.m 1 (⟨24, [1]⟩ : Lin))) (env (.m 1 (⟨25, [1]⟩ : Lin))) (env (.m 1 (⟨26, [1]⟩ : Lin))) (env (.m 1 (⟨27, [1]⟩ : Lin))) (V (.R 0 6)) ((inp 24)) ((inp 25)) ((inp 26)) ((inp 27)) h0 h1 h2 h3 h4

theorem core4_293 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨20, [1]⟩ : Lin)) = (inp 20).zeroExtend 32)
    (h1 : env (.m 1 (⟨21, [1]⟩ : Lin)) = (inp 21).zeroExtend 32)
    (h2 : env (.m 1 (⟨22, [1]⟩ : Lin)) = (inp 22).zeroExtend 32)
    (h3 : env (.m 1 (⟨23, [1]⟩ : Lin)) = (inp 23).zeroExtend 32)
    (h4 : V (.R 0 5) = ((((0 : Word) ||| (inp 20).zeroExtend 32 <<< 0) ||| (inp 21).zeroExtend 32 <<< 8) ||| (inp 22).zeroExtend 32 <<< 16) ||| (inp 23).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨20, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨21, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨22, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨23, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 5) :=
  shape0 (env (.m 1 (⟨20, [1]⟩ : Lin))) (env (.m 1 (⟨21, [1]⟩ : Lin))) (env (.m 1 (⟨22, [1]⟩ : Lin))) (env (.m 1 (⟨23, [1]⟩ : Lin))) (V (.R 0 5)) ((inp 20)) ((inp 21)) ((inp 22)) ((inp 23)) h0 h1 h2 h3 h4

theorem core4_292 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h1 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h2 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h3 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h4 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 4) :=
  shape0 (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4

theorem core4_283 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨220, [1]⟩ : Lin)) = (inp 220).zeroExtend 32)
    (h1 : env (.m 1 (⟨221, [1]⟩ : Lin)) = (inp 221).zeroExtend 32)
    (h2 : env (.m 1 (⟨222, [1]⟩ : Lin)) = (inp 222).zeroExtend 32)
    (h3 : env (.m 1 (⟨223, [1]⟩ : Lin)) = (inp 223).zeroExtend 32)
    (h4 : V (.R 3 7) = ((((0 : Word) ||| (inp 220).zeroExtend 32 <<< 0) ||| (inp 221).zeroExtend 32 <<< 8) ||| (inp 222).zeroExtend 32 <<< 16) ||| (inp 223).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨220, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨221, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨222, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨223, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 7) :=
  shape0 (env (.m 1 (⟨220, [1]⟩ : Lin))) (env (.m 1 (⟨221, [1]⟩ : Lin))) (env (.m 1 (⟨222, [1]⟩ : Lin))) (env (.m 1 (⟨223, [1]⟩ : Lin))) (V (.R 3 7)) ((inp 220)) ((inp 221)) ((inp 222)) ((inp 223)) h0 h1 h2 h3 h4

theorem core4_282 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨216, [1]⟩ : Lin)) = (inp 216).zeroExtend 32)
    (h1 : env (.m 1 (⟨217, [1]⟩ : Lin)) = (inp 217).zeroExtend 32)
    (h2 : env (.m 1 (⟨218, [1]⟩ : Lin)) = (inp 218).zeroExtend 32)
    (h3 : env (.m 1 (⟨219, [1]⟩ : Lin)) = (inp 219).zeroExtend 32)
    (h4 : V (.R 3 6) = ((((0 : Word) ||| (inp 216).zeroExtend 32 <<< 0) ||| (inp 217).zeroExtend 32 <<< 8) ||| (inp 218).zeroExtend 32 <<< 16) ||| (inp 219).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨216, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨217, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨218, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨219, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 6) :=
  shape0 (env (.m 1 (⟨216, [1]⟩ : Lin))) (env (.m 1 (⟨217, [1]⟩ : Lin))) (env (.m 1 (⟨218, [1]⟩ : Lin))) (env (.m 1 (⟨219, [1]⟩ : Lin))) (V (.R 3 6)) ((inp 216)) ((inp 217)) ((inp 218)) ((inp 219)) h0 h1 h2 h3 h4

theorem core4_281 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨212, [1]⟩ : Lin)) = (inp 212).zeroExtend 32)
    (h1 : env (.m 1 (⟨213, [1]⟩ : Lin)) = (inp 213).zeroExtend 32)
    (h2 : env (.m 1 (⟨214, [1]⟩ : Lin)) = (inp 214).zeroExtend 32)
    (h3 : env (.m 1 (⟨215, [1]⟩ : Lin)) = (inp 215).zeroExtend 32)
    (h4 : V (.R 3 5) = ((((0 : Word) ||| (inp 212).zeroExtend 32 <<< 0) ||| (inp 213).zeroExtend 32 <<< 8) ||| (inp 214).zeroExtend 32 <<< 16) ||| (inp 215).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨212, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨213, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨214, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨215, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 5) :=
  shape0 (env (.m 1 (⟨212, [1]⟩ : Lin))) (env (.m 1 (⟨213, [1]⟩ : Lin))) (env (.m 1 (⟨214, [1]⟩ : Lin))) (env (.m 1 (⟨215, [1]⟩ : Lin))) (V (.R 3 5)) ((inp 212)) ((inp 213)) ((inp 214)) ((inp 215)) h0 h1 h2 h3 h4

theorem core4_280 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨208, [1]⟩ : Lin)) = (inp 208).zeroExtend 32)
    (h1 : env (.m 1 (⟨209, [1]⟩ : Lin)) = (inp 209).zeroExtend 32)
    (h2 : env (.m 1 (⟨210, [1]⟩ : Lin)) = (inp 210).zeroExtend 32)
    (h3 : env (.m 1 (⟨211, [1]⟩ : Lin)) = (inp 211).zeroExtend 32)
    (h4 : V (.R 3 4) = ((((0 : Word) ||| (inp 208).zeroExtend 32 <<< 0) ||| (inp 209).zeroExtend 32 <<< 8) ||| (inp 210).zeroExtend 32 <<< 16) ||| (inp 211).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨208, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨209, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨210, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨211, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 4) :=
  shape0 (env (.m 1 (⟨208, [1]⟩ : Lin))) (env (.m 1 (⟨209, [1]⟩ : Lin))) (env (.m 1 (⟨210, [1]⟩ : Lin))) (env (.m 1 (⟨211, [1]⟩ : Lin))) (V (.R 3 4)) ((inp 208)) ((inp 209)) ((inp 210)) ((inp 211)) h0 h1 h2 h3 h4

theorem core4_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨204, [1]⟩ : Lin)) = (inp 204).zeroExtend 32)
    (h1 : env (.m 1 (⟨205, [1]⟩ : Lin)) = (inp 205).zeroExtend 32)
    (h2 : env (.m 1 (⟨206, [1]⟩ : Lin)) = (inp 206).zeroExtend 32)
    (h3 : env (.m 1 (⟨207, [1]⟩ : Lin)) = (inp 207).zeroExtend 32)
    (h4 : V (.R 3 3) = ((((0 : Word) ||| (inp 204).zeroExtend 32 <<< 0) ||| (inp 205).zeroExtend 32 <<< 8) ||| (inp 206).zeroExtend 32 <<< 16) ||| (inp 207).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨204, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨205, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨206, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨207, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 3) :=
  shape0 (env (.m 1 (⟨204, [1]⟩ : Lin))) (env (.m 1 (⟨205, [1]⟩ : Lin))) (env (.m 1 (⟨206, [1]⟩ : Lin))) (env (.m 1 (⟨207, [1]⟩ : Lin))) (V (.R 3 3)) ((inp 204)) ((inp 205)) ((inp 206)) ((inp 207)) h0 h1 h2 h3 h4

theorem core4_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨200, [1]⟩ : Lin)) = (inp 200).zeroExtend 32)
    (h1 : env (.m 1 (⟨201, [1]⟩ : Lin)) = (inp 201).zeroExtend 32)
    (h2 : env (.m 1 (⟨202, [1]⟩ : Lin)) = (inp 202).zeroExtend 32)
    (h3 : env (.m 1 (⟨203, [1]⟩ : Lin)) = (inp 203).zeroExtend 32)
    (h4 : V (.R 3 2) = ((((0 : Word) ||| (inp 200).zeroExtend 32 <<< 0) ||| (inp 201).zeroExtend 32 <<< 8) ||| (inp 202).zeroExtend 32 <<< 16) ||| (inp 203).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨200, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨201, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨202, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨203, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 2) :=
  shape0 (env (.m 1 (⟨200, [1]⟩ : Lin))) (env (.m 1 (⟨201, [1]⟩ : Lin))) (env (.m 1 (⟨202, [1]⟩ : Lin))) (env (.m 1 (⟨203, [1]⟩ : Lin))) (V (.R 3 2)) ((inp 200)) ((inp 201)) ((inp 202)) ((inp 203)) h0 h1 h2 h3 h4

theorem core4_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨196, [1]⟩ : Lin)) = (inp 196).zeroExtend 32)
    (h1 : env (.m 1 (⟨197, [1]⟩ : Lin)) = (inp 197).zeroExtend 32)
    (h2 : env (.m 1 (⟨198, [1]⟩ : Lin)) = (inp 198).zeroExtend 32)
    (h3 : env (.m 1 (⟨199, [1]⟩ : Lin)) = (inp 199).zeroExtend 32)
    (h4 : V (.R 3 1) = ((((0 : Word) ||| (inp 196).zeroExtend 32 <<< 0) ||| (inp 197).zeroExtend 32 <<< 8) ||| (inp 198).zeroExtend 32 <<< 16) ||| (inp 199).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨196, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨197, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨198, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨199, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 1) :=
  shape0 (env (.m 1 (⟨196, [1]⟩ : Lin))) (env (.m 1 (⟨197, [1]⟩ : Lin))) (env (.m 1 (⟨198, [1]⟩ : Lin))) (env (.m 1 (⟨199, [1]⟩ : Lin))) (V (.R 3 1)) ((inp 196)) ((inp 197)) ((inp 198)) ((inp 199)) h0 h1 h2 h3 h4

theorem core4_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨192, [1]⟩ : Lin)) = (inp 192).zeroExtend 32)
    (h1 : env (.m 1 (⟨193, [1]⟩ : Lin)) = (inp 193).zeroExtend 32)
    (h2 : env (.m 1 (⟨194, [1]⟩ : Lin)) = (inp 194).zeroExtend 32)
    (h3 : env (.m 1 (⟨195, [1]⟩ : Lin)) = (inp 195).zeroExtend 32)
    (h4 : V (.R 3 0) = ((((0 : Word) ||| (inp 192).zeroExtend 32 <<< 0) ||| (inp 193).zeroExtend 32 <<< 8) ||| (inp 194).zeroExtend 32 <<< 16) ||| (inp 195).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨192, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨193, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨194, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨195, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 3 0) :=
  shape0 (env (.m 1 (⟨192, [1]⟩ : Lin))) (env (.m 1 (⟨193, [1]⟩ : Lin))) (env (.m 1 (⟨194, [1]⟩ : Lin))) (env (.m 1 (⟨195, [1]⟩ : Lin))) (V (.R 3 0)) ((inp 192)) ((inp 193)) ((inp 194)) ((inp 195)) h0 h1 h2 h3 h4

theorem core4_267 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨156, [1]⟩ : Lin)) = (inp 156).zeroExtend 32)
    (h1 : env (.m 1 (⟨157, [1]⟩ : Lin)) = (inp 157).zeroExtend 32)
    (h2 : env (.m 1 (⟨158, [1]⟩ : Lin)) = (inp 158).zeroExtend 32)
    (h3 : env (.m 1 (⟨159, [1]⟩ : Lin)) = (inp 159).zeroExtend 32)
    (h4 : V (.R 2 7) = ((((0 : Word) ||| (inp 156).zeroExtend 32 <<< 0) ||| (inp 157).zeroExtend 32 <<< 8) ||| (inp 158).zeroExtend 32 <<< 16) ||| (inp 159).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨156, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨157, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨158, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨159, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 7) :=
  shape0 (env (.m 1 (⟨156, [1]⟩ : Lin))) (env (.m 1 (⟨157, [1]⟩ : Lin))) (env (.m 1 (⟨158, [1]⟩ : Lin))) (env (.m 1 (⟨159, [1]⟩ : Lin))) (V (.R 2 7)) ((inp 156)) ((inp 157)) ((inp 158)) ((inp 159)) h0 h1 h2 h3 h4

theorem core4_266 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨152, [1]⟩ : Lin)) = (inp 152).zeroExtend 32)
    (h1 : env (.m 1 (⟨153, [1]⟩ : Lin)) = (inp 153).zeroExtend 32)
    (h2 : env (.m 1 (⟨154, [1]⟩ : Lin)) = (inp 154).zeroExtend 32)
    (h3 : env (.m 1 (⟨155, [1]⟩ : Lin)) = (inp 155).zeroExtend 32)
    (h4 : V (.R 2 6) = ((((0 : Word) ||| (inp 152).zeroExtend 32 <<< 0) ||| (inp 153).zeroExtend 32 <<< 8) ||| (inp 154).zeroExtend 32 <<< 16) ||| (inp 155).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨152, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨153, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨154, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨155, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 6) :=
  shape0 (env (.m 1 (⟨152, [1]⟩ : Lin))) (env (.m 1 (⟨153, [1]⟩ : Lin))) (env (.m 1 (⟨154, [1]⟩ : Lin))) (env (.m 1 (⟨155, [1]⟩ : Lin))) (V (.R 2 6)) ((inp 152)) ((inp 153)) ((inp 154)) ((inp 155)) h0 h1 h2 h3 h4

theorem core4_265 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨148, [1]⟩ : Lin)) = (inp 148).zeroExtend 32)
    (h1 : env (.m 1 (⟨149, [1]⟩ : Lin)) = (inp 149).zeroExtend 32)
    (h2 : env (.m 1 (⟨150, [1]⟩ : Lin)) = (inp 150).zeroExtend 32)
    (h3 : env (.m 1 (⟨151, [1]⟩ : Lin)) = (inp 151).zeroExtend 32)
    (h4 : V (.R 2 5) = ((((0 : Word) ||| (inp 148).zeroExtend 32 <<< 0) ||| (inp 149).zeroExtend 32 <<< 8) ||| (inp 150).zeroExtend 32 <<< 16) ||| (inp 151).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨148, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨149, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨150, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨151, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 5) :=
  shape0 (env (.m 1 (⟨148, [1]⟩ : Lin))) (env (.m 1 (⟨149, [1]⟩ : Lin))) (env (.m 1 (⟨150, [1]⟩ : Lin))) (env (.m 1 (⟨151, [1]⟩ : Lin))) (V (.R 2 5)) ((inp 148)) ((inp 149)) ((inp 150)) ((inp 151)) h0 h1 h2 h3 h4

theorem core4_264 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨144, [1]⟩ : Lin)) = (inp 144).zeroExtend 32)
    (h1 : env (.m 1 (⟨145, [1]⟩ : Lin)) = (inp 145).zeroExtend 32)
    (h2 : env (.m 1 (⟨146, [1]⟩ : Lin)) = (inp 146).zeroExtend 32)
    (h3 : env (.m 1 (⟨147, [1]⟩ : Lin)) = (inp 147).zeroExtend 32)
    (h4 : V (.R 2 4) = ((((0 : Word) ||| (inp 144).zeroExtend 32 <<< 0) ||| (inp 145).zeroExtend 32 <<< 8) ||| (inp 146).zeroExtend 32 <<< 16) ||| (inp 147).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨144, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨145, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨146, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨147, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 4) :=
  shape0 (env (.m 1 (⟨144, [1]⟩ : Lin))) (env (.m 1 (⟨145, [1]⟩ : Lin))) (env (.m 1 (⟨146, [1]⟩ : Lin))) (env (.m 1 (⟨147, [1]⟩ : Lin))) (V (.R 2 4)) ((inp 144)) ((inp 145)) ((inp 146)) ((inp 147)) h0 h1 h2 h3 h4

theorem core4_263 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨140, [1]⟩ : Lin)) = (inp 140).zeroExtend 32)
    (h1 : env (.m 1 (⟨141, [1]⟩ : Lin)) = (inp 141).zeroExtend 32)
    (h2 : env (.m 1 (⟨142, [1]⟩ : Lin)) = (inp 142).zeroExtend 32)
    (h3 : env (.m 1 (⟨143, [1]⟩ : Lin)) = (inp 143).zeroExtend 32)
    (h4 : V (.R 2 3) = ((((0 : Word) ||| (inp 140).zeroExtend 32 <<< 0) ||| (inp 141).zeroExtend 32 <<< 8) ||| (inp 142).zeroExtend 32 <<< 16) ||| (inp 143).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨140, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨141, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨142, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨143, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 3) :=
  shape0 (env (.m 1 (⟨140, [1]⟩ : Lin))) (env (.m 1 (⟨141, [1]⟩ : Lin))) (env (.m 1 (⟨142, [1]⟩ : Lin))) (env (.m 1 (⟨143, [1]⟩ : Lin))) (V (.R 2 3)) ((inp 140)) ((inp 141)) ((inp 142)) ((inp 143)) h0 h1 h2 h3 h4

theorem core4_262 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨136, [1]⟩ : Lin)) = (inp 136).zeroExtend 32)
    (h1 : env (.m 1 (⟨137, [1]⟩ : Lin)) = (inp 137).zeroExtend 32)
    (h2 : env (.m 1 (⟨138, [1]⟩ : Lin)) = (inp 138).zeroExtend 32)
    (h3 : env (.m 1 (⟨139, [1]⟩ : Lin)) = (inp 139).zeroExtend 32)
    (h4 : V (.R 2 2) = ((((0 : Word) ||| (inp 136).zeroExtend 32 <<< 0) ||| (inp 137).zeroExtend 32 <<< 8) ||| (inp 138).zeroExtend 32 <<< 16) ||| (inp 139).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨136, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨137, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨138, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨139, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 2) :=
  shape0 (env (.m 1 (⟨136, [1]⟩ : Lin))) (env (.m 1 (⟨137, [1]⟩ : Lin))) (env (.m 1 (⟨138, [1]⟩ : Lin))) (env (.m 1 (⟨139, [1]⟩ : Lin))) (V (.R 2 2)) ((inp 136)) ((inp 137)) ((inp 138)) ((inp 139)) h0 h1 h2 h3 h4

theorem core4_261 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨132, [1]⟩ : Lin)) = (inp 132).zeroExtend 32)
    (h1 : env (.m 1 (⟨133, [1]⟩ : Lin)) = (inp 133).zeroExtend 32)
    (h2 : env (.m 1 (⟨134, [1]⟩ : Lin)) = (inp 134).zeroExtend 32)
    (h3 : env (.m 1 (⟨135, [1]⟩ : Lin)) = (inp 135).zeroExtend 32)
    (h4 : V (.R 2 1) = ((((0 : Word) ||| (inp 132).zeroExtend 32 <<< 0) ||| (inp 133).zeroExtend 32 <<< 8) ||| (inp 134).zeroExtend 32 <<< 16) ||| (inp 135).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨132, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨133, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨134, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨135, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 1) :=
  shape0 (env (.m 1 (⟨132, [1]⟩ : Lin))) (env (.m 1 (⟨133, [1]⟩ : Lin))) (env (.m 1 (⟨134, [1]⟩ : Lin))) (env (.m 1 (⟨135, [1]⟩ : Lin))) (V (.R 2 1)) ((inp 132)) ((inp 133)) ((inp 134)) ((inp 135)) h0 h1 h2 h3 h4

theorem core4_260 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨128, [1]⟩ : Lin)) = (inp 128).zeroExtend 32)
    (h1 : env (.m 1 (⟨129, [1]⟩ : Lin)) = (inp 129).zeroExtend 32)
    (h2 : env (.m 1 (⟨130, [1]⟩ : Lin)) = (inp 130).zeroExtend 32)
    (h3 : env (.m 1 (⟨131, [1]⟩ : Lin)) = (inp 131).zeroExtend 32)
    (h4 : V (.R 2 0) = ((((0 : Word) ||| (inp 128).zeroExtend 32 <<< 0) ||| (inp 129).zeroExtend 32 <<< 8) ||| (inp 130).zeroExtend 32 <<< 16) ||| (inp 131).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨128, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨129, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨130, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨131, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 2 0) :=
  shape0 (env (.m 1 (⟨128, [1]⟩ : Lin))) (env (.m 1 (⟨129, [1]⟩ : Lin))) (env (.m 1 (⟨130, [1]⟩ : Lin))) (env (.m 1 (⟨131, [1]⟩ : Lin))) (V (.R 2 0)) ((inp 128)) ((inp 129)) ((inp 130)) ((inp 131)) h0 h1 h2 h3 h4

theorem core4_251 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨92, [1]⟩ : Lin)) = (inp 92).zeroExtend 32)
    (h1 : env (.m 1 (⟨93, [1]⟩ : Lin)) = (inp 93).zeroExtend 32)
    (h2 : env (.m 1 (⟨94, [1]⟩ : Lin)) = (inp 94).zeroExtend 32)
    (h3 : env (.m 1 (⟨95, [1]⟩ : Lin)) = (inp 95).zeroExtend 32)
    (h4 : V (.R 1 7) = ((((0 : Word) ||| (inp 92).zeroExtend 32 <<< 0) ||| (inp 93).zeroExtend 32 <<< 8) ||| (inp 94).zeroExtend 32 <<< 16) ||| (inp 95).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨92, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨93, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨94, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨95, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 7) :=
  shape0 (env (.m 1 (⟨92, [1]⟩ : Lin))) (env (.m 1 (⟨93, [1]⟩ : Lin))) (env (.m 1 (⟨94, [1]⟩ : Lin))) (env (.m 1 (⟨95, [1]⟩ : Lin))) (V (.R 1 7)) ((inp 92)) ((inp 93)) ((inp 94)) ((inp 95)) h0 h1 h2 h3 h4

theorem core4_250 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨88, [1]⟩ : Lin)) = (inp 88).zeroExtend 32)
    (h1 : env (.m 1 (⟨89, [1]⟩ : Lin)) = (inp 89).zeroExtend 32)
    (h2 : env (.m 1 (⟨90, [1]⟩ : Lin)) = (inp 90).zeroExtend 32)
    (h3 : env (.m 1 (⟨91, [1]⟩ : Lin)) = (inp 91).zeroExtend 32)
    (h4 : V (.R 1 6) = ((((0 : Word) ||| (inp 88).zeroExtend 32 <<< 0) ||| (inp 89).zeroExtend 32 <<< 8) ||| (inp 90).zeroExtend 32 <<< 16) ||| (inp 91).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨88, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨89, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨90, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨91, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 6) :=
  shape0 (env (.m 1 (⟨88, [1]⟩ : Lin))) (env (.m 1 (⟨89, [1]⟩ : Lin))) (env (.m 1 (⟨90, [1]⟩ : Lin))) (env (.m 1 (⟨91, [1]⟩ : Lin))) (V (.R 1 6)) ((inp 88)) ((inp 89)) ((inp 90)) ((inp 91)) h0 h1 h2 h3 h4

theorem core4_249 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨84, [1]⟩ : Lin)) = (inp 84).zeroExtend 32)
    (h1 : env (.m 1 (⟨85, [1]⟩ : Lin)) = (inp 85).zeroExtend 32)
    (h2 : env (.m 1 (⟨86, [1]⟩ : Lin)) = (inp 86).zeroExtend 32)
    (h3 : env (.m 1 (⟨87, [1]⟩ : Lin)) = (inp 87).zeroExtend 32)
    (h4 : V (.R 1 5) = ((((0 : Word) ||| (inp 84).zeroExtend 32 <<< 0) ||| (inp 85).zeroExtend 32 <<< 8) ||| (inp 86).zeroExtend 32 <<< 16) ||| (inp 87).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨84, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨85, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨86, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨87, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 5) :=
  shape0 (env (.m 1 (⟨84, [1]⟩ : Lin))) (env (.m 1 (⟨85, [1]⟩ : Lin))) (env (.m 1 (⟨86, [1]⟩ : Lin))) (env (.m 1 (⟨87, [1]⟩ : Lin))) (V (.R 1 5)) ((inp 84)) ((inp 85)) ((inp 86)) ((inp 87)) h0 h1 h2 h3 h4

theorem core4_248 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨80, [1]⟩ : Lin)) = (inp 80).zeroExtend 32)
    (h1 : env (.m 1 (⟨81, [1]⟩ : Lin)) = (inp 81).zeroExtend 32)
    (h2 : env (.m 1 (⟨82, [1]⟩ : Lin)) = (inp 82).zeroExtend 32)
    (h3 : env (.m 1 (⟨83, [1]⟩ : Lin)) = (inp 83).zeroExtend 32)
    (h4 : V (.R 1 4) = ((((0 : Word) ||| (inp 80).zeroExtend 32 <<< 0) ||| (inp 81).zeroExtend 32 <<< 8) ||| (inp 82).zeroExtend 32 <<< 16) ||| (inp 83).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨80, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨81, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨82, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨83, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 4) :=
  shape0 (env (.m 1 (⟨80, [1]⟩ : Lin))) (env (.m 1 (⟨81, [1]⟩ : Lin))) (env (.m 1 (⟨82, [1]⟩ : Lin))) (env (.m 1 (⟨83, [1]⟩ : Lin))) (V (.R 1 4)) ((inp 80)) ((inp 81)) ((inp 82)) ((inp 83)) h0 h1 h2 h3 h4

theorem core4_247 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨76, [1]⟩ : Lin)) = (inp 76).zeroExtend 32)
    (h1 : env (.m 1 (⟨77, [1]⟩ : Lin)) = (inp 77).zeroExtend 32)
    (h2 : env (.m 1 (⟨78, [1]⟩ : Lin)) = (inp 78).zeroExtend 32)
    (h3 : env (.m 1 (⟨79, [1]⟩ : Lin)) = (inp 79).zeroExtend 32)
    (h4 : V (.R 1 3) = ((((0 : Word) ||| (inp 76).zeroExtend 32 <<< 0) ||| (inp 77).zeroExtend 32 <<< 8) ||| (inp 78).zeroExtend 32 <<< 16) ||| (inp 79).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨76, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨77, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨78, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨79, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 3) :=
  shape0 (env (.m 1 (⟨76, [1]⟩ : Lin))) (env (.m 1 (⟨77, [1]⟩ : Lin))) (env (.m 1 (⟨78, [1]⟩ : Lin))) (env (.m 1 (⟨79, [1]⟩ : Lin))) (V (.R 1 3)) ((inp 76)) ((inp 77)) ((inp 78)) ((inp 79)) h0 h1 h2 h3 h4

theorem core4_246 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨72, [1]⟩ : Lin)) = (inp 72).zeroExtend 32)
    (h1 : env (.m 1 (⟨73, [1]⟩ : Lin)) = (inp 73).zeroExtend 32)
    (h2 : env (.m 1 (⟨74, [1]⟩ : Lin)) = (inp 74).zeroExtend 32)
    (h3 : env (.m 1 (⟨75, [1]⟩ : Lin)) = (inp 75).zeroExtend 32)
    (h4 : V (.R 1 2) = ((((0 : Word) ||| (inp 72).zeroExtend 32 <<< 0) ||| (inp 73).zeroExtend 32 <<< 8) ||| (inp 74).zeroExtend 32 <<< 16) ||| (inp 75).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨72, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨73, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨74, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨75, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 2) :=
  shape0 (env (.m 1 (⟨72, [1]⟩ : Lin))) (env (.m 1 (⟨73, [1]⟩ : Lin))) (env (.m 1 (⟨74, [1]⟩ : Lin))) (env (.m 1 (⟨75, [1]⟩ : Lin))) (V (.R 1 2)) ((inp 72)) ((inp 73)) ((inp 74)) ((inp 75)) h0 h1 h2 h3 h4

theorem core4_245 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨68, [1]⟩ : Lin)) = (inp 68).zeroExtend 32)
    (h1 : env (.m 1 (⟨69, [1]⟩ : Lin)) = (inp 69).zeroExtend 32)
    (h2 : env (.m 1 (⟨70, [1]⟩ : Lin)) = (inp 70).zeroExtend 32)
    (h3 : env (.m 1 (⟨71, [1]⟩ : Lin)) = (inp 71).zeroExtend 32)
    (h4 : V (.R 1 1) = ((((0 : Word) ||| (inp 68).zeroExtend 32 <<< 0) ||| (inp 69).zeroExtend 32 <<< 8) ||| (inp 70).zeroExtend 32 <<< 16) ||| (inp 71).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨68, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨69, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨70, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨71, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 1) :=
  shape0 (env (.m 1 (⟨68, [1]⟩ : Lin))) (env (.m 1 (⟨69, [1]⟩ : Lin))) (env (.m 1 (⟨70, [1]⟩ : Lin))) (env (.m 1 (⟨71, [1]⟩ : Lin))) (V (.R 1 1)) ((inp 68)) ((inp 69)) ((inp 70)) ((inp 71)) h0 h1 h2 h3 h4

theorem core4_244 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨64, [1]⟩ : Lin)) = (inp 64).zeroExtend 32)
    (h1 : env (.m 1 (⟨65, [1]⟩ : Lin)) = (inp 65).zeroExtend 32)
    (h2 : env (.m 1 (⟨66, [1]⟩ : Lin)) = (inp 66).zeroExtend 32)
    (h3 : env (.m 1 (⟨67, [1]⟩ : Lin)) = (inp 67).zeroExtend 32)
    (h4 : V (.R 1 0) = ((((0 : Word) ||| (inp 64).zeroExtend 32 <<< 0) ||| (inp 65).zeroExtend 32 <<< 8) ||| (inp 66).zeroExtend 32 <<< 16) ||| (inp 67).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨64, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨65, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨66, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨67, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 1 0) :=
  shape0 (env (.m 1 (⟨64, [1]⟩ : Lin))) (env (.m 1 (⟨65, [1]⟩ : Lin))) (env (.m 1 (⟨66, [1]⟩ : Lin))) (env (.m 1 (⟨67, [1]⟩ : Lin))) (V (.R 1 0)) ((inp 64)) ((inp 65)) ((inp 66)) ((inp 67)) h0 h1 h2 h3 h4

theorem core4_235 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨28, [1]⟩ : Lin)) = (inp 28).zeroExtend 32)
    (h1 : env (.m 1 (⟨29, [1]⟩ : Lin)) = (inp 29).zeroExtend 32)
    (h2 : env (.m 1 (⟨30, [1]⟩ : Lin)) = (inp 30).zeroExtend 32)
    (h3 : env (.m 1 (⟨31, [1]⟩ : Lin)) = (inp 31).zeroExtend 32)
    (h4 : V (.R 0 7) = ((((0 : Word) ||| (inp 28).zeroExtend 32 <<< 0) ||| (inp 29).zeroExtend 32 <<< 8) ||| (inp 30).zeroExtend 32 <<< 16) ||| (inp 31).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨28, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨29, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨30, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨31, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 7) :=
  shape0 (env (.m 1 (⟨28, [1]⟩ : Lin))) (env (.m 1 (⟨29, [1]⟩ : Lin))) (env (.m 1 (⟨30, [1]⟩ : Lin))) (env (.m 1 (⟨31, [1]⟩ : Lin))) (V (.R 0 7)) ((inp 28)) ((inp 29)) ((inp 30)) ((inp 31)) h0 h1 h2 h3 h4

theorem core4_234 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨24, [1]⟩ : Lin)) = (inp 24).zeroExtend 32)
    (h1 : env (.m 1 (⟨25, [1]⟩ : Lin)) = (inp 25).zeroExtend 32)
    (h2 : env (.m 1 (⟨26, [1]⟩ : Lin)) = (inp 26).zeroExtend 32)
    (h3 : env (.m 1 (⟨27, [1]⟩ : Lin)) = (inp 27).zeroExtend 32)
    (h4 : V (.R 0 6) = ((((0 : Word) ||| (inp 24).zeroExtend 32 <<< 0) ||| (inp 25).zeroExtend 32 <<< 8) ||| (inp 26).zeroExtend 32 <<< 16) ||| (inp 27).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨24, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨25, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨26, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨27, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 6) :=
  shape0 (env (.m 1 (⟨24, [1]⟩ : Lin))) (env (.m 1 (⟨25, [1]⟩ : Lin))) (env (.m 1 (⟨26, [1]⟩ : Lin))) (env (.m 1 (⟨27, [1]⟩ : Lin))) (V (.R 0 6)) ((inp 24)) ((inp 25)) ((inp 26)) ((inp 27)) h0 h1 h2 h3 h4

theorem core4_233 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨20, [1]⟩ : Lin)) = (inp 20).zeroExtend 32)
    (h1 : env (.m 1 (⟨21, [1]⟩ : Lin)) = (inp 21).zeroExtend 32)
    (h2 : env (.m 1 (⟨22, [1]⟩ : Lin)) = (inp 22).zeroExtend 32)
    (h3 : env (.m 1 (⟨23, [1]⟩ : Lin)) = (inp 23).zeroExtend 32)
    (h4 : V (.R 0 5) = ((((0 : Word) ||| (inp 20).zeroExtend 32 <<< 0) ||| (inp 21).zeroExtend 32 <<< 8) ||| (inp 22).zeroExtend 32 <<< 16) ||| (inp 23).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨20, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨21, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨22, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨23, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 5) :=
  shape0 (env (.m 1 (⟨20, [1]⟩ : Lin))) (env (.m 1 (⟨21, [1]⟩ : Lin))) (env (.m 1 (⟨22, [1]⟩ : Lin))) (env (.m 1 (⟨23, [1]⟩ : Lin))) (V (.R 0 5)) ((inp 20)) ((inp 21)) ((inp 22)) ((inp 23)) h0 h1 h2 h3 h4

theorem core4_232 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨16, [1]⟩ : Lin)) = (inp 16).zeroExtend 32)
    (h1 : env (.m 1 (⟨17, [1]⟩ : Lin)) = (inp 17).zeroExtend 32)
    (h2 : env (.m 1 (⟨18, [1]⟩ : Lin)) = (inp 18).zeroExtend 32)
    (h3 : env (.m 1 (⟨19, [1]⟩ : Lin)) = (inp 19).zeroExtend 32)
    (h4 : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨16, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨17, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨18, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨19, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 4) :=
  shape0 (env (.m 1 (⟨16, [1]⟩ : Lin))) (env (.m 1 (⟨17, [1]⟩ : Lin))) (env (.m 1 (⟨18, [1]⟩ : Lin))) (env (.m 1 (⟨19, [1]⟩ : Lin))) (V (.R 0 4)) ((inp 16)) ((inp 17)) ((inp 18)) ((inp 19)) h0 h1 h2 h3 h4

theorem core4_231 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨12, [1]⟩ : Lin)) = (inp 12).zeroExtend 32)
    (h1 : env (.m 1 (⟨13, [1]⟩ : Lin)) = (inp 13).zeroExtend 32)
    (h2 : env (.m 1 (⟨14, [1]⟩ : Lin)) = (inp 14).zeroExtend 32)
    (h3 : env (.m 1 (⟨15, [1]⟩ : Lin)) = (inp 15).zeroExtend 32)
    (h4 : V (.R 0 3) = ((((0 : Word) ||| (inp 12).zeroExtend 32 <<< 0) ||| (inp 13).zeroExtend 32 <<< 8) ||| (inp 14).zeroExtend 32 <<< 16) ||| (inp 15).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨12, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨13, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨14, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨15, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 3) :=
  shape0 (env (.m 1 (⟨12, [1]⟩ : Lin))) (env (.m 1 (⟨13, [1]⟩ : Lin))) (env (.m 1 (⟨14, [1]⟩ : Lin))) (env (.m 1 (⟨15, [1]⟩ : Lin))) (V (.R 0 3)) ((inp 12)) ((inp 13)) ((inp 14)) ((inp 15)) h0 h1 h2 h3 h4

theorem core4_230 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨8, [1]⟩ : Lin)) = (inp 8).zeroExtend 32)
    (h1 : env (.m 1 (⟨9, [1]⟩ : Lin)) = (inp 9).zeroExtend 32)
    (h2 : env (.m 1 (⟨10, [1]⟩ : Lin)) = (inp 10).zeroExtend 32)
    (h3 : env (.m 1 (⟨11, [1]⟩ : Lin)) = (inp 11).zeroExtend 32)
    (h4 : V (.R 0 2) = ((((0 : Word) ||| (inp 8).zeroExtend 32 <<< 0) ||| (inp 9).zeroExtend 32 <<< 8) ||| (inp 10).zeroExtend 32 <<< 16) ||| (inp 11).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨8, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨9, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨10, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨11, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 2) :=
  shape0 (env (.m 1 (⟨8, [1]⟩ : Lin))) (env (.m 1 (⟨9, [1]⟩ : Lin))) (env (.m 1 (⟨10, [1]⟩ : Lin))) (env (.m 1 (⟨11, [1]⟩ : Lin))) (V (.R 0 2)) ((inp 8)) ((inp 9)) ((inp 10)) ((inp 11)) h0 h1 h2 h3 h4

theorem core4_229 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨4, [1]⟩ : Lin)) = (inp 4).zeroExtend 32)
    (h1 : env (.m 1 (⟨5, [1]⟩ : Lin)) = (inp 5).zeroExtend 32)
    (h2 : env (.m 1 (⟨6, [1]⟩ : Lin)) = (inp 6).zeroExtend 32)
    (h3 : env (.m 1 (⟨7, [1]⟩ : Lin)) = (inp 7).zeroExtend 32)
    (h4 : V (.R 0 1) = ((((0 : Word) ||| (inp 4).zeroExtend 32 <<< 0) ||| (inp 5).zeroExtend 32 <<< 8) ||| (inp 6).zeroExtend 32 <<< 16) ||| (inp 7).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨4, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨5, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨6, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨7, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 1) :=
  shape0 (env (.m 1 (⟨4, [1]⟩ : Lin))) (env (.m 1 (⟨5, [1]⟩ : Lin))) (env (.m 1 (⟨6, [1]⟩ : Lin))) (env (.m 1 (⟨7, [1]⟩ : Lin))) (V (.R 0 1)) ((inp 4)) ((inp 5)) ((inp 6)) ((inp 7)) h0 h1 h2 h3 h4

theorem core4_228 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨0, [1]⟩ : Lin)) = (inp 0).zeroExtend 32)
    (h1 : env (.m 1 (⟨1, [1]⟩ : Lin)) = (inp 1).zeroExtend 32)
    (h2 : env (.m 1 (⟨2, [1]⟩ : Lin)) = (inp 2).zeroExtend 32)
    (h3 : env (.m 1 (⟨3, [1]⟩ : Lin)) = (inp 3).zeroExtend 32)
    (h4 : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨0, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨1, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨2, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨3, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 0 0) :=
  shape0 (env (.m 1 (⟨0, [1]⟩ : Lin))) (env (.m 1 (⟨1, [1]⟩ : Lin))) (env (.m 1 (⟨2, [1]⟩ : Lin))) (env (.m 1 (⟨3, [1]⟩ : Lin))) (V (.R 0 0)) ((inp 0)) ((inp 1)) ((inp 2)) ((inp 3)) h0 h1 h2 h3 h4

theorem step4 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L4) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K4)) L5 := by
  exact invC_of_trees inp env _ T4 L5 (slice_trees_mem prog 4 _ _ 8 K4 K5 T4 slice4 env)
      (And.intro ⟨rfl, core4_315 (qv inp) inp env (hm 108 (by decide)) (hm 109 (by decide)) (hm 110 (by decide)) (hm 111 (by decide)) (qR inp 1 11)⟩
      (And.intro ⟨rfl, core4_314 (qv inp) inp env (hm 104 (by decide)) (hm 105 (by decide)) (hm 106 (by decide)) (hm 107 (by decide)) (qR inp 1 10)⟩
      (And.intro ⟨rfl, core4_313 (qv inp) inp env (hm 100 (by decide)) (hm 101 (by decide)) (hm 102 (by decide)) (hm 103 (by decide)) (qR inp 1 9)⟩
      (And.intro ⟨rfl, core4_312 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core4_311 (qv inp) inp env (hm 92 (by decide)) (hm 93 (by decide)) (hm 94 (by decide)) (hm 95 (by decide)) (qR inp 1 7)⟩
      (And.intro ⟨rfl, core4_310 (qv inp) inp env (hm 88 (by decide)) (hm 89 (by decide)) (hm 90 (by decide)) (hm 91 (by decide)) (qR inp 1 6)⟩
      (And.intro ⟨rfl, core4_309 (qv inp) inp env (hm 84 (by decide)) (hm 85 (by decide)) (hm 86 (by decide)) (hm 87 (by decide)) (qR inp 1 5)⟩
      (And.intro ⟨rfl, core4_308 (qv inp) inp env (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core4_299 (qv inp) inp env (hm 44 (by decide)) (hm 45 (by decide)) (hm 46 (by decide)) (hm 47 (by decide)) (qR inp 0 11)⟩
      (And.intro ⟨rfl, core4_298 (qv inp) inp env (hm 40 (by decide)) (hm 41 (by decide)) (hm 42 (by decide)) (hm 43 (by decide)) (qR inp 0 10)⟩
      (And.intro ⟨rfl, core4_297 (qv inp) inp env (hm 36 (by decide)) (hm 37 (by decide)) (hm 38 (by decide)) (hm 39 (by decide)) (qR inp 0 9)⟩
      (And.intro ⟨rfl, core4_296 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core4_295 (qv inp) inp env (hm 28 (by decide)) (hm 29 (by decide)) (hm 30 (by decide)) (hm 31 (by decide)) (qR inp 0 7)⟩
      (And.intro ⟨rfl, core4_294 (qv inp) inp env (hm 24 (by decide)) (hm 25 (by decide)) (hm 26 (by decide)) (hm 27 (by decide)) (qR inp 0 6)⟩
      (And.intro ⟨rfl, core4_293 (qv inp) inp env (hm 20 (by decide)) (hm 21 (by decide)) (hm 22 (by decide)) (hm 23 (by decide)) (qR inp 0 5)⟩
      (And.intro ⟨rfl, core4_292 (qv inp) inp env (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qR inp 0 4)⟩
      (And.intro ⟨rfl, core4_283 (qv inp) inp env (hm 220 (by decide)) (hm 221 (by decide)) (hm 222 (by decide)) (hm 223 (by decide)) (qR inp 3 7)⟩
      (And.intro ⟨rfl, core4_282 (qv inp) inp env (hm 216 (by decide)) (hm 217 (by decide)) (hm 218 (by decide)) (hm 219 (by decide)) (qR inp 3 6)⟩
      (And.intro ⟨rfl, core4_281 (qv inp) inp env (hm 212 (by decide)) (hm 213 (by decide)) (hm 214 (by decide)) (hm 215 (by decide)) (qR inp 3 5)⟩
      (And.intro ⟨rfl, core4_280 (qv inp) inp env (hm 208 (by decide)) (hm 209 (by decide)) (hm 210 (by decide)) (hm 211 (by decide)) (qR inp 3 4)⟩
      (And.intro ⟨rfl, core4_279 (qv inp) inp env (hm 204 (by decide)) (hm 205 (by decide)) (hm 206 (by decide)) (hm 207 (by decide)) (qR inp 3 3)⟩
      (And.intro ⟨rfl, core4_278 (qv inp) inp env (hm 200 (by decide)) (hm 201 (by decide)) (hm 202 (by decide)) (hm 203 (by decide)) (qR inp 3 2)⟩
      (And.intro ⟨rfl, core4_277 (qv inp) inp env (hm 196 (by decide)) (hm 197 (by decide)) (hm 198 (by decide)) (hm 199 (by decide)) (qR inp 3 1)⟩
      (And.intro ⟨rfl, core4_276 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core4_267 (qv inp) inp env (hm 156 (by decide)) (hm 157 (by decide)) (hm 158 (by decide)) (hm 159 (by decide)) (qR inp 2 7)⟩
      (And.intro ⟨rfl, core4_266 (qv inp) inp env (hm 152 (by decide)) (hm 153 (by decide)) (hm 154 (by decide)) (hm 155 (by decide)) (qR inp 2 6)⟩
      (And.intro ⟨rfl, core4_265 (qv inp) inp env (hm 148 (by decide)) (hm 149 (by decide)) (hm 150 (by decide)) (hm 151 (by decide)) (qR inp 2 5)⟩
      (And.intro ⟨rfl, core4_264 (qv inp) inp env (hm 144 (by decide)) (hm 145 (by decide)) (hm 146 (by decide)) (hm 147 (by decide)) (qR inp 2 4)⟩
      (And.intro ⟨rfl, core4_263 (qv inp) inp env (hm 140 (by decide)) (hm 141 (by decide)) (hm 142 (by decide)) (hm 143 (by decide)) (qR inp 2 3)⟩
      (And.intro ⟨rfl, core4_262 (qv inp) inp env (hm 136 (by decide)) (hm 137 (by decide)) (hm 138 (by decide)) (hm 139 (by decide)) (qR inp 2 2)⟩
      (And.intro ⟨rfl, core4_261 (qv inp) inp env (hm 132 (by decide)) (hm 133 (by decide)) (hm 134 (by decide)) (hm 135 (by decide)) (qR inp 2 1)⟩
      (And.intro ⟨rfl, core4_260 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core4_251 (qv inp) inp env (hm 92 (by decide)) (hm 93 (by decide)) (hm 94 (by decide)) (hm 95 (by decide)) (qR inp 1 7)⟩
      (And.intro ⟨rfl, core4_250 (qv inp) inp env (hm 88 (by decide)) (hm 89 (by decide)) (hm 90 (by decide)) (hm 91 (by decide)) (qR inp 1 6)⟩
      (And.intro ⟨rfl, core4_249 (qv inp) inp env (hm 84 (by decide)) (hm 85 (by decide)) (hm 86 (by decide)) (hm 87 (by decide)) (qR inp 1 5)⟩
      (And.intro ⟨rfl, core4_248 (qv inp) inp env (hm 80 (by decide)) (hm 81 (by decide)) (hm 82 (by decide)) (hm 83 (by decide)) (qR inp 1 4)⟩
      (And.intro ⟨rfl, core4_247 (qv inp) inp env (hm 76 (by decide)) (hm 77 (by decide)) (hm 78 (by decide)) (hm 79 (by decide)) (qR inp 1 3)⟩
      (And.intro ⟨rfl, core4_246 (qv inp) inp env (hm 72 (by decide)) (hm 73 (by decide)) (hm 74 (by decide)) (hm 75 (by decide)) (qR inp 1 2)⟩
      (And.intro ⟨rfl, core4_245 (qv inp) inp env (hm 68 (by decide)) (hm 69 (by decide)) (hm 70 (by decide)) (hm 71 (by decide)) (qR inp 1 1)⟩
      (And.intro ⟨rfl, core4_244 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core4_235 (qv inp) inp env (hm 28 (by decide)) (hm 29 (by decide)) (hm 30 (by decide)) (hm 31 (by decide)) (qR inp 0 7)⟩
      (And.intro ⟨rfl, core4_234 (qv inp) inp env (hm 24 (by decide)) (hm 25 (by decide)) (hm 26 (by decide)) (hm 27 (by decide)) (qR inp 0 6)⟩
      (And.intro ⟨rfl, core4_233 (qv inp) inp env (hm 20 (by decide)) (hm 21 (by decide)) (hm 22 (by decide)) (hm 23 (by decide)) (qR inp 0 5)⟩
      (And.intro ⟨rfl, core4_232 (qv inp) inp env (hm 16 (by decide)) (hm 17 (by decide)) (hm 18 (by decide)) (hm 19 (by decide)) (qR inp 0 4)⟩
      (And.intro ⟨rfl, core4_231 (qv inp) inp env (hm 12 (by decide)) (hm 13 (by decide)) (hm 14 (by decide)) (hm 15 (by decide)) (qR inp 0 3)⟩
      (And.intro ⟨rfl, core4_230 (qv inp) inp env (hm 8 (by decide)) (hm 9 (by decide)) (hm 10 (by decide)) (hm 11 (by decide)) (qR inp 0 2)⟩
      (And.intro ⟨rfl, core4_229 (qv inp) inp env (hm 4 (by decide)) (hm 5 (by decide)) (hm 6 (by decide)) (hm 7 (by decide)) (qR inp 0 1)⟩
      (And.intro ⟨rfl, core4_228 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qR inp 0 0)⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
