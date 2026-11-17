import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D11
import Hashtree.Gen.WinAvxX4P.D10

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice11 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 55 K11 K12 T11 = true := by
  decide +kernel

theorem core11_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape0 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core11_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape0 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core11_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape0 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core11_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨32, [1]⟩ : Lin)) = (inp 32).zeroExtend 32)
    (h1 : env (.m 1 (⟨33, [1]⟩ : Lin)) = (inp 33).zeroExtend 32)
    (h2 : env (.m 1 (⟨34, [1]⟩ : Lin)) = (inp 34).zeroExtend 32)
    (h3 : env (.m 1 (⟨35, [1]⟩ : Lin)) = (inp 35).zeroExtend 32)
    (h4 : V (.W 0 0 8) = bswap (V (.R 0 8)))
    (h5 : V (.R 0 8) = ((((0 : Word) ||| (inp 32).zeroExtend 32 <<< 0) ||| (inp 33).zeroExtend 32 <<< 8) ||| (inp 34).zeroExtend 32 <<< 16) ||| (inp 35).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨32, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨33, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨34, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨35, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 8) :=
  shape0 (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5

theorem core11_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape0 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core11_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape0 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core11_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape0 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core11_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨96, [1]⟩ : Lin)) = (inp 96).zeroExtend 32)
    (h1 : env (.m 1 (⟨97, [1]⟩ : Lin)) = (inp 97).zeroExtend 32)
    (h2 : env (.m 1 (⟨98, [1]⟩ : Lin)) = (inp 98).zeroExtend 32)
    (h3 : env (.m 1 (⟨99, [1]⟩ : Lin)) = (inp 99).zeroExtend 32)
    (h4 : V (.W 1 0 8) = bswap (V (.R 1 8)))
    (h5 : V (.R 1 8) = ((((0 : Word) ||| (inp 96).zeroExtend 32 <<< 0) ||| (inp 97).zeroExtend 32 <<< 8) ||| (inp 98).zeroExtend 32 <<< 16) ||| (inp 99).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨96, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨97, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨98, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨99, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 8) :=
  shape0 (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5

theorem core11_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape0 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core11_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape0 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core11_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape0 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core11_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨160, [1]⟩ : Lin)) = (inp 160).zeroExtend 32)
    (h1 : env (.m 1 (⟨161, [1]⟩ : Lin)) = (inp 161).zeroExtend 32)
    (h2 : env (.m 1 (⟨162, [1]⟩ : Lin)) = (inp 162).zeroExtend 32)
    (h3 : env (.m 1 (⟨163, [1]⟩ : Lin)) = (inp 163).zeroExtend 32)
    (h4 : V (.W 2 0 8) = bswap (V (.R 2 8)))
    (h5 : V (.R 2 8) = ((((0 : Word) ||| (inp 160).zeroExtend 32 <<< 0) ||| (inp 161).zeroExtend 32 <<< 8) ||| (inp 162).zeroExtend 32 <<< 16) ||| (inp 163).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨160, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨161, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨162, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨163, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 8) :=
  shape0 (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5

theorem core11_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape0 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core11_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape0 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core11_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape0 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core11_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨224, [1]⟩ : Lin)) = (inp 224).zeroExtend 32)
    (h1 : env (.m 1 (⟨225, [1]⟩ : Lin)) = (inp 225).zeroExtend 32)
    (h2 : env (.m 1 (⟨226, [1]⟩ : Lin)) = (inp 226).zeroExtend 32)
    (h3 : env (.m 1 (⟨227, [1]⟩ : Lin)) = (inp 227).zeroExtend 32)
    (h4 : V (.W 3 0 8) = bswap (V (.R 3 8)))
    (h5 : V (.R 3 8) = ((((0 : Word) ||| (inp 224).zeroExtend 32 <<< 0) ||| (inp 225).zeroExtend 32 <<< 8) ||| (inp 226).zeroExtend 32 <<< 16) ||| (inp 227).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨224, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨225, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨226, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨227, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 8) :=
  shape0 (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5

theorem core11_311 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨228, [1]⟩ : Lin)) = (inp 228).zeroExtend 32)
    (h1 : env (.m 1 (⟨229, [1]⟩ : Lin)) = (inp 229).zeroExtend 32)
    (h2 : env (.m 1 (⟨230, [1]⟩ : Lin)) = (inp 230).zeroExtend 32)
    (h3 : env (.m 1 (⟨231, [1]⟩ : Lin)) = (inp 231).zeroExtend 32)
    (h4 : V (.W 3 0 9) = bswap (V (.R 3 9)))
    (h5 : V (.R 3 9) = ((((0 : Word) ||| (inp 228).zeroExtend 32 <<< 0) ||| (inp 229).zeroExtend 32 <<< 8) ||| (inp 230).zeroExtend 32 <<< 16) ||| (inp 231).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨228, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨229, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨230, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨231, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 9) :=
  shape0 (env (.m 1 (⟨228, [1]⟩ : Lin))) (env (.m 1 (⟨229, [1]⟩ : Lin))) (env (.m 1 (⟨230, [1]⟩ : Lin))) (env (.m 1 (⟨231, [1]⟩ : Lin))) (V (.W 3 0 9)) (V (.R 3 9)) ((inp 228)) ((inp 229)) ((inp 230)) ((inp 231)) h0 h1 h2 h3 h4 h5

theorem core11_310 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨164, [1]⟩ : Lin)) = (inp 164).zeroExtend 32)
    (h1 : env (.m 1 (⟨165, [1]⟩ : Lin)) = (inp 165).zeroExtend 32)
    (h2 : env (.m 1 (⟨166, [1]⟩ : Lin)) = (inp 166).zeroExtend 32)
    (h3 : env (.m 1 (⟨167, [1]⟩ : Lin)) = (inp 167).zeroExtend 32)
    (h4 : V (.W 2 0 9) = bswap (V (.R 2 9)))
    (h5 : V (.R 2 9) = ((((0 : Word) ||| (inp 164).zeroExtend 32 <<< 0) ||| (inp 165).zeroExtend 32 <<< 8) ||| (inp 166).zeroExtend 32 <<< 16) ||| (inp 167).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨164, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨165, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨166, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨167, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 9) :=
  shape0 (env (.m 1 (⟨164, [1]⟩ : Lin))) (env (.m 1 (⟨165, [1]⟩ : Lin))) (env (.m 1 (⟨166, [1]⟩ : Lin))) (env (.m 1 (⟨167, [1]⟩ : Lin))) (V (.W 2 0 9)) (V (.R 2 9)) ((inp 164)) ((inp 165)) ((inp 166)) ((inp 167)) h0 h1 h2 h3 h4 h5

theorem core11_309 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨100, [1]⟩ : Lin)) = (inp 100).zeroExtend 32)
    (h1 : env (.m 1 (⟨101, [1]⟩ : Lin)) = (inp 101).zeroExtend 32)
    (h2 : env (.m 1 (⟨102, [1]⟩ : Lin)) = (inp 102).zeroExtend 32)
    (h3 : env (.m 1 (⟨103, [1]⟩ : Lin)) = (inp 103).zeroExtend 32)
    (h4 : V (.W 1 0 9) = bswap (V (.R 1 9)))
    (h5 : V (.R 1 9) = ((((0 : Word) ||| (inp 100).zeroExtend 32 <<< 0) ||| (inp 101).zeroExtend 32 <<< 8) ||| (inp 102).zeroExtend 32 <<< 16) ||| (inp 103).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨100, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨101, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨102, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨103, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 9) :=
  shape0 (env (.m 1 (⟨100, [1]⟩ : Lin))) (env (.m 1 (⟨101, [1]⟩ : Lin))) (env (.m 1 (⟨102, [1]⟩ : Lin))) (env (.m 1 (⟨103, [1]⟩ : Lin))) (V (.W 1 0 9)) (V (.R 1 9)) ((inp 100)) ((inp 101)) ((inp 102)) ((inp 103)) h0 h1 h2 h3 h4 h5

theorem core11_308 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨36, [1]⟩ : Lin)) = (inp 36).zeroExtend 32)
    (h1 : env (.m 1 (⟨37, [1]⟩ : Lin)) = (inp 37).zeroExtend 32)
    (h2 : env (.m 1 (⟨38, [1]⟩ : Lin)) = (inp 38).zeroExtend 32)
    (h3 : env (.m 1 (⟨39, [1]⟩ : Lin)) = (inp 39).zeroExtend 32)
    (h4 : V (.W 0 0 9) = bswap (V (.R 0 9)))
    (h5 : V (.R 0 9) = ((((0 : Word) ||| (inp 36).zeroExtend 32 <<< 0) ||| (inp 37).zeroExtend 32 <<< 8) ||| (inp 38).zeroExtend 32 <<< 16) ||| (inp 39).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨36, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨37, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨38, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨39, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 9) :=
  shape0 (env (.m 1 (⟨36, [1]⟩ : Lin))) (env (.m 1 (⟨37, [1]⟩ : Lin))) (env (.m 1 (⟨38, [1]⟩ : Lin))) (env (.m 1 (⟨39, [1]⟩ : Lin))) (V (.W 0 0 9)) (V (.R 0 9)) ((inp 36)) ((inp 37)) ((inp 38)) ((inp 39)) h0 h1 h2 h3 h4 h5

theorem core11_295 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨232, [1]⟩ : Lin)) = (inp 232).zeroExtend 32)
    (h1 : env (.m 1 (⟨233, [1]⟩ : Lin)) = (inp 233).zeroExtend 32)
    (h2 : env (.m 1 (⟨234, [1]⟩ : Lin)) = (inp 234).zeroExtend 32)
    (h3 : env (.m 1 (⟨235, [1]⟩ : Lin)) = (inp 235).zeroExtend 32)
    (h4 : V (.W 3 0 10) = bswap (V (.R 3 10)))
    (h5 : V (.R 3 10) = ((((0 : Word) ||| (inp 232).zeroExtend 32 <<< 0) ||| (inp 233).zeroExtend 32 <<< 8) ||| (inp 234).zeroExtend 32 <<< 16) ||| (inp 235).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨232, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨233, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨234, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨235, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 10) :=
  shape0 (env (.m 1 (⟨232, [1]⟩ : Lin))) (env (.m 1 (⟨233, [1]⟩ : Lin))) (env (.m 1 (⟨234, [1]⟩ : Lin))) (env (.m 1 (⟨235, [1]⟩ : Lin))) (V (.W 3 0 10)) (V (.R 3 10)) ((inp 232)) ((inp 233)) ((inp 234)) ((inp 235)) h0 h1 h2 h3 h4 h5

theorem core11_294 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨168, [1]⟩ : Lin)) = (inp 168).zeroExtend 32)
    (h1 : env (.m 1 (⟨169, [1]⟩ : Lin)) = (inp 169).zeroExtend 32)
    (h2 : env (.m 1 (⟨170, [1]⟩ : Lin)) = (inp 170).zeroExtend 32)
    (h3 : env (.m 1 (⟨171, [1]⟩ : Lin)) = (inp 171).zeroExtend 32)
    (h4 : V (.W 2 0 10) = bswap (V (.R 2 10)))
    (h5 : V (.R 2 10) = ((((0 : Word) ||| (inp 168).zeroExtend 32 <<< 0) ||| (inp 169).zeroExtend 32 <<< 8) ||| (inp 170).zeroExtend 32 <<< 16) ||| (inp 171).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨168, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨169, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨170, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨171, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 10) :=
  shape0 (env (.m 1 (⟨168, [1]⟩ : Lin))) (env (.m 1 (⟨169, [1]⟩ : Lin))) (env (.m 1 (⟨170, [1]⟩ : Lin))) (env (.m 1 (⟨171, [1]⟩ : Lin))) (V (.W 2 0 10)) (V (.R 2 10)) ((inp 168)) ((inp 169)) ((inp 170)) ((inp 171)) h0 h1 h2 h3 h4 h5

theorem core11_293 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨104, [1]⟩ : Lin)) = (inp 104).zeroExtend 32)
    (h1 : env (.m 1 (⟨105, [1]⟩ : Lin)) = (inp 105).zeroExtend 32)
    (h2 : env (.m 1 (⟨106, [1]⟩ : Lin)) = (inp 106).zeroExtend 32)
    (h3 : env (.m 1 (⟨107, [1]⟩ : Lin)) = (inp 107).zeroExtend 32)
    (h4 : V (.W 1 0 10) = bswap (V (.R 1 10)))
    (h5 : V (.R 1 10) = ((((0 : Word) ||| (inp 104).zeroExtend 32 <<< 0) ||| (inp 105).zeroExtend 32 <<< 8) ||| (inp 106).zeroExtend 32 <<< 16) ||| (inp 107).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨104, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨105, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨106, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨107, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 10) :=
  shape0 (env (.m 1 (⟨104, [1]⟩ : Lin))) (env (.m 1 (⟨105, [1]⟩ : Lin))) (env (.m 1 (⟨106, [1]⟩ : Lin))) (env (.m 1 (⟨107, [1]⟩ : Lin))) (V (.W 1 0 10)) (V (.R 1 10)) ((inp 104)) ((inp 105)) ((inp 106)) ((inp 107)) h0 h1 h2 h3 h4 h5

theorem core11_292 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨40, [1]⟩ : Lin)) = (inp 40).zeroExtend 32)
    (h1 : env (.m 1 (⟨41, [1]⟩ : Lin)) = (inp 41).zeroExtend 32)
    (h2 : env (.m 1 (⟨42, [1]⟩ : Lin)) = (inp 42).zeroExtend 32)
    (h3 : env (.m 1 (⟨43, [1]⟩ : Lin)) = (inp 43).zeroExtend 32)
    (h4 : V (.W 0 0 10) = bswap (V (.R 0 10)))
    (h5 : V (.R 0 10) = ((((0 : Word) ||| (inp 40).zeroExtend 32 <<< 0) ||| (inp 41).zeroExtend 32 <<< 8) ||| (inp 42).zeroExtend 32 <<< 16) ||| (inp 43).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨40, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨41, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨42, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨43, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 10) :=
  shape0 (env (.m 1 (⟨40, [1]⟩ : Lin))) (env (.m 1 (⟨41, [1]⟩ : Lin))) (env (.m 1 (⟨42, [1]⟩ : Lin))) (env (.m 1 (⟨43, [1]⟩ : Lin))) (V (.W 0 0 10)) (V (.R 0 10)) ((inp 40)) ((inp 41)) ((inp 42)) ((inp 43)) h0 h1 h2 h3 h4 h5

theorem core11_279 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨236, [1]⟩ : Lin)) = (inp 236).zeroExtend 32)
    (h1 : env (.m 1 (⟨237, [1]⟩ : Lin)) = (inp 237).zeroExtend 32)
    (h2 : env (.m 1 (⟨238, [1]⟩ : Lin)) = (inp 238).zeroExtend 32)
    (h3 : env (.m 1 (⟨239, [1]⟩ : Lin)) = (inp 239).zeroExtend 32)
    (h4 : V (.W 3 0 11) = bswap (V (.R 3 11)))
    (h5 : V (.R 3 11) = ((((0 : Word) ||| (inp 236).zeroExtend 32 <<< 0) ||| (inp 237).zeroExtend 32 <<< 8) ||| (inp 238).zeroExtend 32 <<< 16) ||| (inp 239).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨236, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨237, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨238, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨239, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 3 0 11) :=
  shape0 (env (.m 1 (⟨236, [1]⟩ : Lin))) (env (.m 1 (⟨237, [1]⟩ : Lin))) (env (.m 1 (⟨238, [1]⟩ : Lin))) (env (.m 1 (⟨239, [1]⟩ : Lin))) (V (.W 3 0 11)) (V (.R 3 11)) ((inp 236)) ((inp 237)) ((inp 238)) ((inp 239)) h0 h1 h2 h3 h4 h5

theorem core11_278 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨172, [1]⟩ : Lin)) = (inp 172).zeroExtend 32)
    (h1 : env (.m 1 (⟨173, [1]⟩ : Lin)) = (inp 173).zeroExtend 32)
    (h2 : env (.m 1 (⟨174, [1]⟩ : Lin)) = (inp 174).zeroExtend 32)
    (h3 : env (.m 1 (⟨175, [1]⟩ : Lin)) = (inp 175).zeroExtend 32)
    (h4 : V (.W 2 0 11) = bswap (V (.R 2 11)))
    (h5 : V (.R 2 11) = ((((0 : Word) ||| (inp 172).zeroExtend 32 <<< 0) ||| (inp 173).zeroExtend 32 <<< 8) ||| (inp 174).zeroExtend 32 <<< 16) ||| (inp 175).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨172, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨173, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨174, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨175, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 2 0 11) :=
  shape0 (env (.m 1 (⟨172, [1]⟩ : Lin))) (env (.m 1 (⟨173, [1]⟩ : Lin))) (env (.m 1 (⟨174, [1]⟩ : Lin))) (env (.m 1 (⟨175, [1]⟩ : Lin))) (V (.W 2 0 11)) (V (.R 2 11)) ((inp 172)) ((inp 173)) ((inp 174)) ((inp 175)) h0 h1 h2 h3 h4 h5

theorem core11_277 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨108, [1]⟩ : Lin)) = (inp 108).zeroExtend 32)
    (h1 : env (.m 1 (⟨109, [1]⟩ : Lin)) = (inp 109).zeroExtend 32)
    (h2 : env (.m 1 (⟨110, [1]⟩ : Lin)) = (inp 110).zeroExtend 32)
    (h3 : env (.m 1 (⟨111, [1]⟩ : Lin)) = (inp 111).zeroExtend 32)
    (h4 : V (.W 1 0 11) = bswap (V (.R 1 11)))
    (h5 : V (.R 1 11) = ((((0 : Word) ||| (inp 108).zeroExtend 32 <<< 0) ||| (inp 109).zeroExtend 32 <<< 8) ||| (inp 110).zeroExtend 32 <<< 16) ||| (inp 111).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨108, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨109, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨110, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨111, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 1 0 11) :=
  shape0 (env (.m 1 (⟨108, [1]⟩ : Lin))) (env (.m 1 (⟨109, [1]⟩ : Lin))) (env (.m 1 (⟨110, [1]⟩ : Lin))) (env (.m 1 (⟨111, [1]⟩ : Lin))) (V (.W 1 0 11)) (V (.R 1 11)) ((inp 108)) ((inp 109)) ((inp 110)) ((inp 111)) h0 h1 h2 h3 h4 h5

theorem core11_276 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨44, [1]⟩ : Lin)) = (inp 44).zeroExtend 32)
    (h1 : env (.m 1 (⟨45, [1]⟩ : Lin)) = (inp 45).zeroExtend 32)
    (h2 : env (.m 1 (⟨46, [1]⟩ : Lin)) = (inp 46).zeroExtend 32)
    (h3 : env (.m 1 (⟨47, [1]⟩ : Lin)) = (inp 47).zeroExtend 32)
    (h4 : V (.W 0 0 11) = bswap (V (.R 0 11)))
    (h5 : V (.R 0 11) = ((((0 : Word) ||| (inp 44).zeroExtend 32 <<< 0) ||| (inp 45).zeroExtend 32 <<< 8) ||| (inp 46).zeroExtend 32 <<< 16) ||| (inp 47).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 24) (.const 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 8) (.const 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.var (.m 1 (⟨44, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨45, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨46, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨47, [1]⟩ : Lin))) 0) (.const 255)) 24))) 0) (.const 255)) 24))) = V (.W 0 0 11) :=
  shape0 (env (.m 1 (⟨44, [1]⟩ : Lin))) (env (.m 1 (⟨45, [1]⟩ : Lin))) (env (.m 1 (⟨46, [1]⟩ : Lin))) (env (.m 1 (⟨47, [1]⟩ : Lin))) (V (.W 0 0 11)) (V (.R 0 11)) ((inp 44)) ((inp 45)) ((inp 46)) ((inp 47)) h0 h1 h2 h3 h4 h5

theorem core11_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape17 (env (.n 215)) (env (.n 183)) (env (.n 199)) (env (.n 167)) (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (env (.n 103)) (env (.n 135)) (env (.n 119)) (V (.E 3 0 (5))) (V (.E 3 0 (7))) (V (.E 3 0 (6))) (V (.E 3 0 (8))) (V (.A 3 0 (8))) (V (.A 3 0 (6))) (V (.A 3 0 (7))) (V (.A 3 0 (9))) (V (.KW 3 0 8)) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core11_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape17 (env (.n 214)) (env (.n 182)) (env (.n 198)) (env (.n 166)) (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (env (.n 102)) (env (.n 134)) (env (.n 118)) (V (.E 2 0 (5))) (V (.E 2 0 (7))) (V (.E 2 0 (6))) (V (.E 2 0 (8))) (V (.A 2 0 (8))) (V (.A 2 0 (6))) (V (.A 2 0 (7))) (V (.A 2 0 (9))) (V (.KW 2 0 8)) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core11_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape17 (env (.n 213)) (env (.n 181)) (env (.n 197)) (env (.n 165)) (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (env (.n 101)) (env (.n 133)) (env (.n 117)) (V (.E 1 0 (5))) (V (.E 1 0 (7))) (V (.E 1 0 (6))) (V (.E 1 0 (8))) (V (.A 1 0 (8))) (V (.A 1 0 (6))) (V (.A 1 0 (7))) (V (.A 1 0 (9))) (V (.KW 1 0 8)) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core11_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape17 (env (.n 212)) (env (.n 180)) (env (.n 196)) (env (.n 164)) (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (env (.n 100)) (env (.n 132)) (env (.n 116)) (V (.E 0 0 (5))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) (V (.E 0 0 (8))) (V (.A 0 0 (8))) (V (.A 0 0 (6))) (V (.A 0 0 (7))) (V (.A 0 0 (9))) (V (.KW 0 0 8)) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

theorem core11_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape18 (env (.n 151)) (env (.n 215)) (env (.n 183)) (env (.n 199)) (env (.n 167)) (env (.m 1 (⟨224, [1]⟩ : Lin))) (env (.m 1 (⟨225, [1]⟩ : Lin))) (env (.m 1 (⟨226, [1]⟩ : Lin))) (env (.m 1 (⟨227, [1]⟩ : Lin))) (V (.A 3 0 (5))) (V (.E 3 0 (5))) (V (.E 3 0 (7))) (V (.E 3 0 (6))) (V (.E 3 0 (8))) (V (.E 3 0 (9))) (V (.KW 3 0 8)) (V (.W 3 0 8)) (V (.R 3 8)) ((inp 224)) ((inp 225)) ((inp 226)) ((inp 227)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core11_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape18 (env (.n 150)) (env (.n 214)) (env (.n 182)) (env (.n 198)) (env (.n 166)) (env (.m 1 (⟨160, [1]⟩ : Lin))) (env (.m 1 (⟨161, [1]⟩ : Lin))) (env (.m 1 (⟨162, [1]⟩ : Lin))) (env (.m 1 (⟨163, [1]⟩ : Lin))) (V (.A 2 0 (5))) (V (.E 2 0 (5))) (V (.E 2 0 (7))) (V (.E 2 0 (6))) (V (.E 2 0 (8))) (V (.E 2 0 (9))) (V (.KW 2 0 8)) (V (.W 2 0 8)) (V (.R 2 8)) ((inp 160)) ((inp 161)) ((inp 162)) ((inp 163)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core11_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape18 (env (.n 149)) (env (.n 213)) (env (.n 181)) (env (.n 197)) (env (.n 165)) (env (.m 1 (⟨96, [1]⟩ : Lin))) (env (.m 1 (⟨97, [1]⟩ : Lin))) (env (.m 1 (⟨98, [1]⟩ : Lin))) (env (.m 1 (⟨99, [1]⟩ : Lin))) (V (.A 1 0 (5))) (V (.E 1 0 (5))) (V (.E 1 0 (7))) (V (.E 1 0 (6))) (V (.E 1 0 (8))) (V (.E 1 0 (9))) (V (.KW 1 0 8)) (V (.W 1 0 8)) (V (.R 1 8)) ((inp 96)) ((inp 97)) ((inp 98)) ((inp 99)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem core11_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
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
  shape18 (env (.n 148)) (env (.n 212)) (env (.n 180)) (env (.n 196)) (env (.n 164)) (env (.m 1 (⟨32, [1]⟩ : Lin))) (env (.m 1 (⟨33, [1]⟩ : Lin))) (env (.m 1 (⟨34, [1]⟩ : Lin))) (env (.m 1 (⟨35, [1]⟩ : Lin))) (V (.A 0 0 (5))) (V (.E 0 0 (5))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) (V (.E 0 0 (8))) (V (.E 0 0 (9))) (V (.KW 0 0 8)) (V (.W 0 0 8)) (V (.R 0 8)) ((inp 32)) ((inp 33)) ((inp 34)) ((inp 35)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem step11 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L11) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 55 K11)) L12 := by
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
  exact invC_of_trees inp env _ T11 L12 (slice_trees_mem prog 4 _ _ 55 K11 K12 T11 slice11 env)
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
      (And.intro ⟨rfl, core11_1015 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core11_1014 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core11_1013 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core11_1012 (qv inp) inp env (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
      (And.intro ⟨rfl, core11_1011 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core11_1010 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core11_1009 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core11_1008 (qv inp) inp env (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core11_1007 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core11_1006 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core11_1005 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core11_1004 (qv inp) inp env (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core11_1003 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core11_1002 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core11_1001 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core11_1000 (qv inp) inp env (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core11_311 (qv inp) inp env (hm 228 (by decide)) (hm 229 (by decide)) (hm 230 (by decide)) (hm 231 (by decide)) (qW_R inp 3 9 (by decide)) (qR inp 3 9)⟩
      (And.intro ⟨rfl, core11_310 (qv inp) inp env (hm 164 (by decide)) (hm 165 (by decide)) (hm 166 (by decide)) (hm 167 (by decide)) (qW_R inp 2 9 (by decide)) (qR inp 2 9)⟩
      (And.intro ⟨rfl, core11_309 (qv inp) inp env (hm 100 (by decide)) (hm 101 (by decide)) (hm 102 (by decide)) (hm 103 (by decide)) (qW_R inp 1 9 (by decide)) (qR inp 1 9)⟩
      (And.intro ⟨rfl, core11_308 (qv inp) inp env (hm 36 (by decide)) (hm 37 (by decide)) (hm 38 (by decide)) (hm 39 (by decide)) (qW_R inp 0 9 (by decide)) (qR inp 0 9)⟩
      (And.intro ⟨rfl, core11_295 (qv inp) inp env (hm 232 (by decide)) (hm 233 (by decide)) (hm 234 (by decide)) (hm 235 (by decide)) (qW_R inp 3 10 (by decide)) (qR inp 3 10)⟩
      (And.intro ⟨rfl, core11_294 (qv inp) inp env (hm 168 (by decide)) (hm 169 (by decide)) (hm 170 (by decide)) (hm 171 (by decide)) (qW_R inp 2 10 (by decide)) (qR inp 2 10)⟩
      (And.intro ⟨rfl, core11_293 (qv inp) inp env (hm 104 (by decide)) (hm 105 (by decide)) (hm 106 (by decide)) (hm 107 (by decide)) (qW_R inp 1 10 (by decide)) (qR inp 1 10)⟩
      (And.intro ⟨rfl, core11_292 (qv inp) inp env (hm 40 (by decide)) (hm 41 (by decide)) (hm 42 (by decide)) (hm 43 (by decide)) (qW_R inp 0 10 (by decide)) (qR inp 0 10)⟩
      (And.intro ⟨rfl, core11_279 (qv inp) inp env (hm 236 (by decide)) (hm 237 (by decide)) (hm 238 (by decide)) (hm 239 (by decide)) (qW_R inp 3 11 (by decide)) (qR inp 3 11)⟩
      (And.intro ⟨rfl, core11_278 (qv inp) inp env (hm 172 (by decide)) (hm 173 (by decide)) (hm 174 (by decide)) (hm 175 (by decide)) (qW_R inp 2 11 (by decide)) (qR inp 2 11)⟩
      (And.intro ⟨rfl, core11_277 (qv inp) inp env (hm 108 (by decide)) (hm 109 (by decide)) (hm 110 (by decide)) (hm 111 (by decide)) (qW_R inp 1 11 (by decide)) (qR inp 1 11)⟩
      (And.intro ⟨rfl, core11_276 (qv inp) inp env (hm 44 (by decide)) (hm 45 (by decide)) (hm 46 (by decide)) (hm 47 (by decide)) (qW_R inp 0 11 (by decide)) (qR inp 0 11)⟩
      (And.intro ⟨rfl, core11_215 (qv inp) inp env h128 h136 h132 h140 h156 h148 h152 (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qA_succI inp 3 0 (8) (by decide)) ((qKW inp 3 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core11_214 (qv inp) inp env h129 h137 h133 h141 h157 h149 h153 (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qA_succI inp 2 0 (8) (by decide)) ((qKW inp 2 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core11_213 (qv inp) inp env h130 h138 h134 h142 h158 h150 h154 (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qA_succI inp 1 0 (8) (by decide)) ((qKW inp 1 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core11_212 (qv inp) inp env h131 h139 h135 h143 h159 h151 h155 (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qA_succI inp 0 0 (8) (by decide)) ((qKW inp 0 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
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
      (And.intro ⟨rfl, core11_151 (qv inp) inp env h144 h128 h136 h132 h140 (hm 224 (by decide)) (hm 225 (by decide)) (hm 226 (by decide)) (hm 227 (by decide)) (qE_succI inp 3 0 (8) (by decide)) ((qKW inp 3 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 3 8 (by decide)) (qR inp 3 8)⟩
      (And.intro ⟨rfl, core11_150 (qv inp) inp env h145 h129 h137 h133 h141 (hm 160 (by decide)) (hm 161 (by decide)) (hm 162 (by decide)) (hm 163 (by decide)) (qE_succI inp 2 0 (8) (by decide)) ((qKW inp 2 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 2 8 (by decide)) (qR inp 2 8)⟩
      (And.intro ⟨rfl, core11_149 (qv inp) inp env h146 h130 h138 h134 h142 (hm 96 (by decide)) (hm 97 (by decide)) (hm 98 (by decide)) (hm 99 (by decide)) (qE_succI inp 1 0 (8) (by decide)) ((qKW inp 1 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 1 8 (by decide)) (qR inp 1 8)⟩
      (And.intro ⟨rfl, core11_148 (qv inp) inp env h147 h131 h139 h135 h143 (hm 32 (by decide)) (hm 33 (by decide)) (hm 34 (by decide)) (hm 35 (by decide)) (qE_succI inp 0 0 (8) (by decide)) ((qKW inp 0 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])) (qW_R inp 0 8 (by decide)) (qR inp 0 8)⟩
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
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
