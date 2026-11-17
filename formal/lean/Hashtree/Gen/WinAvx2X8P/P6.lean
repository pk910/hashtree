import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D6
import Hashtree.Gen.WinAvx2X8P.D5

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice6 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K6 K7 T6 = true := by
  decide +kernel

theorem core6_347 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨476, [1]⟩ : Lin)) = (inp 476).zeroExtend 32)
    (h1 : env (.m 1 (⟨477, [1]⟩ : Lin)) = (inp 477).zeroExtend 32)
    (h2 : env (.m 1 (⟨478, [1]⟩ : Lin)) = (inp 478).zeroExtend 32)
    (h3 : env (.m 1 (⟨479, [1]⟩ : Lin)) = (inp 479).zeroExtend 32)
    (h4 : V (.R 7 7) = ((((0 : Word) ||| (inp 476).zeroExtend 32 <<< 0) ||| (inp 477).zeroExtend 32 <<< 8) ||| (inp 478).zeroExtend 32 <<< 16) ||| (inp 479).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨476, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨477, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨478, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨479, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 7) :=
  shape0 (env (.m 1 (⟨476, [1]⟩ : Lin))) (env (.m 1 (⟨477, [1]⟩ : Lin))) (env (.m 1 (⟨478, [1]⟩ : Lin))) (env (.m 1 (⟨479, [1]⟩ : Lin))) (V (.R 7 7)) ((inp 476)) ((inp 477)) ((inp 478)) ((inp 479)) h0 h1 h2 h3 h4

theorem core6_346 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨472, [1]⟩ : Lin)) = (inp 472).zeroExtend 32)
    (h1 : env (.m 1 (⟨473, [1]⟩ : Lin)) = (inp 473).zeroExtend 32)
    (h2 : env (.m 1 (⟨474, [1]⟩ : Lin)) = (inp 474).zeroExtend 32)
    (h3 : env (.m 1 (⟨475, [1]⟩ : Lin)) = (inp 475).zeroExtend 32)
    (h4 : V (.R 7 6) = ((((0 : Word) ||| (inp 472).zeroExtend 32 <<< 0) ||| (inp 473).zeroExtend 32 <<< 8) ||| (inp 474).zeroExtend 32 <<< 16) ||| (inp 475).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨472, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨473, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨474, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨475, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 6) :=
  shape0 (env (.m 1 (⟨472, [1]⟩ : Lin))) (env (.m 1 (⟨473, [1]⟩ : Lin))) (env (.m 1 (⟨474, [1]⟩ : Lin))) (env (.m 1 (⟨475, [1]⟩ : Lin))) (V (.R 7 6)) ((inp 472)) ((inp 473)) ((inp 474)) ((inp 475)) h0 h1 h2 h3 h4

theorem core6_345 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨468, [1]⟩ : Lin)) = (inp 468).zeroExtend 32)
    (h1 : env (.m 1 (⟨469, [1]⟩ : Lin)) = (inp 469).zeroExtend 32)
    (h2 : env (.m 1 (⟨470, [1]⟩ : Lin)) = (inp 470).zeroExtend 32)
    (h3 : env (.m 1 (⟨471, [1]⟩ : Lin)) = (inp 471).zeroExtend 32)
    (h4 : V (.R 7 5) = ((((0 : Word) ||| (inp 468).zeroExtend 32 <<< 0) ||| (inp 469).zeroExtend 32 <<< 8) ||| (inp 470).zeroExtend 32 <<< 16) ||| (inp 471).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨468, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨469, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨470, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨471, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 5) :=
  shape0 (env (.m 1 (⟨468, [1]⟩ : Lin))) (env (.m 1 (⟨469, [1]⟩ : Lin))) (env (.m 1 (⟨470, [1]⟩ : Lin))) (env (.m 1 (⟨471, [1]⟩ : Lin))) (V (.R 7 5)) ((inp 468)) ((inp 469)) ((inp 470)) ((inp 471)) h0 h1 h2 h3 h4

theorem core6_344 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨464, [1]⟩ : Lin)) = (inp 464).zeroExtend 32)
    (h1 : env (.m 1 (⟨465, [1]⟩ : Lin)) = (inp 465).zeroExtend 32)
    (h2 : env (.m 1 (⟨466, [1]⟩ : Lin)) = (inp 466).zeroExtend 32)
    (h3 : env (.m 1 (⟨467, [1]⟩ : Lin)) = (inp 467).zeroExtend 32)
    (h4 : V (.R 7 4) = ((((0 : Word) ||| (inp 464).zeroExtend 32 <<< 0) ||| (inp 465).zeroExtend 32 <<< 8) ||| (inp 466).zeroExtend 32 <<< 16) ||| (inp 467).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨464, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨465, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨466, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨467, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 7 4) :=
  shape0 (env (.m 1 (⟨464, [1]⟩ : Lin))) (env (.m 1 (⟨465, [1]⟩ : Lin))) (env (.m 1 (⟨466, [1]⟩ : Lin))) (env (.m 1 (⟨467, [1]⟩ : Lin))) (V (.R 7 4)) ((inp 464)) ((inp 465)) ((inp 466)) ((inp 467)) h0 h1 h2 h3 h4

theorem core6_331 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨412, [1]⟩ : Lin)) = (inp 412).zeroExtend 32)
    (h1 : env (.m 1 (⟨413, [1]⟩ : Lin)) = (inp 413).zeroExtend 32)
    (h2 : env (.m 1 (⟨414, [1]⟩ : Lin)) = (inp 414).zeroExtend 32)
    (h3 : env (.m 1 (⟨415, [1]⟩ : Lin)) = (inp 415).zeroExtend 32)
    (h4 : V (.R 6 7) = ((((0 : Word) ||| (inp 412).zeroExtend 32 <<< 0) ||| (inp 413).zeroExtend 32 <<< 8) ||| (inp 414).zeroExtend 32 <<< 16) ||| (inp 415).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨412, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨413, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨414, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨415, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 7) :=
  shape0 (env (.m 1 (⟨412, [1]⟩ : Lin))) (env (.m 1 (⟨413, [1]⟩ : Lin))) (env (.m 1 (⟨414, [1]⟩ : Lin))) (env (.m 1 (⟨415, [1]⟩ : Lin))) (V (.R 6 7)) ((inp 412)) ((inp 413)) ((inp 414)) ((inp 415)) h0 h1 h2 h3 h4

theorem core6_330 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨408, [1]⟩ : Lin)) = (inp 408).zeroExtend 32)
    (h1 : env (.m 1 (⟨409, [1]⟩ : Lin)) = (inp 409).zeroExtend 32)
    (h2 : env (.m 1 (⟨410, [1]⟩ : Lin)) = (inp 410).zeroExtend 32)
    (h3 : env (.m 1 (⟨411, [1]⟩ : Lin)) = (inp 411).zeroExtend 32)
    (h4 : V (.R 6 6) = ((((0 : Word) ||| (inp 408).zeroExtend 32 <<< 0) ||| (inp 409).zeroExtend 32 <<< 8) ||| (inp 410).zeroExtend 32 <<< 16) ||| (inp 411).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨408, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨409, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨410, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨411, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 6) :=
  shape0 (env (.m 1 (⟨408, [1]⟩ : Lin))) (env (.m 1 (⟨409, [1]⟩ : Lin))) (env (.m 1 (⟨410, [1]⟩ : Lin))) (env (.m 1 (⟨411, [1]⟩ : Lin))) (V (.R 6 6)) ((inp 408)) ((inp 409)) ((inp 410)) ((inp 411)) h0 h1 h2 h3 h4

theorem core6_329 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨404, [1]⟩ : Lin)) = (inp 404).zeroExtend 32)
    (h1 : env (.m 1 (⟨405, [1]⟩ : Lin)) = (inp 405).zeroExtend 32)
    (h2 : env (.m 1 (⟨406, [1]⟩ : Lin)) = (inp 406).zeroExtend 32)
    (h3 : env (.m 1 (⟨407, [1]⟩ : Lin)) = (inp 407).zeroExtend 32)
    (h4 : V (.R 6 5) = ((((0 : Word) ||| (inp 404).zeroExtend 32 <<< 0) ||| (inp 405).zeroExtend 32 <<< 8) ||| (inp 406).zeroExtend 32 <<< 16) ||| (inp 407).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨404, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨405, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨406, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨407, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 5) :=
  shape0 (env (.m 1 (⟨404, [1]⟩ : Lin))) (env (.m 1 (⟨405, [1]⟩ : Lin))) (env (.m 1 (⟨406, [1]⟩ : Lin))) (env (.m 1 (⟨407, [1]⟩ : Lin))) (V (.R 6 5)) ((inp 404)) ((inp 405)) ((inp 406)) ((inp 407)) h0 h1 h2 h3 h4

theorem core6_328 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.m 1 (⟨400, [1]⟩ : Lin)) = (inp 400).zeroExtend 32)
    (h1 : env (.m 1 (⟨401, [1]⟩ : Lin)) = (inp 401).zeroExtend 32)
    (h2 : env (.m 1 (⟨402, [1]⟩ : Lin)) = (inp 402).zeroExtend 32)
    (h3 : env (.m 1 (⟨403, [1]⟩ : Lin)) = (inp 403).zeroExtend 32)
    (h4 : V (.R 6 4) = ((((0 : Word) ||| (inp 400).zeroExtend 32 <<< 0) ||| (inp 401).zeroExtend 32 <<< 8) ||| (inp 402).zeroExtend 32 <<< 16) ||| (inp 403).zeroExtend 32 <<< 24) :
    E.eval env (.or (.or (.and (.shr (.var (.m 1 (⟨400, [1]⟩ : Lin))) 0) (.const 255)) (.shl (.and (.shr (.var (.m 1 (⟨401, [1]⟩ : Lin))) 0) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.m 1 (⟨402, [1]⟩ : Lin))) 0) (.const 255)) 16) (.shl (.and (.shr (.var (.m 1 (⟨403, [1]⟩ : Lin))) 0) (.const 255)) 24))) = V (.R 6 4) :=
  shape0 (env (.m 1 (⟨400, [1]⟩ : Lin))) (env (.m 1 (⟨401, [1]⟩ : Lin))) (env (.m 1 (⟨402, [1]⟩ : Lin))) (env (.m 1 (⟨403, [1]⟩ : Lin))) (V (.R 6 4)) ((inp 400)) ((inp 401)) ((inp 402)) ((inp 403)) h0 h1 h2 h3 h4

theorem step6 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L6) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K6)) L7 := by
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
  exact invC_of_trees inp env _ T6 L7 (slice_trees_mem prog 4 _ _ 8 K6 K7 T6 slice6 env)
      (And.intro ⟨rfl, core6_347 (qv inp) inp env (hm 476 (by decide)) (hm 477 (by decide)) (hm 478 (by decide)) (hm 479 (by decide)) (qR inp 7 7)⟩
      (And.intro ⟨rfl, core6_346 (qv inp) inp env (hm 472 (by decide)) (hm 473 (by decide)) (hm 474 (by decide)) (hm 475 (by decide)) (qR inp 7 6)⟩
      (And.intro ⟨rfl, core6_345 (qv inp) inp env (hm 468 (by decide)) (hm 469 (by decide)) (hm 470 (by decide)) (hm 471 (by decide)) (qR inp 7 5)⟩
      (And.intro ⟨rfl, core6_344 (qv inp) inp env (hm 464 (by decide)) (hm 465 (by decide)) (hm 466 (by decide)) (hm 467 (by decide)) (qR inp 7 4)⟩
      (And.intro ⟨rfl, h4⟩
      (And.intro ⟨rfl, h5⟩
      (And.intro ⟨rfl, h6⟩
      (And.intro ⟨rfl, h7⟩
      (And.intro ⟨rfl, core6_331 (qv inp) inp env (hm 412 (by decide)) (hm 413 (by decide)) (hm 414 (by decide)) (hm 415 (by decide)) (qR inp 6 7)⟩
      (And.intro ⟨rfl, core6_330 (qv inp) inp env (hm 408 (by decide)) (hm 409 (by decide)) (hm 410 (by decide)) (hm 411 (by decide)) (qR inp 6 6)⟩
      (And.intro ⟨rfl, core6_329 (qv inp) inp env (hm 404 (by decide)) (hm 405 (by decide)) (hm 406 (by decide)) (hm 407 (by decide)) (qR inp 6 5)⟩
      (And.intro ⟨rfl, core6_328 (qv inp) inp env (hm 400 (by decide)) (hm 401 (by decide)) (hm 402 (by decide)) (hm 403 (by decide)) (qR inp 6 4)⟩
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
      (And.intro ⟨rfl, h32⟩
      (And.intro ⟨rfl, h33⟩
      (And.intro ⟨rfl, h40⟩
      (And.intro ⟨rfl, h41⟩
      (And.intro ⟨rfl, h36⟩
      (And.intro ⟨rfl, h37⟩
      (And.intro ⟨rfl, h44⟩
      (And.intro ⟨rfl, h45⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h52⟩
      (And.intro ⟨rfl, h53⟩
      (And.intro ⟨rfl, h54⟩
      (And.intro ⟨rfl, h55⟩
      (And.intro ⟨rfl, h48⟩
      (And.intro ⟨rfl, h49⟩
      (And.intro ⟨rfl, h56⟩
      (And.intro ⟨rfl, h57⟩
      (And.intro ⟨rfl, h52⟩
      (And.intro ⟨rfl, h53⟩
      (And.intro ⟨rfl, h60⟩
      (And.intro ⟨rfl, h61⟩
      (And.intro ⟨rfl, h34⟩
      (And.intro ⟨rfl, h35⟩
      (And.intro ⟨rfl, h42⟩
      (And.intro ⟨rfl, h43⟩
      (And.intro ⟨rfl, h38⟩
      (And.intro ⟨rfl, h39⟩
      (And.intro ⟨rfl, h46⟩
      (And.intro ⟨rfl, h47⟩
      (And.intro ⟨rfl, h50⟩
      (And.intro ⟨rfl, h51⟩
      (And.intro ⟨rfl, h58⟩
      (And.intro ⟨rfl, h59⟩
      (And.intro ⟨rfl, h54⟩
      (And.intro ⟨rfl, h55⟩
      (And.intro ⟨rfl, h62⟩
      (And.intro ⟨rfl, h63⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvx2X8P
