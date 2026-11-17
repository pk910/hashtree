import Hashtree.Asm.Chain

open Hashtree.Asm Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

/-! Shape lemmas: the lane lemmas of the slices are instances (lanes of one round, and rounds of
one kind, share a shape). -/

theorem shape0 (x0 x1 x2 x3 : W32) (y0 : Word) (z0 z1 z2 z3 : Byte)
    (_ : x0 = z0.zeroExtend 32)
    (_ : x1 = z1.zeroExtend 32)
    (_ : x2 = z2.zeroExtend 32)
    (_ : x3 = z3.zeroExtend 32)
    (_ : y0 = ((((0 : Word) ||| z0.zeroExtend 32 <<< 0) ||| z1.zeroExtend 32 <<< 8) ||| z2.zeroExtend 32 <<< 16) ||| z3.zeroExtend 32 <<< 24) :
    ((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) = y0 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape1 (x0 : W32) (y0 y1 : Word)
    (_ : x0 = y0)
    (_ : y1 = bswap (y0)) :
    ((((x0 >>> (24 : Nat)) &&& (255 : W32)) ||| (((x0 >>> (16 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x0 >>> (8 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x0 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape2 (x0 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Word)
    (_ : x0 = y0)
    (_ : y1 = (y2 + Sigma1 (y3) + Ch (y3) (y4) (y5) + y6) + (Sigma0 (y7) + Maj (y7) (y8) (y9)))
    (_ : y2 = y10)
    (_ : y10 = 1541459225#32)
    (_ : y3 = y11)
    (_ : y11 = 1359893119#32)
    (_ : y4 = y12)
    (_ : y12 = 2600822924#32)
    (_ : y5 = y13)
    (_ : y13 = 528734635#32)
    (_ : y6 = 1116352408#32 + y14)
    (_ : y14 = bswap (y0))
    (_ : y7 = y15)
    (_ : y15 = 1779033703#32)
    (_ : y8 = y16)
    (_ : y16 = 3144134277#32)
    (_ : y9 = y17)
    (_ : y17 = 1013904242#32) :
    (((((2070320805 : W32) + (((((x0 >>> (24 : Nat)) &&& (255 : W32)) ||| (((x0 >>> (16 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x0 >>> (8 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x0 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) + (1116352408 : W32))) + (898049835 : W32)) + (980412007 : W32)) + (3458249854 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape3 (x0 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2 + (y3 + Sigma1 (y4) + Ch (y4) (y5) (y6) + y7))
    (_ : y2 = y8)
    (_ : y8 = 2773480762#32)
    (_ : y3 = y9)
    (_ : y9 = 1541459225#32)
    (_ : y4 = y10)
    (_ : y10 = 1359893119#32)
    (_ : y5 = y11)
    (_ : y11 = 2600822924#32)
    (_ : y6 = y12)
    (_ : y12 = 528734635#32)
    (_ : y7 = 1116352408#32 + y13)
    (_ : y13 = bswap (y0)) :
    ((2773480762 : W32) + (((2070320805 : W32) + (((((x0 >>> (24 : Nat)) &&& (255 : W32)) ||| (((x0 >>> (16 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x0 >>> (8 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x0 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) + (1116352408 : W32))) + (898049835 : W32))) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape4 (x0 x1 x2 x3 : W32) (y0 : Word)
    (_ : x0 = y0)
    (_ : x1 = y0)
    (_ : x2 = y0)
    (_ : x3 = y0) :
    ((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) = y0 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape5 (x0 x1 x2 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : y3 = (y4 + Sigma1 (y0) + Ch (y0) (y5) (y6) + y7) + (Sigma0 (y2) + Maj (y2) (y8) (y9)))
    (_ : y4 = y10)
    (_ : y10 = 528734635#32)
    (_ : y5 = y11)
    (_ : y11 = 1359893119#32)
    (_ : y6 = y12)
    (_ : y12 = 2600822924#32)
    (_ : y7 = 1899447441#32 + y1)
    (_ : y8 = y13)
    (_ : y13 = 1779033703#32)
    (_ : y9 = y14)
    (_ : y14 = 3144134277#32) :
    ((((((528734635 : W32) + (((3389733619 : W32) &&& x0) ^^^ (2600822924 : W32))) + (x1 + (1899447441 : W32))) + ((((((x0 >>> (5 : Nat)) ||| (x0 <<< (27 : Nat))) ^^^ x0) >>> (6 : Nat)) ||| ((((x0 >>> (5 : Nat)) ||| (x0 <<< (27 : Nat))) ^^^ x0) <<< (26 : Nat))) ^^^ ((x0 >>> (25 : Nat)) ||| (x0 <<< (7 : Nat))))) + ((x2 &&& (3144134277 : W32)) ||| ((x2 ^^^ (3144134277 : W32)) &&& (1779033703 : W32)))) + ((((((x2 >>> (11 : Nat)) ||| (x2 <<< (21 : Nat))) ^^^ x2) >>> (2 : Nat)) ||| ((((x2 >>> (11 : Nat)) ||| (x2 <<< (21 : Nat))) ^^^ x2) <<< (30 : Nat))) ^^^ ((x2 >>> (22 : Nat)) ||| (x2 <<< (10 : Nat))))) = y3 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape6 (x0 x1 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : y2 = y3 + (y4 + Sigma1 (y0) + Ch (y0) (y5) (y6) + y7))
    (_ : y3 = y8)
    (_ : y8 = 1013904242#32)
    (_ : y4 = y9)
    (_ : y9 = 528734635#32)
    (_ : y5 = y10)
    (_ : y10 = 1359893119#32)
    (_ : y6 = y11)
    (_ : y11 = 2600822924#32)
    (_ : y7 = 1899447441#32 + y1) :
    ((1013904242 : W32) + ((((528734635 : W32) + (((3389733619 : W32) &&& x0) ^^^ (2600822924 : W32))) + (x1 + (1899447441 : W32))) + ((((((x0 >>> (5 : Nat)) ||| (x0 <<< (27 : Nat))) ^^^ x0) >>> (6 : Nat)) ||| ((((x0 >>> (5 : Nat)) ||| (x0 <<< (27 : Nat))) ^^^ x0) <<< (26 : Nat))) ^^^ ((x0 >>> (25 : Nat)) ||| (x0 <<< (7 : Nat)))))) = y2 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape7 (x0 x1 x2 x3 x4 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : y5 = (y6 + Sigma1 (y1) + Ch (y1) (y0) (y7) + y8) + (Sigma0 (y3) + Maj (y3) (y4) (y9)))
    (_ : y6 = y10)
    (_ : y10 = 2600822924#32)
    (_ : y7 = y11)
    (_ : y11 = 1359893119#32)
    (_ : y8 = 3049323471#32 + y2)
    (_ : y9 = y12)
    (_ : y12 = 1779033703#32) :
    ((((((2600822924 : W32) + (((x0 ^^^ (1359893119 : W32)) &&& x1) ^^^ (1359893119 : W32))) + (x2 + (3049323471 : W32))) + ((((((x1 >>> (5 : Nat)) ||| (x1 <<< (27 : Nat))) ^^^ x1) >>> (6 : Nat)) ||| ((((x1 >>> (5 : Nat)) ||| (x1 <<< (27 : Nat))) ^^^ x1) <<< (26 : Nat))) ^^^ ((x1 >>> (25 : Nat)) ||| (x1 <<< (7 : Nat))))) + ((x3 &&& (1779033703 : W32)) ||| ((x3 ^^^ (1779033703 : W32)) &&& x4))) + ((((((x3 >>> (11 : Nat)) ||| (x3 <<< (21 : Nat))) ^^^ x3) >>> (2 : Nat)) ||| ((((x3 >>> (11 : Nat)) ||| (x3 <<< (21 : Nat))) ^^^ x3) <<< (30 : Nat))) ^^^ ((x3 >>> (22 : Nat)) ||| (x3 <<< (10 : Nat))))) = y5 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape8 (x0 x1 x2 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : y3 = y4 + (y5 + Sigma1 (y1) + Ch (y1) (y0) (y6) + y7))
    (_ : y4 = y8)
    (_ : y8 = 3144134277#32)
    (_ : y5 = y9)
    (_ : y9 = 2600822924#32)
    (_ : y6 = y10)
    (_ : y10 = 1359893119#32)
    (_ : y7 = 3049323471#32 + y2) :
    ((3144134277 : W32) + ((((2600822924 : W32) + (((x0 ^^^ (1359893119 : W32)) &&& x1) ^^^ (1359893119 : W32))) + (x2 + (3049323471 : W32))) + ((((((x1 >>> (5 : Nat)) ||| (x1 <<< (27 : Nat))) ^^^ x1) >>> (6 : Nat)) ||| ((((x1 >>> (5 : Nat)) ||| (x1 <<< (27 : Nat))) ^^^ x1) <<< (26 : Nat))) ^^^ ((x1 >>> (25 : Nat)) ||| (x1 <<< (7 : Nat)))))) = y3 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape9 (x0 x1 x2 x3 x4 x5 x6 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : y7 = (y8 + Sigma1 (y2) + Ch (y2) (y0) (y1) + y9) + (Sigma0 (y4) + Maj (y4) (y6) (y5)))
    (_ : y8 = y10)
    (_ : y10 = 1359893119#32)
    (_ : y9 = 3921009573#32 + y3) :
    ((((((1359893119 : W32) + (((x0 ^^^ x1) &&& x2) ^^^ x1)) + (x3 + (3921009573 : W32))) + ((((((x2 >>> (5 : Nat)) ||| (x2 <<< (27 : Nat))) ^^^ x2) >>> (6 : Nat)) ||| ((((x2 >>> (5 : Nat)) ||| (x2 <<< (27 : Nat))) ^^^ x2) <<< (26 : Nat))) ^^^ ((x2 >>> (25 : Nat)) ||| (x2 <<< (7 : Nat))))) + ((x4 &&& x5) ||| ((x4 ^^^ x5) &&& x6))) + ((((((x4 >>> (11 : Nat)) ||| (x4 <<< (21 : Nat))) ^^^ x4) >>> (2 : Nat)) ||| ((((x4 >>> (11 : Nat)) ||| (x4 <<< (21 : Nat))) ^^^ x4) <<< (30 : Nat))) ^^^ ((x4 >>> (22 : Nat)) ||| (x4 <<< (10 : Nat))))) = y7 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape10 (x0 x1 x2 x3 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : y4 = y5 + (y6 + Sigma1 (y2) + Ch (y2) (y0) (y1) + y7))
    (_ : y5 = y8)
    (_ : y8 = 1779033703#32)
    (_ : y6 = y9)
    (_ : y9 = 1359893119#32)
    (_ : y7 = 3921009573#32 + y3) :
    ((1779033703 : W32) + ((((1359893119 : W32) + (((x0 ^^^ x1) &&& x2) ^^^ x1)) + (x3 + (3921009573 : W32))) + ((((((x2 >>> (5 : Nat)) ||| (x2 <<< (27 : Nat))) ^^^ x2) >>> (6 : Nat)) ||| ((((x2 >>> (5 : Nat)) ||| (x2 <<< (27 : Nat))) ^^^ x2) <<< (26 : Nat))) ^^^ ((x2 >>> (25 : Nat)) ||| (x2 <<< (7 : Nat)))))) = y4 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape11 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 961987163#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (961987163 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape12 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 961987163#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (961987163 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape13 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1508970993#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1508970993 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape14 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1508970993#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1508970993 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape15 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2453635748#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2453635748 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape16 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2453635748#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2453635748 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape17 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2870763221#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2870763221 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape18 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2870763221#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2870763221 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape19 (x0 x1 x2 x3 : W32) (y0 y1 : Word) (z0 z1 z2 z3 : Byte)
    (_ : x0 = z0.zeroExtend 32)
    (_ : x1 = z1.zeroExtend 32)
    (_ : x2 = z2.zeroExtend 32)
    (_ : x3 = z3.zeroExtend 32)
    (_ : y0 = bswap (y1))
    (_ : y1 = ((((0 : Word) ||| z0.zeroExtend 32 <<< 0) ||| z1.zeroExtend 32 <<< 8) ||| z2.zeroExtend 32 <<< 16) ||| z3.zeroExtend 32 <<< 24) :
    ((((((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (24 : Nat)) &&& (255 : W32)) ||| (((((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (16 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (8 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) = y0 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape20 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 : Word) (z0 z1 z2 z3 : Byte)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x8 = y4)
    (_ : x9 = y5)
    (_ : x10 = y6)
    (_ : x4 = z0.zeroExtend 32)
    (_ : x5 = z1.zeroExtend 32)
    (_ : x6 = z2.zeroExtend 32)
    (_ : x7 = z3.zeroExtend 32)
    (_ : y7 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y8) + (Sigma0 (y4) + Maj (y4) (y6) (y5)))
    (_ : y8 = 3624381080#32 + y9)
    (_ : y9 = bswap (y10))
    (_ : y10 = ((((0 : Word) ||| z0.zeroExtend 32 <<< 0) ||| z1.zeroExtend 32 <<< 8) ||| z2.zeroExtend 32 <<< 16) ||| z3.zeroExtend 32 <<< 24) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (((((((((x4 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x5 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (24 : Nat)) &&& (255 : W32)) ||| (((((((x4 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x5 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (16 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((((((x4 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x5 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (8 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((((((x4 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x5 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) + (3624381080 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x8 &&& x9) ||| ((x8 ^^^ x9) &&& x10))) + ((((((x8 >>> (11 : Nat)) ||| (x8 <<< (21 : Nat))) ^^^ x8) >>> (2 : Nat)) ||| ((((x8 >>> (11 : Nat)) ||| (x8 <<< (21 : Nat))) ^^^ x8) <<< (30 : Nat))) ^^^ ((x8 >>> (22 : Nat)) ||| (x8 <<< (10 : Nat))))) = y7 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape21 (x0 x1 x2 x3 x4 x5 x6 x7 x8 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 : Word) (z0 z1 z2 z3 : Byte)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = z0.zeroExtend 32)
    (_ : x6 = z1.zeroExtend 32)
    (_ : x7 = z2.zeroExtend 32)
    (_ : x8 = z3.zeroExtend 32)
    (_ : y5 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y6))
    (_ : y6 = 3624381080#32 + y7)
    (_ : y7 = bswap (y8))
    (_ : y8 = ((((0 : Word) ||| z0.zeroExtend 32 <<< 0) ||| z1.zeroExtend 32 <<< 8) ||| z2.zeroExtend 32 <<< 16) ||| z3.zeroExtend 32 <<< 24) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (((((((((x5 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x8 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (24 : Nat)) &&& (255 : W32)) ||| (((((((x5 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x8 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (16 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((((((x5 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x8 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (8 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((((((x5 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x6 >>> (0 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x7 >>> (0 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x8 >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (0 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) + (3624381080 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y5 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape22 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 310598401#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (310598401 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape23 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 310598401#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (310598401 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape24 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 607225278#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (607225278 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape25 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 607225278#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (607225278 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape26 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1426881987#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1426881987 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape27 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1426881987#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1426881987 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape28 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1925078388#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1925078388 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape29 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1925078388#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1925078388 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape30 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2162078206#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2162078206 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape31 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2162078206#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2162078206 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape32 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2614888103#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2614888103 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape33 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2614888103#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2614888103 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape34 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3248222580#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3248222580 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape35 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3248222580#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3248222580 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape36 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W32) (y0 y1 y2 y3 y4 y5 y6 : Word)
    (_ : x0 = y0)
    (_ : x1 = y0)
    (_ : x2 = y0)
    (_ : x3 = y0)
    (_ : x4 = y1)
    (_ : x5 = y1)
    (_ : x6 = y1)
    (_ : x7 = y1)
    (_ : x8 = y2)
    (_ : x9 = y2)
    (_ : x10 = y2)
    (_ : x11 = y2)
    (_ : x12 = y3)
    (_ : x13 = y3)
    (_ : x14 = y3)
    (_ : x15 = y3)
    (_ : y4 = sigma1 (y2) + y5)
    (_ : y5 = y6 + y3)
    (_ : y6 = y1 + sigma0 (y0)) :
    ((((((((((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (11 : Nat)) ||| (((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) <<< (21 : Nat))) ^^^ ((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat))))) >>> (7 : Nat)) ||| ((((((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (11 : Nat)) ||| (((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) <<< (21 : Nat))) ^^^ ((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat))))) <<< (25 : Nat))) ^^^ (((((x0 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x1 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x2 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x3 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (3 : Nat))) + ((((x4 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x5 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x6 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x7 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat))))) + (((((((((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (2 : Nat)) ||| (((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) <<< (30 : Nat))) ^^^ ((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat))))) >>> (17 : Nat)) ||| ((((((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (2 : Nat)) ||| (((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) <<< (30 : Nat))) ^^^ ((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat))))) <<< (15 : Nat))) ^^^ (((((x8 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x9 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x10 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x11 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))) >>> (10 : Nat))) + ((((x12 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x13 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x14 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x15 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat)))))) = y4 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape37 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3835390401#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3835390401 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape38 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3835390401#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3835390401 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape39 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 4022224774#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (4022224774 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape40 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 4022224774#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (4022224774 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape41 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 264347078#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (264347078 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape42 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 264347078#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (264347078 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape43 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 604807628#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (604807628 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape44 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 604807628#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (604807628 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape45 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 770255983#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (770255983 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape46 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 770255983#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (770255983 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape47 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1249150122#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1249150122 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape48 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1249150122#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1249150122 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape49 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1555081692#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1555081692 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape50 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1555081692#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1555081692 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape51 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1996064986#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1996064986 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape52 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1996064986#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1996064986 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape53 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2554220882#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2554220882 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape54 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2554220882#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2554220882 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape55 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2821834349#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2821834349 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape56 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2821834349#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2821834349 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape57 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2952996808#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2952996808 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape58 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2952996808#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2952996808 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape59 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3210313671#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3210313671 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape60 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3210313671#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3210313671 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape61 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3336571891#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3336571891 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape62 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3336571891#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3336571891 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape63 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3584528711#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3584528711 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape64 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3584528711#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3584528711 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape65 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 113926993#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (113926993 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape66 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 113926993#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (113926993 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape67 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 338241895#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (338241895 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape68 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 338241895#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (338241895 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape69 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 666307205#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (666307205 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape70 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 666307205#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (666307205 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape71 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 773529912#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (773529912 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape72 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 773529912#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (773529912 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape73 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1294757372#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1294757372 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape74 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1294757372#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1294757372 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape75 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1396182291#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1396182291 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape76 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1396182291#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1396182291 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape77 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1695183700#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1695183700 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape78 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1695183700#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1695183700 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape79 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1986661051#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1986661051 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape80 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1986661051#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1986661051 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape81 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2177026350#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2177026350 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape82 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2177026350#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2177026350 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape83 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2456956037#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2456956037 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape84 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2456956037#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2456956037 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape85 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2730485921#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2730485921 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape86 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2730485921#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2730485921 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape87 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2820302411#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2820302411 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape88 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2820302411#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2820302411 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape89 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3259730800#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3259730800 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape90 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3259730800#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3259730800 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape91 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3345764771#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3345764771 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape92 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3345764771#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3345764771 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape93 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3516065817#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3516065817 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape94 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3516065817#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3516065817 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape95 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3600352804#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3600352804 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape96 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3600352804#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3600352804 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape97 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 4094571909#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (4094571909 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape98 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 4094571909#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (4094571909 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape99 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 275423344#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (275423344 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape100 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 275423344#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (275423344 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape101 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 430227734#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (430227734 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape102 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 430227734#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (430227734 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape103 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 506948616#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (506948616 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape104 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 506948616#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (506948616 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape105 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 659060556#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (659060556 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape106 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 659060556#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (659060556 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape107 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 883997877#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (883997877 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape108 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 883997877#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (883997877 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape109 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 958139571#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (958139571 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape110 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 958139571#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (958139571 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape111 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1322822218#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1322822218 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape112 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1322822218#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1322822218 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape113 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1537002063#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1537002063 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape114 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1537002063#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1537002063 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape115 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1747873779#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1747873779 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape116 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1747873779#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1747873779 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape117 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 1955562222#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (1955562222 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape118 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 1955562222#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (1955562222 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape119 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2024104815#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2024104815 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape120 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2024104815#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2024104815 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape121 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2227730452#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2227730452 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape122 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2227730452#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2227730452 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape123 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2361852424#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2361852424 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape124 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2361852424#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2361852424 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape125 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2428436474#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2428436474 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape126 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2428436474#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2428436474 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape127 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 2756734187#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (2756734187 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape128 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 2756734187#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (2756734187 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape129 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3204031479#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3204031479 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape130 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3204031479#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3204031479 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape131 (x0 x1 x2 x3 x4 x5 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : y6 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y7))
    (_ : y7 = 3329325298#32 + y5) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + (x5 + (3329325298 : W32))) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y6 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape132 (x0 x1 x2 x3 x4 x5 x6 x7 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : x7 = y7)
    (_ : y8 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y9) + (Sigma0 (y5) + Maj (y5) (y7) (y6)))
    (_ : y9 = 3329325298#32 + y4) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + (x4 + (3329325298 : W32))) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x5 &&& x6) ||| ((x5 ^^^ x6) &&& x7))) + ((((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) >>> (2 : Nat)) ||| ((((x5 >>> (11 : Nat)) ||| (x5 <<< (21 : Nat))) ^^^ x5) <<< (30 : Nat))) ^^^ ((x5 >>> (22 : Nat)) ||| (x5 <<< (10 : Nat))))) = y8 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape133 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 1779033703#32) :
    (x0 + (1779033703 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape134 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 3144134277#32) :
    (x0 + (3144134277 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape135 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 1013904242#32) :
    (x0 + (1013904242 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape136 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 2773480762#32) :
    (x0 + (2773480762 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape137 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 1359893119#32) :
    (x0 + (1359893119 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape138 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 2600822924#32) :
    (x0 + (2600822924 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape139 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 528734635#32) :
    (x0 + (528734635 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape140 (x0 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : y1 = y2)
    (_ : y2 = y3 + y0)
    (_ : y3 = 1541459225#32) :
    (x0 + (1541459225 : W32)) = y1 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape141 (x0 x1 x2 x3 x4 x5 x6 : W32) (y0 y1 y2 y3 y4 y5 y6 y7 y8 : Word) (k0 : W32)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : x5 = y5)
    (_ : x6 = y6)
    (_ : y7 = (y0 + Sigma1 (y3) + Ch (y3) (y1) (y2) + y8) + (Sigma0 (y4) + Maj (y4) (y6) (y5)))
    (_ : y8 = k0) :
    (((((x0 + (((x1 ^^^ x2) &&& x3) ^^^ x2)) + k0) + ((((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) >>> (6 : Nat)) ||| ((((x3 >>> (5 : Nat)) ||| (x3 <<< (27 : Nat))) ^^^ x3) <<< (26 : Nat))) ^^^ ((x3 >>> (25 : Nat)) ||| (x3 <<< (7 : Nat))))) + ((x4 &&& x5) ||| ((x4 ^^^ x5) &&& x6))) + ((((((x4 >>> (11 : Nat)) ||| (x4 <<< (21 : Nat))) ^^^ x4) >>> (2 : Nat)) ||| ((((x4 >>> (11 : Nat)) ||| (x4 <<< (21 : Nat))) ^^^ x4) <<< (30 : Nat))) ^^^ ((x4 >>> (22 : Nat)) ||| (x4 <<< (10 : Nat))))) = y7 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape142 (x0 x1 x2 x3 x4 : W32) (y0 y1 y2 y3 y4 y5 y6 : Word) (k0 : W32)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y2)
    (_ : x3 = y3)
    (_ : x4 = y4)
    (_ : y5 = y0 + (y1 + Sigma1 (y4) + Ch (y4) (y2) (y3) + y6))
    (_ : y6 = k0) :
    (x0 + (((x1 + (((x2 ^^^ x3) &&& x4) ^^^ x3)) + k0) + ((((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) >>> (6 : Nat)) ||| ((((x4 >>> (5 : Nat)) ||| (x4 <<< (27 : Nat))) ^^^ x4) <<< (26 : Nat))) ^^^ ((x4 >>> (25 : Nat)) ||| (x4 <<< (7 : Nat)))))) = y5 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

theorem shape143 (x0 x1 x2 x3 x4 : W32) (y0 y1 y2 y3 : Word)
    (_ : x0 = y0)
    (_ : x1 = y1)
    (_ : x2 = y1)
    (_ : x3 = y1)
    (_ : x4 = y1)
    (_ : y2 = y3 + y0)
    (_ : y3 = y1) :
    (x0 + ((((x1 >>> (0 : Nat)) &&& (255 : W32)) ||| (((x2 >>> (8 : Nat)) &&& (255 : W32)) <<< (8 : Nat))) ||| ((((x3 >>> (16 : Nat)) &&& (255 : W32)) <<< (16 : Nat)) ||| (((x4 >>> (24 : Nat)) &&& (255 : W32)) <<< (24 : Nat))))) = y2 := by
  simp_all only [Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals first | bv_decide | bv_decide (config := { acNf := true, timeout := 300 })

end Hashtree.Gen.WinAvx2X8P
