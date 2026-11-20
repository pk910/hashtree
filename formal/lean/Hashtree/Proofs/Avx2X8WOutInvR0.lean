import Hashtree.Proofs.Avx2X8WOutLab
import Hashtree.Proofs.Avx2X8WOutCutT0
import Hashtree.Proofs.Avx2X8WOutCutX0
import Hashtree.Proofs.Avx2X8WOutCutTS0
import Hashtree.Proofs.Avx2X8WOutCutXS0
import Hashtree.Proofs.Avx2X8WBodyR0
import Hashtree.Proofs.Avx2X8WBodyR0S

/-! R2c x8 — the pilot's invariant chain lifted to the W cuts at residue 0 (generated):
the first pass (`Hashtree.Proofs.Avx2X8WBodyR0.G210`), a later pass (`Hashtree.Proofs.Avx2X8WBodyR0S.GS210`), and the four tails. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.Avx2X8 Hashtree.Gen.Avx2X8P
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip
open Hashtree.Proofs.Avx512X16WOut (invC_lift invC_lift')

namespace Hashtree.Proofs.Avx2X8WOut

theorem stepW0_2 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L2) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 8 (shiftK8 0 K2))) L3 :=
  invC_lift inp env prog 4 m0q m8 _ _ 8 K2 K3 (shiftK8 0 K2) (shiftK8 0 K3) T2 L3
    slice2 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_2 lab8_2 (step2 inp env hI hm)

theorem stepW0_3 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L3) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 8 (shiftK8 0 K3))) L4 :=
  invC_lift inp env prog 4 m0q m8 _ _ 8 K3 K4 (shiftK8 0 K3) (shiftK8 0 K4) T3 L4
    slice3 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_3 lab8_3 (step3 inp env hI hm)

theorem stepW0_4 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L4) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 8 (shiftK8 0 K4))) L5 :=
  invC_lift inp env prog 4 m0q m8 _ _ 8 K4 K5 (shiftK8 0 K4) (shiftK8 0 K5) T4 L5
    slice4 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_4 lab8_4 (step4 inp env hI hm)

theorem stepW0_5 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L5) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 8 (shiftK8 0 K5))) L6 :=
  invC_lift inp env prog 4 m0q m8 _ _ 8 K5 K6 (shiftK8 0 K5) (shiftK8 0 K6) T5 L6
    slice5 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_5 lab8_5 (step5 inp env hI hm)

theorem stepW0_6 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L6) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 61 (shiftK8 0 K6))) L7 :=
  invC_lift inp env prog 4 m0q m8 _ _ 61 K6 K7 (shiftK8 0 K6) (shiftK8 0 K7) T6 L7
    slice6 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_6 lab8_6 (step6 inp env hI hm)

theorem stepW0_7 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L7) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K7))) L8 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K7 K8 (shiftK8 0 K7) (shiftK8 0 K8) T7 L8
    slice7 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_7 lab8_7 (step7 inp env hI hm)

theorem stepW0_8 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L8) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K8))) L9 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K8 K9 (shiftK8 0 K8) (shiftK8 0 K9) T8 L9
    slice8 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_8 lab8_8 (step8 inp env hI hm)

theorem stepW0_9 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L9) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K9))) L10 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K9 K10 (shiftK8 0 K9) (shiftK8 0 K10) T9 L10
    slice9 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_9 lab8_9 (step9 inp env hI hm)

theorem stepW0_10 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L10) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K10))) L11 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K10 K11 (shiftK8 0 K10) (shiftK8 0 K11) T10 L11
    slice10 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_10 lab8_10 (step10 inp env hI hm)

theorem stepW0_11 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L11) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K11))) L12 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K11 K12 (shiftK8 0 K11) (shiftK8 0 K12) T11 L12
    slice11 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_11 lab8_11 (step11 inp env hI hm)

theorem stepW0_12 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L12) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K12))) L13 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K12 K13 (shiftK8 0 K12) (shiftK8 0 K13) T12 L13
    slice12 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_12 lab8_12 (step12 inp env hI hm)

theorem stepW0_13 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L13) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K13))) L14 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K13 K14 (shiftK8 0 K13) (shiftK8 0 K14) T13 L14
    slice13 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_13 lab8_13 (step13 inp env hI hm)

theorem stepW0_14 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L14) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 86 (shiftK8 0 K14))) L15 :=
  invC_lift inp env prog 4 m0q m8 _ _ 86 K14 K15 (shiftK8 0 K14) (shiftK8 0 K15) T14 L15
    slice14 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_14 lab8_14 (step14 inp env hI hm)

theorem stepW0_15 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L15) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K15))) L16 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K15 K16 (shiftK8 0 K15) (shiftK8 0 K16) T15 L16
    slice15 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_15 lab8_15 (step15 inp env hI hm)

theorem stepW0_16 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L16) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K16))) L17 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K16 K17 (shiftK8 0 K16) (shiftK8 0 K17) T16 L17
    slice16 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_16 lab8_16 (step16 inp env hI hm)

theorem stepW0_17 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L17) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K17))) L18 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K17 K18 (shiftK8 0 K17) (shiftK8 0 K18) T17 L18
    slice17 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_17 lab8_17 (step17 inp env hI hm)

theorem stepW0_18 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L18) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 38 (shiftK8 0 K18))) L19 :=
  invC_lift inp env prog 4 m0q m8 _ _ 38 K18 K19 (shiftK8 0 K18) (shiftK8 0 K19) T18 L19
    slice18 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_18 lab8_18 (step18 inp env hI hm)

theorem stepW0_19 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L19) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K19))) L20 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K19 K20 (shiftK8 0 K19) (shiftK8 0 K20) T19 L20
    slice19 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_19 lab8_19 (step19 inp env hI hm)

theorem stepW0_20 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L20) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K20))) L21 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K20 K21 (shiftK8 0 K20) (shiftK8 0 K21) T20 L21
    slice20 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_20 lab8_20 (step20 inp env hI hm)

theorem stepW0_21 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L21) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K21))) L22 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K21 K22 (shiftK8 0 K21) (shiftK8 0 K22) T21 L22
    slice21 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_21 lab8_21 (step21 inp env hI hm)

theorem stepW0_22 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L22) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K22))) L23 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K22 K23 (shiftK8 0 K22) (shiftK8 0 K23) T22 L23
    slice22 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_22 lab8_22 (step22 inp env hI hm)

theorem stepW0_23 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L23) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K23))) L24 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K23 K24 (shiftK8 0 K23) (shiftK8 0 K24) T23 L24
    slice23 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_23 lab8_23 (step23 inp env hI hm)

theorem stepW0_24 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L24) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K24))) L25 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K24 K25 (shiftK8 0 K24) (shiftK8 0 K25) T24 L25
    slice24 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_24 lab8_24 (step24 inp env hI hm)

theorem stepW0_25 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L25) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K25))) L26 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K25 K26 (shiftK8 0 K25) (shiftK8 0 K26) T25 L26
    slice25 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_25 lab8_25 (step25 inp env hI hm)

theorem stepW0_26 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L26) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K26))) L27 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K26 K27 (shiftK8 0 K26) (shiftK8 0 K27) T26 L27
    slice26 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_26 lab8_26 (step26 inp env hI hm)

theorem stepW0_27 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L27) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K27))) L28 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K27 K28 (shiftK8 0 K27) (shiftK8 0 K28) T27 L28
    slice27 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_27 lab8_27 (step27 inp env hI hm)

theorem stepW0_28 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L28) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K28))) L29 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K28 K29 (shiftK8 0 K28) (shiftK8 0 K29) T28 L29
    slice28 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_28 lab8_28 (step28 inp env hI hm)

theorem stepW0_29 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L29) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K29))) L30 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K29 K30 (shiftK8 0 K29) (shiftK8 0 K30) T29 L30
    slice29 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_29 lab8_29 (step29 inp env hI hm)

theorem stepW0_30 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L30) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K30))) L31 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K30 K31 (shiftK8 0 K30) (shiftK8 0 K31) T30 L31
    slice30 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_30 lab8_30 (step30 inp env hI hm)

theorem stepW0_31 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L31) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K31))) L32 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K31 K32 (shiftK8 0 K31) (shiftK8 0 K32) T31 L32
    slice31 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_31 lab8_31 (step31 inp env hI hm)

theorem stepW0_32 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L32) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K32))) L33 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K32 K33 (shiftK8 0 K32) (shiftK8 0 K33) T32 L33
    slice32 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_32 lab8_32 (step32 inp env hI hm)

theorem stepW0_33 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L33) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K33))) L34 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K33 K34 (shiftK8 0 K33) (shiftK8 0 K34) T33 L34
    slice33 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_33 lab8_33 (step33 inp env hI hm)

theorem stepW0_34 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L34) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K34))) L35 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K34 K35 (shiftK8 0 K34) (shiftK8 0 K35) T34 L35
    slice34 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_34 lab8_34 (step34 inp env hI hm)

theorem stepW0_35 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L35) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K35))) L36 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K35 K36 (shiftK8 0 K35) (shiftK8 0 K36) T35 L36
    slice35 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_35 lab8_35 (step35 inp env hI hm)

theorem stepW0_36 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L36) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K36))) L37 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K36 K37 (shiftK8 0 K36) (shiftK8 0 K37) T36 L37
    slice36 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_36 lab8_36 (step36 inp env hI hm)

theorem stepW0_37 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L37) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K37))) L38 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K37 K38 (shiftK8 0 K37) (shiftK8 0 K38) T37 L38
    slice37 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_37 lab8_37 (step37 inp env hI hm)

theorem stepW0_38 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L38) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K38))) L39 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K38 K39 (shiftK8 0 K38) (shiftK8 0 K39) T38 L39
    slice38 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_38 lab8_38 (step38 inp env hI hm)

theorem stepW0_39 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L39) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K39))) L40 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K39 K40 (shiftK8 0 K39) (shiftK8 0 K40) T39 L40
    slice39 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_39 lab8_39 (step39 inp env hI hm)

theorem stepW0_40 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L40) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K40))) L41 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K40 K41 (shiftK8 0 K40) (shiftK8 0 K41) T40 L41
    slice40 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_40 lab8_40 (step40 inp env hI hm)

theorem stepW0_41 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L41) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K41))) L42 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K41 K42 (shiftK8 0 K41) (shiftK8 0 K42) T41 L42
    slice41 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_41 lab8_41 (step41 inp env hI hm)

theorem stepW0_42 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L42) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K42))) L43 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K42 K43 (shiftK8 0 K42) (shiftK8 0 K43) T42 L43
    slice42 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_42 lab8_42 (step42 inp env hI hm)

theorem stepW0_43 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L43) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K43))) L44 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K43 K44 (shiftK8 0 K43) (shiftK8 0 K44) T43 L44
    slice43 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_43 lab8_43 (step43 inp env hI hm)

theorem stepW0_44 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L44) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K44))) L45 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K44 K45 (shiftK8 0 K44) (shiftK8 0 K45) T44 L45
    slice44 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_44 lab8_44 (step44 inp env hI hm)

theorem stepW0_45 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L45) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K45))) L46 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K45 K46 (shiftK8 0 K45) (shiftK8 0 K46) T45 L46
    slice45 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_45 lab8_45 (step45 inp env hI hm)

theorem stepW0_46 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L46) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K46))) L47 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K46 K47 (shiftK8 0 K46) (shiftK8 0 K47) T46 L47
    slice46 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_46 lab8_46 (step46 inp env hI hm)

theorem stepW0_47 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L47) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K47))) L48 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K47 K48 (shiftK8 0 K47) (shiftK8 0 K48) T47 L48
    slice47 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_47 lab8_47 (step47 inp env hI hm)

theorem stepW0_48 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L48) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K48))) L49 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K48 K49 (shiftK8 0 K48) (shiftK8 0 K49) T48 L49
    slice48 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_48 lab8_48 (step48 inp env hI hm)

theorem stepW0_49 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L49) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K49))) L50 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K49 K50 (shiftK8 0 K49) (shiftK8 0 K50) T49 L50
    slice49 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_49 lab8_49 (step49 inp env hI hm)

theorem stepW0_50 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L50) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K50))) L51 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K50 K51 (shiftK8 0 K50) (shiftK8 0 K51) T50 L51
    slice50 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_50 lab8_50 (step50 inp env hI hm)

theorem stepW0_51 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L51) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K51))) L52 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K51 K52 (shiftK8 0 K51) (shiftK8 0 K52) T51 L52
    slice51 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_51 lab8_51 (step51 inp env hI hm)

theorem stepW0_52 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L52) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K52))) L53 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K52 K53 (shiftK8 0 K52) (shiftK8 0 K53) T52 L53
    slice52 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_52 lab8_52 (step52 inp env hI hm)

theorem stepW0_53 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L53) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K53))) L54 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K53 K54 (shiftK8 0 K53) (shiftK8 0 K54) T53 L54
    slice53 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_53 lab8_53 (step53 inp env hI hm)

theorem stepW0_54 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L54) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K54))) L55 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K54 K55 (shiftK8 0 K54) (shiftK8 0 K55) T54 L55
    slice54 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_54 lab8_54 (step54 inp env hI hm)

theorem stepW0_55 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L55) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K55))) L56 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K55 K56 (shiftK8 0 K55) (shiftK8 0 K56) T55 L56
    slice55 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_55 lab8_55 (step55 inp env hI hm)

theorem stepW0_56 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L56) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K56))) L57 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K56 K57 (shiftK8 0 K56) (shiftK8 0 K57) T56 L57
    slice56 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_56 lab8_56 (step56 inp env hI hm)

theorem stepW0_57 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L57) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K57))) L58 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K57 K58 (shiftK8 0 K57) (shiftK8 0 K58) T57 L58
    slice57 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_57 lab8_57 (step57 inp env hI hm)

theorem stepW0_58 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L58) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K58))) L59 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K58 K59 (shiftK8 0 K58) (shiftK8 0 K59) T58 L59
    slice58 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_58 lab8_58 (step58 inp env hI hm)

theorem stepW0_59 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L59) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K59))) L60 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K59 K60 (shiftK8 0 K59) (shiftK8 0 K60) T59 L60
    slice59 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_59 lab8_59 (step59 inp env hI hm)

theorem stepW0_60 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L60) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K60))) L61 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K60 K61 (shiftK8 0 K60) (shiftK8 0 K61) T60 L61
    slice60 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_60 lab8_60 (step60 inp env hI hm)

theorem stepW0_61 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L61) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K61))) L62 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K61 K62 (shiftK8 0 K61) (shiftK8 0 K62) T61 L62
    slice61 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_61 lab8_61 (step61 inp env hI hm)

theorem stepW0_62 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L62) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K62))) L63 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K62 K63 (shiftK8 0 K62) (shiftK8 0 K63) T62 L63
    slice62 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_62 lab8_62 (step62 inp env hI hm)

theorem stepW0_63 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L63) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K63))) L64 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K63 K64 (shiftK8 0 K63) (shiftK8 0 K64) T63 L64
    slice63 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_63 lab8_63 (step63 inp env hI hm)

theorem stepW0_64 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L64) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K64))) L65 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K64 K65 (shiftK8 0 K64) (shiftK8 0 K65) T64 L65
    slice64 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_64 lab8_64 (step64 inp env hI hm)

theorem stepW0_65 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L65) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K65))) L66 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K65 K66 (shiftK8 0 K65) (shiftK8 0 K66) T65 L66
    slice65 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_65 lab8_65 (step65 inp env hI hm)

theorem stepW0_66 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L66) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K66))) L67 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K66 K67 (shiftK8 0 K66) (shiftK8 0 K67) T66 L67
    slice66 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_66 lab8_66 (step66 inp env hI hm)

theorem stepW0_67 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L67) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K67))) L68 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K67 K68 (shiftK8 0 K67) (shiftK8 0 K68) T67 L68
    slice67 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_67 lab8_67 (step67 inp env hI hm)

theorem stepW0_68 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L68) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K68))) L69 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K68 K69 (shiftK8 0 K68) (shiftK8 0 K69) T68 L69
    slice68 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_68 lab8_68 (step68 inp env hI hm)

theorem stepW0_69 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L69) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K69))) L70 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K69 K70 (shiftK8 0 K69) (shiftK8 0 K70) T69 L70
    slice69 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_69 lab8_69 (step69 inp env hI hm)

theorem stepW0_70 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L70) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K70))) L71 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K70 K71 (shiftK8 0 K70) (shiftK8 0 K71) T70 L71
    slice70 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_70 lab8_70 (step70 inp env hI hm)

theorem stepW0_71 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L71) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K71))) L72 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K71 K72 (shiftK8 0 K71) (shiftK8 0 K72) T71 L72
    slice71 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_71 lab8_71 (step71 inp env hI hm)

theorem stepW0_72 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L72) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K72))) L73 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K72 K73 (shiftK8 0 K72) (shiftK8 0 K73) T72 L73
    slice72 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_72 lab8_72 (step72 inp env hI hm)

theorem stepW0_73 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L73) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K73))) L74 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K73 K74 (shiftK8 0 K73) (shiftK8 0 K74) T73 L74
    slice73 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_73 lab8_73 (step73 inp env hI hm)

theorem stepW0_74 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L74) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K74))) L75 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K74 K75 (shiftK8 0 K74) (shiftK8 0 K75) T74 L75
    slice74 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_74 lab8_74 (step74 inp env hI hm)

theorem stepW0_75 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L75) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K75))) L76 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K75 K76 (shiftK8 0 K75) (shiftK8 0 K76) T75 L76
    slice75 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_75 lab8_75 (step75 inp env hI hm)

theorem stepW0_76 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L76) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K76))) L77 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K76 K77 (shiftK8 0 K76) (shiftK8 0 K77) T76 L77
    slice76 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_76 lab8_76 (step76 inp env hI hm)

theorem stepW0_77 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L77) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K77))) L78 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K77 K78 (shiftK8 0 K77) (shiftK8 0 K78) T77 L78
    slice77 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_77 lab8_77 (step77 inp env hI hm)

theorem stepW0_78 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L78) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K78))) L79 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K78 K79 (shiftK8 0 K78) (shiftK8 0 K79) T78 L79
    slice78 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_78 lab8_78 (step78 inp env hI hm)

theorem stepW0_79 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L79) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K79))) L80 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K79 K80 (shiftK8 0 K79) (shiftK8 0 K80) T79 L80
    slice79 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_79 lab8_79 (step79 inp env hI hm)

theorem stepW0_80 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L80) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K80))) L81 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K80 K81 (shiftK8 0 K80) (shiftK8 0 K81) T80 L81
    slice80 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_80 lab8_80 (step80 inp env hI hm)

theorem stepW0_81 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L81) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K81))) L82 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K81 K82 (shiftK8 0 K81) (shiftK8 0 K82) T81 L82
    slice81 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_81 lab8_81 (step81 inp env hI hm)

theorem stepW0_82 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L82) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K82))) L83 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K82 K83 (shiftK8 0 K82) (shiftK8 0 K83) T82 L83
    slice82 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_82 lab8_82 (step82 inp env hI hm)

theorem stepW0_83 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L83) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K83))) L84 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K83 K84 (shiftK8 0 K83) (shiftK8 0 K84) T83 L84
    slice83 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_83 lab8_83 (step83 inp env hI hm)

theorem stepW0_84 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L84) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K84))) L85 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K84 K85 (shiftK8 0 K84) (shiftK8 0 K85) T84 L85
    slice84 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_84 lab8_84 (step84 inp env hI hm)

theorem stepW0_85 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L85) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K85))) L86 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K85 K86 (shiftK8 0 K85) (shiftK8 0 K86) T85 L86
    slice85 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_85 lab8_85 (step85 inp env hI hm)

theorem stepW0_86 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L86) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K86))) L87 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K86 K87 (shiftK8 0 K86) (shiftK8 0 K87) T86 L87
    slice86 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_86 lab8_86 (step86 inp env hI hm)

theorem stepW0_87 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L87) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K87))) L88 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K87 K88 (shiftK8 0 K87) (shiftK8 0 K88) T87 L88
    slice87 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_87 lab8_87 (step87 inp env hI hm)

theorem stepW0_88 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L88) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K88))) L89 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K88 K89 (shiftK8 0 K88) (shiftK8 0 K89) T88 L89
    slice88 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_88 lab8_88 (step88 inp env hI hm)

theorem stepW0_89 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L89) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K89))) L90 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K89 K90 (shiftK8 0 K89) (shiftK8 0 K90) T89 L90
    slice89 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_89 lab8_89 (step89 inp env hI hm)

theorem stepW0_90 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L90) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K90))) L91 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K90 K91 (shiftK8 0 K90) (shiftK8 0 K91) T90 L91
    slice90 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_90 lab8_90 (step90 inp env hI hm)

theorem stepW0_91 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L91) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K91))) L92 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K91 K92 (shiftK8 0 K91) (shiftK8 0 K92) T91 L92
    slice91 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_91 lab8_91 (step91 inp env hI hm)

theorem stepW0_92 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L92) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K92))) L93 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K92 K93 (shiftK8 0 K92) (shiftK8 0 K93) T92 L93
    slice92 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_92 lab8_92 (step92 inp env hI hm)

theorem stepW0_93 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L93) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K93))) L94 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K93 K94 (shiftK8 0 K93) (shiftK8 0 K94) T93 L94
    slice93 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_93 lab8_93 (step93 inp env hI hm)

theorem stepW0_94 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L94) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K94))) L95 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K94 K95 (shiftK8 0 K94) (shiftK8 0 K95) T94 L95
    slice94 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_94 lab8_94 (step94 inp env hI hm)

theorem stepW0_95 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L95) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K95))) L96 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K95 K96 (shiftK8 0 K95) (shiftK8 0 K96) T95 L96
    slice95 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_95 lab8_95 (step95 inp env hI hm)

theorem stepW0_96 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L96) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K96))) L97 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K96 K97 (shiftK8 0 K96) (shiftK8 0 K97) T96 L97
    slice96 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_96 lab8_96 (step96 inp env hI hm)

theorem stepW0_97 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L97) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K97))) L98 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K97 K98 (shiftK8 0 K97) (shiftK8 0 K98) T97 L98
    slice97 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_97 lab8_97 (step97 inp env hI hm)

theorem stepW0_98 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L98) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K98))) L99 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K98 K99 (shiftK8 0 K98) (shiftK8 0 K99) T98 L99
    slice98 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_98 lab8_98 (step98 inp env hI hm)

theorem stepW0_99 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L99) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K99))) L100 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K99 K100 (shiftK8 0 K99) (shiftK8 0 K100) T99 L100
    slice99 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_99 lab8_99 (step99 inp env hI hm)

theorem stepW0_100 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L100) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K100))) L101 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K100 K101 (shiftK8 0 K100) (shiftK8 0 K101) T100 L101
    slice100 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_100 lab8_100 (step100 inp env hI hm)

theorem stepW0_101 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L101) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K101))) L102 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K101 K102 (shiftK8 0 K101) (shiftK8 0 K102) T101 L102
    slice101 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_101 lab8_101 (step101 inp env hI hm)

theorem stepW0_102 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L102) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K102))) L103 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K102 K103 (shiftK8 0 K102) (shiftK8 0 K103) T102 L103
    slice102 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_102 lab8_102 (step102 inp env hI hm)

theorem stepW0_103 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L103) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K103))) L104 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K103 K104 (shiftK8 0 K103) (shiftK8 0 K104) T103 L104
    slice103 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_103 lab8_103 (step103 inp env hI hm)

theorem stepW0_104 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L104) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K104))) L105 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K104 K105 (shiftK8 0 K104) (shiftK8 0 K105) T104 L105
    slice104 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_104 lab8_104 (step104 inp env hI hm)

theorem stepW0_105 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L105) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K105))) L106 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K105 K106 (shiftK8 0 K105) (shiftK8 0 K106) T105 L106
    slice105 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_105 lab8_105 (step105 inp env hI hm)

theorem stepW0_106 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L106) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K106))) L107 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K106 K107 (shiftK8 0 K106) (shiftK8 0 K107) T106 L107
    slice106 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_106 lab8_106 (step106 inp env hI hm)

theorem stepW0_107 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L107) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K107))) L108 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K107 K108 (shiftK8 0 K107) (shiftK8 0 K108) T107 L108
    slice107 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_107 lab8_107 (step107 inp env hI hm)

theorem stepW0_108 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L108) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K108))) L109 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K108 K109 (shiftK8 0 K108) (shiftK8 0 K109) T108 L109
    slice108 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_108 lab8_108 (step108 inp env hI hm)

theorem stepW0_109 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L109) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K109))) L110 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K109 K110 (shiftK8 0 K109) (shiftK8 0 K110) T109 L110
    slice109 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_109 lab8_109 (step109 inp env hI hm)

theorem stepW0_110 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L110) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K110))) L111 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K110 K111 (shiftK8 0 K110) (shiftK8 0 K111) T110 L111
    slice110 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_110 lab8_110 (step110 inp env hI hm)

theorem stepW0_111 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L111) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K111))) L112 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K111 K112 (shiftK8 0 K111) (shiftK8 0 K112) T111 L112
    slice111 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_111 lab8_111 (step111 inp env hI hm)

theorem stepW0_112 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L112) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K112))) L113 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K112 K113 (shiftK8 0 K112) (shiftK8 0 K113) T112 L113
    slice112 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_112 lab8_112 (step112 inp env hI hm)

theorem stepW0_113 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L113) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K113))) L114 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K113 K114 (shiftK8 0 K113) (shiftK8 0 K114) T113 L114
    slice113 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_113 lab8_113 (step113 inp env hI hm)

theorem stepW0_114 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L114) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K114))) L115 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K114 K115 (shiftK8 0 K114) (shiftK8 0 K115) T114 L115
    slice114 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_114 lab8_114 (step114 inp env hI hm)

theorem stepW0_115 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L115) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K115))) L116 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K115 K116 (shiftK8 0 K115) (shiftK8 0 K116) T115 L116
    slice115 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_115 lab8_115 (step115 inp env hI hm)

theorem stepW0_116 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L116) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 25 (shiftK8 0 K116))) L117 :=
  invC_lift inp env prog 4 m0q m8 _ _ 25 K116 K117 (shiftK8 0 K116) (shiftK8 0 K117) T116 L117
    slice116 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_116 lab8_116 (step116 inp env hI hm)

theorem stepW0_117 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L117) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 37 (shiftK8 0 K117))) L118 :=
  invC_lift inp env prog 4 m0q m8 _ _ 37 K117 K118 (shiftK8 0 K117) (shiftK8 0 K118) T117 L118
    slice117 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_117 lab8_117 (step117 inp env hI hm)

theorem stepW0_118 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L118) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K118))) L119 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K118 K119 (shiftK8 0 K118) (shiftK8 0 K119) T118 L119
    slice118 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_118 lab8_118 (step118 inp env hI hm)

theorem stepW0_119 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L119) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K119))) L120 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K119 K120 (shiftK8 0 K119) (shiftK8 0 K120) T119 L120
    slice119 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_119 lab8_119 (step119 inp env hI hm)

theorem stepW0_120 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L120) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K120))) L121 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K120 K121 (shiftK8 0 K120) (shiftK8 0 K121) T120 L121
    slice120 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_120 lab8_120 (step120 inp env hI hm)

theorem stepW0_121 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L121) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K121))) L122 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K121 K122 (shiftK8 0 K121) (shiftK8 0 K122) T121 L122
    slice121 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_121 lab8_121 (step121 inp env hI hm)

theorem stepW0_122 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L122) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K122))) L123 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K122 K123 (shiftK8 0 K122) (shiftK8 0 K123) T122 L123
    slice122 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_122 lab8_122 (step122 inp env hI hm)

theorem stepW0_123 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L123) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K123))) L124 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K123 K124 (shiftK8 0 K123) (shiftK8 0 K124) T123 L124
    slice123 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_123 lab8_123 (step123 inp env hI hm)

theorem stepW0_124 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L124) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K124))) L125 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K124 K125 (shiftK8 0 K124) (shiftK8 0 K125) T124 L125
    slice124 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_124 lab8_124 (step124 inp env hI hm)

theorem stepW0_125 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L125) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K125))) L126 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K125 K126 (shiftK8 0 K125) (shiftK8 0 K126) T125 L126
    slice125 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_125 lab8_125 (step125 inp env hI hm)

theorem stepW0_126 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L126) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 46 (shiftK8 0 K126))) L127 :=
  invC_lift inp env prog 4 m0q m8 _ _ 46 K126 K127 (shiftK8 0 K126) (shiftK8 0 K127) T126 L127
    slice126 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_126 lab8_126 (step126 inp env hI hm)

theorem stepW0_127 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L127) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K127))) L128 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K127 K128 (shiftK8 0 K127) (shiftK8 0 K128) T127 L128
    slice127 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_127 lab8_127 (step127 inp env hI hm)

theorem stepW0_128 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L128) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K128))) L129 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K128 K129 (shiftK8 0 K128) (shiftK8 0 K129) T128 L129
    slice128 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_128 lab8_128 (step128 inp env hI hm)

theorem stepW0_129 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L129) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K129))) L130 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K129 K130 (shiftK8 0 K129) (shiftK8 0 K130) T129 L130
    slice129 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_129 lab8_129 (step129 inp env hI hm)

theorem stepW0_130 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L130) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K130))) L131 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K130 K131 (shiftK8 0 K130) (shiftK8 0 K131) T130 L131
    slice130 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_130 lab8_130 (step130 inp env hI hm)

theorem stepW0_131 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L131) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K131))) L132 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K131 K132 (shiftK8 0 K131) (shiftK8 0 K132) T131 L132
    slice131 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_131 lab8_131 (step131 inp env hI hm)

theorem stepW0_132 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L132) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K132))) L133 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K132 K133 (shiftK8 0 K132) (shiftK8 0 K133) T132 L133
    slice132 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_132 lab8_132 (step132 inp env hI hm)

theorem stepW0_133 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L133) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K133))) L134 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K133 K134 (shiftK8 0 K133) (shiftK8 0 K134) T133 L134
    slice133 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_133 lab8_133 (step133 inp env hI hm)

theorem stepW0_134 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L134) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K134))) L135 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K134 K135 (shiftK8 0 K134) (shiftK8 0 K135) T134 L135
    slice134 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_134 lab8_134 (step134 inp env hI hm)

theorem stepW0_135 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L135) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K135))) L136 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K135 K136 (shiftK8 0 K135) (shiftK8 0 K136) T135 L136
    slice135 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_135 lab8_135 (step135 inp env hI hm)

theorem stepW0_136 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L136) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K136))) L137 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K136 K137 (shiftK8 0 K136) (shiftK8 0 K137) T136 L137
    slice136 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_136 lab8_136 (step136 inp env hI hm)

theorem stepW0_137 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L137) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K137))) L138 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K137 K138 (shiftK8 0 K137) (shiftK8 0 K138) T137 L138
    slice137 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_137 lab8_137 (step137 inp env hI hm)

theorem stepW0_138 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L138) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K138))) L139 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K138 K139 (shiftK8 0 K138) (shiftK8 0 K139) T138 L139
    slice138 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_138 lab8_138 (step138 inp env hI hm)

theorem stepW0_139 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L139) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K139))) L140 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K139 K140 (shiftK8 0 K139) (shiftK8 0 K140) T139 L140
    slice139 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_139 lab8_139 (step139 inp env hI hm)

theorem stepW0_140 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L140) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K140))) L141 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K140 K141 (shiftK8 0 K140) (shiftK8 0 K141) T140 L141
    slice140 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_140 lab8_140 (step140 inp env hI hm)

theorem stepW0_141 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L141) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K141))) L142 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K141 K142 (shiftK8 0 K141) (shiftK8 0 K142) T141 L142
    slice141 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_141 lab8_141 (step141 inp env hI hm)

theorem stepW0_142 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L142) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K142))) L143 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K142 K143 (shiftK8 0 K142) (shiftK8 0 K143) T142 L143
    slice142 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_142 lab8_142 (step142 inp env hI hm)

theorem stepW0_143 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L143) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K143))) L144 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K143 K144 (shiftK8 0 K143) (shiftK8 0 K144) T143 L144
    slice143 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_143 lab8_143 (step143 inp env hI hm)

theorem stepW0_144 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L144) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K144))) L145 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K144 K145 (shiftK8 0 K144) (shiftK8 0 K145) T144 L145
    slice144 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_144 lab8_144 (step144 inp env hI hm)

theorem stepW0_145 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L145) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K145))) L146 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K145 K146 (shiftK8 0 K145) (shiftK8 0 K146) T145 L146
    slice145 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_145 lab8_145 (step145 inp env hI hm)

theorem stepW0_146 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L146) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K146))) L147 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K146 K147 (shiftK8 0 K146) (shiftK8 0 K147) T146 L147
    slice146 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_146 lab8_146 (step146 inp env hI hm)

theorem stepW0_147 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L147) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K147))) L148 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K147 K148 (shiftK8 0 K147) (shiftK8 0 K148) T147 L148
    slice147 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_147 lab8_147 (step147 inp env hI hm)

theorem stepW0_148 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L148) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K148))) L149 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K148 K149 (shiftK8 0 K148) (shiftK8 0 K149) T148 L149
    slice148 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_148 lab8_148 (step148 inp env hI hm)

theorem stepW0_149 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L149) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K149))) L150 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K149 K150 (shiftK8 0 K149) (shiftK8 0 K150) T149 L150
    slice149 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_149 lab8_149 (step149 inp env hI hm)

theorem stepW0_150 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L150) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K150))) L151 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K150 K151 (shiftK8 0 K150) (shiftK8 0 K151) T150 L151
    slice150 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_150 lab8_150 (step150 inp env hI hm)

theorem stepW0_151 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L151) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K151))) L152 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K151 K152 (shiftK8 0 K151) (shiftK8 0 K152) T151 L152
    slice151 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_151 lab8_151 (step151 inp env hI hm)

theorem stepW0_152 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L152) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K152))) L153 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K152 K153 (shiftK8 0 K152) (shiftK8 0 K153) T152 L153
    slice152 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_152 lab8_152 (step152 inp env hI hm)

theorem stepW0_153 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L153) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K153))) L154 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K153 K154 (shiftK8 0 K153) (shiftK8 0 K154) T153 L154
    slice153 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_153 lab8_153 (step153 inp env hI hm)

theorem stepW0_154 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L154) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K154))) L155 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K154 K155 (shiftK8 0 K154) (shiftK8 0 K155) T154 L155
    slice154 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_154 lab8_154 (step154 inp env hI hm)

theorem stepW0_155 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L155) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K155))) L156 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K155 K156 (shiftK8 0 K155) (shiftK8 0 K156) T155 L156
    slice155 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_155 lab8_155 (step155 inp env hI hm)

theorem stepW0_156 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L156) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K156))) L157 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K156 K157 (shiftK8 0 K156) (shiftK8 0 K157) T156 L157
    slice156 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_156 lab8_156 (step156 inp env hI hm)

theorem stepW0_157 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L157) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K157))) L158 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K157 K158 (shiftK8 0 K157) (shiftK8 0 K158) T157 L158
    slice157 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_157 lab8_157 (step157 inp env hI hm)

theorem stepW0_158 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L158) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K158))) L159 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K158 K159 (shiftK8 0 K158) (shiftK8 0 K159) T158 L159
    slice158 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_158 lab8_158 (step158 inp env hI hm)

theorem stepW0_159 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L159) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K159))) L160 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K159 K160 (shiftK8 0 K159) (shiftK8 0 K160) T159 L160
    slice159 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_159 lab8_159 (step159 inp env hI hm)

theorem stepW0_160 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L160) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K160))) L161 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K160 K161 (shiftK8 0 K160) (shiftK8 0 K161) T160 L161
    slice160 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_160 lab8_160 (step160 inp env hI hm)

theorem stepW0_161 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L161) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K161))) L162 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K161 K162 (shiftK8 0 K161) (shiftK8 0 K162) T161 L162
    slice161 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_161 lab8_161 (step161 inp env hI hm)

theorem stepW0_162 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L162) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K162))) L163 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K162 K163 (shiftK8 0 K162) (shiftK8 0 K163) T162 L163
    slice162 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_162 lab8_162 (step162 inp env hI hm)

theorem stepW0_163 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L163) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K163))) L164 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K163 K164 (shiftK8 0 K163) (shiftK8 0 K164) T163 L164
    slice163 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_163 lab8_163 (step163 inp env hI hm)

theorem stepW0_164 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L164) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K164))) L165 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K164 K165 (shiftK8 0 K164) (shiftK8 0 K165) T164 L165
    slice164 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_164 lab8_164 (step164 inp env hI hm)

theorem stepW0_165 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L165) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K165))) L166 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K165 K166 (shiftK8 0 K165) (shiftK8 0 K166) T165 L166
    slice165 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_165 lab8_165 (step165 inp env hI hm)

theorem stepW0_166 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L166) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K166))) L167 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K166 K167 (shiftK8 0 K166) (shiftK8 0 K167) T166 L167
    slice166 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_166 lab8_166 (step166 inp env hI hm)

theorem stepW0_167 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L167) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K167))) L168 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K167 K168 (shiftK8 0 K167) (shiftK8 0 K168) T167 L168
    slice167 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_167 lab8_167 (step167 inp env hI hm)

theorem stepW0_168 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L168) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K168))) L169 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K168 K169 (shiftK8 0 K168) (shiftK8 0 K169) T168 L169
    slice168 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_168 lab8_168 (step168 inp env hI hm)

theorem stepW0_169 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L169) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K169))) L170 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K169 K170 (shiftK8 0 K169) (shiftK8 0 K170) T169 L170
    slice169 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_169 lab8_169 (step169 inp env hI hm)

theorem stepW0_170 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L170) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K170))) L171 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K170 K171 (shiftK8 0 K170) (shiftK8 0 K171) T170 L171
    slice170 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_170 lab8_170 (step170 inp env hI hm)

theorem stepW0_171 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L171) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K171))) L172 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K171 K172 (shiftK8 0 K171) (shiftK8 0 K172) T171 L172
    slice171 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_171 lab8_171 (step171 inp env hI hm)

theorem stepW0_172 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L172) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K172))) L173 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K172 K173 (shiftK8 0 K172) (shiftK8 0 K173) T172 L173
    slice172 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_172 lab8_172 (step172 inp env hI hm)

theorem stepW0_173 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L173) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K173))) L174 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K173 K174 (shiftK8 0 K173) (shiftK8 0 K174) T173 L174
    slice173 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_173 lab8_173 (step173 inp env hI hm)

theorem stepW0_174 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L174) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K174))) L175 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K174 K175 (shiftK8 0 K174) (shiftK8 0 K175) T174 L175
    slice174 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_174 lab8_174 (step174 inp env hI hm)

theorem stepW0_175 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L175) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K175))) L176 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K175 K176 (shiftK8 0 K175) (shiftK8 0 K176) T175 L176
    slice175 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_175 lab8_175 (step175 inp env hI hm)

theorem stepW0_176 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L176) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K176))) L177 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K176 K177 (shiftK8 0 K176) (shiftK8 0 K177) T176 L177
    slice176 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_176 lab8_176 (step176 inp env hI hm)

theorem stepW0_177 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L177) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K177))) L178 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K177 K178 (shiftK8 0 K177) (shiftK8 0 K178) T177 L178
    slice177 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_177 lab8_177 (step177 inp env hI hm)

theorem stepW0_178 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L178) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K178))) L179 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K178 K179 (shiftK8 0 K178) (shiftK8 0 K179) T178 L179
    slice178 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_178 lab8_178 (step178 inp env hI hm)

theorem stepW0_179 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L179) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K179))) L180 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K179 K180 (shiftK8 0 K179) (shiftK8 0 K180) T179 L180
    slice179 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_179 lab8_179 (step179 inp env hI hm)

theorem stepW0_180 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L180) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K180))) L181 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K180 K181 (shiftK8 0 K180) (shiftK8 0 K181) T180 L181
    slice180 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_180 lab8_180 (step180 inp env hI hm)

theorem stepW0_181 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L181) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K181))) L182 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K181 K182 (shiftK8 0 K181) (shiftK8 0 K182) T181 L182
    slice181 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_181 lab8_181 (step181 inp env hI hm)

theorem stepW0_182 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L182) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K182))) L183 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K182 K183 (shiftK8 0 K182) (shiftK8 0 K183) T182 L183
    slice182 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_182 lab8_182 (step182 inp env hI hm)

theorem stepW0_183 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L183) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K183))) L184 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K183 K184 (shiftK8 0 K183) (shiftK8 0 K184) T183 L184
    slice183 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_183 lab8_183 (step183 inp env hI hm)

theorem stepW0_184 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L184) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K184))) L185 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K184 K185 (shiftK8 0 K184) (shiftK8 0 K185) T184 L185
    slice184 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_184 lab8_184 (step184 inp env hI hm)

theorem stepW0_185 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L185) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K185))) L186 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K185 K186 (shiftK8 0 K185) (shiftK8 0 K186) T185 L186
    slice185 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_185 lab8_185 (step185 inp env hI hm)

theorem stepW0_186 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L186) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K186))) L187 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K186 K187 (shiftK8 0 K186) (shiftK8 0 K187) T186 L187
    slice186 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_186 lab8_186 (step186 inp env hI hm)

theorem stepW0_187 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L187) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K187))) L188 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K187 K188 (shiftK8 0 K187) (shiftK8 0 K188) T187 L188
    slice187 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_187 lab8_187 (step187 inp env hI hm)

theorem stepW0_188 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L188) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K188))) L189 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K188 K189 (shiftK8 0 K188) (shiftK8 0 K189) T188 L189
    slice188 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_188 lab8_188 (step188 inp env hI hm)

theorem stepW0_189 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L189) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 36 (shiftK8 0 K189))) L190 :=
  invC_lift inp env prog 4 m0q m8 _ _ 36 K189 K190 (shiftK8 0 K189) (shiftK8 0 K190) T189 L190
    slice189 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_189 lab8_189 (step189 inp env hI hm)

theorem stepW0_190 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L190) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K190))) L191 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K190 K191 (shiftK8 0 K190) (shiftK8 0 K191) T190 L191
    slice190 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_190 lab8_190 (step190 inp env hI hm)

theorem stepW0_191 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L191) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K191))) L192 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K191 K192 (shiftK8 0 K191) (shiftK8 0 K192) T191 L192
    slice191 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_191 lab8_191 (step191 inp env hI hm)

theorem stepW0_192 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L192) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K192))) L193 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K192 K193 (shiftK8 0 K192) (shiftK8 0 K193) T192 L193
    slice192 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_192 lab8_192 (step192 inp env hI hm)

theorem stepW0_193 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L193) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K193))) L194 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K193 K194 (shiftK8 0 K193) (shiftK8 0 K194) T193 L194
    slice193 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_193 lab8_193 (step193 inp env hI hm)

theorem stepW0_194 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L194) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K194))) L195 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K194 K195 (shiftK8 0 K194) (shiftK8 0 K195) T194 L195
    slice194 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_194 lab8_194 (step194 inp env hI hm)

theorem stepW0_195 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L195) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K195))) L196 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K195 K196 (shiftK8 0 K195) (shiftK8 0 K196) T195 L196
    slice195 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_195 lab8_195 (step195 inp env hI hm)

theorem stepW0_196 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L196) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K196))) L197 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K196 K197 (shiftK8 0 K196) (shiftK8 0 K197) T196 L197
    slice196 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_196 lab8_196 (step196 inp env hI hm)

theorem stepW0_197 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L197) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K197))) L198 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K197 K198 (shiftK8 0 K197) (shiftK8 0 K198) T197 L198
    slice197 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_197 lab8_197 (step197 inp env hI hm)

theorem stepW0_198 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L198) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K198))) L199 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K198 K199 (shiftK8 0 K198) (shiftK8 0 K199) T198 L199
    slice198 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_198 lab8_198 (step198 inp env hI hm)

theorem stepW0_199 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L199) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K199))) L200 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K199 K200 (shiftK8 0 K199) (shiftK8 0 K200) T199 L200
    slice199 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_199 lab8_199 (step199 inp env hI hm)

theorem stepW0_200 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L200) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K200))) L201 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K200 K201 (shiftK8 0 K200) (shiftK8 0 K201) T200 L201
    slice200 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_200 lab8_200 (step200 inp env hI hm)

theorem stepW0_201 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L201) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K201))) L202 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K201 K202 (shiftK8 0 K201) (shiftK8 0 K202) T201 L202
    slice201 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_201 lab8_201 (step201 inp env hI hm)

theorem stepW0_202 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L202) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 3 (shiftK8 0 K202))) L203 :=
  invC_lift inp env prog 4 m0q m8 _ _ 3 K202 K203 (shiftK8 0 K202) (shiftK8 0 K203) T202 L203
    slice202 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_202 lab8_202 (step202 inp env hI hm)

theorem stepW0_203 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K203))) L204 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K203 K204 (shiftK8 0 K203) (shiftK8 0 K204) T203 L204
    slice203 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_203 lab8_203 (step203 inp env hI hm)

theorem stepW0_204 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L204) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 1 (shiftK8 0 K204))) L205 :=
  invC_lift inp env prog 4 m0q m8 _ _ 1 K204 K205 (shiftK8 0 K204) (shiftK8 0 K205) T204 L205
    slice204 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_204 lab8_204 (step204 inp env hI hm)

theorem stepW0_205 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L205) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K205))) L206 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K205 K206 (shiftK8 0 K205) (shiftK8 0 K206) T205 L206
    slice205 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_205 lab8_205 (step205 inp env hI hm)

theorem stepW0_206 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L206) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K206))) L207 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K206 K207 (shiftK8 0 K206) (shiftK8 0 K207) T206 L207
    slice206 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_206 lab8_206 (step206 inp env hI hm)

theorem stepW0_207 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L207) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K207))) L208 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K207 K208 (shiftK8 0 K207) (shiftK8 0 K208) T207 L208
    slice207 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_207 lab8_207 (step207 inp env hI hm)

theorem stepW0_208 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L208) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K208))) L209 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K208 K209 (shiftK8 0 K208) (shiftK8 0 K209) T208 L209
    slice208 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_208 lab8_208 (step208 inp env hI hm)

theorem stepW0_209 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L209) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 2 (shiftK8 0 K209))) L210 :=
  invC_lift inp env prog 4 m0q m8 _ _ 2 K209 K210 (shiftK8 0 K209) (shiftK8 0 K210) T209 L210
    slice209 Hashtree.Proofs.Avx2X8WBodyR0.sliceW_209 lab8_209 (step209 inp env hI hm)

theorem stepS0_2 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L2) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 8 (KHs 0))) L3 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 8 K2 K3 (KHs 0) (KH3s 0) T2 L3
    slice2 Hashtree.Proofs.Avx2X8WBodyR0S.sliceV2s lab8_2 (step2 inp env hI hm)

theorem stepS0_3 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L3) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 8 (KH3s 0))) L4 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 8 K3 K4 (KH3s 0) (stripK8 0 K4) T3 L4
    slice3 Hashtree.Proofs.Avx2X8WBodyR0S.sliceV3s lab8_3 (step3 inp env hI hm)

theorem stepS0_4 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L4) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 8 (stripK8 0 K4))) L5 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 8 K4 K5 (stripK8 0 K4) (stripK8 0 K5) T4 L5
    slice4 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_4 lab8_4 (step4 inp env hI hm)

theorem stepS0_5 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L5) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 8 (stripK8 0 K5))) L6 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 8 K5 K6 (stripK8 0 K5) (stripK8 0 K6) T5 L6
    slice5 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_5 lab8_5 (step5 inp env hI hm)

theorem stepS0_6 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L6) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 61 (stripK8 0 K6))) L7 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 61 K6 K7 (stripK8 0 K6) (stripK8 0 K7) T6 L7
    slice6 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_6 lab8_6 (step6 inp env hI hm)

theorem stepS0_7 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L7) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K7))) L8 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K7 K8 (stripK8 0 K7) (stripK8 0 K8) T7 L8
    slice7 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_7 lab8_7 (step7 inp env hI hm)

theorem stepS0_8 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L8) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K8))) L9 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K8 K9 (stripK8 0 K8) (stripK8 0 K9) T8 L9
    slice8 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_8 lab8_8 (step8 inp env hI hm)

theorem stepS0_9 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L9) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K9))) L10 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K9 K10 (stripK8 0 K9) (stripK8 0 K10) T9 L10
    slice9 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_9 lab8_9 (step9 inp env hI hm)

theorem stepS0_10 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L10) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K10))) L11 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K10 K11 (stripK8 0 K10) (stripK8 0 K11) T10 L11
    slice10 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_10 lab8_10 (step10 inp env hI hm)

theorem stepS0_11 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L11) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K11))) L12 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K11 K12 (stripK8 0 K11) (stripK8 0 K12) T11 L12
    slice11 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_11 lab8_11 (step11 inp env hI hm)

theorem stepS0_12 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L12) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K12))) L13 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K12 K13 (stripK8 0 K12) (stripK8 0 K13) T12 L13
    slice12 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_12 lab8_12 (step12 inp env hI hm)

theorem stepS0_13 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L13) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K13))) L14 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K13 K14 (stripK8 0 K13) (stripK8 0 K14) T13 L14
    slice13 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_13 lab8_13 (step13 inp env hI hm)

theorem stepS0_14 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L14) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 86 (stripK8 0 K14))) L15 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 86 K14 K15 (stripK8 0 K14) (stripK8 0 K15) T14 L15
    slice14 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_14 lab8_14 (step14 inp env hI hm)

theorem stepS0_15 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L15) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K15))) L16 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K15 K16 (stripK8 0 K15) (stripK8 0 K16) T15 L16
    slice15 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_15 lab8_15 (step15 inp env hI hm)

theorem stepS0_16 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L16) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K16))) L17 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K16 K17 (stripK8 0 K16) (stripK8 0 K17) T16 L17
    slice16 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_16 lab8_16 (step16 inp env hI hm)

theorem stepS0_17 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L17) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K17))) L18 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K17 K18 (stripK8 0 K17) (stripK8 0 K18) T17 L18
    slice17 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_17 lab8_17 (step17 inp env hI hm)

theorem stepS0_18 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L18) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 38 (stripK8 0 K18))) L19 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 38 K18 K19 (stripK8 0 K18) (stripK8 0 K19) T18 L19
    slice18 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_18 lab8_18 (step18 inp env hI hm)

theorem stepS0_19 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L19) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K19))) L20 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K19 K20 (stripK8 0 K19) (stripK8 0 K20) T19 L20
    slice19 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_19 lab8_19 (step19 inp env hI hm)

theorem stepS0_20 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L20) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K20))) L21 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K20 K21 (stripK8 0 K20) (stripK8 0 K21) T20 L21
    slice20 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_20 lab8_20 (step20 inp env hI hm)

theorem stepS0_21 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L21) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K21))) L22 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K21 K22 (stripK8 0 K21) (stripK8 0 K22) T21 L22
    slice21 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_21 lab8_21 (step21 inp env hI hm)

theorem stepS0_22 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L22) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K22))) L23 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K22 K23 (stripK8 0 K22) (stripK8 0 K23) T22 L23
    slice22 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_22 lab8_22 (step22 inp env hI hm)

theorem stepS0_23 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L23) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K23))) L24 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K23 K24 (stripK8 0 K23) (stripK8 0 K24) T23 L24
    slice23 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_23 lab8_23 (step23 inp env hI hm)

theorem stepS0_24 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L24) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K24))) L25 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K24 K25 (stripK8 0 K24) (stripK8 0 K25) T24 L25
    slice24 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_24 lab8_24 (step24 inp env hI hm)

theorem stepS0_25 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L25) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K25))) L26 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K25 K26 (stripK8 0 K25) (stripK8 0 K26) T25 L26
    slice25 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_25 lab8_25 (step25 inp env hI hm)

theorem stepS0_26 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L26) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K26))) L27 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K26 K27 (stripK8 0 K26) (stripK8 0 K27) T26 L27
    slice26 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_26 lab8_26 (step26 inp env hI hm)

theorem stepS0_27 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L27) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K27))) L28 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K27 K28 (stripK8 0 K27) (stripK8 0 K28) T27 L28
    slice27 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_27 lab8_27 (step27 inp env hI hm)

theorem stepS0_28 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L28) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K28))) L29 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K28 K29 (stripK8 0 K28) (stripK8 0 K29) T28 L29
    slice28 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_28 lab8_28 (step28 inp env hI hm)

theorem stepS0_29 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L29) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K29))) L30 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K29 K30 (stripK8 0 K29) (stripK8 0 K30) T29 L30
    slice29 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_29 lab8_29 (step29 inp env hI hm)

theorem stepS0_30 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L30) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K30))) L31 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K30 K31 (stripK8 0 K30) (stripK8 0 K31) T30 L31
    slice30 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_30 lab8_30 (step30 inp env hI hm)

theorem stepS0_31 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L31) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K31))) L32 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K31 K32 (stripK8 0 K31) (stripK8 0 K32) T31 L32
    slice31 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_31 lab8_31 (step31 inp env hI hm)

theorem stepS0_32 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L32) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K32))) L33 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K32 K33 (stripK8 0 K32) (stripK8 0 K33) T32 L33
    slice32 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_32 lab8_32 (step32 inp env hI hm)

theorem stepS0_33 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L33) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K33))) L34 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K33 K34 (stripK8 0 K33) (stripK8 0 K34) T33 L34
    slice33 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_33 lab8_33 (step33 inp env hI hm)

theorem stepS0_34 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L34) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K34))) L35 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K34 K35 (stripK8 0 K34) (stripK8 0 K35) T34 L35
    slice34 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_34 lab8_34 (step34 inp env hI hm)

theorem stepS0_35 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L35) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K35))) L36 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K35 K36 (stripK8 0 K35) (stripK8 0 K36) T35 L36
    slice35 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_35 lab8_35 (step35 inp env hI hm)

theorem stepS0_36 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L36) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K36))) L37 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K36 K37 (stripK8 0 K36) (stripK8 0 K37) T36 L37
    slice36 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_36 lab8_36 (step36 inp env hI hm)

theorem stepS0_37 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L37) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K37))) L38 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K37 K38 (stripK8 0 K37) (stripK8 0 K38) T37 L38
    slice37 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_37 lab8_37 (step37 inp env hI hm)

theorem stepS0_38 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L38) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K38))) L39 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K38 K39 (stripK8 0 K38) (stripK8 0 K39) T38 L39
    slice38 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_38 lab8_38 (step38 inp env hI hm)

theorem stepS0_39 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L39) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K39))) L40 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K39 K40 (stripK8 0 K39) (stripK8 0 K40) T39 L40
    slice39 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_39 lab8_39 (step39 inp env hI hm)

theorem stepS0_40 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L40) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K40))) L41 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K40 K41 (stripK8 0 K40) (stripK8 0 K41) T40 L41
    slice40 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_40 lab8_40 (step40 inp env hI hm)

theorem stepS0_41 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L41) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K41))) L42 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K41 K42 (stripK8 0 K41) (stripK8 0 K42) T41 L42
    slice41 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_41 lab8_41 (step41 inp env hI hm)

theorem stepS0_42 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L42) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K42))) L43 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K42 K43 (stripK8 0 K42) (stripK8 0 K43) T42 L43
    slice42 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_42 lab8_42 (step42 inp env hI hm)

theorem stepS0_43 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L43) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K43))) L44 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K43 K44 (stripK8 0 K43) (stripK8 0 K44) T43 L44
    slice43 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_43 lab8_43 (step43 inp env hI hm)

theorem stepS0_44 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L44) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K44))) L45 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K44 K45 (stripK8 0 K44) (stripK8 0 K45) T44 L45
    slice44 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_44 lab8_44 (step44 inp env hI hm)

theorem stepS0_45 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L45) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K45))) L46 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K45 K46 (stripK8 0 K45) (stripK8 0 K46) T45 L46
    slice45 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_45 lab8_45 (step45 inp env hI hm)

theorem stepS0_46 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L46) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K46))) L47 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K46 K47 (stripK8 0 K46) (stripK8 0 K47) T46 L47
    slice46 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_46 lab8_46 (step46 inp env hI hm)

theorem stepS0_47 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L47) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K47))) L48 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K47 K48 (stripK8 0 K47) (stripK8 0 K48) T47 L48
    slice47 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_47 lab8_47 (step47 inp env hI hm)

theorem stepS0_48 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L48) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K48))) L49 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K48 K49 (stripK8 0 K48) (stripK8 0 K49) T48 L49
    slice48 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_48 lab8_48 (step48 inp env hI hm)

theorem stepS0_49 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L49) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K49))) L50 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K49 K50 (stripK8 0 K49) (stripK8 0 K50) T49 L50
    slice49 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_49 lab8_49 (step49 inp env hI hm)

theorem stepS0_50 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L50) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K50))) L51 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K50 K51 (stripK8 0 K50) (stripK8 0 K51) T50 L51
    slice50 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_50 lab8_50 (step50 inp env hI hm)

theorem stepS0_51 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L51) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K51))) L52 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K51 K52 (stripK8 0 K51) (stripK8 0 K52) T51 L52
    slice51 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_51 lab8_51 (step51 inp env hI hm)

theorem stepS0_52 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L52) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K52))) L53 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K52 K53 (stripK8 0 K52) (stripK8 0 K53) T52 L53
    slice52 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_52 lab8_52 (step52 inp env hI hm)

theorem stepS0_53 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L53) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K53))) L54 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K53 K54 (stripK8 0 K53) (stripK8 0 K54) T53 L54
    slice53 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_53 lab8_53 (step53 inp env hI hm)

theorem stepS0_54 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L54) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K54))) L55 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K54 K55 (stripK8 0 K54) (stripK8 0 K55) T54 L55
    slice54 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_54 lab8_54 (step54 inp env hI hm)

theorem stepS0_55 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L55) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K55))) L56 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K55 K56 (stripK8 0 K55) (stripK8 0 K56) T55 L56
    slice55 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_55 lab8_55 (step55 inp env hI hm)

theorem stepS0_56 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L56) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K56))) L57 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K56 K57 (stripK8 0 K56) (stripK8 0 K57) T56 L57
    slice56 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_56 lab8_56 (step56 inp env hI hm)

theorem stepS0_57 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L57) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K57))) L58 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K57 K58 (stripK8 0 K57) (stripK8 0 K58) T57 L58
    slice57 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_57 lab8_57 (step57 inp env hI hm)

theorem stepS0_58 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L58) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K58))) L59 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K58 K59 (stripK8 0 K58) (stripK8 0 K59) T58 L59
    slice58 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_58 lab8_58 (step58 inp env hI hm)

theorem stepS0_59 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L59) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K59))) L60 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K59 K60 (stripK8 0 K59) (stripK8 0 K60) T59 L60
    slice59 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_59 lab8_59 (step59 inp env hI hm)

theorem stepS0_60 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L60) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K60))) L61 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K60 K61 (stripK8 0 K60) (stripK8 0 K61) T60 L61
    slice60 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_60 lab8_60 (step60 inp env hI hm)

theorem stepS0_61 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L61) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K61))) L62 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K61 K62 (stripK8 0 K61) (stripK8 0 K62) T61 L62
    slice61 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_61 lab8_61 (step61 inp env hI hm)

theorem stepS0_62 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L62) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K62))) L63 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K62 K63 (stripK8 0 K62) (stripK8 0 K63) T62 L63
    slice62 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_62 lab8_62 (step62 inp env hI hm)

theorem stepS0_63 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L63) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K63))) L64 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K63 K64 (stripK8 0 K63) (stripK8 0 K64) T63 L64
    slice63 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_63 lab8_63 (step63 inp env hI hm)

theorem stepS0_64 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L64) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K64))) L65 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K64 K65 (stripK8 0 K64) (stripK8 0 K65) T64 L65
    slice64 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_64 lab8_64 (step64 inp env hI hm)

theorem stepS0_65 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L65) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K65))) L66 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K65 K66 (stripK8 0 K65) (stripK8 0 K66) T65 L66
    slice65 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_65 lab8_65 (step65 inp env hI hm)

theorem stepS0_66 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L66) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K66))) L67 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K66 K67 (stripK8 0 K66) (stripK8 0 K67) T66 L67
    slice66 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_66 lab8_66 (step66 inp env hI hm)

theorem stepS0_67 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L67) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K67))) L68 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K67 K68 (stripK8 0 K67) (stripK8 0 K68) T67 L68
    slice67 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_67 lab8_67 (step67 inp env hI hm)

theorem stepS0_68 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L68) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K68))) L69 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K68 K69 (stripK8 0 K68) (stripK8 0 K69) T68 L69
    slice68 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_68 lab8_68 (step68 inp env hI hm)

theorem stepS0_69 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L69) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K69))) L70 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K69 K70 (stripK8 0 K69) (stripK8 0 K70) T69 L70
    slice69 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_69 lab8_69 (step69 inp env hI hm)

theorem stepS0_70 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L70) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K70))) L71 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K70 K71 (stripK8 0 K70) (stripK8 0 K71) T70 L71
    slice70 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_70 lab8_70 (step70 inp env hI hm)

theorem stepS0_71 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L71) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K71))) L72 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K71 K72 (stripK8 0 K71) (stripK8 0 K72) T71 L72
    slice71 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_71 lab8_71 (step71 inp env hI hm)

theorem stepS0_72 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L72) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K72))) L73 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K72 K73 (stripK8 0 K72) (stripK8 0 K73) T72 L73
    slice72 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_72 lab8_72 (step72 inp env hI hm)

theorem stepS0_73 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L73) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K73))) L74 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K73 K74 (stripK8 0 K73) (stripK8 0 K74) T73 L74
    slice73 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_73 lab8_73 (step73 inp env hI hm)

theorem stepS0_74 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L74) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K74))) L75 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K74 K75 (stripK8 0 K74) (stripK8 0 K75) T74 L75
    slice74 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_74 lab8_74 (step74 inp env hI hm)

theorem stepS0_75 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L75) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K75))) L76 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K75 K76 (stripK8 0 K75) (stripK8 0 K76) T75 L76
    slice75 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_75 lab8_75 (step75 inp env hI hm)

theorem stepS0_76 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L76) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K76))) L77 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K76 K77 (stripK8 0 K76) (stripK8 0 K77) T76 L77
    slice76 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_76 lab8_76 (step76 inp env hI hm)

theorem stepS0_77 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L77) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K77))) L78 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K77 K78 (stripK8 0 K77) (stripK8 0 K78) T77 L78
    slice77 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_77 lab8_77 (step77 inp env hI hm)

theorem stepS0_78 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L78) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K78))) L79 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K78 K79 (stripK8 0 K78) (stripK8 0 K79) T78 L79
    slice78 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_78 lab8_78 (step78 inp env hI hm)

theorem stepS0_79 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L79) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K79))) L80 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K79 K80 (stripK8 0 K79) (stripK8 0 K80) T79 L80
    slice79 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_79 lab8_79 (step79 inp env hI hm)

theorem stepS0_80 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L80) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K80))) L81 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K80 K81 (stripK8 0 K80) (stripK8 0 K81) T80 L81
    slice80 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_80 lab8_80 (step80 inp env hI hm)

theorem stepS0_81 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L81) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K81))) L82 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K81 K82 (stripK8 0 K81) (stripK8 0 K82) T81 L82
    slice81 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_81 lab8_81 (step81 inp env hI hm)

theorem stepS0_82 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L82) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K82))) L83 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K82 K83 (stripK8 0 K82) (stripK8 0 K83) T82 L83
    slice82 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_82 lab8_82 (step82 inp env hI hm)

theorem stepS0_83 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L83) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K83))) L84 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K83 K84 (stripK8 0 K83) (stripK8 0 K84) T83 L84
    slice83 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_83 lab8_83 (step83 inp env hI hm)

theorem stepS0_84 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L84) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K84))) L85 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K84 K85 (stripK8 0 K84) (stripK8 0 K85) T84 L85
    slice84 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_84 lab8_84 (step84 inp env hI hm)

theorem stepS0_85 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L85) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K85))) L86 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K85 K86 (stripK8 0 K85) (stripK8 0 K86) T85 L86
    slice85 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_85 lab8_85 (step85 inp env hI hm)

theorem stepS0_86 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L86) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K86))) L87 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K86 K87 (stripK8 0 K86) (stripK8 0 K87) T86 L87
    slice86 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_86 lab8_86 (step86 inp env hI hm)

theorem stepS0_87 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L87) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K87))) L88 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K87 K88 (stripK8 0 K87) (stripK8 0 K88) T87 L88
    slice87 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_87 lab8_87 (step87 inp env hI hm)

theorem stepS0_88 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L88) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K88))) L89 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K88 K89 (stripK8 0 K88) (stripK8 0 K89) T88 L89
    slice88 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_88 lab8_88 (step88 inp env hI hm)

theorem stepS0_89 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L89) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K89))) L90 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K89 K90 (stripK8 0 K89) (stripK8 0 K90) T89 L90
    slice89 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_89 lab8_89 (step89 inp env hI hm)

theorem stepS0_90 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L90) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K90))) L91 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K90 K91 (stripK8 0 K90) (stripK8 0 K91) T90 L91
    slice90 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_90 lab8_90 (step90 inp env hI hm)

theorem stepS0_91 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L91) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K91))) L92 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K91 K92 (stripK8 0 K91) (stripK8 0 K92) T91 L92
    slice91 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_91 lab8_91 (step91 inp env hI hm)

theorem stepS0_92 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L92) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K92))) L93 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K92 K93 (stripK8 0 K92) (stripK8 0 K93) T92 L93
    slice92 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_92 lab8_92 (step92 inp env hI hm)

theorem stepS0_93 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L93) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K93))) L94 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K93 K94 (stripK8 0 K93) (stripK8 0 K94) T93 L94
    slice93 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_93 lab8_93 (step93 inp env hI hm)

theorem stepS0_94 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L94) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K94))) L95 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K94 K95 (stripK8 0 K94) (stripK8 0 K95) T94 L95
    slice94 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_94 lab8_94 (step94 inp env hI hm)

theorem stepS0_95 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L95) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K95))) L96 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K95 K96 (stripK8 0 K95) (stripK8 0 K96) T95 L96
    slice95 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_95 lab8_95 (step95 inp env hI hm)

theorem stepS0_96 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L96) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K96))) L97 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K96 K97 (stripK8 0 K96) (stripK8 0 K97) T96 L97
    slice96 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_96 lab8_96 (step96 inp env hI hm)

theorem stepS0_97 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L97) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K97))) L98 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K97 K98 (stripK8 0 K97) (stripK8 0 K98) T97 L98
    slice97 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_97 lab8_97 (step97 inp env hI hm)

theorem stepS0_98 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L98) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K98))) L99 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K98 K99 (stripK8 0 K98) (stripK8 0 K99) T98 L99
    slice98 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_98 lab8_98 (step98 inp env hI hm)

theorem stepS0_99 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L99) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K99))) L100 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K99 K100 (stripK8 0 K99) (stripK8 0 K100) T99 L100
    slice99 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_99 lab8_99 (step99 inp env hI hm)

theorem stepS0_100 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L100) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K100))) L101 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K100 K101 (stripK8 0 K100) (stripK8 0 K101) T100 L101
    slice100 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_100 lab8_100 (step100 inp env hI hm)

theorem stepS0_101 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L101) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K101))) L102 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K101 K102 (stripK8 0 K101) (stripK8 0 K102) T101 L102
    slice101 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_101 lab8_101 (step101 inp env hI hm)

theorem stepS0_102 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L102) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K102))) L103 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K102 K103 (stripK8 0 K102) (stripK8 0 K103) T102 L103
    slice102 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_102 lab8_102 (step102 inp env hI hm)

theorem stepS0_103 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L103) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K103))) L104 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K103 K104 (stripK8 0 K103) (stripK8 0 K104) T103 L104
    slice103 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_103 lab8_103 (step103 inp env hI hm)

theorem stepS0_104 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L104) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K104))) L105 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K104 K105 (stripK8 0 K104) (stripK8 0 K105) T104 L105
    slice104 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_104 lab8_104 (step104 inp env hI hm)

theorem stepS0_105 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L105) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K105))) L106 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K105 K106 (stripK8 0 K105) (stripK8 0 K106) T105 L106
    slice105 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_105 lab8_105 (step105 inp env hI hm)

theorem stepS0_106 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L106) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K106))) L107 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K106 K107 (stripK8 0 K106) (stripK8 0 K107) T106 L107
    slice106 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_106 lab8_106 (step106 inp env hI hm)

theorem stepS0_107 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L107) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K107))) L108 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K107 K108 (stripK8 0 K107) (stripK8 0 K108) T107 L108
    slice107 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_107 lab8_107 (step107 inp env hI hm)

theorem stepS0_108 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L108) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K108))) L109 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K108 K109 (stripK8 0 K108) (stripK8 0 K109) T108 L109
    slice108 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_108 lab8_108 (step108 inp env hI hm)

theorem stepS0_109 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L109) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K109))) L110 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K109 K110 (stripK8 0 K109) (stripK8 0 K110) T109 L110
    slice109 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_109 lab8_109 (step109 inp env hI hm)

theorem stepS0_110 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L110) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K110))) L111 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K110 K111 (stripK8 0 K110) (stripK8 0 K111) T110 L111
    slice110 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_110 lab8_110 (step110 inp env hI hm)

theorem stepS0_111 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L111) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K111))) L112 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K111 K112 (stripK8 0 K111) (stripK8 0 K112) T111 L112
    slice111 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_111 lab8_111 (step111 inp env hI hm)

theorem stepS0_112 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L112) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K112))) L113 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K112 K113 (stripK8 0 K112) (stripK8 0 K113) T112 L113
    slice112 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_112 lab8_112 (step112 inp env hI hm)

theorem stepS0_113 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L113) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K113))) L114 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K113 K114 (stripK8 0 K113) (stripK8 0 K114) T113 L114
    slice113 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_113 lab8_113 (step113 inp env hI hm)

theorem stepS0_114 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L114) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K114))) L115 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K114 K115 (stripK8 0 K114) (stripK8 0 K115) T114 L115
    slice114 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_114 lab8_114 (step114 inp env hI hm)

theorem stepS0_115 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L115) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K115))) L116 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K115 K116 (stripK8 0 K115) (stripK8 0 K116) T115 L116
    slice115 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_115 lab8_115 (step115 inp env hI hm)

theorem stepS0_116 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L116) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 25 (stripK8 0 K116))) L117 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 25 K116 K117 (stripK8 0 K116) (stripK8 0 K117) T116 L117
    slice116 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_116 lab8_116 (step116 inp env hI hm)

theorem stepS0_117 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L117) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 37 (stripK8 0 K117))) L118 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 37 K117 K118 (stripK8 0 K117) (stripK8 0 K118) T117 L118
    slice117 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_117 lab8_117 (step117 inp env hI hm)

theorem stepS0_118 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L118) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K118))) L119 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K118 K119 (stripK8 0 K118) (stripK8 0 K119) T118 L119
    slice118 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_118 lab8_118 (step118 inp env hI hm)

theorem stepS0_119 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L119) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K119))) L120 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K119 K120 (stripK8 0 K119) (stripK8 0 K120) T119 L120
    slice119 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_119 lab8_119 (step119 inp env hI hm)

theorem stepS0_120 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L120) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K120))) L121 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K120 K121 (stripK8 0 K120) (stripK8 0 K121) T120 L121
    slice120 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_120 lab8_120 (step120 inp env hI hm)

theorem stepS0_121 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L121) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K121))) L122 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K121 K122 (stripK8 0 K121) (stripK8 0 K122) T121 L122
    slice121 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_121 lab8_121 (step121 inp env hI hm)

theorem stepS0_122 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L122) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K122))) L123 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K122 K123 (stripK8 0 K122) (stripK8 0 K123) T122 L123
    slice122 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_122 lab8_122 (step122 inp env hI hm)

theorem stepS0_123 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L123) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K123))) L124 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K123 K124 (stripK8 0 K123) (stripK8 0 K124) T123 L124
    slice123 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_123 lab8_123 (step123 inp env hI hm)

theorem stepS0_124 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L124) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K124))) L125 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K124 K125 (stripK8 0 K124) (stripK8 0 K125) T124 L125
    slice124 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_124 lab8_124 (step124 inp env hI hm)

theorem stepS0_125 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L125) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K125))) L126 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K125 K126 (stripK8 0 K125) (stripK8 0 K126) T125 L126
    slice125 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_125 lab8_125 (step125 inp env hI hm)

theorem stepS0_126 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L126) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 46 (stripK8 0 K126))) L127 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 46 K126 K127 (stripK8 0 K126) (stripK8 0 K127) T126 L127
    slice126 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_126 lab8_126 (step126 inp env hI hm)

theorem stepS0_127 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L127) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K127))) L128 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K127 K128 (stripK8 0 K127) (stripK8 0 K128) T127 L128
    slice127 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_127 lab8_127 (step127 inp env hI hm)

theorem stepS0_128 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L128) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K128))) L129 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K128 K129 (stripK8 0 K128) (stripK8 0 K129) T128 L129
    slice128 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_128 lab8_128 (step128 inp env hI hm)

theorem stepS0_129 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L129) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K129))) L130 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K129 K130 (stripK8 0 K129) (stripK8 0 K130) T129 L130
    slice129 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_129 lab8_129 (step129 inp env hI hm)

theorem stepS0_130 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L130) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K130))) L131 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K130 K131 (stripK8 0 K130) (stripK8 0 K131) T130 L131
    slice130 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_130 lab8_130 (step130 inp env hI hm)

theorem stepS0_131 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L131) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K131))) L132 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K131 K132 (stripK8 0 K131) (stripK8 0 K132) T131 L132
    slice131 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_131 lab8_131 (step131 inp env hI hm)

theorem stepS0_132 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L132) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K132))) L133 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K132 K133 (stripK8 0 K132) (stripK8 0 K133) T132 L133
    slice132 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_132 lab8_132 (step132 inp env hI hm)

theorem stepS0_133 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L133) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K133))) L134 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K133 K134 (stripK8 0 K133) (stripK8 0 K134) T133 L134
    slice133 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_133 lab8_133 (step133 inp env hI hm)

theorem stepS0_134 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L134) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K134))) L135 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K134 K135 (stripK8 0 K134) (stripK8 0 K135) T134 L135
    slice134 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_134 lab8_134 (step134 inp env hI hm)

theorem stepS0_135 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L135) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K135))) L136 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K135 K136 (stripK8 0 K135) (stripK8 0 K136) T135 L136
    slice135 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_135 lab8_135 (step135 inp env hI hm)

theorem stepS0_136 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L136) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K136))) L137 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K136 K137 (stripK8 0 K136) (stripK8 0 K137) T136 L137
    slice136 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_136 lab8_136 (step136 inp env hI hm)

theorem stepS0_137 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L137) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K137))) L138 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K137 K138 (stripK8 0 K137) (stripK8 0 K138) T137 L138
    slice137 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_137 lab8_137 (step137 inp env hI hm)

theorem stepS0_138 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L138) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K138))) L139 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K138 K139 (stripK8 0 K138) (stripK8 0 K139) T138 L139
    slice138 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_138 lab8_138 (step138 inp env hI hm)

theorem stepS0_139 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L139) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K139))) L140 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K139 K140 (stripK8 0 K139) (stripK8 0 K140) T139 L140
    slice139 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_139 lab8_139 (step139 inp env hI hm)

theorem stepS0_140 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L140) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K140))) L141 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K140 K141 (stripK8 0 K140) (stripK8 0 K141) T140 L141
    slice140 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_140 lab8_140 (step140 inp env hI hm)

theorem stepS0_141 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L141) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K141))) L142 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K141 K142 (stripK8 0 K141) (stripK8 0 K142) T141 L142
    slice141 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_141 lab8_141 (step141 inp env hI hm)

theorem stepS0_142 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L142) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K142))) L143 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K142 K143 (stripK8 0 K142) (stripK8 0 K143) T142 L143
    slice142 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_142 lab8_142 (step142 inp env hI hm)

theorem stepS0_143 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L143) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K143))) L144 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K143 K144 (stripK8 0 K143) (stripK8 0 K144) T143 L144
    slice143 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_143 lab8_143 (step143 inp env hI hm)

theorem stepS0_144 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L144) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K144))) L145 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K144 K145 (stripK8 0 K144) (stripK8 0 K145) T144 L145
    slice144 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_144 lab8_144 (step144 inp env hI hm)

theorem stepS0_145 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L145) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K145))) L146 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K145 K146 (stripK8 0 K145) (stripK8 0 K146) T145 L146
    slice145 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_145 lab8_145 (step145 inp env hI hm)

theorem stepS0_146 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L146) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K146))) L147 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K146 K147 (stripK8 0 K146) (stripK8 0 K147) T146 L147
    slice146 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_146 lab8_146 (step146 inp env hI hm)

theorem stepS0_147 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L147) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K147))) L148 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K147 K148 (stripK8 0 K147) (stripK8 0 K148) T147 L148
    slice147 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_147 lab8_147 (step147 inp env hI hm)

theorem stepS0_148 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L148) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K148))) L149 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K148 K149 (stripK8 0 K148) (stripK8 0 K149) T148 L149
    slice148 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_148 lab8_148 (step148 inp env hI hm)

theorem stepS0_149 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L149) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K149))) L150 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K149 K150 (stripK8 0 K149) (stripK8 0 K150) T149 L150
    slice149 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_149 lab8_149 (step149 inp env hI hm)

theorem stepS0_150 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L150) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K150))) L151 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K150 K151 (stripK8 0 K150) (stripK8 0 K151) T150 L151
    slice150 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_150 lab8_150 (step150 inp env hI hm)

theorem stepS0_151 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L151) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K151))) L152 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K151 K152 (stripK8 0 K151) (stripK8 0 K152) T151 L152
    slice151 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_151 lab8_151 (step151 inp env hI hm)

theorem stepS0_152 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L152) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K152))) L153 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K152 K153 (stripK8 0 K152) (stripK8 0 K153) T152 L153
    slice152 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_152 lab8_152 (step152 inp env hI hm)

theorem stepS0_153 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L153) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K153))) L154 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K153 K154 (stripK8 0 K153) (stripK8 0 K154) T153 L154
    slice153 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_153 lab8_153 (step153 inp env hI hm)

theorem stepS0_154 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L154) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K154))) L155 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K154 K155 (stripK8 0 K154) (stripK8 0 K155) T154 L155
    slice154 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_154 lab8_154 (step154 inp env hI hm)

theorem stepS0_155 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L155) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K155))) L156 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K155 K156 (stripK8 0 K155) (stripK8 0 K156) T155 L156
    slice155 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_155 lab8_155 (step155 inp env hI hm)

theorem stepS0_156 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L156) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K156))) L157 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K156 K157 (stripK8 0 K156) (stripK8 0 K157) T156 L157
    slice156 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_156 lab8_156 (step156 inp env hI hm)

theorem stepS0_157 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L157) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K157))) L158 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K157 K158 (stripK8 0 K157) (stripK8 0 K158) T157 L158
    slice157 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_157 lab8_157 (step157 inp env hI hm)

theorem stepS0_158 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L158) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K158))) L159 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K158 K159 (stripK8 0 K158) (stripK8 0 K159) T158 L159
    slice158 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_158 lab8_158 (step158 inp env hI hm)

theorem stepS0_159 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L159) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K159))) L160 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K159 K160 (stripK8 0 K159) (stripK8 0 K160) T159 L160
    slice159 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_159 lab8_159 (step159 inp env hI hm)

theorem stepS0_160 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L160) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K160))) L161 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K160 K161 (stripK8 0 K160) (stripK8 0 K161) T160 L161
    slice160 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_160 lab8_160 (step160 inp env hI hm)

theorem stepS0_161 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L161) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K161))) L162 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K161 K162 (stripK8 0 K161) (stripK8 0 K162) T161 L162
    slice161 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_161 lab8_161 (step161 inp env hI hm)

theorem stepS0_162 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L162) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K162))) L163 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K162 K163 (stripK8 0 K162) (stripK8 0 K163) T162 L163
    slice162 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_162 lab8_162 (step162 inp env hI hm)

theorem stepS0_163 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L163) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K163))) L164 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K163 K164 (stripK8 0 K163) (stripK8 0 K164) T163 L164
    slice163 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_163 lab8_163 (step163 inp env hI hm)

theorem stepS0_164 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L164) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K164))) L165 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K164 K165 (stripK8 0 K164) (stripK8 0 K165) T164 L165
    slice164 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_164 lab8_164 (step164 inp env hI hm)

theorem stepS0_165 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L165) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K165))) L166 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K165 K166 (stripK8 0 K165) (stripK8 0 K166) T165 L166
    slice165 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_165 lab8_165 (step165 inp env hI hm)

theorem stepS0_166 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L166) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K166))) L167 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K166 K167 (stripK8 0 K166) (stripK8 0 K167) T166 L167
    slice166 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_166 lab8_166 (step166 inp env hI hm)

theorem stepS0_167 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L167) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K167))) L168 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K167 K168 (stripK8 0 K167) (stripK8 0 K168) T167 L168
    slice167 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_167 lab8_167 (step167 inp env hI hm)

theorem stepS0_168 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L168) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K168))) L169 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K168 K169 (stripK8 0 K168) (stripK8 0 K169) T168 L169
    slice168 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_168 lab8_168 (step168 inp env hI hm)

theorem stepS0_169 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L169) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K169))) L170 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K169 K170 (stripK8 0 K169) (stripK8 0 K170) T169 L170
    slice169 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_169 lab8_169 (step169 inp env hI hm)

theorem stepS0_170 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L170) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K170))) L171 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K170 K171 (stripK8 0 K170) (stripK8 0 K171) T170 L171
    slice170 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_170 lab8_170 (step170 inp env hI hm)

theorem stepS0_171 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L171) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K171))) L172 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K171 K172 (stripK8 0 K171) (stripK8 0 K172) T171 L172
    slice171 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_171 lab8_171 (step171 inp env hI hm)

theorem stepS0_172 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L172) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K172))) L173 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K172 K173 (stripK8 0 K172) (stripK8 0 K173) T172 L173
    slice172 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_172 lab8_172 (step172 inp env hI hm)

theorem stepS0_173 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L173) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K173))) L174 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K173 K174 (stripK8 0 K173) (stripK8 0 K174) T173 L174
    slice173 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_173 lab8_173 (step173 inp env hI hm)

theorem stepS0_174 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L174) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K174))) L175 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K174 K175 (stripK8 0 K174) (stripK8 0 K175) T174 L175
    slice174 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_174 lab8_174 (step174 inp env hI hm)

theorem stepS0_175 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L175) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K175))) L176 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K175 K176 (stripK8 0 K175) (stripK8 0 K176) T175 L176
    slice175 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_175 lab8_175 (step175 inp env hI hm)

theorem stepS0_176 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L176) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K176))) L177 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K176 K177 (stripK8 0 K176) (stripK8 0 K177) T176 L177
    slice176 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_176 lab8_176 (step176 inp env hI hm)

theorem stepS0_177 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L177) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K177))) L178 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K177 K178 (stripK8 0 K177) (stripK8 0 K178) T177 L178
    slice177 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_177 lab8_177 (step177 inp env hI hm)

theorem stepS0_178 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L178) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K178))) L179 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K178 K179 (stripK8 0 K178) (stripK8 0 K179) T178 L179
    slice178 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_178 lab8_178 (step178 inp env hI hm)

theorem stepS0_179 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L179) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K179))) L180 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K179 K180 (stripK8 0 K179) (stripK8 0 K180) T179 L180
    slice179 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_179 lab8_179 (step179 inp env hI hm)

theorem stepS0_180 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L180) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K180))) L181 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K180 K181 (stripK8 0 K180) (stripK8 0 K181) T180 L181
    slice180 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_180 lab8_180 (step180 inp env hI hm)

theorem stepS0_181 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L181) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K181))) L182 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K181 K182 (stripK8 0 K181) (stripK8 0 K182) T181 L182
    slice181 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_181 lab8_181 (step181 inp env hI hm)

theorem stepS0_182 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L182) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K182))) L183 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K182 K183 (stripK8 0 K182) (stripK8 0 K183) T182 L183
    slice182 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_182 lab8_182 (step182 inp env hI hm)

theorem stepS0_183 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L183) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K183))) L184 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K183 K184 (stripK8 0 K183) (stripK8 0 K184) T183 L184
    slice183 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_183 lab8_183 (step183 inp env hI hm)

theorem stepS0_184 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L184) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K184))) L185 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K184 K185 (stripK8 0 K184) (stripK8 0 K185) T184 L185
    slice184 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_184 lab8_184 (step184 inp env hI hm)

theorem stepS0_185 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L185) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K185))) L186 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K185 K186 (stripK8 0 K185) (stripK8 0 K186) T185 L186
    slice185 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_185 lab8_185 (step185 inp env hI hm)

theorem stepS0_186 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L186) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K186))) L187 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K186 K187 (stripK8 0 K186) (stripK8 0 K187) T186 L187
    slice186 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_186 lab8_186 (step186 inp env hI hm)

theorem stepS0_187 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L187) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K187))) L188 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K187 K188 (stripK8 0 K187) (stripK8 0 K188) T187 L188
    slice187 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_187 lab8_187 (step187 inp env hI hm)

theorem stepS0_188 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L188) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K188))) L189 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K188 K189 (stripK8 0 K188) (stripK8 0 K189) T188 L189
    slice188 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_188 lab8_188 (step188 inp env hI hm)

theorem stepS0_189 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L189) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 36 (stripK8 0 K189))) L190 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 36 K189 K190 (stripK8 0 K189) (stripK8 0 K190) T189 L190
    slice189 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_189 lab8_189 (step189 inp env hI hm)

theorem stepS0_190 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L190) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K190))) L191 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K190 K191 (stripK8 0 K190) (stripK8 0 K191) T190 L191
    slice190 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_190 lab8_190 (step190 inp env hI hm)

theorem stepS0_191 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L191) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K191))) L192 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K191 K192 (stripK8 0 K191) (stripK8 0 K192) T191 L192
    slice191 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_191 lab8_191 (step191 inp env hI hm)

theorem stepS0_192 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L192) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K192))) L193 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K192 K193 (stripK8 0 K192) (stripK8 0 K193) T192 L193
    slice192 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_192 lab8_192 (step192 inp env hI hm)

theorem stepS0_193 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L193) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K193))) L194 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K193 K194 (stripK8 0 K193) (stripK8 0 K194) T193 L194
    slice193 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_193 lab8_193 (step193 inp env hI hm)

theorem stepS0_194 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L194) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K194))) L195 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K194 K195 (stripK8 0 K194) (stripK8 0 K195) T194 L195
    slice194 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_194 lab8_194 (step194 inp env hI hm)

theorem stepS0_195 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L195) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K195))) L196 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K195 K196 (stripK8 0 K195) (stripK8 0 K196) T195 L196
    slice195 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_195 lab8_195 (step195 inp env hI hm)

theorem stepS0_196 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L196) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K196))) L197 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K196 K197 (stripK8 0 K196) (stripK8 0 K197) T196 L197
    slice196 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_196 lab8_196 (step196 inp env hI hm)

theorem stepS0_197 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L197) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K197))) L198 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K197 K198 (stripK8 0 K197) (stripK8 0 K198) T197 L198
    slice197 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_197 lab8_197 (step197 inp env hI hm)

theorem stepS0_198 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L198) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K198))) L199 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K198 K199 (stripK8 0 K198) (stripK8 0 K199) T198 L199
    slice198 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_198 lab8_198 (step198 inp env hI hm)

theorem stepS0_199 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L199) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K199))) L200 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K199 K200 (stripK8 0 K199) (stripK8 0 K200) T199 L200
    slice199 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_199 lab8_199 (step199 inp env hI hm)

theorem stepS0_200 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L200) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K200))) L201 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K200 K201 (stripK8 0 K200) (stripK8 0 K201) T200 L201
    slice200 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_200 lab8_200 (step200 inp env hI hm)

theorem stepS0_201 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L201) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K201))) L202 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K201 K202 (stripK8 0 K201) (stripK8 0 K202) T201 L202
    slice201 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_201 lab8_201 (step201 inp env hI hm)

theorem stepS0_202 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L202) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 3 (stripK8 0 K202))) L203 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 3 K202 K203 (stripK8 0 K202) (stripK8 0 K203) T202 L203
    slice202 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_202 lab8_202 (step202 inp env hI hm)

theorem stepS0_203 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L203) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K203))) L204 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K203 K204 (stripK8 0 K203) (stripK8 0 K204) T203 L204
    slice203 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_203 lab8_203 (step203 inp env hI hm)

theorem stepS0_204 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L204) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 1 (stripK8 0 K204))) L205 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 1 K204 K205 (stripK8 0 K204) (stripK8 0 K205) T204 L205
    slice204 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_204 lab8_204 (step204 inp env hI hm)

theorem stepS0_205 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L205) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K205))) L206 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K205 K206 (stripK8 0 K205) (stripK8 0 K206) T205 L206
    slice205 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_205 lab8_205 (step205 inp env hI hm)

theorem stepS0_206 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L206) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K206))) L207 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K206 K207 (stripK8 0 K206) (stripK8 0 K207) T206 L207
    slice206 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_206 lab8_206 (step206 inp env hI hm)

theorem stepS0_207 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L207) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K207))) L208 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K207 K208 (stripK8 0 K207) (stripK8 0 K208) T207 L208
    slice207 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_207 lab8_207 (step207 inp env hI hm)

theorem stepS0_208 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L208) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K208))) L209 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K208 K209 (stripK8 0 K208) (stripK8 0 K209) T208 L209
    slice208 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_208 lab8_208 (step208 inp env hI hm)

theorem stepS0_209 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L209) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 2 (stripK8 0 K209))) L210 :=
  invC_lift inp env prog 4 m0q (m8P 0) _ _ 2 K209 K210 (stripK8 0 K209) (stripK8 0 K210) T209 L210
    slice209 Hashtree.Proofs.Avx2X8WBodyR0S.sliceS_209 lab8_209 (step209 inp env hI hm)

theorem stepT0 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L210) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcB 27 (shiftK8 0 K210))) L211t :=
  invC_lift' inp env prog 4 m0q _ 31 K210 K211 m8 orcB 27 (shiftK8 0 K210) (KT 0) T210t L211t
    slice210t chkT_0 lab8_210t (invC_sub inp _ (step210 inp env hI hm))

theorem stepX0 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L210) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m8 orcEx 31 (shiftK8 0 K210))) L211t :=
  invC_lift inp env prog 4 m0q m8 _ orcEx 31 K210 K211 (shiftK8 0 K210) (KTE 0) T210t L211t
    slice210t chkX_0 lab8_210t (invC_sub inp _ (step210 inp env hI hm))

theorem stepTS0 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L210) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcB 27 (stripK8 0 K210))) L211t :=
  invC_lift' inp env prog 4 m0q _ 31 K210 K211 (m8P 0) orcB 27 (stripK8 0 K210) (KTs 0) T210t L211t
    slice210t chkTS_0 lab8_210t (invC_sub inp _ (step210 inp env hI hm))

theorem stepXS0 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L210) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 (m8P 0) orcEx 31 (stripK8 0 K210))) L211t :=
  invC_lift inp env prog 4 m0q (m8P 0) _ orcEx 31 K210 K211 (stripK8 0 K210) (KTEs 0) T210t L211t
    slice210t chkXS_0 lab8_210t (invC_sub inp _ (step210 inp env hI hm))

/-- The first-pass chain: from the empty invariant at the pass head to `L210`. -/
theorem invW0_body (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G210 env1) L210 := by
  have i2 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G2 env1) L2 := True.intro
  have i3 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G3 env1) L3 := stepW0_2 inp (Hashtree.Proofs.Avx2X8WBodyR0.G2 env1) i2 hm
  have i4 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G4 env1) L4 := stepW0_3 inp (Hashtree.Proofs.Avx2X8WBodyR0.G3 env1) i3 hm
  have i5 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G5 env1) L5 := stepW0_4 inp (Hashtree.Proofs.Avx2X8WBodyR0.G4 env1) i4 hm
  have i6 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G6 env1) L6 := stepW0_5 inp (Hashtree.Proofs.Avx2X8WBodyR0.G5 env1) i5 hm
  have i7 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G7 env1) L7 := stepW0_6 inp (Hashtree.Proofs.Avx2X8WBodyR0.G6 env1) i6 hm
  have i8 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G8 env1) L8 := stepW0_7 inp (Hashtree.Proofs.Avx2X8WBodyR0.G7 env1) i7 hm
  have i9 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G9 env1) L9 := stepW0_8 inp (Hashtree.Proofs.Avx2X8WBodyR0.G8 env1) i8 hm
  have i10 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G10 env1) L10 := stepW0_9 inp (Hashtree.Proofs.Avx2X8WBodyR0.G9 env1) i9 hm
  have i11 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G11 env1) L11 := stepW0_10 inp (Hashtree.Proofs.Avx2X8WBodyR0.G10 env1) i10 hm
  have i12 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G12 env1) L12 := stepW0_11 inp (Hashtree.Proofs.Avx2X8WBodyR0.G11 env1) i11 hm
  have i13 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G13 env1) L13 := stepW0_12 inp (Hashtree.Proofs.Avx2X8WBodyR0.G12 env1) i12 hm
  have i14 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G14 env1) L14 := stepW0_13 inp (Hashtree.Proofs.Avx2X8WBodyR0.G13 env1) i13 hm
  have i15 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G15 env1) L15 := stepW0_14 inp (Hashtree.Proofs.Avx2X8WBodyR0.G14 env1) i14 hm
  have i16 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G16 env1) L16 := stepW0_15 inp (Hashtree.Proofs.Avx2X8WBodyR0.G15 env1) i15 hm
  have i17 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G17 env1) L17 := stepW0_16 inp (Hashtree.Proofs.Avx2X8WBodyR0.G16 env1) i16 hm
  have i18 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G18 env1) L18 := stepW0_17 inp (Hashtree.Proofs.Avx2X8WBodyR0.G17 env1) i17 hm
  have i19 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G19 env1) L19 := stepW0_18 inp (Hashtree.Proofs.Avx2X8WBodyR0.G18 env1) i18 hm
  have i20 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G20 env1) L20 := stepW0_19 inp (Hashtree.Proofs.Avx2X8WBodyR0.G19 env1) i19 hm
  have i21 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G21 env1) L21 := stepW0_20 inp (Hashtree.Proofs.Avx2X8WBodyR0.G20 env1) i20 hm
  have i22 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G22 env1) L22 := stepW0_21 inp (Hashtree.Proofs.Avx2X8WBodyR0.G21 env1) i21 hm
  have i23 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G23 env1) L23 := stepW0_22 inp (Hashtree.Proofs.Avx2X8WBodyR0.G22 env1) i22 hm
  have i24 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G24 env1) L24 := stepW0_23 inp (Hashtree.Proofs.Avx2X8WBodyR0.G23 env1) i23 hm
  have i25 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G25 env1) L25 := stepW0_24 inp (Hashtree.Proofs.Avx2X8WBodyR0.G24 env1) i24 hm
  have i26 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G26 env1) L26 := stepW0_25 inp (Hashtree.Proofs.Avx2X8WBodyR0.G25 env1) i25 hm
  have i27 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G27 env1) L27 := stepW0_26 inp (Hashtree.Proofs.Avx2X8WBodyR0.G26 env1) i26 hm
  have i28 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G28 env1) L28 := stepW0_27 inp (Hashtree.Proofs.Avx2X8WBodyR0.G27 env1) i27 hm
  have i29 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G29 env1) L29 := stepW0_28 inp (Hashtree.Proofs.Avx2X8WBodyR0.G28 env1) i28 hm
  have i30 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G30 env1) L30 := stepW0_29 inp (Hashtree.Proofs.Avx2X8WBodyR0.G29 env1) i29 hm
  have i31 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G31 env1) L31 := stepW0_30 inp (Hashtree.Proofs.Avx2X8WBodyR0.G30 env1) i30 hm
  have i32 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G32 env1) L32 := stepW0_31 inp (Hashtree.Proofs.Avx2X8WBodyR0.G31 env1) i31 hm
  have i33 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G33 env1) L33 := stepW0_32 inp (Hashtree.Proofs.Avx2X8WBodyR0.G32 env1) i32 hm
  have i34 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G34 env1) L34 := stepW0_33 inp (Hashtree.Proofs.Avx2X8WBodyR0.G33 env1) i33 hm
  have i35 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G35 env1) L35 := stepW0_34 inp (Hashtree.Proofs.Avx2X8WBodyR0.G34 env1) i34 hm
  have i36 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G36 env1) L36 := stepW0_35 inp (Hashtree.Proofs.Avx2X8WBodyR0.G35 env1) i35 hm
  have i37 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G37 env1) L37 := stepW0_36 inp (Hashtree.Proofs.Avx2X8WBodyR0.G36 env1) i36 hm
  have i38 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G38 env1) L38 := stepW0_37 inp (Hashtree.Proofs.Avx2X8WBodyR0.G37 env1) i37 hm
  have i39 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G39 env1) L39 := stepW0_38 inp (Hashtree.Proofs.Avx2X8WBodyR0.G38 env1) i38 hm
  have i40 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G40 env1) L40 := stepW0_39 inp (Hashtree.Proofs.Avx2X8WBodyR0.G39 env1) i39 hm
  have i41 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G41 env1) L41 := stepW0_40 inp (Hashtree.Proofs.Avx2X8WBodyR0.G40 env1) i40 hm
  have i42 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G42 env1) L42 := stepW0_41 inp (Hashtree.Proofs.Avx2X8WBodyR0.G41 env1) i41 hm
  have i43 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G43 env1) L43 := stepW0_42 inp (Hashtree.Proofs.Avx2X8WBodyR0.G42 env1) i42 hm
  have i44 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G44 env1) L44 := stepW0_43 inp (Hashtree.Proofs.Avx2X8WBodyR0.G43 env1) i43 hm
  have i45 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G45 env1) L45 := stepW0_44 inp (Hashtree.Proofs.Avx2X8WBodyR0.G44 env1) i44 hm
  have i46 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G46 env1) L46 := stepW0_45 inp (Hashtree.Proofs.Avx2X8WBodyR0.G45 env1) i45 hm
  have i47 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G47 env1) L47 := stepW0_46 inp (Hashtree.Proofs.Avx2X8WBodyR0.G46 env1) i46 hm
  have i48 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G48 env1) L48 := stepW0_47 inp (Hashtree.Proofs.Avx2X8WBodyR0.G47 env1) i47 hm
  have i49 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G49 env1) L49 := stepW0_48 inp (Hashtree.Proofs.Avx2X8WBodyR0.G48 env1) i48 hm
  have i50 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G50 env1) L50 := stepW0_49 inp (Hashtree.Proofs.Avx2X8WBodyR0.G49 env1) i49 hm
  have i51 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G51 env1) L51 := stepW0_50 inp (Hashtree.Proofs.Avx2X8WBodyR0.G50 env1) i50 hm
  have i52 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G52 env1) L52 := stepW0_51 inp (Hashtree.Proofs.Avx2X8WBodyR0.G51 env1) i51 hm
  have i53 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G53 env1) L53 := stepW0_52 inp (Hashtree.Proofs.Avx2X8WBodyR0.G52 env1) i52 hm
  have i54 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G54 env1) L54 := stepW0_53 inp (Hashtree.Proofs.Avx2X8WBodyR0.G53 env1) i53 hm
  have i55 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G55 env1) L55 := stepW0_54 inp (Hashtree.Proofs.Avx2X8WBodyR0.G54 env1) i54 hm
  have i56 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G56 env1) L56 := stepW0_55 inp (Hashtree.Proofs.Avx2X8WBodyR0.G55 env1) i55 hm
  have i57 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G57 env1) L57 := stepW0_56 inp (Hashtree.Proofs.Avx2X8WBodyR0.G56 env1) i56 hm
  have i58 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G58 env1) L58 := stepW0_57 inp (Hashtree.Proofs.Avx2X8WBodyR0.G57 env1) i57 hm
  have i59 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G59 env1) L59 := stepW0_58 inp (Hashtree.Proofs.Avx2X8WBodyR0.G58 env1) i58 hm
  have i60 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G60 env1) L60 := stepW0_59 inp (Hashtree.Proofs.Avx2X8WBodyR0.G59 env1) i59 hm
  have i61 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G61 env1) L61 := stepW0_60 inp (Hashtree.Proofs.Avx2X8WBodyR0.G60 env1) i60 hm
  have i62 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G62 env1) L62 := stepW0_61 inp (Hashtree.Proofs.Avx2X8WBodyR0.G61 env1) i61 hm
  have i63 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G63 env1) L63 := stepW0_62 inp (Hashtree.Proofs.Avx2X8WBodyR0.G62 env1) i62 hm
  have i64 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G64 env1) L64 := stepW0_63 inp (Hashtree.Proofs.Avx2X8WBodyR0.G63 env1) i63 hm
  have i65 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G65 env1) L65 := stepW0_64 inp (Hashtree.Proofs.Avx2X8WBodyR0.G64 env1) i64 hm
  have i66 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G66 env1) L66 := stepW0_65 inp (Hashtree.Proofs.Avx2X8WBodyR0.G65 env1) i65 hm
  have i67 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G67 env1) L67 := stepW0_66 inp (Hashtree.Proofs.Avx2X8WBodyR0.G66 env1) i66 hm
  have i68 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G68 env1) L68 := stepW0_67 inp (Hashtree.Proofs.Avx2X8WBodyR0.G67 env1) i67 hm
  have i69 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G69 env1) L69 := stepW0_68 inp (Hashtree.Proofs.Avx2X8WBodyR0.G68 env1) i68 hm
  have i70 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G70 env1) L70 := stepW0_69 inp (Hashtree.Proofs.Avx2X8WBodyR0.G69 env1) i69 hm
  have i71 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G71 env1) L71 := stepW0_70 inp (Hashtree.Proofs.Avx2X8WBodyR0.G70 env1) i70 hm
  have i72 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G72 env1) L72 := stepW0_71 inp (Hashtree.Proofs.Avx2X8WBodyR0.G71 env1) i71 hm
  have i73 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G73 env1) L73 := stepW0_72 inp (Hashtree.Proofs.Avx2X8WBodyR0.G72 env1) i72 hm
  have i74 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G74 env1) L74 := stepW0_73 inp (Hashtree.Proofs.Avx2X8WBodyR0.G73 env1) i73 hm
  have i75 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G75 env1) L75 := stepW0_74 inp (Hashtree.Proofs.Avx2X8WBodyR0.G74 env1) i74 hm
  have i76 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G76 env1) L76 := stepW0_75 inp (Hashtree.Proofs.Avx2X8WBodyR0.G75 env1) i75 hm
  have i77 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G77 env1) L77 := stepW0_76 inp (Hashtree.Proofs.Avx2X8WBodyR0.G76 env1) i76 hm
  have i78 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G78 env1) L78 := stepW0_77 inp (Hashtree.Proofs.Avx2X8WBodyR0.G77 env1) i77 hm
  have i79 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G79 env1) L79 := stepW0_78 inp (Hashtree.Proofs.Avx2X8WBodyR0.G78 env1) i78 hm
  have i80 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G80 env1) L80 := stepW0_79 inp (Hashtree.Proofs.Avx2X8WBodyR0.G79 env1) i79 hm
  have i81 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G81 env1) L81 := stepW0_80 inp (Hashtree.Proofs.Avx2X8WBodyR0.G80 env1) i80 hm
  have i82 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G82 env1) L82 := stepW0_81 inp (Hashtree.Proofs.Avx2X8WBodyR0.G81 env1) i81 hm
  have i83 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G83 env1) L83 := stepW0_82 inp (Hashtree.Proofs.Avx2X8WBodyR0.G82 env1) i82 hm
  have i84 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G84 env1) L84 := stepW0_83 inp (Hashtree.Proofs.Avx2X8WBodyR0.G83 env1) i83 hm
  have i85 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G85 env1) L85 := stepW0_84 inp (Hashtree.Proofs.Avx2X8WBodyR0.G84 env1) i84 hm
  have i86 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G86 env1) L86 := stepW0_85 inp (Hashtree.Proofs.Avx2X8WBodyR0.G85 env1) i85 hm
  have i87 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G87 env1) L87 := stepW0_86 inp (Hashtree.Proofs.Avx2X8WBodyR0.G86 env1) i86 hm
  have i88 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G88 env1) L88 := stepW0_87 inp (Hashtree.Proofs.Avx2X8WBodyR0.G87 env1) i87 hm
  have i89 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G89 env1) L89 := stepW0_88 inp (Hashtree.Proofs.Avx2X8WBodyR0.G88 env1) i88 hm
  have i90 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G90 env1) L90 := stepW0_89 inp (Hashtree.Proofs.Avx2X8WBodyR0.G89 env1) i89 hm
  have i91 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G91 env1) L91 := stepW0_90 inp (Hashtree.Proofs.Avx2X8WBodyR0.G90 env1) i90 hm
  have i92 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G92 env1) L92 := stepW0_91 inp (Hashtree.Proofs.Avx2X8WBodyR0.G91 env1) i91 hm
  have i93 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G93 env1) L93 := stepW0_92 inp (Hashtree.Proofs.Avx2X8WBodyR0.G92 env1) i92 hm
  have i94 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G94 env1) L94 := stepW0_93 inp (Hashtree.Proofs.Avx2X8WBodyR0.G93 env1) i93 hm
  have i95 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G95 env1) L95 := stepW0_94 inp (Hashtree.Proofs.Avx2X8WBodyR0.G94 env1) i94 hm
  have i96 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G96 env1) L96 := stepW0_95 inp (Hashtree.Proofs.Avx2X8WBodyR0.G95 env1) i95 hm
  have i97 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G97 env1) L97 := stepW0_96 inp (Hashtree.Proofs.Avx2X8WBodyR0.G96 env1) i96 hm
  have i98 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G98 env1) L98 := stepW0_97 inp (Hashtree.Proofs.Avx2X8WBodyR0.G97 env1) i97 hm
  have i99 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G99 env1) L99 := stepW0_98 inp (Hashtree.Proofs.Avx2X8WBodyR0.G98 env1) i98 hm
  have i100 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G100 env1) L100 := stepW0_99 inp (Hashtree.Proofs.Avx2X8WBodyR0.G99 env1) i99 hm
  have i101 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G101 env1) L101 := stepW0_100 inp (Hashtree.Proofs.Avx2X8WBodyR0.G100 env1) i100 hm
  have i102 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G102 env1) L102 := stepW0_101 inp (Hashtree.Proofs.Avx2X8WBodyR0.G101 env1) i101 hm
  have i103 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G103 env1) L103 := stepW0_102 inp (Hashtree.Proofs.Avx2X8WBodyR0.G102 env1) i102 hm
  have i104 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G104 env1) L104 := stepW0_103 inp (Hashtree.Proofs.Avx2X8WBodyR0.G103 env1) i103 hm
  have i105 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G105 env1) L105 := stepW0_104 inp (Hashtree.Proofs.Avx2X8WBodyR0.G104 env1) i104 hm
  have i106 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G106 env1) L106 := stepW0_105 inp (Hashtree.Proofs.Avx2X8WBodyR0.G105 env1) i105 hm
  have i107 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G107 env1) L107 := stepW0_106 inp (Hashtree.Proofs.Avx2X8WBodyR0.G106 env1) i106 hm
  have i108 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G108 env1) L108 := stepW0_107 inp (Hashtree.Proofs.Avx2X8WBodyR0.G107 env1) i107 hm
  have i109 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G109 env1) L109 := stepW0_108 inp (Hashtree.Proofs.Avx2X8WBodyR0.G108 env1) i108 hm
  have i110 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G110 env1) L110 := stepW0_109 inp (Hashtree.Proofs.Avx2X8WBodyR0.G109 env1) i109 hm
  have i111 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G111 env1) L111 := stepW0_110 inp (Hashtree.Proofs.Avx2X8WBodyR0.G110 env1) i110 hm
  have i112 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G112 env1) L112 := stepW0_111 inp (Hashtree.Proofs.Avx2X8WBodyR0.G111 env1) i111 hm
  have i113 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G113 env1) L113 := stepW0_112 inp (Hashtree.Proofs.Avx2X8WBodyR0.G112 env1) i112 hm
  have i114 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G114 env1) L114 := stepW0_113 inp (Hashtree.Proofs.Avx2X8WBodyR0.G113 env1) i113 hm
  have i115 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G115 env1) L115 := stepW0_114 inp (Hashtree.Proofs.Avx2X8WBodyR0.G114 env1) i114 hm
  have i116 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G116 env1) L116 := stepW0_115 inp (Hashtree.Proofs.Avx2X8WBodyR0.G115 env1) i115 hm
  have i117 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G117 env1) L117 := stepW0_116 inp (Hashtree.Proofs.Avx2X8WBodyR0.G116 env1) i116 hm
  have i118 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G118 env1) L118 := stepW0_117 inp (Hashtree.Proofs.Avx2X8WBodyR0.G117 env1) i117 hm
  have i119 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G119 env1) L119 := stepW0_118 inp (Hashtree.Proofs.Avx2X8WBodyR0.G118 env1) i118 hm
  have i120 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G120 env1) L120 := stepW0_119 inp (Hashtree.Proofs.Avx2X8WBodyR0.G119 env1) i119 hm
  have i121 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G121 env1) L121 := stepW0_120 inp (Hashtree.Proofs.Avx2X8WBodyR0.G120 env1) i120 hm
  have i122 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G122 env1) L122 := stepW0_121 inp (Hashtree.Proofs.Avx2X8WBodyR0.G121 env1) i121 hm
  have i123 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G123 env1) L123 := stepW0_122 inp (Hashtree.Proofs.Avx2X8WBodyR0.G122 env1) i122 hm
  have i124 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G124 env1) L124 := stepW0_123 inp (Hashtree.Proofs.Avx2X8WBodyR0.G123 env1) i123 hm
  have i125 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G125 env1) L125 := stepW0_124 inp (Hashtree.Proofs.Avx2X8WBodyR0.G124 env1) i124 hm
  have i126 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G126 env1) L126 := stepW0_125 inp (Hashtree.Proofs.Avx2X8WBodyR0.G125 env1) i125 hm
  have i127 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G127 env1) L127 := stepW0_126 inp (Hashtree.Proofs.Avx2X8WBodyR0.G126 env1) i126 hm
  have i128 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G128 env1) L128 := stepW0_127 inp (Hashtree.Proofs.Avx2X8WBodyR0.G127 env1) i127 hm
  have i129 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G129 env1) L129 := stepW0_128 inp (Hashtree.Proofs.Avx2X8WBodyR0.G128 env1) i128 hm
  have i130 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G130 env1) L130 := stepW0_129 inp (Hashtree.Proofs.Avx2X8WBodyR0.G129 env1) i129 hm
  have i131 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G131 env1) L131 := stepW0_130 inp (Hashtree.Proofs.Avx2X8WBodyR0.G130 env1) i130 hm
  have i132 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G132 env1) L132 := stepW0_131 inp (Hashtree.Proofs.Avx2X8WBodyR0.G131 env1) i131 hm
  have i133 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G133 env1) L133 := stepW0_132 inp (Hashtree.Proofs.Avx2X8WBodyR0.G132 env1) i132 hm
  have i134 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G134 env1) L134 := stepW0_133 inp (Hashtree.Proofs.Avx2X8WBodyR0.G133 env1) i133 hm
  have i135 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G135 env1) L135 := stepW0_134 inp (Hashtree.Proofs.Avx2X8WBodyR0.G134 env1) i134 hm
  have i136 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G136 env1) L136 := stepW0_135 inp (Hashtree.Proofs.Avx2X8WBodyR0.G135 env1) i135 hm
  have i137 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G137 env1) L137 := stepW0_136 inp (Hashtree.Proofs.Avx2X8WBodyR0.G136 env1) i136 hm
  have i138 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G138 env1) L138 := stepW0_137 inp (Hashtree.Proofs.Avx2X8WBodyR0.G137 env1) i137 hm
  have i139 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G139 env1) L139 := stepW0_138 inp (Hashtree.Proofs.Avx2X8WBodyR0.G138 env1) i138 hm
  have i140 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G140 env1) L140 := stepW0_139 inp (Hashtree.Proofs.Avx2X8WBodyR0.G139 env1) i139 hm
  have i141 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G141 env1) L141 := stepW0_140 inp (Hashtree.Proofs.Avx2X8WBodyR0.G140 env1) i140 hm
  have i142 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G142 env1) L142 := stepW0_141 inp (Hashtree.Proofs.Avx2X8WBodyR0.G141 env1) i141 hm
  have i143 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G143 env1) L143 := stepW0_142 inp (Hashtree.Proofs.Avx2X8WBodyR0.G142 env1) i142 hm
  have i144 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G144 env1) L144 := stepW0_143 inp (Hashtree.Proofs.Avx2X8WBodyR0.G143 env1) i143 hm
  have i145 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G145 env1) L145 := stepW0_144 inp (Hashtree.Proofs.Avx2X8WBodyR0.G144 env1) i144 hm
  have i146 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G146 env1) L146 := stepW0_145 inp (Hashtree.Proofs.Avx2X8WBodyR0.G145 env1) i145 hm
  have i147 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G147 env1) L147 := stepW0_146 inp (Hashtree.Proofs.Avx2X8WBodyR0.G146 env1) i146 hm
  have i148 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G148 env1) L148 := stepW0_147 inp (Hashtree.Proofs.Avx2X8WBodyR0.G147 env1) i147 hm
  have i149 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G149 env1) L149 := stepW0_148 inp (Hashtree.Proofs.Avx2X8WBodyR0.G148 env1) i148 hm
  have i150 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G150 env1) L150 := stepW0_149 inp (Hashtree.Proofs.Avx2X8WBodyR0.G149 env1) i149 hm
  have i151 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G151 env1) L151 := stepW0_150 inp (Hashtree.Proofs.Avx2X8WBodyR0.G150 env1) i150 hm
  have i152 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G152 env1) L152 := stepW0_151 inp (Hashtree.Proofs.Avx2X8WBodyR0.G151 env1) i151 hm
  have i153 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G153 env1) L153 := stepW0_152 inp (Hashtree.Proofs.Avx2X8WBodyR0.G152 env1) i152 hm
  have i154 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G154 env1) L154 := stepW0_153 inp (Hashtree.Proofs.Avx2X8WBodyR0.G153 env1) i153 hm
  have i155 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G155 env1) L155 := stepW0_154 inp (Hashtree.Proofs.Avx2X8WBodyR0.G154 env1) i154 hm
  have i156 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G156 env1) L156 := stepW0_155 inp (Hashtree.Proofs.Avx2X8WBodyR0.G155 env1) i155 hm
  have i157 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G157 env1) L157 := stepW0_156 inp (Hashtree.Proofs.Avx2X8WBodyR0.G156 env1) i156 hm
  have i158 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G158 env1) L158 := stepW0_157 inp (Hashtree.Proofs.Avx2X8WBodyR0.G157 env1) i157 hm
  have i159 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G159 env1) L159 := stepW0_158 inp (Hashtree.Proofs.Avx2X8WBodyR0.G158 env1) i158 hm
  have i160 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G160 env1) L160 := stepW0_159 inp (Hashtree.Proofs.Avx2X8WBodyR0.G159 env1) i159 hm
  have i161 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G161 env1) L161 := stepW0_160 inp (Hashtree.Proofs.Avx2X8WBodyR0.G160 env1) i160 hm
  have i162 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G162 env1) L162 := stepW0_161 inp (Hashtree.Proofs.Avx2X8WBodyR0.G161 env1) i161 hm
  have i163 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G163 env1) L163 := stepW0_162 inp (Hashtree.Proofs.Avx2X8WBodyR0.G162 env1) i162 hm
  have i164 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G164 env1) L164 := stepW0_163 inp (Hashtree.Proofs.Avx2X8WBodyR0.G163 env1) i163 hm
  have i165 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G165 env1) L165 := stepW0_164 inp (Hashtree.Proofs.Avx2X8WBodyR0.G164 env1) i164 hm
  have i166 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G166 env1) L166 := stepW0_165 inp (Hashtree.Proofs.Avx2X8WBodyR0.G165 env1) i165 hm
  have i167 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G167 env1) L167 := stepW0_166 inp (Hashtree.Proofs.Avx2X8WBodyR0.G166 env1) i166 hm
  have i168 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G168 env1) L168 := stepW0_167 inp (Hashtree.Proofs.Avx2X8WBodyR0.G167 env1) i167 hm
  have i169 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G169 env1) L169 := stepW0_168 inp (Hashtree.Proofs.Avx2X8WBodyR0.G168 env1) i168 hm
  have i170 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G170 env1) L170 := stepW0_169 inp (Hashtree.Proofs.Avx2X8WBodyR0.G169 env1) i169 hm
  have i171 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G171 env1) L171 := stepW0_170 inp (Hashtree.Proofs.Avx2X8WBodyR0.G170 env1) i170 hm
  have i172 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G172 env1) L172 := stepW0_171 inp (Hashtree.Proofs.Avx2X8WBodyR0.G171 env1) i171 hm
  have i173 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G173 env1) L173 := stepW0_172 inp (Hashtree.Proofs.Avx2X8WBodyR0.G172 env1) i172 hm
  have i174 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G174 env1) L174 := stepW0_173 inp (Hashtree.Proofs.Avx2X8WBodyR0.G173 env1) i173 hm
  have i175 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G175 env1) L175 := stepW0_174 inp (Hashtree.Proofs.Avx2X8WBodyR0.G174 env1) i174 hm
  have i176 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G176 env1) L176 := stepW0_175 inp (Hashtree.Proofs.Avx2X8WBodyR0.G175 env1) i175 hm
  have i177 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G177 env1) L177 := stepW0_176 inp (Hashtree.Proofs.Avx2X8WBodyR0.G176 env1) i176 hm
  have i178 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G178 env1) L178 := stepW0_177 inp (Hashtree.Proofs.Avx2X8WBodyR0.G177 env1) i177 hm
  have i179 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G179 env1) L179 := stepW0_178 inp (Hashtree.Proofs.Avx2X8WBodyR0.G178 env1) i178 hm
  have i180 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G180 env1) L180 := stepW0_179 inp (Hashtree.Proofs.Avx2X8WBodyR0.G179 env1) i179 hm
  have i181 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G181 env1) L181 := stepW0_180 inp (Hashtree.Proofs.Avx2X8WBodyR0.G180 env1) i180 hm
  have i182 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G182 env1) L182 := stepW0_181 inp (Hashtree.Proofs.Avx2X8WBodyR0.G181 env1) i181 hm
  have i183 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G183 env1) L183 := stepW0_182 inp (Hashtree.Proofs.Avx2X8WBodyR0.G182 env1) i182 hm
  have i184 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G184 env1) L184 := stepW0_183 inp (Hashtree.Proofs.Avx2X8WBodyR0.G183 env1) i183 hm
  have i185 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G185 env1) L185 := stepW0_184 inp (Hashtree.Proofs.Avx2X8WBodyR0.G184 env1) i184 hm
  have i186 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G186 env1) L186 := stepW0_185 inp (Hashtree.Proofs.Avx2X8WBodyR0.G185 env1) i185 hm
  have i187 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G187 env1) L187 := stepW0_186 inp (Hashtree.Proofs.Avx2X8WBodyR0.G186 env1) i186 hm
  have i188 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G188 env1) L188 := stepW0_187 inp (Hashtree.Proofs.Avx2X8WBodyR0.G187 env1) i187 hm
  have i189 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G189 env1) L189 := stepW0_188 inp (Hashtree.Proofs.Avx2X8WBodyR0.G188 env1) i188 hm
  have i190 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G190 env1) L190 := stepW0_189 inp (Hashtree.Proofs.Avx2X8WBodyR0.G189 env1) i189 hm
  have i191 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G191 env1) L191 := stepW0_190 inp (Hashtree.Proofs.Avx2X8WBodyR0.G190 env1) i190 hm
  have i192 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G192 env1) L192 := stepW0_191 inp (Hashtree.Proofs.Avx2X8WBodyR0.G191 env1) i191 hm
  have i193 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G193 env1) L193 := stepW0_192 inp (Hashtree.Proofs.Avx2X8WBodyR0.G192 env1) i192 hm
  have i194 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G194 env1) L194 := stepW0_193 inp (Hashtree.Proofs.Avx2X8WBodyR0.G193 env1) i193 hm
  have i195 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G195 env1) L195 := stepW0_194 inp (Hashtree.Proofs.Avx2X8WBodyR0.G194 env1) i194 hm
  have i196 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G196 env1) L196 := stepW0_195 inp (Hashtree.Proofs.Avx2X8WBodyR0.G195 env1) i195 hm
  have i197 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G197 env1) L197 := stepW0_196 inp (Hashtree.Proofs.Avx2X8WBodyR0.G196 env1) i196 hm
  have i198 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G198 env1) L198 := stepW0_197 inp (Hashtree.Proofs.Avx2X8WBodyR0.G197 env1) i197 hm
  have i199 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G199 env1) L199 := stepW0_198 inp (Hashtree.Proofs.Avx2X8WBodyR0.G198 env1) i198 hm
  have i200 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G200 env1) L200 := stepW0_199 inp (Hashtree.Proofs.Avx2X8WBodyR0.G199 env1) i199 hm
  have i201 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G201 env1) L201 := stepW0_200 inp (Hashtree.Proofs.Avx2X8WBodyR0.G200 env1) i200 hm
  have i202 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G202 env1) L202 := stepW0_201 inp (Hashtree.Proofs.Avx2X8WBodyR0.G201 env1) i201 hm
  have i203 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G203 env1) L203 := stepW0_202 inp (Hashtree.Proofs.Avx2X8WBodyR0.G202 env1) i202 hm
  have i204 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G204 env1) L204 := stepW0_203 inp (Hashtree.Proofs.Avx2X8WBodyR0.G203 env1) i203 hm
  have i205 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G205 env1) L205 := stepW0_204 inp (Hashtree.Proofs.Avx2X8WBodyR0.G204 env1) i204 hm
  have i206 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G206 env1) L206 := stepW0_205 inp (Hashtree.Proofs.Avx2X8WBodyR0.G205 env1) i205 hm
  have i207 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G207 env1) L207 := stepW0_206 inp (Hashtree.Proofs.Avx2X8WBodyR0.G206 env1) i206 hm
  have i208 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G208 env1) L208 := stepW0_207 inp (Hashtree.Proofs.Avx2X8WBodyR0.G207 env1) i207 hm
  have i209 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G209 env1) L209 := stepW0_208 inp (Hashtree.Proofs.Avx2X8WBodyR0.G208 env1) i208 hm
  have i210 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0.G210 env1) L210 := stepW0_209 inp (Hashtree.Proofs.Avx2X8WBodyR0.G209 env1) i209 hm
  exact i210

/-- The later-pass chain: from the empty invariant at the pass head to `L210`. -/
theorem invS0_body (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS210 env1) L210 := by
  have i2 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS2 env1) L2 := True.intro
  have i3 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS3 env1) L3 := stepS0_2 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS2 env1) i2 hm
  have i4 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS4 env1) L4 := stepS0_3 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS3 env1) i3 hm
  have i5 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS5 env1) L5 := stepS0_4 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS4 env1) i4 hm
  have i6 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS6 env1) L6 := stepS0_5 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS5 env1) i5 hm
  have i7 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS7 env1) L7 := stepS0_6 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS6 env1) i6 hm
  have i8 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS8 env1) L8 := stepS0_7 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS7 env1) i7 hm
  have i9 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS9 env1) L9 := stepS0_8 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS8 env1) i8 hm
  have i10 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS10 env1) L10 := stepS0_9 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS9 env1) i9 hm
  have i11 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS11 env1) L11 := stepS0_10 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS10 env1) i10 hm
  have i12 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS12 env1) L12 := stepS0_11 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS11 env1) i11 hm
  have i13 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS13 env1) L13 := stepS0_12 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS12 env1) i12 hm
  have i14 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS14 env1) L14 := stepS0_13 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS13 env1) i13 hm
  have i15 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS15 env1) L15 := stepS0_14 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS14 env1) i14 hm
  have i16 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS16 env1) L16 := stepS0_15 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS15 env1) i15 hm
  have i17 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS17 env1) L17 := stepS0_16 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS16 env1) i16 hm
  have i18 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS18 env1) L18 := stepS0_17 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS17 env1) i17 hm
  have i19 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS19 env1) L19 := stepS0_18 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS18 env1) i18 hm
  have i20 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS20 env1) L20 := stepS0_19 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS19 env1) i19 hm
  have i21 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS21 env1) L21 := stepS0_20 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS20 env1) i20 hm
  have i22 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS22 env1) L22 := stepS0_21 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS21 env1) i21 hm
  have i23 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS23 env1) L23 := stepS0_22 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS22 env1) i22 hm
  have i24 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS24 env1) L24 := stepS0_23 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS23 env1) i23 hm
  have i25 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS25 env1) L25 := stepS0_24 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS24 env1) i24 hm
  have i26 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS26 env1) L26 := stepS0_25 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS25 env1) i25 hm
  have i27 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS27 env1) L27 := stepS0_26 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS26 env1) i26 hm
  have i28 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS28 env1) L28 := stepS0_27 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS27 env1) i27 hm
  have i29 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS29 env1) L29 := stepS0_28 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS28 env1) i28 hm
  have i30 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS30 env1) L30 := stepS0_29 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS29 env1) i29 hm
  have i31 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS31 env1) L31 := stepS0_30 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS30 env1) i30 hm
  have i32 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS32 env1) L32 := stepS0_31 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS31 env1) i31 hm
  have i33 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS33 env1) L33 := stepS0_32 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS32 env1) i32 hm
  have i34 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS34 env1) L34 := stepS0_33 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS33 env1) i33 hm
  have i35 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS35 env1) L35 := stepS0_34 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS34 env1) i34 hm
  have i36 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS36 env1) L36 := stepS0_35 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS35 env1) i35 hm
  have i37 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS37 env1) L37 := stepS0_36 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS36 env1) i36 hm
  have i38 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS38 env1) L38 := stepS0_37 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS37 env1) i37 hm
  have i39 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS39 env1) L39 := stepS0_38 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS38 env1) i38 hm
  have i40 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS40 env1) L40 := stepS0_39 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS39 env1) i39 hm
  have i41 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS41 env1) L41 := stepS0_40 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS40 env1) i40 hm
  have i42 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS42 env1) L42 := stepS0_41 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS41 env1) i41 hm
  have i43 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS43 env1) L43 := stepS0_42 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS42 env1) i42 hm
  have i44 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS44 env1) L44 := stepS0_43 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS43 env1) i43 hm
  have i45 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS45 env1) L45 := stepS0_44 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS44 env1) i44 hm
  have i46 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS46 env1) L46 := stepS0_45 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS45 env1) i45 hm
  have i47 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS47 env1) L47 := stepS0_46 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS46 env1) i46 hm
  have i48 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS48 env1) L48 := stepS0_47 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS47 env1) i47 hm
  have i49 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS49 env1) L49 := stepS0_48 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS48 env1) i48 hm
  have i50 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS50 env1) L50 := stepS0_49 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS49 env1) i49 hm
  have i51 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS51 env1) L51 := stepS0_50 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS50 env1) i50 hm
  have i52 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS52 env1) L52 := stepS0_51 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS51 env1) i51 hm
  have i53 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS53 env1) L53 := stepS0_52 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS52 env1) i52 hm
  have i54 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS54 env1) L54 := stepS0_53 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS53 env1) i53 hm
  have i55 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS55 env1) L55 := stepS0_54 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS54 env1) i54 hm
  have i56 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS56 env1) L56 := stepS0_55 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS55 env1) i55 hm
  have i57 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS57 env1) L57 := stepS0_56 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS56 env1) i56 hm
  have i58 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS58 env1) L58 := stepS0_57 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS57 env1) i57 hm
  have i59 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS59 env1) L59 := stepS0_58 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS58 env1) i58 hm
  have i60 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS60 env1) L60 := stepS0_59 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS59 env1) i59 hm
  have i61 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS61 env1) L61 := stepS0_60 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS60 env1) i60 hm
  have i62 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS62 env1) L62 := stepS0_61 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS61 env1) i61 hm
  have i63 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS63 env1) L63 := stepS0_62 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS62 env1) i62 hm
  have i64 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS64 env1) L64 := stepS0_63 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS63 env1) i63 hm
  have i65 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS65 env1) L65 := stepS0_64 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS64 env1) i64 hm
  have i66 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS66 env1) L66 := stepS0_65 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS65 env1) i65 hm
  have i67 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS67 env1) L67 := stepS0_66 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS66 env1) i66 hm
  have i68 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS68 env1) L68 := stepS0_67 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS67 env1) i67 hm
  have i69 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS69 env1) L69 := stepS0_68 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS68 env1) i68 hm
  have i70 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS70 env1) L70 := stepS0_69 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS69 env1) i69 hm
  have i71 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS71 env1) L71 := stepS0_70 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS70 env1) i70 hm
  have i72 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS72 env1) L72 := stepS0_71 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS71 env1) i71 hm
  have i73 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS73 env1) L73 := stepS0_72 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS72 env1) i72 hm
  have i74 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS74 env1) L74 := stepS0_73 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS73 env1) i73 hm
  have i75 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS75 env1) L75 := stepS0_74 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS74 env1) i74 hm
  have i76 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS76 env1) L76 := stepS0_75 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS75 env1) i75 hm
  have i77 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS77 env1) L77 := stepS0_76 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS76 env1) i76 hm
  have i78 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS78 env1) L78 := stepS0_77 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS77 env1) i77 hm
  have i79 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS79 env1) L79 := stepS0_78 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS78 env1) i78 hm
  have i80 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS80 env1) L80 := stepS0_79 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS79 env1) i79 hm
  have i81 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS81 env1) L81 := stepS0_80 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS80 env1) i80 hm
  have i82 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS82 env1) L82 := stepS0_81 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS81 env1) i81 hm
  have i83 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS83 env1) L83 := stepS0_82 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS82 env1) i82 hm
  have i84 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS84 env1) L84 := stepS0_83 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS83 env1) i83 hm
  have i85 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS85 env1) L85 := stepS0_84 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS84 env1) i84 hm
  have i86 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS86 env1) L86 := stepS0_85 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS85 env1) i85 hm
  have i87 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS87 env1) L87 := stepS0_86 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS86 env1) i86 hm
  have i88 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS88 env1) L88 := stepS0_87 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS87 env1) i87 hm
  have i89 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS89 env1) L89 := stepS0_88 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS88 env1) i88 hm
  have i90 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS90 env1) L90 := stepS0_89 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS89 env1) i89 hm
  have i91 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS91 env1) L91 := stepS0_90 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS90 env1) i90 hm
  have i92 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS92 env1) L92 := stepS0_91 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS91 env1) i91 hm
  have i93 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS93 env1) L93 := stepS0_92 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS92 env1) i92 hm
  have i94 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS94 env1) L94 := stepS0_93 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS93 env1) i93 hm
  have i95 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS95 env1) L95 := stepS0_94 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS94 env1) i94 hm
  have i96 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS96 env1) L96 := stepS0_95 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS95 env1) i95 hm
  have i97 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS97 env1) L97 := stepS0_96 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS96 env1) i96 hm
  have i98 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS98 env1) L98 := stepS0_97 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS97 env1) i97 hm
  have i99 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS99 env1) L99 := stepS0_98 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS98 env1) i98 hm
  have i100 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS100 env1) L100 := stepS0_99 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS99 env1) i99 hm
  have i101 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS101 env1) L101 := stepS0_100 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS100 env1) i100 hm
  have i102 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS102 env1) L102 := stepS0_101 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS101 env1) i101 hm
  have i103 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS103 env1) L103 := stepS0_102 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS102 env1) i102 hm
  have i104 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS104 env1) L104 := stepS0_103 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS103 env1) i103 hm
  have i105 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS105 env1) L105 := stepS0_104 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS104 env1) i104 hm
  have i106 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS106 env1) L106 := stepS0_105 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS105 env1) i105 hm
  have i107 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS107 env1) L107 := stepS0_106 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS106 env1) i106 hm
  have i108 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS108 env1) L108 := stepS0_107 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS107 env1) i107 hm
  have i109 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS109 env1) L109 := stepS0_108 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS108 env1) i108 hm
  have i110 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS110 env1) L110 := stepS0_109 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS109 env1) i109 hm
  have i111 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS111 env1) L111 := stepS0_110 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS110 env1) i110 hm
  have i112 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS112 env1) L112 := stepS0_111 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS111 env1) i111 hm
  have i113 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS113 env1) L113 := stepS0_112 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS112 env1) i112 hm
  have i114 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS114 env1) L114 := stepS0_113 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS113 env1) i113 hm
  have i115 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS115 env1) L115 := stepS0_114 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS114 env1) i114 hm
  have i116 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS116 env1) L116 := stepS0_115 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS115 env1) i115 hm
  have i117 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS117 env1) L117 := stepS0_116 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS116 env1) i116 hm
  have i118 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS118 env1) L118 := stepS0_117 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS117 env1) i117 hm
  have i119 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS119 env1) L119 := stepS0_118 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS118 env1) i118 hm
  have i120 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS120 env1) L120 := stepS0_119 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS119 env1) i119 hm
  have i121 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS121 env1) L121 := stepS0_120 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS120 env1) i120 hm
  have i122 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS122 env1) L122 := stepS0_121 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS121 env1) i121 hm
  have i123 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS123 env1) L123 := stepS0_122 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS122 env1) i122 hm
  have i124 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS124 env1) L124 := stepS0_123 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS123 env1) i123 hm
  have i125 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS125 env1) L125 := stepS0_124 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS124 env1) i124 hm
  have i126 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS126 env1) L126 := stepS0_125 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS125 env1) i125 hm
  have i127 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS127 env1) L127 := stepS0_126 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS126 env1) i126 hm
  have i128 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS128 env1) L128 := stepS0_127 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS127 env1) i127 hm
  have i129 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS129 env1) L129 := stepS0_128 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS128 env1) i128 hm
  have i130 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS130 env1) L130 := stepS0_129 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS129 env1) i129 hm
  have i131 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS131 env1) L131 := stepS0_130 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS130 env1) i130 hm
  have i132 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS132 env1) L132 := stepS0_131 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS131 env1) i131 hm
  have i133 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS133 env1) L133 := stepS0_132 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS132 env1) i132 hm
  have i134 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS134 env1) L134 := stepS0_133 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS133 env1) i133 hm
  have i135 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS135 env1) L135 := stepS0_134 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS134 env1) i134 hm
  have i136 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS136 env1) L136 := stepS0_135 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS135 env1) i135 hm
  have i137 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS137 env1) L137 := stepS0_136 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS136 env1) i136 hm
  have i138 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS138 env1) L138 := stepS0_137 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS137 env1) i137 hm
  have i139 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS139 env1) L139 := stepS0_138 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS138 env1) i138 hm
  have i140 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS140 env1) L140 := stepS0_139 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS139 env1) i139 hm
  have i141 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS141 env1) L141 := stepS0_140 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS140 env1) i140 hm
  have i142 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS142 env1) L142 := stepS0_141 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS141 env1) i141 hm
  have i143 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS143 env1) L143 := stepS0_142 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS142 env1) i142 hm
  have i144 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS144 env1) L144 := stepS0_143 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS143 env1) i143 hm
  have i145 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS145 env1) L145 := stepS0_144 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS144 env1) i144 hm
  have i146 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS146 env1) L146 := stepS0_145 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS145 env1) i145 hm
  have i147 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS147 env1) L147 := stepS0_146 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS146 env1) i146 hm
  have i148 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS148 env1) L148 := stepS0_147 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS147 env1) i147 hm
  have i149 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS149 env1) L149 := stepS0_148 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS148 env1) i148 hm
  have i150 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS150 env1) L150 := stepS0_149 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS149 env1) i149 hm
  have i151 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS151 env1) L151 := stepS0_150 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS150 env1) i150 hm
  have i152 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS152 env1) L152 := stepS0_151 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS151 env1) i151 hm
  have i153 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS153 env1) L153 := stepS0_152 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS152 env1) i152 hm
  have i154 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS154 env1) L154 := stepS0_153 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS153 env1) i153 hm
  have i155 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS155 env1) L155 := stepS0_154 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS154 env1) i154 hm
  have i156 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS156 env1) L156 := stepS0_155 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS155 env1) i155 hm
  have i157 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS157 env1) L157 := stepS0_156 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS156 env1) i156 hm
  have i158 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS158 env1) L158 := stepS0_157 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS157 env1) i157 hm
  have i159 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS159 env1) L159 := stepS0_158 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS158 env1) i158 hm
  have i160 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS160 env1) L160 := stepS0_159 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS159 env1) i159 hm
  have i161 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS161 env1) L161 := stepS0_160 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS160 env1) i160 hm
  have i162 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS162 env1) L162 := stepS0_161 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS161 env1) i161 hm
  have i163 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS163 env1) L163 := stepS0_162 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS162 env1) i162 hm
  have i164 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS164 env1) L164 := stepS0_163 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS163 env1) i163 hm
  have i165 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS165 env1) L165 := stepS0_164 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS164 env1) i164 hm
  have i166 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS166 env1) L166 := stepS0_165 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS165 env1) i165 hm
  have i167 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS167 env1) L167 := stepS0_166 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS166 env1) i166 hm
  have i168 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS168 env1) L168 := stepS0_167 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS167 env1) i167 hm
  have i169 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS169 env1) L169 := stepS0_168 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS168 env1) i168 hm
  have i170 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS170 env1) L170 := stepS0_169 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS169 env1) i169 hm
  have i171 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS171 env1) L171 := stepS0_170 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS170 env1) i170 hm
  have i172 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS172 env1) L172 := stepS0_171 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS171 env1) i171 hm
  have i173 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS173 env1) L173 := stepS0_172 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS172 env1) i172 hm
  have i174 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS174 env1) L174 := stepS0_173 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS173 env1) i173 hm
  have i175 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS175 env1) L175 := stepS0_174 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS174 env1) i174 hm
  have i176 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS176 env1) L176 := stepS0_175 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS175 env1) i175 hm
  have i177 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS177 env1) L177 := stepS0_176 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS176 env1) i176 hm
  have i178 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS178 env1) L178 := stepS0_177 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS177 env1) i177 hm
  have i179 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS179 env1) L179 := stepS0_178 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS178 env1) i178 hm
  have i180 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS180 env1) L180 := stepS0_179 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS179 env1) i179 hm
  have i181 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS181 env1) L181 := stepS0_180 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS180 env1) i180 hm
  have i182 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS182 env1) L182 := stepS0_181 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS181 env1) i181 hm
  have i183 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS183 env1) L183 := stepS0_182 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS182 env1) i182 hm
  have i184 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS184 env1) L184 := stepS0_183 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS183 env1) i183 hm
  have i185 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS185 env1) L185 := stepS0_184 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS184 env1) i184 hm
  have i186 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS186 env1) L186 := stepS0_185 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS185 env1) i185 hm
  have i187 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS187 env1) L187 := stepS0_186 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS186 env1) i186 hm
  have i188 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS188 env1) L188 := stepS0_187 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS187 env1) i187 hm
  have i189 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS189 env1) L189 := stepS0_188 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS188 env1) i188 hm
  have i190 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS190 env1) L190 := stepS0_189 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS189 env1) i189 hm
  have i191 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS191 env1) L191 := stepS0_190 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS190 env1) i190 hm
  have i192 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS192 env1) L192 := stepS0_191 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS191 env1) i191 hm
  have i193 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS193 env1) L193 := stepS0_192 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS192 env1) i192 hm
  have i194 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS194 env1) L194 := stepS0_193 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS193 env1) i193 hm
  have i195 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS195 env1) L195 := stepS0_194 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS194 env1) i194 hm
  have i196 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS196 env1) L196 := stepS0_195 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS195 env1) i195 hm
  have i197 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS197 env1) L197 := stepS0_196 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS196 env1) i196 hm
  have i198 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS198 env1) L198 := stepS0_197 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS197 env1) i197 hm
  have i199 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS199 env1) L199 := stepS0_198 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS198 env1) i198 hm
  have i200 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS200 env1) L200 := stepS0_199 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS199 env1) i199 hm
  have i201 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS201 env1) L201 := stepS0_200 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS200 env1) i200 hm
  have i202 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS202 env1) L202 := stepS0_201 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS201 env1) i201 hm
  have i203 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS203 env1) L203 := stepS0_202 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS202 env1) i202 hm
  have i204 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS204 env1) L204 := stepS0_203 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS203 env1) i203 hm
  have i205 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS205 env1) L205 := stepS0_204 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS204 env1) i204 hm
  have i206 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS206 env1) L206 := stepS0_205 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS205 env1) i205 hm
  have i207 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS207 env1) L207 := stepS0_206 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS206 env1) i206 hm
  have i208 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS208 env1) L208 := stepS0_207 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS207 env1) i207 hm
  have i209 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS209 env1) L209 := stepS0_208 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS208 env1) i208 hm
  have i210 : InvC inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS210 env1) L210 := stepS0_209 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS209 env1) i209 hm
  exact i210

theorem invT0 (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (envAbs (Hashtree.Proofs.Avx2X8WBodyR0.G210 env1) (run prog 4 m8 orcB 27 (shiftK8 0 K210))) L211t :=
  stepT0 inp (Hashtree.Proofs.Avx2X8WBodyR0.G210 env1) (invW0_body inp env1 hm) hm

theorem invX0 (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (envAbs (Hashtree.Proofs.Avx2X8WBodyR0.G210 env1) (run prog 4 m8 orcEx 31 (shiftK8 0 K210))) L211t :=
  stepX0 inp (Hashtree.Proofs.Avx2X8WBodyR0.G210 env1) (invW0_body inp env1 hm) hm

theorem invTS0 (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (envAbs (Hashtree.Proofs.Avx2X8WBodyR0S.GS210 env1) (run prog 4 (m8P 0) orcB 27 (stripK8 0 K210))) L211t :=
  stepTS0 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS210 env1) (invS0_body inp env1 hm) hm

theorem invXS0 (inp : Nat → Byte) (env1 : Key → W32) (hm : HMem 512 inp env1) :
    InvC inp (envAbs (Hashtree.Proofs.Avx2X8WBodyR0S.GS210 env1) (run prog 4 (m8P 0) orcEx 31 (stripK8 0 K210))) L211t :=
  stepXS0 inp (Hashtree.Proofs.Avx2X8WBodyR0S.GS210 env1) (invS0_body inp env1 hm) hm

end Hashtree.Proofs.Avx2X8WOut
