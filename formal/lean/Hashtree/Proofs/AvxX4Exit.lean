import Hashtree.Gen.AvxX4P.Final
import Hashtree.Proofs.AvxX4LoopTurn
import Hashtree.Proofs.AvxX4LoopFrame

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.SpecQ Hashtree.Spec Hashtree.Kernels.X86.AvxX4
namespace Hashtree.Proofs.AvxX4Exit
open Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4LoopTurn
open Hashtree.Proofs.AvxX4LoopFrame

/-- The pilot's head trees check unchanged from the loop invariant head. -/
theorem KHL2_headT : sliceCheck prog 4 m0q (fun _ => false) 68 KHL2 K1 T0 = true := by
  decide +kernel

/-- The environment at the pilot's cut `K1`, reached from the loop invariant head. -/
def H (env : Key → W32) : Key → W32 :=
  envAbs env (run prog 4 m0q (fun _ => false) 68 KHL2)

/-- The environment at the pilot's exit cut `K201`, reached from the loop invariant head
through the whole body and the 27-step exit slice. -/
def EF (env : Key → W32) : Key → W32 :=
  envAbs (G200 (H env)) (run prog 4 m0q (fun pc => decide (pc ∈ ([6] : List Nat))) 27 K200)

/-- The pilot's `L1` tree facts hold at the head slice from the loop invariant head. -/
theorem inv_head (inp : Nat → Byte) (env : Key → W32) (hm : HMem 256 inp env) :
    InvC inp (H env) L1 := by
  exact invC_of_trees inp env _ T0 L1 (slice_trees_mem prog 4 _ _ 68 KHL2 K1 T0 KHL2_headT env)
      (And.intro ⟨rfl, core0_1015 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core0_1014 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core0_1013 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core0_1012 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      (And.intro ⟨rfl, core0_1011 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core0_1010 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core0_1009 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core0_1008 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core0_1007 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core0_1006 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core0_1005 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core0_1004 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core0_1003 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core0_1002 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core0_1001 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core0_1000 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core0_311 (qv inp) inp env (hm 196 (by decide)) (hm 197 (by decide)) (hm 198 (by decide)) (hm 199 (by decide)) (qW_R inp 3 1 (by decide)) (qR inp 3 1)⟩
      (And.intro ⟨rfl, core0_310 (qv inp) inp env (hm 132 (by decide)) (hm 133 (by decide)) (hm 134 (by decide)) (hm 135 (by decide)) (qW_R inp 2 1 (by decide)) (qR inp 2 1)⟩
      (And.intro ⟨rfl, core0_309 (qv inp) inp env (hm 68 (by decide)) (hm 69 (by decide)) (hm 70 (by decide)) (hm 71 (by decide)) (qW_R inp 1 1 (by decide)) (qR inp 1 1)⟩
      (And.intro ⟨rfl, core0_308 (qv inp) inp env (hm 4 (by decide)) (hm 5 (by decide)) (hm 6 (by decide)) (hm 7 (by decide)) (qW_R inp 0 1 (by decide)) (qR inp 0 1)⟩
      (And.intro ⟨rfl, core0_295 (qv inp) inp env (hm 200 (by decide)) (hm 201 (by decide)) (hm 202 (by decide)) (hm 203 (by decide)) (qW_R inp 3 2 (by decide)) (qR inp 3 2)⟩
      (And.intro ⟨rfl, core0_294 (qv inp) inp env (hm 136 (by decide)) (hm 137 (by decide)) (hm 138 (by decide)) (hm 139 (by decide)) (qW_R inp 2 2 (by decide)) (qR inp 2 2)⟩
      (And.intro ⟨rfl, core0_293 (qv inp) inp env (hm 72 (by decide)) (hm 73 (by decide)) (hm 74 (by decide)) (hm 75 (by decide)) (qW_R inp 1 2 (by decide)) (qR inp 1 2)⟩
      (And.intro ⟨rfl, core0_292 (qv inp) inp env (hm 8 (by decide)) (hm 9 (by decide)) (hm 10 (by decide)) (hm 11 (by decide)) (qW_R inp 0 2 (by decide)) (qR inp 0 2)⟩
      (And.intro ⟨rfl, core0_279 (qv inp) inp env (hm 204 (by decide)) (hm 205 (by decide)) (hm 206 (by decide)) (hm 207 (by decide)) (qW_R inp 3 3 (by decide)) (qR inp 3 3)⟩
      (And.intro ⟨rfl, core0_278 (qv inp) inp env (hm 140 (by decide)) (hm 141 (by decide)) (hm 142 (by decide)) (hm 143 (by decide)) (qW_R inp 2 3 (by decide)) (qR inp 2 3)⟩
      (And.intro ⟨rfl, core0_277 (qv inp) inp env (hm 76 (by decide)) (hm 77 (by decide)) (hm 78 (by decide)) (hm 79 (by decide)) (qW_R inp 1 3 (by decide)) (qR inp 1 3)⟩
      (And.intro ⟨rfl, core0_276 (qv inp) inp env (hm 12 (by decide)) (hm 13 (by decide)) (hm 14 (by decide)) (hm 15 (by decide)) (qW_R inp 0 3 (by decide)) (qR inp 0 3)⟩
      (And.intro ⟨rfl, core0_215 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qA_succI inp 3 0 (0) (by decide)) (qE_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 3 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 3 0 (by decide)) (qR inp 3 0) (qA_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core0_214 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qA_succI inp 2 0 (0) (by decide)) (qE_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 2 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 2 0 (by decide)) (qR inp 2 0) (qA_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core0_213 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qA_succI inp 1 0 (0) (by decide)) (qE_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 1 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 1 0 (by decide)) (qR inp 1 0) (qA_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core0_212 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qA_succI inp 0 0 (0) (by decide)) (qE_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 0 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 0 0 (by decide)) (qR inp 0 0) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32))⟩
      (And.intro ⟨rfl, core0_151 (qv inp) inp env (hm 192 (by decide)) (hm 193 (by decide)) (hm 194 (by decide)) (hm 195 (by decide)) (qE_succI inp 3 0 (0) (by decide)) (qA_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 3 0 3 (-3) (by decide) (by decide)) ((qH0 inp 3 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 3 0 0 (0) (by decide) (by decide)) ((qH0 inp 3 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 3 0 1 (-1) (by decide) (by decide)) ((qH0 inp 3 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 3 0 2 (-2) (by decide) (by decide)) ((qH0 inp 3 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 3 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 3 0 (by decide)) (qR inp 3 0)⟩
      (And.intro ⟨rfl, core0_150 (qv inp) inp env (hm 128 (by decide)) (hm 129 (by decide)) (hm 130 (by decide)) (hm 131 (by decide)) (qE_succI inp 2 0 (0) (by decide)) (qA_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 2 0 3 (-3) (by decide) (by decide)) ((qH0 inp 2 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 2 0 0 (0) (by decide) (by decide)) ((qH0 inp 2 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 2 0 1 (-1) (by decide) (by decide)) ((qH0 inp 2 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 2 0 2 (-2) (by decide) (by decide)) ((qH0 inp 2 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 2 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 2 0 (by decide)) (qR inp 2 0)⟩
      (And.intro ⟨rfl, core0_149 (qv inp) inp env (hm 64 (by decide)) (hm 65 (by decide)) (hm 66 (by decide)) (hm 67 (by decide)) (qE_succI inp 1 0 (0) (by decide)) (qA_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 1 0 3 (-3) (by decide) (by decide)) ((qH0 inp 1 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 1 0 0 (0) (by decide) (by decide)) ((qH0 inp 1 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 1 0 1 (-1) (by decide) (by decide)) ((qH0 inp 1 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 1 0 2 (-2) (by decide) (by decide)) ((qH0 inp 1 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 1 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 1 0 (by decide)) (qR inp 1 0)⟩
      (And.intro ⟨rfl, core0_148 (qv inp) inp env (hm 0 (by decide)) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide)) (qE_succI inp 0 0 (0) (by decide)) (qA_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 0 0 3 (-3) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW inp 0 0 0).trans (by rw [show Spec.K 0 = 1116352408#32 from by decide])) (qW_R inp 0 0 (by decide)) (qR inp 0 0)⟩
      trivial))))))))))))))))))))))))))))))))))))


/-- The pilot's whole output-label chain from the loop invariant head: `step1 .. step200`
applied to `inv_head`. -/
theorem inv_chain (inp : Nat → Byte) (env : Key → W32) (hm : HMem 256 inp env) :
    InvC inp (EF env) L201 := by
  have i1 : InvC inp (H env) L1 := inv_head inp env hm
  have i2 : InvC inp (G2 (H env)) L2 := step1 inp (G1 (H env)) i1 hm
  have i3 : InvC inp (G3 (H env)) L3 := step2 inp (G2 (H env)) i2 hm
  have i4 : InvC inp (G4 (H env)) L4 := step3 inp (G3 (H env)) i3 hm
  have i5 : InvC inp (G5 (H env)) L5 := step4 inp (G4 (H env)) i4 hm
  have i6 : InvC inp (G6 (H env)) L6 := step5 inp (G5 (H env)) i5 hm
  have i7 : InvC inp (G7 (H env)) L7 := step6 inp (G6 (H env)) i6 hm
  have i8 : InvC inp (G8 (H env)) L8 := step7 inp (G7 (H env)) i7 hm
  have i9 : InvC inp (G9 (H env)) L9 := step8 inp (G8 (H env)) i8 hm
  have i10 : InvC inp (G10 (H env)) L10 := step9 inp (G9 (H env)) i9 hm
  have i11 : InvC inp (G11 (H env)) L11 := step10 inp (G10 (H env)) i10 hm
  have i12 : InvC inp (G12 (H env)) L12 := step11 inp (G11 (H env)) i11 hm
  have i13 : InvC inp (G13 (H env)) L13 := step12 inp (G12 (H env)) i12 hm
  have i14 : InvC inp (G14 (H env)) L14 := step13 inp (G13 (H env)) i13 hm
  have i15 : InvC inp (G15 (H env)) L15 := step14 inp (G14 (H env)) i14 hm
  have i16 : InvC inp (G16 (H env)) L16 := step15 inp (G15 (H env)) i15 hm
  have i17 : InvC inp (G17 (H env)) L17 := step16 inp (G16 (H env)) i16 hm
  have i18 : InvC inp (G18 (H env)) L18 := step17 inp (G17 (H env)) i17 hm
  have i19 : InvC inp (G19 (H env)) L19 := step18 inp (G18 (H env)) i18 hm
  have i20 : InvC inp (G20 (H env)) L20 := step19 inp (G19 (H env)) i19 hm
  have i21 : InvC inp (G21 (H env)) L21 := step20 inp (G20 (H env)) i20 hm
  have i22 : InvC inp (G22 (H env)) L22 := step21 inp (G21 (H env)) i21 hm
  have i23 : InvC inp (G23 (H env)) L23 := step22 inp (G22 (H env)) i22 hm
  have i24 : InvC inp (G24 (H env)) L24 := step23 inp (G23 (H env)) i23 hm
  have i25 : InvC inp (G25 (H env)) L25 := step24 inp (G24 (H env)) i24 hm
  have i26 : InvC inp (G26 (H env)) L26 := step25 inp (G25 (H env)) i25 hm
  have i27 : InvC inp (G27 (H env)) L27 := step26 inp (G26 (H env)) i26 hm
  have i28 : InvC inp (G28 (H env)) L28 := step27 inp (G27 (H env)) i27 hm
  have i29 : InvC inp (G29 (H env)) L29 := step28 inp (G28 (H env)) i28 hm
  have i30 : InvC inp (G30 (H env)) L30 := step29 inp (G29 (H env)) i29 hm
  have i31 : InvC inp (G31 (H env)) L31 := step30 inp (G30 (H env)) i30 hm
  have i32 : InvC inp (G32 (H env)) L32 := step31 inp (G31 (H env)) i31 hm
  have i33 : InvC inp (G33 (H env)) L33 := step32 inp (G32 (H env)) i32 hm
  have i34 : InvC inp (G34 (H env)) L34 := step33 inp (G33 (H env)) i33 hm
  have i35 : InvC inp (G35 (H env)) L35 := step34 inp (G34 (H env)) i34 hm
  have i36 : InvC inp (G36 (H env)) L36 := step35 inp (G35 (H env)) i35 hm
  have i37 : InvC inp (G37 (H env)) L37 := step36 inp (G36 (H env)) i36 hm
  have i38 : InvC inp (G38 (H env)) L38 := step37 inp (G37 (H env)) i37 hm
  have i39 : InvC inp (G39 (H env)) L39 := step38 inp (G38 (H env)) i38 hm
  have i40 : InvC inp (G40 (H env)) L40 := step39 inp (G39 (H env)) i39 hm
  have i41 : InvC inp (G41 (H env)) L41 := step40 inp (G40 (H env)) i40 hm
  have i42 : InvC inp (G42 (H env)) L42 := step41 inp (G41 (H env)) i41 hm
  have i43 : InvC inp (G43 (H env)) L43 := step42 inp (G42 (H env)) i42 hm
  have i44 : InvC inp (G44 (H env)) L44 := step43 inp (G43 (H env)) i43 hm
  have i45 : InvC inp (G45 (H env)) L45 := step44 inp (G44 (H env)) i44 hm
  have i46 : InvC inp (G46 (H env)) L46 := step45 inp (G45 (H env)) i45 hm
  have i47 : InvC inp (G47 (H env)) L47 := step46 inp (G46 (H env)) i46 hm
  have i48 : InvC inp (G48 (H env)) L48 := step47 inp (G47 (H env)) i47 hm
  have i49 : InvC inp (G49 (H env)) L49 := step48 inp (G48 (H env)) i48 hm
  have i50 : InvC inp (G50 (H env)) L50 := step49 inp (G49 (H env)) i49 hm
  have i51 : InvC inp (G51 (H env)) L51 := step50 inp (G50 (H env)) i50 hm
  have i52 : InvC inp (G52 (H env)) L52 := step51 inp (G51 (H env)) i51 hm
  have i53 : InvC inp (G53 (H env)) L53 := step52 inp (G52 (H env)) i52 hm
  have i54 : InvC inp (G54 (H env)) L54 := step53 inp (G53 (H env)) i53 hm
  have i55 : InvC inp (G55 (H env)) L55 := step54 inp (G54 (H env)) i54 hm
  have i56 : InvC inp (G56 (H env)) L56 := step55 inp (G55 (H env)) i55 hm
  have i57 : InvC inp (G57 (H env)) L57 := step56 inp (G56 (H env)) i56 hm
  have i58 : InvC inp (G58 (H env)) L58 := step57 inp (G57 (H env)) i57 hm
  have i59 : InvC inp (G59 (H env)) L59 := step58 inp (G58 (H env)) i58 hm
  have i60 : InvC inp (G60 (H env)) L60 := step59 inp (G59 (H env)) i59 hm
  have i61 : InvC inp (G61 (H env)) L61 := step60 inp (G60 (H env)) i60 hm
  have i62 : InvC inp (G62 (H env)) L62 := step61 inp (G61 (H env)) i61 hm
  have i63 : InvC inp (G63 (H env)) L63 := step62 inp (G62 (H env)) i62 hm
  have i64 : InvC inp (G64 (H env)) L64 := step63 inp (G63 (H env)) i63 hm
  have i65 : InvC inp (G65 (H env)) L65 := step64 inp (G64 (H env)) i64 hm
  have i66 : InvC inp (G66 (H env)) L66 := step65 inp (G65 (H env)) i65 hm
  have i67 : InvC inp (G67 (H env)) L67 := step66 inp (G66 (H env)) i66 hm
  have i68 : InvC inp (G68 (H env)) L68 := step67 inp (G67 (H env)) i67 hm
  have i69 : InvC inp (G69 (H env)) L69 := step68 inp (G68 (H env)) i68 hm
  have i70 : InvC inp (G70 (H env)) L70 := step69 inp (G69 (H env)) i69 hm
  have i71 : InvC inp (G71 (H env)) L71 := step70 inp (G70 (H env)) i70 hm
  have i72 : InvC inp (G72 (H env)) L72 := step71 inp (G71 (H env)) i71 hm
  have i73 : InvC inp (G73 (H env)) L73 := step72 inp (G72 (H env)) i72 hm
  have i74 : InvC inp (G74 (H env)) L74 := step73 inp (G73 (H env)) i73 hm
  have i75 : InvC inp (G75 (H env)) L75 := step74 inp (G74 (H env)) i74 hm
  have i76 : InvC inp (G76 (H env)) L76 := step75 inp (G75 (H env)) i75 hm
  have i77 : InvC inp (G77 (H env)) L77 := step76 inp (G76 (H env)) i76 hm
  have i78 : InvC inp (G78 (H env)) L78 := step77 inp (G77 (H env)) i77 hm
  have i79 : InvC inp (G79 (H env)) L79 := step78 inp (G78 (H env)) i78 hm
  have i80 : InvC inp (G80 (H env)) L80 := step79 inp (G79 (H env)) i79 hm
  have i81 : InvC inp (G81 (H env)) L81 := step80 inp (G80 (H env)) i80 hm
  have i82 : InvC inp (G82 (H env)) L82 := step81 inp (G81 (H env)) i81 hm
  have i83 : InvC inp (G83 (H env)) L83 := step82 inp (G82 (H env)) i82 hm
  have i84 : InvC inp (G84 (H env)) L84 := step83 inp (G83 (H env)) i83 hm
  have i85 : InvC inp (G85 (H env)) L85 := step84 inp (G84 (H env)) i84 hm
  have i86 : InvC inp (G86 (H env)) L86 := step85 inp (G85 (H env)) i85 hm
  have i87 : InvC inp (G87 (H env)) L87 := step86 inp (G86 (H env)) i86 hm
  have i88 : InvC inp (G88 (H env)) L88 := step87 inp (G87 (H env)) i87 hm
  have i89 : InvC inp (G89 (H env)) L89 := step88 inp (G88 (H env)) i88 hm
  have i90 : InvC inp (G90 (H env)) L90 := step89 inp (G89 (H env)) i89 hm
  have i91 : InvC inp (G91 (H env)) L91 := step90 inp (G90 (H env)) i90 hm
  have i92 : InvC inp (G92 (H env)) L92 := step91 inp (G91 (H env)) i91 hm
  have i93 : InvC inp (G93 (H env)) L93 := step92 inp (G92 (H env)) i92 hm
  have i94 : InvC inp (G94 (H env)) L94 := step93 inp (G93 (H env)) i93 hm
  have i95 : InvC inp (G95 (H env)) L95 := step94 inp (G94 (H env)) i94 hm
  have i96 : InvC inp (G96 (H env)) L96 := step95 inp (G95 (H env)) i95 hm
  have i97 : InvC inp (G97 (H env)) L97 := step96 inp (G96 (H env)) i96 hm
  have i98 : InvC inp (G98 (H env)) L98 := step97 inp (G97 (H env)) i97 hm
  have i99 : InvC inp (G99 (H env)) L99 := step98 inp (G98 (H env)) i98 hm
  have i100 : InvC inp (G100 (H env)) L100 := step99 inp (G99 (H env)) i99 hm
  have i101 : InvC inp (G101 (H env)) L101 := step100 inp (G100 (H env)) i100 hm
  have i102 : InvC inp (G102 (H env)) L102 := step101 inp (G101 (H env)) i101 hm
  have i103 : InvC inp (G103 (H env)) L103 := step102 inp (G102 (H env)) i102 hm
  have i104 : InvC inp (G104 (H env)) L104 := step103 inp (G103 (H env)) i103 hm
  have i105 : InvC inp (G105 (H env)) L105 := step104 inp (G104 (H env)) i104 hm
  have i106 : InvC inp (G106 (H env)) L106 := step105 inp (G105 (H env)) i105 hm
  have i107 : InvC inp (G107 (H env)) L107 := step106 inp (G106 (H env)) i106 hm
  have i108 : InvC inp (G108 (H env)) L108 := step107 inp (G107 (H env)) i107 hm
  have i109 : InvC inp (G109 (H env)) L109 := step108 inp (G108 (H env)) i108 hm
  have i110 : InvC inp (G110 (H env)) L110 := step109 inp (G109 (H env)) i109 hm
  have i111 : InvC inp (G111 (H env)) L111 := step110 inp (G110 (H env)) i110 hm
  have i112 : InvC inp (G112 (H env)) L112 := step111 inp (G111 (H env)) i111 hm
  have i113 : InvC inp (G113 (H env)) L113 := step112 inp (G112 (H env)) i112 hm
  have i114 : InvC inp (G114 (H env)) L114 := step113 inp (G113 (H env)) i113 hm
  have i115 : InvC inp (G115 (H env)) L115 := step114 inp (G114 (H env)) i114 hm
  have i116 : InvC inp (G116 (H env)) L116 := step115 inp (G115 (H env)) i115 hm
  have i117 : InvC inp (G117 (H env)) L117 := step116 inp (G116 (H env)) i116 hm
  have i118 : InvC inp (G118 (H env)) L118 := step117 inp (G117 (H env)) i117 hm
  have i119 : InvC inp (G119 (H env)) L119 := step118 inp (G118 (H env)) i118 hm
  have i120 : InvC inp (G120 (H env)) L120 := step119 inp (G119 (H env)) i119 hm
  have i121 : InvC inp (G121 (H env)) L121 := step120 inp (G120 (H env)) i120 hm
  have i122 : InvC inp (G122 (H env)) L122 := step121 inp (G121 (H env)) i121 hm
  have i123 : InvC inp (G123 (H env)) L123 := step122 inp (G122 (H env)) i122 hm
  have i124 : InvC inp (G124 (H env)) L124 := step123 inp (G123 (H env)) i123 hm
  have i125 : InvC inp (G125 (H env)) L125 := step124 inp (G124 (H env)) i124 hm
  have i126 : InvC inp (G126 (H env)) L126 := step125 inp (G125 (H env)) i125 hm
  have i127 : InvC inp (G127 (H env)) L127 := step126 inp (G126 (H env)) i126 hm
  have i128 : InvC inp (G128 (H env)) L128 := step127 inp (G127 (H env)) i127 hm
  have i129 : InvC inp (G129 (H env)) L129 := step128 inp (G128 (H env)) i128 hm
  have i130 : InvC inp (G130 (H env)) L130 := step129 inp (G129 (H env)) i129 hm
  have i131 : InvC inp (G131 (H env)) L131 := step130 inp (G130 (H env)) i130 hm
  have i132 : InvC inp (G132 (H env)) L132 := step131 inp (G131 (H env)) i131 hm
  have i133 : InvC inp (G133 (H env)) L133 := step132 inp (G132 (H env)) i132 hm
  have i134 : InvC inp (G134 (H env)) L134 := step133 inp (G133 (H env)) i133 hm
  have i135 : InvC inp (G135 (H env)) L135 := step134 inp (G134 (H env)) i134 hm
  have i136 : InvC inp (G136 (H env)) L136 := step135 inp (G135 (H env)) i135 hm
  have i137 : InvC inp (G137 (H env)) L137 := step136 inp (G136 (H env)) i136 hm
  have i138 : InvC inp (G138 (H env)) L138 := step137 inp (G137 (H env)) i137 hm
  have i139 : InvC inp (G139 (H env)) L139 := step138 inp (G138 (H env)) i138 hm
  have i140 : InvC inp (G140 (H env)) L140 := step139 inp (G139 (H env)) i139 hm
  have i141 : InvC inp (G141 (H env)) L141 := step140 inp (G140 (H env)) i140 hm
  have i142 : InvC inp (G142 (H env)) L142 := step141 inp (G141 (H env)) i141 hm
  have i143 : InvC inp (G143 (H env)) L143 := step142 inp (G142 (H env)) i142 hm
  have i144 : InvC inp (G144 (H env)) L144 := step143 inp (G143 (H env)) i143 hm
  have i145 : InvC inp (G145 (H env)) L145 := step144 inp (G144 (H env)) i144 hm
  have i146 : InvC inp (G146 (H env)) L146 := step145 inp (G145 (H env)) i145 hm
  have i147 : InvC inp (G147 (H env)) L147 := step146 inp (G146 (H env)) i146 hm
  have i148 : InvC inp (G148 (H env)) L148 := step147 inp (G147 (H env)) i147 hm
  have i149 : InvC inp (G149 (H env)) L149 := step148 inp (G148 (H env)) i148 hm
  have i150 : InvC inp (G150 (H env)) L150 := step149 inp (G149 (H env)) i149 hm
  have i151 : InvC inp (G151 (H env)) L151 := step150 inp (G150 (H env)) i150 hm
  have i152 : InvC inp (G152 (H env)) L152 := step151 inp (G151 (H env)) i151 hm
  have i153 : InvC inp (G153 (H env)) L153 := step152 inp (G152 (H env)) i152 hm
  have i154 : InvC inp (G154 (H env)) L154 := step153 inp (G153 (H env)) i153 hm
  have i155 : InvC inp (G155 (H env)) L155 := step154 inp (G154 (H env)) i154 hm
  have i156 : InvC inp (G156 (H env)) L156 := step155 inp (G155 (H env)) i155 hm
  have i157 : InvC inp (G157 (H env)) L157 := step156 inp (G156 (H env)) i156 hm
  have i158 : InvC inp (G158 (H env)) L158 := step157 inp (G157 (H env)) i157 hm
  have i159 : InvC inp (G159 (H env)) L159 := step158 inp (G158 (H env)) i158 hm
  have i160 : InvC inp (G160 (H env)) L160 := step159 inp (G159 (H env)) i159 hm
  have i161 : InvC inp (G161 (H env)) L161 := step160 inp (G160 (H env)) i160 hm
  have i162 : InvC inp (G162 (H env)) L162 := step161 inp (G161 (H env)) i161 hm
  have i163 : InvC inp (G163 (H env)) L163 := step162 inp (G162 (H env)) i162 hm
  have i164 : InvC inp (G164 (H env)) L164 := step163 inp (G163 (H env)) i163 hm
  have i165 : InvC inp (G165 (H env)) L165 := step164 inp (G164 (H env)) i164 hm
  have i166 : InvC inp (G166 (H env)) L166 := step165 inp (G165 (H env)) i165 hm
  have i167 : InvC inp (G167 (H env)) L167 := step166 inp (G166 (H env)) i166 hm
  have i168 : InvC inp (G168 (H env)) L168 := step167 inp (G167 (H env)) i167 hm
  have i169 : InvC inp (G169 (H env)) L169 := step168 inp (G168 (H env)) i168 hm
  have i170 : InvC inp (G170 (H env)) L170 := step169 inp (G169 (H env)) i169 hm
  have i171 : InvC inp (G171 (H env)) L171 := step170 inp (G170 (H env)) i170 hm
  have i172 : InvC inp (G172 (H env)) L172 := step171 inp (G171 (H env)) i171 hm
  have i173 : InvC inp (G173 (H env)) L173 := step172 inp (G172 (H env)) i172 hm
  have i174 : InvC inp (G174 (H env)) L174 := step173 inp (G173 (H env)) i173 hm
  have i175 : InvC inp (G175 (H env)) L175 := step174 inp (G174 (H env)) i174 hm
  have i176 : InvC inp (G176 (H env)) L176 := step175 inp (G175 (H env)) i175 hm
  have i177 : InvC inp (G177 (H env)) L177 := step176 inp (G176 (H env)) i176 hm
  have i178 : InvC inp (G178 (H env)) L178 := step177 inp (G177 (H env)) i177 hm
  have i179 : InvC inp (G179 (H env)) L179 := step178 inp (G178 (H env)) i178 hm
  have i180 : InvC inp (G180 (H env)) L180 := step179 inp (G179 (H env)) i179 hm
  have i181 : InvC inp (G181 (H env)) L181 := step180 inp (G180 (H env)) i180 hm
  have i182 : InvC inp (G182 (H env)) L182 := step181 inp (G181 (H env)) i181 hm
  have i183 : InvC inp (G183 (H env)) L183 := step182 inp (G182 (H env)) i182 hm
  have i184 : InvC inp (G184 (H env)) L184 := step183 inp (G183 (H env)) i183 hm
  have i185 : InvC inp (G185 (H env)) L185 := step184 inp (G184 (H env)) i184 hm
  have i186 : InvC inp (G186 (H env)) L186 := step185 inp (G185 (H env)) i185 hm
  have i187 : InvC inp (G187 (H env)) L187 := step186 inp (G186 (H env)) i186 hm
  have i188 : InvC inp (G188 (H env)) L188 := step187 inp (G187 (H env)) i187 hm
  have i189 : InvC inp (G189 (H env)) L189 := step188 inp (G188 (H env)) i188 hm
  have i190 : InvC inp (G190 (H env)) L190 := step189 inp (G189 (H env)) i189 hm
  have i191 : InvC inp (G191 (H env)) L191 := step190 inp (G190 (H env)) i190 hm
  have i192 : InvC inp (G192 (H env)) L192 := step191 inp (G191 (H env)) i191 hm
  have i193 : InvC inp (G193 (H env)) L193 := step192 inp (G192 (H env)) i192 hm
  have i194 : InvC inp (G194 (H env)) L194 := step193 inp (G193 (H env)) i193 hm
  have i195 : InvC inp (G195 (H env)) L195 := step194 inp (G194 (H env)) i194 hm
  have i196 : InvC inp (G196 (H env)) L196 := step195 inp (G195 (H env)) i195 hm
  have i197 : InvC inp (G197 (H env)) L197 := step196 inp (G196 (H env)) i196 hm
  have i198 : InvC inp (G198 (H env)) L198 := step197 inp (G197 (H env)) i197 hm
  have i199 : InvC inp (G199 (H env)) L199 := step198 inp (G198 (H env)) i198 hm
  have i200 : InvC inp (G200 (H env)) L200 := step199 inp (G199 (H env)) i199 hm
  have i201 : InvC inp (EF env) L201 := step200 inp (G200 (H env)) i200 hm
  exact i201


theorem K201_assume : K201.assume = A1 := by
  decide +kernel

/-- The exit slice's conditions at any residual count in `[4, 8)`. -/
theorem asm1ge (σ : Nat → Int) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∀ p ∈ A1, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A1, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;>
    omega

/-- The last batch at a residual count `s ∈ [4, 8)`: head slice, body, 27-step exit slice
from the loop invariant head to the pilot's exit cut. -/
theorem run_finalS (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel env σ m0q mem0c) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    run prog 4 mem0c orcC (68 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (mapState env σ KHL2) = mapState (EF env) σ K201 := by
  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24
  have hHead := (slice_sound env σ m0q mem0c h0 prog 4 (fun _ => false)
    orcC 68 KHL2 K1 [] KHL2_head KHL2_err
    (assumeOk_of σ K1 Hashtree.Proofs.AvxX4LoopTurn.A0 rfl
      (Hashtree.Proofs.AvxX4LoopTurn.asm0ge σ hge))).1
  have hH : run prog 4 mem0c orcC 68 (mapState env σ KHL2) =
      mapState (G1 (H env)) σ K1 := hHead
  have hm : Mem0Rel (H env) σ m0q mem0c := mem0Rel_envAbs env σ m0q mem0c kq h0 _
  have hB := body_run (H env) σ mem0c orcC hm hge
  have hm2 := body_mem (H env) σ mem0c hm
  have hExit := (slice_sound (G200 (H env)) σ m0q mem0c hm2 prog 4
    (fun pc => decide (pc ∈ ([6] : List Nat))) orcC 27 K200 K201 T200 slice200 K200_err
    (assumeOk_of σ K201 A1 K201_assume (asm1ge σ hge hlt))).1
  rw [run_add, run_add, hH, hB]
  exact hExit

/-- The pilot's output bytes for the final batch at a residual count `s ∈ [4, 8)`.  The
`inp` argument is the batch's input window (`fun o => inp (256*j + o)`). -/
theorem out_finalS (inp : Nat → Byte) (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel env σ m0q mem0c) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8)
    (hm : HMem 256 inp env) :
    ∀ n i b, n < 4 → i < 8 → b < 4 → ∃ x,
      lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)
        (run prog 4 mem0c orcC (68 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (mapState env σ KHL2)).mem = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by
  rw [run_finalS env σ mem0c orcC h0 hge hlt]
  have hF := inv_chain inp env hm
  have g0 := hF.1; have hF := hF.2
  have g1 := hF.1; have hF := hF.2
  have g2 := hF.1; have hF := hF.2
  have g3 := hF.1; have hF := hF.2
  have g4 := hF.1; have hF := hF.2
  have g5 := hF.1; have hF := hF.2
  have g6 := hF.1; have hF := hF.2
  have g7 := hF.1; have hF := hF.2
  have g8 := hF.1; have hF := hF.2
  have g9 := hF.1; have hF := hF.2
  have g10 := hF.1; have hF := hF.2
  have g11 := hF.1; have hF := hF.2
  have g12 := hF.1; have hF := hF.2
  have g13 := hF.1; have hF := hF.2
  have g14 := hF.1; have hF := hF.2
  have g15 := hF.1; have hF := hF.2
  have g16 := hF.1; have hF := hF.2
  have g17 := hF.1; have hF := hF.2
  have g18 := hF.1; have hF := hF.2
  have g19 := hF.1; have hF := hF.2
  have g20 := hF.1; have hF := hF.2
  have g21 := hF.1; have hF := hF.2
  have g22 := hF.1; have hF := hF.2
  have g23 := hF.1; have hF := hF.2
  have g24 := hF.1; have hF := hF.2
  have g25 := hF.1; have hF := hF.2
  have g26 := hF.1; have hF := hF.2
  have g27 := hF.1; have hF := hF.2
  have g28 := hF.1; have hF := hF.2
  have g29 := hF.1; have hF := hF.2
  have g30 := hF.1; have hF := hF.2
  have g31 := hF.1; have hF := hF.2
  have g32 := hF.1; have hF := hF.2
  have g33 := hF.1; have hF := hF.2
  have g34 := hF.1; have hF := hF.2
  have g35 := hF.1; have hF := hF.2
  have g36 := hF.1; have hF := hF.2
  have g37 := hF.1; have hF := hF.2
  have g38 := hF.1; have hF := hF.2
  have g39 := hF.1; have hF := hF.2
  have g40 := hF.1; have hF := hF.2
  have g41 := hF.1; have hF := hF.2
  have g42 := hF.1; have hF := hF.2
  have g43 := hF.1; have hF := hF.2
  have g44 := hF.1; have hF := hF.2
  have g45 := hF.1; have hF := hF.2
  have g46 := hF.1; have hF := hF.2
  have g47 := hF.1; have hF := hF.2
  have g48 := hF.1; have hF := hF.2
  have g49 := hF.1; have hF := hF.2
  have g50 := hF.1; have hF := hF.2
  have g51 := hF.1; have hF := hF.2
  have g52 := hF.1; have hF := hF.2
  have g53 := hF.1; have hF := hF.2
  have g54 := hF.1; have hF := hF.2
  have g55 := hF.1; have hF := hF.2
  have g56 := hF.1; have hF := hF.2
  have g57 := hF.1; have hF := hF.2
  have g58 := hF.1; have hF := hF.2
  have g59 := hF.1; have hF := hF.2
  have g60 := hF.1; have hF := hF.2
  have g61 := hF.1; have hF := hF.2
  have g62 := hF.1; have hF := hF.2
  have g63 := hF.1; have hF := hF.2
  have g64 := hF.1; have hF := hF.2
  have g65 := hF.1; have hF := hF.2
  have g66 := hF.1; have hF := hF.2
  have g67 := hF.1; have hF := hF.2
  have g68 := hF.1; have hF := hF.2
  have g69 := hF.1; have hF := hF.2
  have g70 := hF.1; have hF := hF.2
  have g71 := hF.1; have hF := hF.2
  have g72 := hF.1; have hF := hF.2
  have g73 := hF.1; have hF := hF.2
  have g74 := hF.1; have hF := hF.2
  have g75 := hF.1; have hF := hF.2
  have g76 := hF.1; have hF := hF.2
  have g77 := hF.1; have hF := hF.2
  have g78 := hF.1; have hF := hF.2
  have g79 := hF.1; have hF := hF.2
  have g80 := hF.1; have hF := hF.2
  have g81 := hF.1; have hF := hF.2
  have g82 := hF.1; have hF := hF.2
  have g83 := hF.1; have hF := hF.2
  have g84 := hF.1; have hF := hF.2
  have g85 := hF.1; have hF := hF.2
  have g86 := hF.1; have hF := hF.2
  have g87 := hF.1; have hF := hF.2
  have g88 := hF.1; have hF := hF.2
  have g89 := hF.1; have hF := hF.2
  have g90 := hF.1; have hF := hF.2
  have g91 := hF.1; have hF := hF.2
  have g92 := hF.1; have hF := hF.2
  have g93 := hF.1; have hF := hF.2
  have g94 := hF.1; have hF := hF.2
  have g95 := hF.1; have hF := hF.2
  have g96 := hF.1; have hF := hF.2
  have g97 := hF.1; have hF := hF.2
  have g98 := hF.1; have hF := hF.2
  have g99 := hF.1; have hF := hF.2
  have g100 := hF.1; have hF := hF.2
  have g101 := hF.1; have hF := hF.2
  have g102 := hF.1; have hF := hF.2
  have g103 := hF.1; have hF := hF.2
  have g104 := hF.1; have hF := hF.2
  have g105 := hF.1; have hF := hF.2
  have g106 := hF.1; have hF := hF.2
  have g107 := hF.1; have hF := hF.2
  have g108 := hF.1; have hF := hF.2
  have g109 := hF.1; have hF := hF.2
  have g110 := hF.1; have hF := hF.2
  have g111 := hF.1; have hF := hF.2
  have g112 := hF.1; have hF := hF.2
  have g113 := hF.1; have hF := hF.2
  have g114 := hF.1; have hF := hF.2
  have g115 := hF.1; have hF := hF.2
  have g116 := hF.1; have hF := hF.2
  have g117 := hF.1; have hF := hF.2
  have g118 := hF.1; have hF := hF.2
  have g119 := hF.1; have hF := hF.2
  have g120 := hF.1; have hF := hF.2
  have g121 := hF.1; have hF := hF.2
  have g122 := hF.1; have hF := hF.2
  have g123 := hF.1; have hF := hF.2
  have g124 := hF.1; have hF := hF.2
  have g125 := hF.1; have hF := hF.2
  have g126 := hF.1; have hF := hF.2
  have g127 := hF.1; have hF := hF.2
  have g128 := hF.1; have hF := hF.2
  have g129 := hF.1; have hF := hF.2
  have g130 := hF.1; have hF := hF.2
  have g131 := hF.1; have hF := hF.2
  have g132 := hF.1; have hF := hF.2
  have g133 := hF.1; have hF := hF.2
  have g134 := hF.1; have hF := hF.2
  have g135 := hF.1; have hF := hF.2
  have g136 := hF.1; have hF := hF.2
  have g137 := hF.1; have hF := hF.2
  have g138 := hF.1; have hF := hF.2
  have g139 := hF.1; have hF := hF.2
  have g140 := hF.1; have hF := hF.2
  have g141 := hF.1; have hF := hF.2
  have g142 := hF.1; have hF := hF.2
  have g143 := hF.1; have hF := hF.2
  have g144 := hF.1; have hF := hF.2
  have g145 := hF.1; have hF := hF.2
  have g146 := hF.1; have hF := hF.2
  have g147 := hF.1; have hF := hF.2
  have g148 := hF.1; have hF := hF.2
  have g149 := hF.1; have hF := hF.2
  have g150 := hF.1; have hF := hF.2
  have g151 := hF.1; have hF := hF.2
  have g152 := hF.1; have hF := hF.2
  have g153 := hF.1; have hF := hF.2
  have g154 := hF.1; have hF := hF.2
  have g155 := hF.1; have hF := hF.2
  have g156 := hF.1; have hF := hF.2
  have g157 := hF.1; have hF := hF.2
  have g158 := hF.1; have hF := hF.2
  have g159 := hF.1; have hF := hF.2
  have g160 := hF.1; have hF := hF.2
  have g161 := hF.1; have hF := hF.2
  have g162 := hF.1; have hF := hF.2
  have g163 := hF.1; have hF := hF.2
  have g164 := hF.1; have hF := hF.2
  have g165 := hF.1; have hF := hF.2
  have g166 := hF.1; have hF := hF.2
  have g167 := hF.1; have hF := hF.2
  have g168 := hF.1; have hF := hF.2
  have g169 := hF.1; have hF := hF.2
  have g170 := hF.1; have hF := hF.2
  have g171 := hF.1; have hF := hF.2
  have g172 := hF.1; have hF := hF.2
  have g173 := hF.1; have hF := hF.2
  have g174 := hF.1; have hF := hF.2
  have g175 := hF.1; have hF := hF.2
  have g176 := hF.1; have hF := hF.2
  have g177 := hF.1; have hF := hF.2
  have g178 := hF.1; have hF := hF.2
  have g179 := hF.1; have hF := hF.2
  have g180 := hF.1; have hF := hF.2
  have g181 := hF.1; have hF := hF.2
  have g182 := hF.1; have hF := hF.2
  have g183 := hF.1; have hF := hF.2
  have g184 := hF.1; have hF := hF.2
  have g185 := hF.1; have hF := hF.2
  have g186 := hF.1; have hF := hF.2
  have g187 := hF.1; have hF := hF.2
  have g188 := hF.1; have hF := hF.2
  have g189 := hF.1; have hF := hF.2
  have g190 := hF.1; have hF := hF.2
  have g191 := hF.1; have hF := hF.2
  have g192 := hF.1; have hF := hF.2
  have g193 := hF.1; have hF := hF.2
  have g194 := hF.1; have hF := hF.2
  have g195 := hF.1; have hF := hF.2
  have g196 := hF.1; have hF := hF.2
  have g197 := hF.1; have hF := hF.2
  have g198 := hF.1; have hF := hF.2
  have g199 := hF.1; have hF := hF.2
  have g200 := hF.1; have hF := hF.2
  have g201 := hF.1; have hF := hF.2
  have g202 := hF.1; have hF := hF.2
  have g203 := hF.1; have hF := hF.2
  have g204 := hF.1; have hF := hF.2
  have g205 := hF.1; have hF := hF.2
  have g206 := hF.1; have hF := hF.2
  have g207 := hF.1; have hF := hF.2
  have g208 := hF.1; have hF := hF.2
  have g209 := hF.1; have hF := hF.2
  have g210 := hF.1; have hF := hF.2
  have g211 := hF.1; have hF := hF.2
  have g212 := hF.1; have hF := hF.2
  have g213 := hF.1; have hF := hF.2
  have g214 := hF.1; have hF := hF.2
  have g215 := hF.1; have hF := hF.2
  have g216 := hF.1; have hF := hF.2
  have g217 := hF.1; have hF := hF.2
  have g218 := hF.1; have hF := hF.2
  have g219 := hF.1; have hF := hF.2
  have g220 := hF.1; have hF := hF.2
  have g221 := hF.1; have hF := hF.2
  have g222 := hF.1; have hF := hF.2
  have g223 := hF.1; have hF := hF.2
  have g224 := hF.1; have hF := hF.2
  have g225 := hF.1; have hF := hF.2
  have g226 := hF.1; have hF := hF.2
  have g227 := hF.1; have hF := hF.2
  have g228 := hF.1; have hF := hF.2
  have g229 := hF.1; have hF := hF.2
  have g230 := hF.1; have hF := hF.2
  have g231 := hF.1; have hF := hF.2
  have g232 := hF.1; have hF := hF.2
  have g233 := hF.1; have hF := hF.2
  have g234 := hF.1; have hF := hF.2
  have g235 := hF.1; have hF := hF.2
  have g236 := hF.1; have hF := hF.2
  have g237 := hF.1; have hF := hF.2
  have g238 := hF.1; have hF := hF.2
  have g239 := hF.1; have hF := hF.2
  have g240 := hF.1; have hF := hF.2
  have g241 := hF.1; have hF := hF.2
  have g242 := hF.1; have hF := hF.2
  have g243 := hF.1; have hF := hF.2
  have g244 := hF.1; have hF := hF.2
  have g245 := hF.1; have hF := hF.2
  have g246 := hF.1; have hF := hF.2
  have g247 := hF.1; have hF := hF.2
  have g248 := hF.1; have hF := hF.2
  have g249 := hF.1; have hF := hF.2
  have g250 := hF.1; have hF := hF.2
  have g251 := hF.1; have hF := hF.2
  have g252 := hF.1; have hF := hF.2
  have g253 := hF.1; have hF := hF.2
  have g254 := hF.1; have hF := hF.2
  have g255 := hF.1; have hF := hF.2
  have g256 := hF.1; have hF := hF.2
  have g257 := hF.1; have hF := hF.2
  have g258 := hF.1; have hF := hF.2
  have g259 := hF.1; have hF := hF.2
  have g260 := hF.1; have hF := hF.2
  have g261 := hF.1; have hF := hF.2
  have g262 := hF.1; have hF := hF.2
  have g263 := hF.1; have hF := hF.2
  have g264 := hF.1; have hF := hF.2
  have g265 := hF.1; have hF := hF.2
  have g266 := hF.1; have hF := hF.2
  have g267 := hF.1; have hF := hF.2
  have g268 := hF.1; have hF := hF.2
  have g269 := hF.1; have hF := hF.2
  have g270 := hF.1; have hF := hF.2
  have g271 := hF.1; have hF := hF.2
  have g272 := hF.1; have hF := hF.2
  have g273 := hF.1; have hF := hF.2
  have g274 := hF.1; have hF := hF.2
  have g275 := hF.1; have hF := hF.2
  have g276 := hF.1; have hF := hF.2
  have g277 := hF.1; have hF := hF.2
  have g278 := hF.1; have hF := hF.2
  have g279 := hF.1; have hF := hF.2
  have g280 := hF.1; have hF := hF.2
  have g281 := hF.1; have hF := hF.2
  have g282 := hF.1; have hF := hF.2
  have g283 := hF.1; have hF := hF.2
  have g284 := hF.1; have hF := hF.2
  have g285 := hF.1; have hF := hF.2
  have g286 := hF.1; have hF := hF.2
  have g287 := hF.1; have hF := hF.2
  have g288 := hF.1; have hF := hF.2
  have g289 := hF.1; have hF := hF.2
  have g290 := hF.1; have hF := hF.2
  have g291 := hF.1; have hF := hF.2
  have g292 := hF.1; have hF := hF.2
  have g293 := hF.1; have hF := hF.2
  have g294 := hF.1; have hF := hF.2
  have g295 := hF.1; have hF := hF.2
  have g296 := hF.1; have hF := hF.2
  have g297 := hF.1; have hF := hF.2
  have g298 := hF.1; have hF := hF.2
  have g299 := hF.1; have hF := hF.2
  have g300 := hF.1; have hF := hF.2
  have g301 := hF.1; have hF := hF.2
  have g302 := hF.1; have hF := hF.2
  have g303 := hF.1; have hF := hF.2
  have g304 := hF.1; have hF := hF.2
  have g305 := hF.1; have hF := hF.2
  have g306 := hF.1; have hF := hF.2
  have g307 := hF.1; have hF := hF.2
  have g308 := hF.1; have hF := hF.2
  have g309 := hF.1; have hF := hF.2
  have g310 := hF.1; have hF := hF.2
  have g311 := hF.1; have hF := hF.2
  have g312 := hF.1; have hF := hF.2
  have g313 := hF.1; have hF := hF.2
  have g314 := hF.1; have hF := hF.2
  have g315 := hF.1; have hF := hF.2
  have g316 := hF.1; have hF := hF.2
  have g317 := hF.1; have hF := hF.2
  have g318 := hF.1; have hF := hF.2
  have g319 := hF.1; have hF := hF.2
  have g320 := hF.1; have hF := hF.2
  have g321 := hF.1; have hF := hF.2
  have g322 := hF.1; have hF := hF.2
  have g323 := hF.1; have hF := hF.2
  have g324 := hF.1; have hF := hF.2
  have g325 := hF.1; have hF := hF.2
  have g326 := hF.1; have hF := hF.2
  have g327 := hF.1; have hF := hF.2
  have g328 := hF.1; have hF := hF.2
  have g329 := hF.1; have hF := hF.2
  have g330 := hF.1; have hF := hF.2
  have g331 := hF.1; have hF := hF.2
  have g332 := hF.1; have hF := hF.2
  have g333 := hF.1; have hF := hF.2
  have g334 := hF.1; have hF := hF.2
  have g335 := hF.1; have hF := hF.2
  have g336 := hF.1; have hF := hF.2
  have g337 := hF.1; have hF := hF.2
  have g338 := hF.1; have hF := hF.2
  have g339 := hF.1; have hF := hF.2
  have g340 := hF.1; have hF := hF.2
  have g341 := hF.1; have hF := hF.2
  have g342 := hF.1; have hF := hF.2
  have g343 := hF.1; have hF := hF.2
  have g344 := hF.1; have hF := hF.2
  have g345 := hF.1; have hF := hF.2
  have g346 := hF.1; have hF := hF.2
  have g347 := hF.1; have hF := hF.2
  have g348 := hF.1; have hF := hF.2
  have g349 := hF.1; have hF := hF.2
  have g350 := hF.1; have hF := hF.2
  have g351 := hF.1; have hF := hF.2
  have g352 := hF.1; have hF := hF.2
  have g353 := hF.1; have hF := hF.2
  have g354 := hF.1; have hF := hF.2
  have g355 := hF.1; have hF := hF.2
  have g356 := hF.1; have hF := hF.2
  have g357 := hF.1; have hF := hF.2
  have g358 := hF.1; have hF := hF.2
  have g359 := hF.1; have hF := hF.2
  have g360 := hF.1; have hF := hF.2
  have g361 := hF.1; have hF := hF.2
  have g362 := hF.1; have hF := hF.2
  have g363 := hF.1; have hF := hF.2
  have g364 := hF.1; have hF := hF.2
  have g365 := hF.1; have hF := hF.2
  have g366 := hF.1; have hF := hF.2
  have g367 := hF.1; have hF := hF.2
  have g368 := hF.1; have hF := hF.2
  have g369 := hF.1; have hF := hF.2
  have g370 := hF.1; have hF := hF.2
  have g371 := hF.1; have hF := hF.2
  have g372 := hF.1; have hF := hF.2
  have g373 := hF.1; have hF := hF.2
  have g374 := hF.1; have hF := hF.2
  have g375 := hF.1; have hF := hF.2
  have g376 := hF.1; have hF := hF.2
  have g377 := hF.1; have hF := hF.2
  have g378 := hF.1; have hF := hF.2
  have g379 := hF.1; have hF := hF.2
  have g380 := hF.1; have hF := hF.2
  have g381 := hF.1; have hF := hF.2
  have g382 := hF.1; have hF := hF.2
  have g383 := hF.1; have hF := hF.2
  have g384 := hF.1; have hF := hF.2
  have g385 := hF.1; have hF := hF.2
  have g386 := hF.1; have hF := hF.2
  have g387 := hF.1; have hF := hF.2
  have g388 := hF.1; have hF := hF.2
  have g389 := hF.1; have hF := hF.2
  have g390 := hF.1; have hF := hF.2
  have g391 := hF.1; have hF := hF.2
  have g392 := hF.1; have hF := hF.2
  have g393 := hF.1; have hF := hF.2
  have g394 := hF.1; have hF := hF.2
  have g395 := hF.1; have hF := hF.2
  have g396 := hF.1; have hF := hF.2
  have g397 := hF.1; have hF := hF.2
  have g398 := hF.1; have hF := hF.2
  have g399 := hF.1; have hF := hF.2
  have g400 := hF.1; have hF := hF.2
  have g401 := hF.1; have hF := hF.2
  have g402 := hF.1; have hF := hF.2
  have g403 := hF.1; have hF := hF.2
  have g404 := hF.1; have hF := hF.2
  have g405 := hF.1; have hF := hF.2
  have g406 := hF.1; have hF := hF.2
  have g407 := hF.1; have hF := hF.2
  have g408 := hF.1; have hF := hF.2
  have g409 := hF.1; have hF := hF.2
  have g410 := hF.1; have hF := hF.2
  have g411 := hF.1; have hF := hF.2
  have g412 := hF.1; have hF := hF.2
  have g413 := hF.1; have hF := hF.2
  have g414 := hF.1; have hF := hF.2
  have g415 := hF.1; have hF := hF.2
  have g416 := hF.1; have hF := hF.2
  have g417 := hF.1; have hF := hF.2
  have g418 := hF.1; have hF := hF.2
  have g419 := hF.1; have hF := hF.2
  have g420 := hF.1; have hF := hF.2
  have g421 := hF.1; have hF := hF.2
  have g422 := hF.1; have hF := hF.2
  have g423 := hF.1; have hF := hF.2
  have g424 := hF.1; have hF := hF.2
  have g425 := hF.1; have hF := hF.2
  have g426 := hF.1; have hF := hF.2
  have g427 := hF.1; have hF := hF.2
  have g428 := hF.1; have hF := hF.2
  have g429 := hF.1; have hF := hF.2
  have g430 := hF.1; have hF := hF.2
  have g431 := hF.1; have hF := hF.2
  have g432 := hF.1; have hF := hF.2
  have g433 := hF.1; have hF := hF.2
  have g434 := hF.1; have hF := hF.2
  have g435 := hF.1; have hF := hF.2
  have g436 := hF.1; have hF := hF.2
  have g437 := hF.1; have hF := hF.2
  have g438 := hF.1; have hF := hF.2
  have g439 := hF.1; have hF := hF.2
  have g440 := hF.1; have hF := hF.2
  have g441 := hF.1; have hF := hF.2
  have g442 := hF.1; have hF := hF.2
  have g443 := hF.1; have hF := hF.2
  have g444 := hF.1; have hF := hF.2
  have g445 := hF.1; have hF := hF.2
  have g446 := hF.1; have hF := hF.2
  have g447 := hF.1; have hF := hF.2
  have g448 := hF.1; have hF := hF.2
  have g449 := hF.1; have hF := hF.2
  have g450 := hF.1; have hF := hF.2
  have g451 := hF.1; have hF := hF.2
  have g452 := hF.1; have hF := hF.2
  have g453 := hF.1; have hF := hF.2
  have g454 := hF.1; have hF := hF.2
  have g455 := hF.1; have hF := hF.2
  have g456 := hF.1; have hF := hF.2
  have g457 := hF.1; have hF := hF.2
  have g458 := hF.1; have hF := hF.2
  have g459 := hF.1; have hF := hF.2
  have g460 := hF.1; have hF := hF.2
  have g461 := hF.1; have hF := hF.2
  have g462 := hF.1; have hF := hF.2
  have g463 := hF.1; have hF := hF.2
  have g464 := hF.1; have hF := hF.2
  have g465 := hF.1; have hF := hF.2
  have g466 := hF.1; have hF := hF.2
  have g467 := hF.1; have hF := hF.2
  have g468 := hF.1; have hF := hF.2
  have g469 := hF.1; have hF := hF.2
  have g470 := hF.1; have hF := hF.2
  have g471 := hF.1; have hF := hF.2
  have g472 := hF.1; have hF := hF.2
  have g473 := hF.1; have hF := hF.2
  have g474 := hF.1; have hF := hF.2
  have g475 := hF.1; have hF := hF.2
  have g476 := hF.1; have hF := hF.2
  have g477 := hF.1; have hF := hF.2
  have g478 := hF.1; have hF := hF.2
  have g479 := hF.1; have hF := hF.2
  have g480 := hF.1; have hF := hF.2
  have g481 := hF.1; have hF := hF.2
  have g482 := hF.1; have hF := hF.2
  have g483 := hF.1; have hF := hF.2
  have g484 := hF.1; have hF := hF.2
  have g485 := hF.1; have hF := hF.2
  have g486 := hF.1; have hF := hF.2
  have g487 := hF.1; have hF := hF.2
  have g488 := hF.1; have hF := hF.2
  have g489 := hF.1; have hF := hF.2
  have g490 := hF.1; have hF := hF.2
  have g491 := hF.1; have hF := hF.2
  have g492 := hF.1; have hF := hF.2
  have g493 := hF.1; have hF := hF.2
  have g494 := hF.1; have hF := hF.2
  have g495 := hF.1; have hF := hF.2
  have g496 := hF.1; have hF := hF.2
  have g497 := hF.1; have hF := hF.2
  have g498 := hF.1; have hF := hF.2
  have g499 := hF.1; have hF := hF.2
  have g500 := hF.1; have hF := hF.2
  have g501 := hF.1; have hF := hF.2
  have g502 := hF.1; have hF := hF.2
  have g503 := hF.1; have hF := hF.2
  have g504 := hF.1; have hF := hF.2
  have g505 := hF.1; have hF := hF.2
  have g506 := hF.1; have hF := hF.2
  have g507 := hF.1; have hF := hF.2
  have g508 := hF.1; have hF := hF.2
  have g509 := hF.1; have hF := hF.2
  have g510 := hF.1; have hF := hF.2
  have g511 := hF.1; have hF := hF.2
  have g512 := hF.1; have hF := hF.2
  have g513 := hF.1; have hF := hF.2
  have g514 := hF.1; have hF := hF.2
  have g515 := hF.1; have hF := hF.2
  have g516 := hF.1; have hF := hF.2
  have g517 := hF.1; have hF := hF.2
  have g518 := hF.1; have hF := hF.2
  have g519 := hF.1; have hF := hF.2
  have g520 := hF.1; have hF := hF.2
  have g521 := hF.1; have hF := hF.2
  have g522 := hF.1; have hF := hF.2
  have g523 := hF.1; have hF := hF.2
  have g524 := hF.1; have hF := hF.2
  have g525 := hF.1; have hF := hF.2
  have g526 := hF.1; have hF := hF.2
  have g527 := hF.1; have hF := hF.2
  have g528 := hF.1; have hF := hF.2
  have g529 := hF.1; have hF := hF.2
  have g530 := hF.1; have hF := hF.2
  have g531 := hF.1; have hF := hF.2
  have g532 := hF.1; have hF := hF.2
  have g533 := hF.1; have hF := hF.2
  have g534 := hF.1; have hF := hF.2
  have g535 := hF.1; have hF := hF.2
  have g536 := hF.1; have hF := hF.2
  have g537 := hF.1; have hF := hF.2
  have g538 := hF.1; have hF := hF.2
  have g539 := hF.1; have hF := hF.2
  have g540 := hF.1; have hF := hF.2
  have g541 := hF.1; have hF := hF.2
  have g542 := hF.1; have hF := hF.2
  have g543 := hF.1; have hF := hF.2
  have g544 := hF.1; have hF := hF.2
  have g545 := hF.1; have hF := hF.2
  have g546 := hF.1; have hF := hF.2
  have g547 := hF.1; have hF := hF.2
  have g548 := hF.1; have hF := hF.2
  have g549 := hF.1; have hF := hF.2
  have g550 := hF.1; have hF := hF.2
  have g551 := hF.1; have hF := hF.2
  have g552 := hF.1; have hF := hF.2
  have g553 := hF.1; have hF := hF.2
  have g554 := hF.1; have hF := hF.2
  have g555 := hF.1; have hF := hF.2
  have g556 := hF.1; have hF := hF.2
  have g557 := hF.1; have hF := hF.2
  have g558 := hF.1; have hF := hF.2
  have g559 := hF.1; have hF := hF.2
  have g560 := hF.1; have hF := hF.2
  have g561 := hF.1; have hF := hF.2
  have g562 := hF.1; have hF := hF.2
  have g563 := hF.1; have hF := hF.2
  have g564 := hF.1; have hF := hF.2
  have g565 := hF.1; have hF := hF.2
  have g566 := hF.1; have hF := hF.2
  have g567 := hF.1; have hF := hF.2
  have g568 := hF.1; have hF := hF.2
  have g569 := hF.1; have hF := hF.2
  have g570 := hF.1; have hF := hF.2
  have g571 := hF.1; have hF := hF.2
  have g572 := hF.1; have hF := hF.2
  have g573 := hF.1; have hF := hF.2
  have g574 := hF.1; have hF := hF.2
  have g575 := hF.1; have hF := hF.2
  have g576 := hF.1; have hF := hF.2
  have g577 := hF.1; have hF := hF.2
  have g578 := hF.1; have hF := hF.2
  have g579 := hF.1; have hF := hF.2
  have g580 := hF.1; have hF := hF.2
  have g581 := hF.1; have hF := hF.2
  have g582 := hF.1; have hF := hF.2
  have g583 := hF.1; have hF := hF.2
  have g584 := hF.1; have hF := hF.2
  have g585 := hF.1; have hF := hF.2
  have g586 := hF.1; have hF := hF.2
  have g587 := hF.1; have hF := hF.2
  have g588 := hF.1; have hF := hF.2
  have g589 := hF.1; have hF := hF.2
  have g590 := hF.1; have hF := hF.2
  have g591 := hF.1; have hF := hF.2
  have g592 := hF.1; have hF := hF.2
  have g593 := hF.1; have hF := hF.2
  have g594 := hF.1; have hF := hF.2
  have g595 := hF.1; have hF := hF.2
  have g596 := hF.1; have hF := hF.2
  have g597 := hF.1; have hF := hF.2
  have g598 := hF.1; have hF := hF.2
  have g599 := hF.1; have hF := hF.2
  have g600 := hF.1; have hF := hF.2
  have g601 := hF.1; have hF := hF.2
  have g602 := hF.1; have hF := hF.2
  have g603 := hF.1; have hF := hF.2
  have g604 := hF.1; have hF := hF.2
  have g605 := hF.1; have hF := hF.2
  have g606 := hF.1; have hF := hF.2
  have g607 := hF.1; have hF := hF.2
  have g608 := hF.1; have hF := hF.2
  have g609 := hF.1; have hF := hF.2
  have g610 := hF.1; have hF := hF.2
  have g611 := hF.1; have hF := hF.2
  have g612 := hF.1; have hF := hF.2
  have g613 := hF.1; have hF := hF.2
  have g614 := hF.1; have hF := hF.2
  have g615 := hF.1; have hF := hF.2
  have g616 := hF.1; have hF := hF.2
  have g617 := hF.1; have hF := hF.2
  have g618 := hF.1; have hF := hF.2
  have g619 := hF.1; have hF := hF.2
  have g620 := hF.1; have hF := hF.2
  have g621 := hF.1; have hF := hF.2
  have g622 := hF.1; have hF := hF.2
  have g623 := hF.1; have hF := hF.2
  have g624 := hF.1; have hF := hF.2
  have g625 := hF.1; have hF := hF.2
  have g626 := hF.1; have hF := hF.2
  have g627 := hF.1; have hF := hF.2
  have g628 := hF.1; have hF := hF.2
  have g629 := hF.1; have hF := hF.2
  have g630 := hF.1; have hF := hF.2
  have g631 := hF.1; have hF := hF.2
  have g632 := hF.1; have hF := hF.2
  have g633 := hF.1; have hF := hF.2
  have g634 := hF.1; have hF := hF.2
  have g635 := hF.1; have hF := hF.2
  have g636 := hF.1; have hF := hF.2
  have g637 := hF.1; have hF := hF.2
  have g638 := hF.1; have hF := hF.2
  have g639 := hF.1; have hF := hF.2
  have g640 := hF.1; have hF := hF.2
  have g641 := hF.1; have hF := hF.2
  have g642 := hF.1; have hF := hF.2
  have g643 := hF.1; have hF := hF.2
  have g644 := hF.1; have hF := hF.2
  have g645 := hF.1; have hF := hF.2
  have g646 := hF.1; have hF := hF.2
  have g647 := hF.1; have hF := hF.2
  have g648 := hF.1; have hF := hF.2
  have g649 := hF.1; have hF := hF.2
  have g650 := hF.1; have hF := hF.2
  have g651 := hF.1; have hF := hF.2
  have g652 := hF.1; have hF := hF.2
  have g653 := hF.1; have hF := hF.2
  have g654 := hF.1; have hF := hF.2
  have g655 := hF.1; have hF := hF.2
  have g656 := hF.1; have hF := hF.2
  have g657 := hF.1; have hF := hF.2
  have g658 := hF.1; have hF := hF.2
  have g659 := hF.1; have hF := hF.2
  have g660 := hF.1; have hF := hF.2
  have g661 := hF.1; have hF := hF.2
  have g662 := hF.1; have hF := hF.2
  have g663 := hF.1; have hF := hF.2
  have g664 := hF.1; have hF := hF.2
  have g665 := hF.1; have hF := hF.2
  have g666 := hF.1; have hF := hF.2
  have g667 := hF.1; have hF := hF.2
  have g668 := hF.1; have hF := hF.2
  have g669 := hF.1; have hF := hF.2
  have g670 := hF.1; have hF := hF.2
  have g671 := hF.1; have hF := hF.2
  have g672 := hF.1; have hF := hF.2
  have g673 := hF.1; have hF := hF.2
  have g674 := hF.1; have hF := hF.2
  have g675 := hF.1; have hF := hF.2
  have g676 := hF.1; have hF := hF.2
  have g677 := hF.1; have hF := hF.2
  have g678 := hF.1; have hF := hF.2
  have g679 := hF.1; have hF := hF.2
  have g680 := hF.1; have hF := hF.2
  have g681 := hF.1; have hF := hF.2
  have g682 := hF.1; have hF := hF.2
  have g683 := hF.1; have hF := hF.2
  have g684 := hF.1; have hF := hF.2
  have g685 := hF.1; have hF := hF.2
  have g686 := hF.1; have hF := hF.2
  have g687 := hF.1; have hF := hF.2
  have g688 := hF.1; have hF := hF.2
  have g689 := hF.1; have hF := hF.2
  have g690 := hF.1; have hF := hF.2
  have g691 := hF.1; have hF := hF.2
  have g692 := hF.1; have hF := hF.2
  have g693 := hF.1; have hF := hF.2
  have g694 := hF.1; have hF := hF.2
  have g695 := hF.1; have hF := hF.2
  have g696 := hF.1; have hF := hF.2
  have g697 := hF.1; have hF := hF.2
  have g698 := hF.1; have hF := hF.2
  have g699 := hF.1; have hF := hF.2
  have g700 := hF.1; have hF := hF.2
  have g701 := hF.1; have hF := hF.2
  have g702 := hF.1; have hF := hF.2
  have g703 := hF.1; have hF := hF.2
  have g704 := hF.1; have hF := hF.2
  have g705 := hF.1; have hF := hF.2
  have g706 := hF.1; have hF := hF.2
  have g707 := hF.1; have hF := hF.2
  have g708 := hF.1; have hF := hF.2
  have g709 := hF.1; have hF := hF.2
  have g710 := hF.1; have hF := hF.2
  have g711 := hF.1; have hF := hF.2
  have g712 := hF.1; have hF := hF.2
  have g713 := hF.1; have hF := hF.2
  have g714 := hF.1; have hF := hF.2
  have g715 := hF.1; have hF := hF.2
  have g716 := hF.1; have hF := hF.2
  have g717 := hF.1; have hF := hF.2
  have g718 := hF.1; have hF := hF.2
  have g719 := hF.1; have hF := hF.2
  have g720 := hF.1; have hF := hF.2
  have g721 := hF.1; have hF := hF.2
  have g722 := hF.1; have hF := hF.2
  have g723 := hF.1; have hF := hF.2
  have g724 := hF.1; have hF := hF.2
  have g725 := hF.1; have hF := hF.2
  have g726 := hF.1; have hF := hF.2
  have g727 := hF.1; have hF := hF.2
  have g728 := hF.1; have hF := hF.2
  have g729 := hF.1; have hF := hF.2
  have g730 := hF.1; have hF := hF.2
  have g731 := hF.1; have hF := hF.2
  have g732 := hF.1; have hF := hF.2
  have g733 := hF.1; have hF := hF.2
  have g734 := hF.1; have hF := hF.2
  have g735 := hF.1; have hF := hF.2
  have g736 := hF.1; have hF := hF.2
  have g737 := hF.1; have hF := hF.2
  have g738 := hF.1; have hF := hF.2
  have g739 := hF.1; have hF := hF.2
  have g740 := hF.1; have hF := hF.2
  have g741 := hF.1; have hF := hF.2
  have g742 := hF.1; have hF := hF.2
  have g743 := hF.1; have hF := hF.2
  have g744 := hF.1; have hF := hF.2
  have g745 := hF.1; have hF := hF.2
  have g746 := hF.1; have hF := hF.2
  have g747 := hF.1; have hF := hF.2
  have g748 := hF.1; have hF := hF.2
  have g749 := hF.1; have hF := hF.2
  have g750 := hF.1; have hF := hF.2
  have g751 := hF.1; have hF := hF.2
  have g752 := hF.1; have hF := hF.2
  have g753 := hF.1; have hF := hF.2
  have g754 := hF.1; have hF := hF.2
  have g755 := hF.1; have hF := hF.2
  have g756 := hF.1; have hF := hF.2
  have g757 := hF.1; have hF := hF.2
  have g758 := hF.1; have hF := hF.2
  have g759 := hF.1; have hF := hF.2
  have g760 := hF.1; have hF := hF.2
  have g761 := hF.1; have hF := hF.2
  have g762 := hF.1; have hF := hF.2
  have g763 := hF.1; have hF := hF.2
  have g764 := hF.1; have hF := hF.2
  have g765 := hF.1; have hF := hF.2
  have g766 := hF.1; have hF := hF.2
  have g767 := hF.1; have hF := hF.2
  have g768 := hF.1; have hF := hF.2
  have g769 := hF.1; have hF := hF.2
  have g770 := hF.1; have hF := hF.2
  have g771 := hF.1; have hF := hF.2
  have g772 := hF.1; have hF := hF.2
  have g773 := hF.1; have hF := hF.2
  have g774 := hF.1; have hF := hF.2
  have g775 := hF.1; have hF := hF.2
  have g776 := hF.1; have hF := hF.2
  have g777 := hF.1; have hF := hF.2
  have g778 := hF.1; have hF := hF.2
  have g779 := hF.1; have hF := hF.2
  have g780 := hF.1; have hF := hF.2
  have g781 := hF.1; have hF := hF.2
  have g782 := hF.1; have hF := hF.2
  have g783 := hF.1; have hF := hF.2
  have g784 := hF.1; have hF := hF.2
  have g785 := hF.1; have hF := hF.2
  have g786 := hF.1; have hF := hF.2
  have g787 := hF.1; have hF := hF.2
  have g788 := hF.1; have hF := hF.2
  have g789 := hF.1; have hF := hF.2
  have g790 := hF.1; have hF := hF.2
  have g791 := hF.1; have hF := hF.2
  have g792 := hF.1; have hF := hF.2
  have g793 := hF.1; have hF := hF.2
  have g794 := hF.1; have hF := hF.2
  have g795 := hF.1; have hF := hF.2
  have g796 := hF.1; have hF := hF.2
  have g797 := hF.1; have hF := hF.2
  have g798 := hF.1; have hF := hF.2
  have g799 := hF.1; have hF := hF.2
  have g800 := hF.1; have hF := hF.2
  have g801 := hF.1; have hF := hF.2
  have g802 := hF.1; have hF := hF.2
  have g803 := hF.1; have hF := hF.2
  have g804 := hF.1; have hF := hF.2
  have g805 := hF.1; have hF := hF.2
  have g806 := hF.1; have hF := hF.2
  have g807 := hF.1; have hF := hF.2
  have g808 := hF.1; have hF := hF.2
  have g809 := hF.1; have hF := hF.2
  have g810 := hF.1; have hF := hF.2
  have g811 := hF.1; have hF := hF.2
  have g812 := hF.1; have hF := hF.2
  have g813 := hF.1; have hF := hF.2
  have g814 := hF.1; have hF := hF.2
  have g815 := hF.1; have hF := hF.2
  have g816 := hF.1; have hF := hF.2
  have g817 := hF.1; have hF := hF.2
  have g818 := hF.1; have hF := hF.2
  have g819 := hF.1; have hF := hF.2
  have g820 := hF.1; have hF := hF.2
  have g821 := hF.1; have hF := hF.2
  have g822 := hF.1; have hF := hF.2
  have g823 := hF.1; have hF := hF.2
  have g824 := hF.1; have hF := hF.2
  have g825 := hF.1; have hF := hF.2
  have g826 := hF.1; have hF := hF.2
  have g827 := hF.1; have hF := hF.2
  have g828 := hF.1; have hF := hF.2
  have g829 := hF.1; have hF := hF.2
  have g830 := hF.1; have hF := hF.2
  have g831 := hF.1; have hF := hF.2
  have g832 := hF.1; have hF := hF.2
  have g833 := hF.1; have hF := hF.2
  have g834 := hF.1; have hF := hF.2
  have g835 := hF.1; have hF := hF.2
  have g836 := hF.1; have hF := hF.2
  have g837 := hF.1; have hF := hF.2
  have g838 := hF.1; have hF := hF.2
  have g839 := hF.1; have hF := hF.2
  have g840 := hF.1; have hF := hF.2
  have g841 := hF.1; have hF := hF.2
  have g842 := hF.1; have hF := hF.2
  have g843 := hF.1; have hF := hF.2
  have g844 := hF.1; have hF := hF.2
  have g845 := hF.1; have hF := hF.2
  have g846 := hF.1; have hF := hF.2
  have g847 := hF.1; have hF := hF.2
  have g848 := hF.1; have hF := hF.2
  have g849 := hF.1; have hF := hF.2
  have g850 := hF.1; have hF := hF.2
  have g851 := hF.1; have hF := hF.2
  have g852 := hF.1; have hF := hF.2
  have g853 := hF.1; have hF := hF.2
  have g854 := hF.1; have hF := hF.2
  have g855 := hF.1; have hF := hF.2
  have g856 := hF.1; have hF := hF.2
  have g857 := hF.1; have hF := hF.2
  have g858 := hF.1; have hF := hF.2
  have g859 := hF.1; have hF := hF.2
  have g860 := hF.1; have hF := hF.2
  have g861 := hF.1; have hF := hF.2
  have g862 := hF.1; have hF := hF.2
  have g863 := hF.1; have hF := hF.2
  have g864 := hF.1; have hF := hF.2
  have g865 := hF.1; have hF := hF.2
  have g866 := hF.1; have hF := hF.2
  have g867 := hF.1; have hF := hF.2
  have g868 := hF.1; have hF := hF.2
  have g869 := hF.1; have hF := hF.2
  have g870 := hF.1; have hF := hF.2
  have g871 := hF.1; have hF := hF.2
  have g872 := hF.1; have hF := hF.2
  have g873 := hF.1; have hF := hF.2
  have g874 := hF.1; have hF := hF.2
  have g875 := hF.1; have hF := hF.2
  have g876 := hF.1; have hF := hF.2
  have g877 := hF.1; have hF := hF.2
  have g878 := hF.1; have hF := hF.2
  have g879 := hF.1; have hF := hF.2
  have g880 := hF.1; have hF := hF.2
  have g881 := hF.1; have hF := hF.2
  have g882 := hF.1; have hF := hF.2
  have g883 := hF.1; have hF := hF.2
  have g884 := hF.1; have hF := hF.2
  have g885 := hF.1; have hF := hF.2
  have g886 := hF.1; have hF := hF.2
  have g887 := hF.1; have hF := hF.2
  have g888 := hF.1; have hF := hF.2
  have g889 := hF.1; have hF := hF.2
  have g890 := hF.1; have hF := hF.2
  have g891 := hF.1; have hF := hF.2
  have g892 := hF.1; have hF := hF.2
  have g893 := hF.1; have hF := hF.2
  have g894 := hF.1; have hF := hF.2
  have g895 := hF.1; have hF := hF.2
  have g896 := hF.1; have hF := hF.2
  have g897 := hF.1; have hF := hF.2
  have g898 := hF.1; have hF := hF.2
  have g899 := hF.1; have hF := hF.2
  have g900 := hF.1; have hF := hF.2
  have g901 := hF.1; have hF := hF.2
  have g902 := hF.1; have hF := hF.2
  have g903 := hF.1; have hF := hF.2
  have g904 := hF.1; have hF := hF.2
  have g905 := hF.1; have hF := hF.2
  have g906 := hF.1; have hF := hF.2
  have g907 := hF.1; have hF := hF.2
  have g908 := hF.1; have hF := hF.2
  have g909 := hF.1; have hF := hF.2
  have g910 := hF.1; have hF := hF.2
  have g911 := hF.1; have hF := hF.2
  have g912 := hF.1; have hF := hF.2
  have g913 := hF.1; have hF := hF.2
  have g914 := hF.1; have hF := hF.2
  have g915 := hF.1; have hF := hF.2
  have g916 := hF.1; have hF := hF.2
  have g917 := hF.1; have hF := hF.2
  have g918 := hF.1; have hF := hF.2
  have g919 := hF.1; have hF := hF.2
  have g920 := hF.1; have hF := hF.2
  have g921 := hF.1; have hF := hF.2
  have g922 := hF.1; have hF := hF.2
  have g923 := hF.1; have hF := hF.2
  have g924 := hF.1; have hF := hF.2
  have g925 := hF.1; have hF := hF.2
  have g926 := hF.1; have hF := hF.2
  have g927 := hF.1; have hF := hF.2
  have g928 := hF.1; have hF := hF.2
  have g929 := hF.1; have hF := hF.2
  have g930 := hF.1; have hF := hF.2
  have g931 := hF.1; have hF := hF.2
  have g932 := hF.1; have hF := hF.2
  have g933 := hF.1; have hF := hF.2
  have g934 := hF.1; have hF := hF.2
  have g935 := hF.1; have hF := hF.2
  have g936 := hF.1; have hF := hF.2
  have g937 := hF.1; have hF := hF.2
  have g938 := hF.1; have hF := hF.2
  have g939 := hF.1; have hF := hF.2
  have g940 := hF.1; have hF := hF.2
  have g941 := hF.1; have hF := hF.2
  have g942 := hF.1; have hF := hF.2
  have g943 := hF.1; have hF := hF.2
  have g944 := hF.1; have hF := hF.2
  have g945 := hF.1; have hF := hF.2
  have g946 := hF.1; have hF := hF.2
  have g947 := hF.1; have hF := hF.2
  have g948 := hF.1; have hF := hF.2
  have g949 := hF.1; have hF := hF.2
  have g950 := hF.1; have hF := hF.2
  have g951 := hF.1; have hF := hF.2
  have g952 := hF.1; have hF := hF.2
  have g953 := hF.1; have hF := hF.2
  have g954 := hF.1; have hF := hF.2
  have g955 := hF.1; have hF := hF.2
  have g956 := hF.1; have hF := hF.2
  have g957 := hF.1; have hF := hF.2
  have g958 := hF.1; have hF := hF.2
  have g959 := hF.1; have hF := hF.2
  have g960 := hF.1; have hF := hF.2
  have g961 := hF.1; have hF := hF.2
  have g962 := hF.1; have hF := hF.2
  have g963 := hF.1; have hF := hF.2
  have g964 := hF.1; have hF := hF.2
  have g965 := hF.1; have hF := hF.2
  have g966 := hF.1; have hF := hF.2
  have g967 := hF.1; have hF := hF.2
  have g968 := hF.1; have hF := hF.2
  have g969 := hF.1; have hF := hF.2
  have g970 := hF.1; have hF := hF.2
  have g971 := hF.1; have hF := hF.2
  have g972 := hF.1; have hF := hF.2
  have g973 := hF.1; have hF := hF.2
  have g974 := hF.1; have hF := hF.2
  have g975 := hF.1; have hF := hF.2
  have g976 := hF.1; have hF := hF.2
  have g977 := hF.1; have hF := hF.2
  have g978 := hF.1; have hF := hF.2
  have g979 := hF.1; have hF := hF.2
  have g980 := hF.1; have hF := hF.2
  have g981 := hF.1; have hF := hF.2
  have g982 := hF.1; have hF := hF.2
  have g983 := hF.1; have hF := hF.2
  have g984 := hF.1; have hF := hF.2
  have g985 := hF.1; have hF := hF.2
  have g986 := hF.1; have hF := hF.2
  have g987 := hF.1; have hF := hF.2
  have g988 := hF.1; have hF := hF.2
  have g989 := hF.1; have hF := hF.2
  have g990 := hF.1; have hF := hF.2
  have g991 := hF.1; have hF := hF.2
  have g992 := hF.1; have hF := hF.2
  have g993 := hF.1; have hF := hF.2
  have g994 := hF.1; have hF := hF.2
  have g995 := hF.1; have hF := hF.2
  have g996 := hF.1; have hF := hF.2
  have g997 := hF.1; have hF := hF.2
  have g998 := hF.1; have hF := hF.2
  have g999 := hF.1; have hF := hF.2
  have g1000 := hF.1; have hF := hF.2
  have g1001 := hF.1; have hF := hF.2
  have g1002 := hF.1; have hF := hF.2
  have g1003 := hF.1; have hF := hF.2
  have g1004 := hF.1; have hF := hF.2
  have g1005 := hF.1; have hF := hF.2
  have g1006 := hF.1; have hF := hF.2
  have g1007 := hF.1; have hF := hF.2
  have g1008 := hF.1; have hF := hF.2
  have g1009 := hF.1; have hF := hF.2
  have g1010 := hF.1; have hF := hF.2
  have g1011 := hF.1; have hF := hF.2
  have g1012 := hF.1; have hF := hF.2
  have g1013 := hF.1; have hF := hF.2
  have g1014 := hF.1; have hF := hF.2
  have g1015 := hF.1; have hF := hF.2
  have g1016 := hF.1; have hF := hF.2
  have g1017 := hF.1; have hF := hF.2
  have g1018 := hF.1; have hF := hF.2
  have g1019 := hF.1; have hF := hF.2
  have g1020 := hF.1; have hF := hF.2
  have g1021 := hF.1; have hF := hF.2
  have g1022 := hF.1; have hF := hF.2
  have g1023 := hF.1; have hF := hF.2
  have g1024 := hF.1; have hF := hF.2
  have g1025 := hF.1; have hF := hF.2
  have g1026 := hF.1; have hF := hF.2
  have g1027 := hF.1; have hF := hF.2
  have g1028 := hF.1; have hF := hF.2
  have g1029 := hF.1; have hF := hF.2
  have g1030 := hF.1; have hF := hF.2
  have g1031 := hF.1; have hF := hF.2
  have g1032 := hF.1; have hF := hF.2
  have g1033 := hF.1; have hF := hF.2
  have g1034 := hF.1; have hF := hF.2
  have g1035 := hF.1; have hF := hF.2
  have g1036 := hF.1; have hF := hF.2
  have g1037 := hF.1; have hF := hF.2
  have g1038 := hF.1; have hF := hF.2
  have g1039 := hF.1; have hF := hF.2
  have g1040 := hF.1; have hF := hF.2
  have g1041 := hF.1; have hF := hF.2
  have g1042 := hF.1; have hF := hF.2
  have g1043 := hF.1; have hF := hF.2
  have g1044 := hF.1; have hF := hF.2
  have g1045 := hF.1; have hF := hF.2
  have g1046 := hF.1; have hF := hF.2
  have g1047 := hF.1; have hF := hF.2
  have g1048 := hF.1; have hF := hF.2
  have g1049 := hF.1; have hF := hF.2
  have g1050 := hF.1; have hF := hF.2
  have g1051 := hF.1; have hF := hF.2
  have g1052 := hF.1; have hF := hF.2
  have g1053 := hF.1; have hF := hF.2
  have g1054 := hF.1; have hF := hF.2
  have g1055 := hF.1; have hF := hF.2
  have g1056 := hF.1; have hF := hF.2
  have g1057 := hF.1; have hF := hF.2
  have g1058 := hF.1; have hF := hF.2
  have g1059 := hF.1; have hF := hF.2
  have g1060 := hF.1; have hF := hF.2
  have g1061 := hF.1; have hF := hF.2
  have g1062 := hF.1; have hF := hF.2
  have g1063 := hF.1; have hF := hF.2
  have g1064 := hF.1; have hF := hF.2
  have g1065 := hF.1; have hF := hF.2
  have g1066 := hF.1; have hF := hF.2
  have g1067 := hF.1; have hF := hF.2
  have g1068 := hF.1; have hF := hF.2
  have g1069 := hF.1; have hF := hF.2
  have g1070 := hF.1; have hF := hF.2
  have g1071 := hF.1; have hF := hF.2
  have g1072 := hF.1; have hF := hF.2
  have g1073 := hF.1; have hF := hF.2
  have g1074 := hF.1; have hF := hF.2
  have g1075 := hF.1; have hF := hF.2
  have g1076 := hF.1; have hF := hF.2
  have g1077 := hF.1; have hF := hF.2
  have g1078 := hF.1; have hF := hF.2
  have g1079 := hF.1; have hF := hF.2
  have g1080 := hF.1; have hF := hF.2
  have g1081 := hF.1; have hF := hF.2
  have g1082 := hF.1; have hF := hF.2
  have g1083 := hF.1; have hF := hF.2
  have g1084 := hF.1; have hF := hF.2
  have g1085 := hF.1; have hF := hF.2
  have g1086 := hF.1; have hF := hF.2
  have g1087 := hF.1; have hF := hF.2
  have g1088 := hF.1; have hF := hF.2
  have g1089 := hF.1; have hF := hF.2
  have g1090 := hF.1; have hF := hF.2
  have g1091 := hF.1; have hF := hF.2
  have g1092 := hF.1; have hF := hF.2
  have g1093 := hF.1; have hF := hF.2
  have g1094 := hF.1; have hF := hF.2
  have g1095 := hF.1; have hF := hF.2
  have g1096 := hF.1; have hF := hF.2
  have g1097 := hF.1; have hF := hF.2
  have g1098 := hF.1; have hF := hF.2
  have g1099 := hF.1; have hF := hF.2
  have g1100 := hF.1; have hF := hF.2
  have g1101 := hF.1; have hF := hF.2
  have g1102 := hF.1; have hF := hF.2
  have g1103 := hF.1; have hF := hF.2
  have g1104 := hF.1; have hF := hF.2
  have g1105 := hF.1; have hF := hF.2
  have g1106 := hF.1; have hF := hF.2
  have g1107 := hF.1; have hF := hF.2
  have g1108 := hF.1; have hF := hF.2
  have g1109 := hF.1; have hF := hF.2
  have g1110 := hF.1; have hF := hF.2
  have g1111 := hF.1; have hF := hF.2
  have g1112 := hF.1; have hF := hF.2
  have g1113 := hF.1; have hF := hF.2
  have g1114 := hF.1; have hF := hF.2
  have g1115 := hF.1; have hF := hF.2
  have g1116 := hF.1; have hF := hF.2
  have g1117 := hF.1; have hF := hF.2
  have g1118 := hF.1; have hF := hF.2
  have g1119 := hF.1; have hF := hF.2
  have g1120 := hF.1; have hF := hF.2
  have g1121 := hF.1; have hF := hF.2
  have g1122 := hF.1; have hF := hF.2
  have g1123 := hF.1; have hF := hF.2
  have g1124 := hF.1; have hF := hF.2
  have g1125 := hF.1; have hF := hF.2
  have g1126 := hF.1; have hF := hF.2
  have g1127 := hF.1; have hF := hF.2
  have g1128 := hF.1; have hF := hF.2
  have g1129 := hF.1; have hF := hF.2
  have g1130 := hF.1; have hF := hF.2
  have g1131 := hF.1; have hF := hF.2
  have g1132 := hF.1; have hF := hF.2
  have g1133 := hF.1; have hF := hF.2
  have g1134 := hF.1; have hF := hF.2
  have g1135 := hF.1; have hF := hF.2
  have g1136 := hF.1; have hF := hF.2
  have g1137 := hF.1; have hF := hF.2
  have g1138 := hF.1; have hF := hF.2
  have g1139 := hF.1; have hF := hF.2
  have g1140 := hF.1; have hF := hF.2
  have g1141 := hF.1; have hF := hF.2
  have g1142 := hF.1; have hF := hF.2
  have g1143 := hF.1; have hF := hF.2
  have g1144 := hF.1; have hF := hF.2
  have g1145 := hF.1; have hF := hF.2
  have g1146 := hF.1; have hF := hF.2
  have g1147 := hF.1; have hF := hF.2
  have g1148 := hF.1; have hF := hF.2
  have g1149 := hF.1; have hF := hF.2
  have g1150 := hF.1; have hF := hF.2
  have g1151 := hF.1; have hF := hF.2
  have g1152 := hF.1; have hF := hF.2
  have g1153 := hF.1; have hF := hF.2
  have g1154 := hF.1; have hF := hF.2
  have g1155 := hF.1; have hF := hF.2
  have g1156 := hF.1; have hF := hF.2
  have g1157 := hF.1; have hF := hF.2
  have g1158 := hF.1; have hF := hF.2
  have g1159 := hF.1; have hF := hF.2
  have g1160 := hF.1; have hF := hF.2
  have g1161 := hF.1; have hF := hF.2
  have g1162 := hF.1; have hF := hF.2
  have g1163 := hF.1; have hF := hF.2
  have g1164 := hF.1; have hF := hF.2
  have g1165 := hF.1; have hF := hF.2
  have g1166 := hF.1; have hF := hF.2
  have g1167 := hF.1; have hF := hF.2
  have g1168 := hF.1; have hF := hF.2
  have g1169 := hF.1; have hF := hF.2
  have g1170 := hF.1; have hF := hF.2
  have g1171 := hF.1; have hF := hF.2
  have g1172 := hF.1; have hF := hF.2
  have g1173 := hF.1; have hF := hF.2
  have g1174 := hF.1; have hF := hF.2
  have g1175 := hF.1; have hF := hF.2
  have g1176 := hF.1; have hF := hF.2
  have g1177 := hF.1; have hF := hF.2
  have g1178 := hF.1; have hF := hF.2
  have g1179 := hF.1; have hF := hF.2
  have g1180 := hF.1; have hF := hF.2
  have g1181 := hF.1; have hF := hF.2
  have g1182 := hF.1; have hF := hF.2
  have g1183 := hF.1; have hF := hF.2
  have g1184 := hF.1; have hF := hF.2
  have g1185 := hF.1; have hF := hF.2
  have g1186 := hF.1; have hF := hF.2
  have g1187 := hF.1; have hF := hF.2
  have g1188 := hF.1; have hF := hF.2
  have g1189 := hF.1; have hF := hF.2
  have g1190 := hF.1; have hF := hF.2
  have g1191 := hF.1; have hF := hF.2
  have g1192 := hF.1; have hF := hF.2
  have g1193 := hF.1; have hF := hF.2
  have g1194 := hF.1; have hF := hF.2
  have g1195 := hF.1; have hF := hF.2
  have g1196 := hF.1; have hF := hF.2
  have g1197 := hF.1; have hF := hF.2
  have g1198 := hF.1; have hF := hF.2
  have g1199 := hF.1; have hF := hF.2
  have g1200 := hF.1; have hF := hF.2
  have g1201 := hF.1; have hF := hF.2
  have g1202 := hF.1; have hF := hF.2
  have g1203 := hF.1; have hF := hF.2
  have g1204 := hF.1; have hF := hF.2
  have g1205 := hF.1; have hF := hF.2
  have g1206 := hF.1; have hF := hF.2
  have g1207 := hF.1; have hF := hF.2
  have g1208 := hF.1; have hF := hF.2
  have g1209 := hF.1; have hF := hF.2
  have g1210 := hF.1; have hF := hF.2
  have g1211 := hF.1; have hF := hF.2
  have g1212 := hF.1; have hF := hF.2
  have g1213 := hF.1; have hF := hF.2
  have g1214 := hF.1; have hF := hF.2
  have g1215 := hF.1; have hF := hF.2
  have g1216 := hF.1; have hF := hF.2
  have g1217 := hF.1; have hF := hF.2
  have g1218 := hF.1; have hF := hF.2
  have g1219 := hF.1; have hF := hF.2
  have g1220 := hF.1; have hF := hF.2
  have g1221 := hF.1; have hF := hF.2
  have g1222 := hF.1; have hF := hF.2
  have g1223 := hF.1; have hF := hF.2
  have g1224 := hF.1; have hF := hF.2
  have g1225 := hF.1; have hF := hF.2
  have g1226 := hF.1; have hF := hF.2
  have g1227 := hF.1; have hF := hF.2
  have g1228 := hF.1; have hF := hF.2
  have g1229 := hF.1; have hF := hF.2
  have g1230 := hF.1; have hF := hF.2
  have g1231 := hF.1; have hF := hF.2
  have g1232 := hF.1; have hF := hF.2
  have g1233 := hF.1; have hF := hF.2
  have g1234 := hF.1; have hF := hF.2
  have g1235 := hF.1; have hF := hF.2
  have g1236 := hF.1; have hF := hF.2
  have g1237 := hF.1; have hF := hF.2
  have g1238 := hF.1; have hF := hF.2
  have g1239 := hF.1; have hF := hF.2
  have g1240 := hF.1; have hF := hF.2
  have g1241 := hF.1; have hF := hF.2
  have g1242 := hF.1; have hF := hF.2
  have g1243 := hF.1; have hF := hF.2
  have g1244 := hF.1; have hF := hF.2
  have g1245 := hF.1; have hF := hF.2
  have g1246 := hF.1; have hF := hF.2
  have g1247 := hF.1; have hF := hF.2
  have g1248 := hF.1; have hF := hF.2
  have g1249 := hF.1; have hF := hF.2
  have g1250 := hF.1; have hF := hF.2
  have g1251 := hF.1; have hF := hF.2
  have g1252 := hF.1; have hF := hF.2
  have g1253 := hF.1; have hF := hF.2
  have g1254 := hF.1; have hF := hF.2
  have g1255 := hF.1; have hF := hF.2
  have g1256 := hF.1; have hF := hF.2
  have g1257 := hF.1; have hF := hF.2
  have g1258 := hF.1; have hF := hF.2
  have g1259 := hF.1; have hF := hF.2
  have g1260 := hF.1; have hF := hF.2
  have g1261 := hF.1; have hF := hF.2
  have g1262 := hF.1; have hF := hF.2
  have g1263 := hF.1; have hF := hF.2
  have g1264 := hF.1; have hF := hF.2
  have g1265 := hF.1; have hF := hF.2
  have g1266 := hF.1; have hF := hF.2
  have g1267 := hF.1; have hF := hF.2
  have g1268 := hF.1; have hF := hF.2
  have g1269 := hF.1; have hF := hF.2
  have g1270 := hF.1; have hF := hF.2
  have g1271 := hF.1; have hF := hF.2
  have g1272 := hF.1; have hF := hF.2
  have g1273 := hF.1; have hF := hF.2
  have g1274 := hF.1; have hF := hF.2
  have g1275 := hF.1; have hF := hF.2
  have g1276 := hF.1; have hF := hF.2
  have g1277 := hF.1; have hF := hF.2
  have g1278 := hF.1; have hF := hF.2
  have g1279 := hF.1; have hF := hF.2
  have g1280 := hF.1; have hF := hF.2
  have g1281 := hF.1; have hF := hF.2
  have g1282 := hF.1; have hF := hF.2
  have g1283 := hF.1; have hF := hF.2
  have g1284 := hF.1; have hF := hF.2
  have g1285 := hF.1; have hF := hF.2
  have g1286 := hF.1; have hF := hF.2
  have g1287 := hF.1; have hF := hF.2
  have g1288 := hF.1; have hF := hF.2
  have g1289 := hF.1; have hF := hF.2
  have g1290 := hF.1; have hF := hF.2
  have g1291 := hF.1; have hF := hF.2
  have g1292 := hF.1; have hF := hF.2
  have g1293 := hF.1; have hF := hF.2
  have g1294 := hF.1; have hF := hF.2
  have g1295 := hF.1; have hF := hF.2
  have g1296 := hF.1; have hF := hF.2
  have g1297 := hF.1; have hF := hF.2
  have g1298 := hF.1; have hF := hF.2
  have g1299 := hF.1; have hF := hF.2
  have g1300 := hF.1; have hF := hF.2
  have g1301 := hF.1; have hF := hF.2
  have g1302 := hF.1; have hF := hF.2
  have g1303 := hF.1; have hF := hF.2
  have g1304 := hF.1; have hF := hF.2
  have g1305 := hF.1; have hF := hF.2
  have g1306 := hF.1; have hF := hF.2
  have g1307 := hF.1; have hF := hF.2
  have g1308 := hF.1; have hF := hF.2
  have g1309 := hF.1; have hF := hF.2
  have g1310 := hF.1; have hF := hF.2
  have g1311 := hF.1; have hF := hF.2
  have g1312 := hF.1; have hF := hF.2
  have g1313 := hF.1; have hF := hF.2
  have g1314 := hF.1; have hF := hF.2
  have g1315 := hF.1; have hF := hF.2
  have g1316 := hF.1; have hF := hF.2
  have g1317 := hF.1; have hF := hF.2
  have g1318 := hF.1; have hF := hF.2
  have g1319 := hF.1; have hF := hF.2
  have g1320 := hF.1; have hF := hF.2
  have g1321 := hF.1; have hF := hF.2
  have g1322 := hF.1; have hF := hF.2
  have g1323 := hF.1; have hF := hF.2
  intro n i b hn hi hb
  match n, i, b, hn, hi, hb with
  | 0, 0, 0, _, _, _ => exact ⟨EF env (.n 1127), outCell_sound _ σ K201 0 1127 0 (by decide),
      by rw [show EF env (.n 1127) = qv inp (.HB 0 0) from g1152,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 0 0 (by decide) (by decide)]; rfl⟩
  | 0, 0, 1, _, _, _ => exact ⟨EF env (.n 1126), outCell_sound _ σ K201 1 1126 1 (by decide),
      by rw [show EF env (.n 1126) = qv inp (.HB 0 0) from g1153,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 0 1 (by decide) (by decide)]; rfl⟩
  | 0, 0, 2, _, _, _ => exact ⟨EF env (.n 1125), outCell_sound _ σ K201 2 1125 2 (by decide),
      by rw [show EF env (.n 1125) = qv inp (.HB 0 0) from g1154,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 0 2 (by decide) (by decide)]; rfl⟩
  | 0, 0, 3, _, _, _ => exact ⟨EF env (.n 1124), outCell_sound _ σ K201 3 1124 3 (by decide),
      by rw [show EF env (.n 1124) = qv inp (.HB 0 0) from g1155,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 0 3 (by decide) (by decide)]; rfl⟩
  | 0, 1, 0, _, _, _ => exact ⟨EF env (.n 1123), outCell_sound _ σ K201 4 1123 0 (by decide),
      by rw [show EF env (.n 1123) = qv inp (.HB 0 1) from g1156,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 1 0 (by decide) (by decide)]; rfl⟩
  | 0, 1, 1, _, _, _ => exact ⟨EF env (.n 1122), outCell_sound _ σ K201 5 1122 1 (by decide),
      by rw [show EF env (.n 1122) = qv inp (.HB 0 1) from g1157,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 1 1 (by decide) (by decide)]; rfl⟩
  | 0, 1, 2, _, _, _ => exact ⟨EF env (.n 1121), outCell_sound _ σ K201 6 1121 2 (by decide),
      by rw [show EF env (.n 1121) = qv inp (.HB 0 1) from g1158,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 1 2 (by decide) (by decide)]; rfl⟩
  | 0, 1, 3, _, _, _ => exact ⟨EF env (.n 1120), outCell_sound _ σ K201 7 1120 3 (by decide),
      by rw [show EF env (.n 1120) = qv inp (.HB 0 1) from g1159,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 1 3 (by decide) (by decide)]; rfl⟩
  | 0, 2, 0, _, _, _ => exact ⟨EF env (.n 1119), outCell_sound _ σ K201 8 1119 0 (by decide),
      by rw [show EF env (.n 1119) = qv inp (.HB 0 2) from g1160,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 2 0 (by decide) (by decide)]; rfl⟩
  | 0, 2, 1, _, _, _ => exact ⟨EF env (.n 1118), outCell_sound _ σ K201 9 1118 1 (by decide),
      by rw [show EF env (.n 1118) = qv inp (.HB 0 2) from g1161,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 2 1 (by decide) (by decide)]; rfl⟩
  | 0, 2, 2, _, _, _ => exact ⟨EF env (.n 1117), outCell_sound _ σ K201 10 1117 2 (by decide),
      by rw [show EF env (.n 1117) = qv inp (.HB 0 2) from g1162,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 2 2 (by decide) (by decide)]; rfl⟩
  | 0, 2, 3, _, _, _ => exact ⟨EF env (.n 1116), outCell_sound _ σ K201 11 1116 3 (by decide),
      by rw [show EF env (.n 1116) = qv inp (.HB 0 2) from g1163,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 2 3 (by decide) (by decide)]; rfl⟩
  | 0, 3, 0, _, _, _ => exact ⟨EF env (.n 1115), outCell_sound _ σ K201 12 1115 0 (by decide),
      by rw [show EF env (.n 1115) = qv inp (.HB 0 3) from g1164,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 3 0 (by decide) (by decide)]; rfl⟩
  | 0, 3, 1, _, _, _ => exact ⟨EF env (.n 1114), outCell_sound _ σ K201 13 1114 1 (by decide),
      by rw [show EF env (.n 1114) = qv inp (.HB 0 3) from g1165,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 3 1 (by decide) (by decide)]; rfl⟩
  | 0, 3, 2, _, _, _ => exact ⟨EF env (.n 1113), outCell_sound _ σ K201 14 1113 2 (by decide),
      by rw [show EF env (.n 1113) = qv inp (.HB 0 3) from g1166,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 3 2 (by decide) (by decide)]; rfl⟩
  | 0, 3, 3, _, _, _ => exact ⟨EF env (.n 1112), outCell_sound _ σ K201 15 1112 3 (by decide),
      by rw [show EF env (.n 1112) = qv inp (.HB 0 3) from g1167,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 3 3 (by decide) (by decide)]; rfl⟩
  | 0, 4, 0, _, _, _ => exact ⟨EF env (.n 1111), outCell_sound _ σ K201 16 1111 0 (by decide),
      by rw [show EF env (.n 1111) = qv inp (.HB 0 4) from g1168,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 4 0 (by decide) (by decide)]; rfl⟩
  | 0, 4, 1, _, _, _ => exact ⟨EF env (.n 1110), outCell_sound _ σ K201 17 1110 1 (by decide),
      by rw [show EF env (.n 1110) = qv inp (.HB 0 4) from g1169,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 4 1 (by decide) (by decide)]; rfl⟩
  | 0, 4, 2, _, _, _ => exact ⟨EF env (.n 1109), outCell_sound _ σ K201 18 1109 2 (by decide),
      by rw [show EF env (.n 1109) = qv inp (.HB 0 4) from g1170,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 4 2 (by decide) (by decide)]; rfl⟩
  | 0, 4, 3, _, _, _ => exact ⟨EF env (.n 1108), outCell_sound _ σ K201 19 1108 3 (by decide),
      by rw [show EF env (.n 1108) = qv inp (.HB 0 4) from g1171,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 4 3 (by decide) (by decide)]; rfl⟩
  | 0, 5, 0, _, _, _ => exact ⟨EF env (.n 1107), outCell_sound _ σ K201 20 1107 0 (by decide),
      by rw [show EF env (.n 1107) = qv inp (.HB 0 5) from g1172,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 5 0 (by decide) (by decide)]; rfl⟩
  | 0, 5, 1, _, _, _ => exact ⟨EF env (.n 1106), outCell_sound _ σ K201 21 1106 1 (by decide),
      by rw [show EF env (.n 1106) = qv inp (.HB 0 5) from g1173,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 5 1 (by decide) (by decide)]; rfl⟩
  | 0, 5, 2, _, _, _ => exact ⟨EF env (.n 1105), outCell_sound _ σ K201 22 1105 2 (by decide),
      by rw [show EF env (.n 1105) = qv inp (.HB 0 5) from g1174,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 5 2 (by decide) (by decide)]; rfl⟩
  | 0, 5, 3, _, _, _ => exact ⟨EF env (.n 1104), outCell_sound _ σ K201 23 1104 3 (by decide),
      by rw [show EF env (.n 1104) = qv inp (.HB 0 5) from g1175,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 5 3 (by decide) (by decide)]; rfl⟩
  | 0, 6, 0, _, _, _ => exact ⟨EF env (.n 1103), outCell_sound _ σ K201 24 1103 0 (by decide),
      by rw [show EF env (.n 1103) = qv inp (.HB 0 6) from g1176,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 6 0 (by decide) (by decide)]; rfl⟩
  | 0, 6, 1, _, _, _ => exact ⟨EF env (.n 1102), outCell_sound _ σ K201 25 1102 1 (by decide),
      by rw [show EF env (.n 1102) = qv inp (.HB 0 6) from g1177,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 6 1 (by decide) (by decide)]; rfl⟩
  | 0, 6, 2, _, _, _ => exact ⟨EF env (.n 1101), outCell_sound _ σ K201 26 1101 2 (by decide),
      by rw [show EF env (.n 1101) = qv inp (.HB 0 6) from g1178,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 6 2 (by decide) (by decide)]; rfl⟩
  | 0, 6, 3, _, _, _ => exact ⟨EF env (.n 1100), outCell_sound _ σ K201 27 1100 3 (by decide),
      by rw [show EF env (.n 1100) = qv inp (.HB 0 6) from g1179,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 6 3 (by decide) (by decide)]; rfl⟩
  | 0, 7, 0, _, _, _ => exact ⟨EF env (.n 1099), outCell_sound _ σ K201 28 1099 0 (by decide),
      by rw [show EF env (.n 1099) = qv inp (.HB 0 7) from g1180,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 7 0 (by decide) (by decide)]; rfl⟩
  | 0, 7, 1, _, _, _ => exact ⟨EF env (.n 1098), outCell_sound _ σ K201 29 1098 1 (by decide),
      by rw [show EF env (.n 1098) = qv inp (.HB 0 7) from g1181,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 7 1 (by decide) (by decide)]; rfl⟩
  | 0, 7, 2, _, _, _ => exact ⟨EF env (.n 1097), outCell_sound _ σ K201 30 1097 2 (by decide),
      by rw [show EF env (.n 1097) = qv inp (.HB 0 7) from g1182,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 7 2 (by decide) (by decide)]; rfl⟩
  | 0, 7, 3, _, _, _ => exact ⟨EF env (.n 1096), outCell_sound _ σ K201 31 1096 3 (by decide),
      by rw [show EF env (.n 1096) = qv inp (.HB 0 7) from g1183,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 7 3 (by decide) (by decide)]; rfl⟩
  | 1, 0, 0, _, _, _ => exact ⟨EF env (.n 1095), outCell_sound _ σ K201 32 1095 0 (by decide),
      by rw [show EF env (.n 1095) = qv inp (.HB 1 0) from g1184,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 0 0 (by decide) (by decide)]; rfl⟩
  | 1, 0, 1, _, _, _ => exact ⟨EF env (.n 1094), outCell_sound _ σ K201 33 1094 1 (by decide),
      by rw [show EF env (.n 1094) = qv inp (.HB 1 0) from g1185,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 0 1 (by decide) (by decide)]; rfl⟩
  | 1, 0, 2, _, _, _ => exact ⟨EF env (.n 1093), outCell_sound _ σ K201 34 1093 2 (by decide),
      by rw [show EF env (.n 1093) = qv inp (.HB 1 0) from g1186,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 0 2 (by decide) (by decide)]; rfl⟩
  | 1, 0, 3, _, _, _ => exact ⟨EF env (.n 1092), outCell_sound _ σ K201 35 1092 3 (by decide),
      by rw [show EF env (.n 1092) = qv inp (.HB 1 0) from g1187,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 0 3 (by decide) (by decide)]; rfl⟩
  | 1, 1, 0, _, _, _ => exact ⟨EF env (.n 1091), outCell_sound _ σ K201 36 1091 0 (by decide),
      by rw [show EF env (.n 1091) = qv inp (.HB 1 1) from g1188,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 1 0 (by decide) (by decide)]; rfl⟩
  | 1, 1, 1, _, _, _ => exact ⟨EF env (.n 1090), outCell_sound _ σ K201 37 1090 1 (by decide),
      by rw [show EF env (.n 1090) = qv inp (.HB 1 1) from g1189,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 1 1 (by decide) (by decide)]; rfl⟩
  | 1, 1, 2, _, _, _ => exact ⟨EF env (.n 1089), outCell_sound _ σ K201 38 1089 2 (by decide),
      by rw [show EF env (.n 1089) = qv inp (.HB 1 1) from g1190,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 1 2 (by decide) (by decide)]; rfl⟩
  | 1, 1, 3, _, _, _ => exact ⟨EF env (.n 1088), outCell_sound _ σ K201 39 1088 3 (by decide),
      by rw [show EF env (.n 1088) = qv inp (.HB 1 1) from g1191,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 1 3 (by decide) (by decide)]; rfl⟩
  | 1, 2, 0, _, _, _ => exact ⟨EF env (.n 1087), outCell_sound _ σ K201 40 1087 0 (by decide),
      by rw [show EF env (.n 1087) = qv inp (.HB 1 2) from g1192,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 2 0 (by decide) (by decide)]; rfl⟩
  | 1, 2, 1, _, _, _ => exact ⟨EF env (.n 1086), outCell_sound _ σ K201 41 1086 1 (by decide),
      by rw [show EF env (.n 1086) = qv inp (.HB 1 2) from g1193,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 2 1 (by decide) (by decide)]; rfl⟩
  | 1, 2, 2, _, _, _ => exact ⟨EF env (.n 1085), outCell_sound _ σ K201 42 1085 2 (by decide),
      by rw [show EF env (.n 1085) = qv inp (.HB 1 2) from g1194,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 2 2 (by decide) (by decide)]; rfl⟩
  | 1, 2, 3, _, _, _ => exact ⟨EF env (.n 1084), outCell_sound _ σ K201 43 1084 3 (by decide),
      by rw [show EF env (.n 1084) = qv inp (.HB 1 2) from g1195,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 2 3 (by decide) (by decide)]; rfl⟩
  | 1, 3, 0, _, _, _ => exact ⟨EF env (.n 1083), outCell_sound _ σ K201 44 1083 0 (by decide),
      by rw [show EF env (.n 1083) = qv inp (.HB 1 3) from g1196,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 3 0 (by decide) (by decide)]; rfl⟩
  | 1, 3, 1, _, _, _ => exact ⟨EF env (.n 1082), outCell_sound _ σ K201 45 1082 1 (by decide),
      by rw [show EF env (.n 1082) = qv inp (.HB 1 3) from g1197,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 3 1 (by decide) (by decide)]; rfl⟩
  | 1, 3, 2, _, _, _ => exact ⟨EF env (.n 1081), outCell_sound _ σ K201 46 1081 2 (by decide),
      by rw [show EF env (.n 1081) = qv inp (.HB 1 3) from g1198,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 3 2 (by decide) (by decide)]; rfl⟩
  | 1, 3, 3, _, _, _ => exact ⟨EF env (.n 1080), outCell_sound _ σ K201 47 1080 3 (by decide),
      by rw [show EF env (.n 1080) = qv inp (.HB 1 3) from g1199,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 3 3 (by decide) (by decide)]; rfl⟩
  | 1, 4, 0, _, _, _ => exact ⟨EF env (.n 1079), outCell_sound _ σ K201 48 1079 0 (by decide),
      by rw [show EF env (.n 1079) = qv inp (.HB 1 4) from g1200,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 4 0 (by decide) (by decide)]; rfl⟩
  | 1, 4, 1, _, _, _ => exact ⟨EF env (.n 1078), outCell_sound _ σ K201 49 1078 1 (by decide),
      by rw [show EF env (.n 1078) = qv inp (.HB 1 4) from g1201,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 4 1 (by decide) (by decide)]; rfl⟩
  | 1, 4, 2, _, _, _ => exact ⟨EF env (.n 1077), outCell_sound _ σ K201 50 1077 2 (by decide),
      by rw [show EF env (.n 1077) = qv inp (.HB 1 4) from g1202,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 4 2 (by decide) (by decide)]; rfl⟩
  | 1, 4, 3, _, _, _ => exact ⟨EF env (.n 1076), outCell_sound _ σ K201 51 1076 3 (by decide),
      by rw [show EF env (.n 1076) = qv inp (.HB 1 4) from g1203,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 4 3 (by decide) (by decide)]; rfl⟩
  | 1, 5, 0, _, _, _ => exact ⟨EF env (.n 1075), outCell_sound _ σ K201 52 1075 0 (by decide),
      by rw [show EF env (.n 1075) = qv inp (.HB 1 5) from g1204,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 5 0 (by decide) (by decide)]; rfl⟩
  | 1, 5, 1, _, _, _ => exact ⟨EF env (.n 1074), outCell_sound _ σ K201 53 1074 1 (by decide),
      by rw [show EF env (.n 1074) = qv inp (.HB 1 5) from g1205,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 5 1 (by decide) (by decide)]; rfl⟩
  | 1, 5, 2, _, _, _ => exact ⟨EF env (.n 1073), outCell_sound _ σ K201 54 1073 2 (by decide),
      by rw [show EF env (.n 1073) = qv inp (.HB 1 5) from g1206,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 5 2 (by decide) (by decide)]; rfl⟩
  | 1, 5, 3, _, _, _ => exact ⟨EF env (.n 1072), outCell_sound _ σ K201 55 1072 3 (by decide),
      by rw [show EF env (.n 1072) = qv inp (.HB 1 5) from g1207,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 5 3 (by decide) (by decide)]; rfl⟩
  | 1, 6, 0, _, _, _ => exact ⟨EF env (.n 1071), outCell_sound _ σ K201 56 1071 0 (by decide),
      by rw [show EF env (.n 1071) = qv inp (.HB 1 6) from g1208,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 6 0 (by decide) (by decide)]; rfl⟩
  | 1, 6, 1, _, _, _ => exact ⟨EF env (.n 1070), outCell_sound _ σ K201 57 1070 1 (by decide),
      by rw [show EF env (.n 1070) = qv inp (.HB 1 6) from g1209,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 6 1 (by decide) (by decide)]; rfl⟩
  | 1, 6, 2, _, _, _ => exact ⟨EF env (.n 1069), outCell_sound _ σ K201 58 1069 2 (by decide),
      by rw [show EF env (.n 1069) = qv inp (.HB 1 6) from g1210,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 6 2 (by decide) (by decide)]; rfl⟩
  | 1, 6, 3, _, _, _ => exact ⟨EF env (.n 1068), outCell_sound _ σ K201 59 1068 3 (by decide),
      by rw [show EF env (.n 1068) = qv inp (.HB 1 6) from g1211,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 6 3 (by decide) (by decide)]; rfl⟩
  | 1, 7, 0, _, _, _ => exact ⟨EF env (.n 1067), outCell_sound _ σ K201 60 1067 0 (by decide),
      by rw [show EF env (.n 1067) = qv inp (.HB 1 7) from g1212,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 7 0 (by decide) (by decide)]; rfl⟩
  | 1, 7, 1, _, _, _ => exact ⟨EF env (.n 1066), outCell_sound _ σ K201 61 1066 1 (by decide),
      by rw [show EF env (.n 1066) = qv inp (.HB 1 7) from g1213,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 7 1 (by decide) (by decide)]; rfl⟩
  | 1, 7, 2, _, _, _ => exact ⟨EF env (.n 1065), outCell_sound _ σ K201 62 1065 2 (by decide),
      by rw [show EF env (.n 1065) = qv inp (.HB 1 7) from g1214,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 7 2 (by decide) (by decide)]; rfl⟩
  | 1, 7, 3, _, _, _ => exact ⟨EF env (.n 1064), outCell_sound _ σ K201 63 1064 3 (by decide),
      by rw [show EF env (.n 1064) = qv inp (.HB 1 7) from g1215,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 7 3 (by decide) (by decide)]; rfl⟩
  | 2, 0, 0, _, _, _ => exact ⟨EF env (.n 1063), outCell_sound _ σ K201 64 1063 0 (by decide),
      by rw [show EF env (.n 1063) = qv inp (.HB 2 0) from g1216,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 0 0 (by decide) (by decide)]; rfl⟩
  | 2, 0, 1, _, _, _ => exact ⟨EF env (.n 1062), outCell_sound _ σ K201 65 1062 1 (by decide),
      by rw [show EF env (.n 1062) = qv inp (.HB 2 0) from g1217,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 0 1 (by decide) (by decide)]; rfl⟩
  | 2, 0, 2, _, _, _ => exact ⟨EF env (.n 1061), outCell_sound _ σ K201 66 1061 2 (by decide),
      by rw [show EF env (.n 1061) = qv inp (.HB 2 0) from g1218,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 0 2 (by decide) (by decide)]; rfl⟩
  | 2, 0, 3, _, _, _ => exact ⟨EF env (.n 1060), outCell_sound _ σ K201 67 1060 3 (by decide),
      by rw [show EF env (.n 1060) = qv inp (.HB 2 0) from g1219,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 0 3 (by decide) (by decide)]; rfl⟩
  | 2, 1, 0, _, _, _ => exact ⟨EF env (.n 1059), outCell_sound _ σ K201 68 1059 0 (by decide),
      by rw [show EF env (.n 1059) = qv inp (.HB 2 1) from g1220,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 1 0 (by decide) (by decide)]; rfl⟩
  | 2, 1, 1, _, _, _ => exact ⟨EF env (.n 1058), outCell_sound _ σ K201 69 1058 1 (by decide),
      by rw [show EF env (.n 1058) = qv inp (.HB 2 1) from g1221,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 1 1 (by decide) (by decide)]; rfl⟩
  | 2, 1, 2, _, _, _ => exact ⟨EF env (.n 1057), outCell_sound _ σ K201 70 1057 2 (by decide),
      by rw [show EF env (.n 1057) = qv inp (.HB 2 1) from g1222,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 1 2 (by decide) (by decide)]; rfl⟩
  | 2, 1, 3, _, _, _ => exact ⟨EF env (.n 1056), outCell_sound _ σ K201 71 1056 3 (by decide),
      by rw [show EF env (.n 1056) = qv inp (.HB 2 1) from g1223,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 1 3 (by decide) (by decide)]; rfl⟩
  | 2, 2, 0, _, _, _ => exact ⟨EF env (.n 1055), outCell_sound _ σ K201 72 1055 0 (by decide),
      by rw [show EF env (.n 1055) = qv inp (.HB 2 2) from g1224,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 2 0 (by decide) (by decide)]; rfl⟩
  | 2, 2, 1, _, _, _ => exact ⟨EF env (.n 1054), outCell_sound _ σ K201 73 1054 1 (by decide),
      by rw [show EF env (.n 1054) = qv inp (.HB 2 2) from g1225,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 2 1 (by decide) (by decide)]; rfl⟩
  | 2, 2, 2, _, _, _ => exact ⟨EF env (.n 1053), outCell_sound _ σ K201 74 1053 2 (by decide),
      by rw [show EF env (.n 1053) = qv inp (.HB 2 2) from g1226,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 2 2 (by decide) (by decide)]; rfl⟩
  | 2, 2, 3, _, _, _ => exact ⟨EF env (.n 1052), outCell_sound _ σ K201 75 1052 3 (by decide),
      by rw [show EF env (.n 1052) = qv inp (.HB 2 2) from g1227,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 2 3 (by decide) (by decide)]; rfl⟩
  | 2, 3, 0, _, _, _ => exact ⟨EF env (.n 1051), outCell_sound _ σ K201 76 1051 0 (by decide),
      by rw [show EF env (.n 1051) = qv inp (.HB 2 3) from g1228,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 3 0 (by decide) (by decide)]; rfl⟩
  | 2, 3, 1, _, _, _ => exact ⟨EF env (.n 1050), outCell_sound _ σ K201 77 1050 1 (by decide),
      by rw [show EF env (.n 1050) = qv inp (.HB 2 3) from g1229,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 3 1 (by decide) (by decide)]; rfl⟩
  | 2, 3, 2, _, _, _ => exact ⟨EF env (.n 1049), outCell_sound _ σ K201 78 1049 2 (by decide),
      by rw [show EF env (.n 1049) = qv inp (.HB 2 3) from g1230,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 3 2 (by decide) (by decide)]; rfl⟩
  | 2, 3, 3, _, _, _ => exact ⟨EF env (.n 1048), outCell_sound _ σ K201 79 1048 3 (by decide),
      by rw [show EF env (.n 1048) = qv inp (.HB 2 3) from g1231,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 3 3 (by decide) (by decide)]; rfl⟩
  | 2, 4, 0, _, _, _ => exact ⟨EF env (.n 1047), outCell_sound _ σ K201 80 1047 0 (by decide),
      by rw [show EF env (.n 1047) = qv inp (.HB 2 4) from g1232,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 4 0 (by decide) (by decide)]; rfl⟩
  | 2, 4, 1, _, _, _ => exact ⟨EF env (.n 1046), outCell_sound _ σ K201 81 1046 1 (by decide),
      by rw [show EF env (.n 1046) = qv inp (.HB 2 4) from g1233,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 4 1 (by decide) (by decide)]; rfl⟩
  | 2, 4, 2, _, _, _ => exact ⟨EF env (.n 1045), outCell_sound _ σ K201 82 1045 2 (by decide),
      by rw [show EF env (.n 1045) = qv inp (.HB 2 4) from g1234,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 4 2 (by decide) (by decide)]; rfl⟩
  | 2, 4, 3, _, _, _ => exact ⟨EF env (.n 1044), outCell_sound _ σ K201 83 1044 3 (by decide),
      by rw [show EF env (.n 1044) = qv inp (.HB 2 4) from g1235,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 4 3 (by decide) (by decide)]; rfl⟩
  | 2, 5, 0, _, _, _ => exact ⟨EF env (.n 1043), outCell_sound _ σ K201 84 1043 0 (by decide),
      by rw [show EF env (.n 1043) = qv inp (.HB 2 5) from g1236,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 5 0 (by decide) (by decide)]; rfl⟩
  | 2, 5, 1, _, _, _ => exact ⟨EF env (.n 1042), outCell_sound _ σ K201 85 1042 1 (by decide),
      by rw [show EF env (.n 1042) = qv inp (.HB 2 5) from g1237,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 5 1 (by decide) (by decide)]; rfl⟩
  | 2, 5, 2, _, _, _ => exact ⟨EF env (.n 1041), outCell_sound _ σ K201 86 1041 2 (by decide),
      by rw [show EF env (.n 1041) = qv inp (.HB 2 5) from g1238,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 5 2 (by decide) (by decide)]; rfl⟩
  | 2, 5, 3, _, _, _ => exact ⟨EF env (.n 1040), outCell_sound _ σ K201 87 1040 3 (by decide),
      by rw [show EF env (.n 1040) = qv inp (.HB 2 5) from g1239,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 5 3 (by decide) (by decide)]; rfl⟩
  | 2, 6, 0, _, _, _ => exact ⟨EF env (.n 1039), outCell_sound _ σ K201 88 1039 0 (by decide),
      by rw [show EF env (.n 1039) = qv inp (.HB 2 6) from g1240,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 6 0 (by decide) (by decide)]; rfl⟩
  | 2, 6, 1, _, _, _ => exact ⟨EF env (.n 1038), outCell_sound _ σ K201 89 1038 1 (by decide),
      by rw [show EF env (.n 1038) = qv inp (.HB 2 6) from g1241,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 6 1 (by decide) (by decide)]; rfl⟩
  | 2, 6, 2, _, _, _ => exact ⟨EF env (.n 1037), outCell_sound _ σ K201 90 1037 2 (by decide),
      by rw [show EF env (.n 1037) = qv inp (.HB 2 6) from g1242,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 6 2 (by decide) (by decide)]; rfl⟩
  | 2, 6, 3, _, _, _ => exact ⟨EF env (.n 1036), outCell_sound _ σ K201 91 1036 3 (by decide),
      by rw [show EF env (.n 1036) = qv inp (.HB 2 6) from g1243,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 6 3 (by decide) (by decide)]; rfl⟩
  | 2, 7, 0, _, _, _ => exact ⟨EF env (.n 1035), outCell_sound _ σ K201 92 1035 0 (by decide),
      by rw [show EF env (.n 1035) = qv inp (.HB 2 7) from g1244,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 7 0 (by decide) (by decide)]; rfl⟩
  | 2, 7, 1, _, _, _ => exact ⟨EF env (.n 1034), outCell_sound _ σ K201 93 1034 1 (by decide),
      by rw [show EF env (.n 1034) = qv inp (.HB 2 7) from g1245,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 7 1 (by decide) (by decide)]; rfl⟩
  | 2, 7, 2, _, _, _ => exact ⟨EF env (.n 1033), outCell_sound _ σ K201 94 1033 2 (by decide),
      by rw [show EF env (.n 1033) = qv inp (.HB 2 7) from g1246,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 7 2 (by decide) (by decide)]; rfl⟩
  | 2, 7, 3, _, _, _ => exact ⟨EF env (.n 1032), outCell_sound _ σ K201 95 1032 3 (by decide),
      by rw [show EF env (.n 1032) = qv inp (.HB 2 7) from g1247,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 7 3 (by decide) (by decide)]; rfl⟩
  | 3, 0, 0, _, _, _ => exact ⟨EF env (.n 1031), outCell_sound _ σ K201 96 1031 0 (by decide),
      by rw [show EF env (.n 1031) = qv inp (.HB 3 0) from g1248,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 0 0 (by decide) (by decide)]; rfl⟩
  | 3, 0, 1, _, _, _ => exact ⟨EF env (.n 1030), outCell_sound _ σ K201 97 1030 1 (by decide),
      by rw [show EF env (.n 1030) = qv inp (.HB 3 0) from g1249,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 0 1 (by decide) (by decide)]; rfl⟩
  | 3, 0, 2, _, _, _ => exact ⟨EF env (.n 1029), outCell_sound _ σ K201 98 1029 2 (by decide),
      by rw [show EF env (.n 1029) = qv inp (.HB 3 0) from g1250,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 0 2 (by decide) (by decide)]; rfl⟩
  | 3, 0, 3, _, _, _ => exact ⟨EF env (.n 1028), outCell_sound _ σ K201 99 1028 3 (by decide),
      by rw [show EF env (.n 1028) = qv inp (.HB 3 0) from g1251,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 0 3 (by decide) (by decide)]; rfl⟩
  | 3, 1, 0, _, _, _ => exact ⟨EF env (.n 1027), outCell_sound _ σ K201 100 1027 0 (by decide),
      by rw [show EF env (.n 1027) = qv inp (.HB 3 1) from g1252,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 1 0 (by decide) (by decide)]; rfl⟩
  | 3, 1, 1, _, _, _ => exact ⟨EF env (.n 1026), outCell_sound _ σ K201 101 1026 1 (by decide),
      by rw [show EF env (.n 1026) = qv inp (.HB 3 1) from g1253,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 1 1 (by decide) (by decide)]; rfl⟩
  | 3, 1, 2, _, _, _ => exact ⟨EF env (.n 1025), outCell_sound _ σ K201 102 1025 2 (by decide),
      by rw [show EF env (.n 1025) = qv inp (.HB 3 1) from g1254,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 1 2 (by decide) (by decide)]; rfl⟩
  | 3, 1, 3, _, _, _ => exact ⟨EF env (.n 1024), outCell_sound _ σ K201 103 1024 3 (by decide),
      by rw [show EF env (.n 1024) = qv inp (.HB 3 1) from g1255,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 1 3 (by decide) (by decide)]; rfl⟩
  | 3, 2, 0, _, _, _ => exact ⟨EF env (.n 1023), outCell_sound _ σ K201 104 1023 0 (by decide),
      by rw [show EF env (.n 1023) = qv inp (.HB 3 2) from g1256,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 2 0 (by decide) (by decide)]; rfl⟩
  | 3, 2, 1, _, _, _ => exact ⟨EF env (.n 1022), outCell_sound _ σ K201 105 1022 1 (by decide),
      by rw [show EF env (.n 1022) = qv inp (.HB 3 2) from g1257,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 2 1 (by decide) (by decide)]; rfl⟩
  | 3, 2, 2, _, _, _ => exact ⟨EF env (.n 1021), outCell_sound _ σ K201 106 1021 2 (by decide),
      by rw [show EF env (.n 1021) = qv inp (.HB 3 2) from g1258,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 2 2 (by decide) (by decide)]; rfl⟩
  | 3, 2, 3, _, _, _ => exact ⟨EF env (.n 1020), outCell_sound _ σ K201 107 1020 3 (by decide),
      by rw [show EF env (.n 1020) = qv inp (.HB 3 2) from g1259,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 2 3 (by decide) (by decide)]; rfl⟩
  | 3, 3, 0, _, _, _ => exact ⟨EF env (.n 1019), outCell_sound _ σ K201 108 1019 0 (by decide),
      by rw [show EF env (.n 1019) = qv inp (.HB 3 3) from g1260,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 3 0 (by decide) (by decide)]; rfl⟩
  | 3, 3, 1, _, _, _ => exact ⟨EF env (.n 1018), outCell_sound _ σ K201 109 1018 1 (by decide),
      by rw [show EF env (.n 1018) = qv inp (.HB 3 3) from g1261,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 3 1 (by decide) (by decide)]; rfl⟩
  | 3, 3, 2, _, _, _ => exact ⟨EF env (.n 1017), outCell_sound _ σ K201 110 1017 2 (by decide),
      by rw [show EF env (.n 1017) = qv inp (.HB 3 3) from g1262,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 3 2 (by decide) (by decide)]; rfl⟩
  | 3, 3, 3, _, _, _ => exact ⟨EF env (.n 1016), outCell_sound _ σ K201 111 1016 3 (by decide),
      by rw [show EF env (.n 1016) = qv inp (.HB 3 3) from g1263,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 3 3 (by decide) (by decide)]; rfl⟩
  | 3, 4, 0, _, _, _ => exact ⟨EF env (.n 1015), outCell_sound _ σ K201 112 1015 0 (by decide),
      by rw [show EF env (.n 1015) = qv inp (.HB 3 4) from g1264,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 4 0 (by decide) (by decide)]; rfl⟩
  | 3, 4, 1, _, _, _ => exact ⟨EF env (.n 1014), outCell_sound _ σ K201 113 1014 1 (by decide),
      by rw [show EF env (.n 1014) = qv inp (.HB 3 4) from g1265,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 4 1 (by decide) (by decide)]; rfl⟩
  | 3, 4, 2, _, _, _ => exact ⟨EF env (.n 1013), outCell_sound _ σ K201 114 1013 2 (by decide),
      by rw [show EF env (.n 1013) = qv inp (.HB 3 4) from g1266,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 4 2 (by decide) (by decide)]; rfl⟩
  | 3, 4, 3, _, _, _ => exact ⟨EF env (.n 1012), outCell_sound _ σ K201 115 1012 3 (by decide),
      by rw [show EF env (.n 1012) = qv inp (.HB 3 4) from g1267,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 4 3 (by decide) (by decide)]; rfl⟩
  | 3, 5, 0, _, _, _ => exact ⟨EF env (.n 1011), outCell_sound _ σ K201 116 1011 0 (by decide),
      by rw [show EF env (.n 1011) = qv inp (.HB 3 5) from g1268,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 5 0 (by decide) (by decide)]; rfl⟩
  | 3, 5, 1, _, _, _ => exact ⟨EF env (.n 1010), outCell_sound _ σ K201 117 1010 1 (by decide),
      by rw [show EF env (.n 1010) = qv inp (.HB 3 5) from g1269,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 5 1 (by decide) (by decide)]; rfl⟩
  | 3, 5, 2, _, _, _ => exact ⟨EF env (.n 1009), outCell_sound _ σ K201 118 1009 2 (by decide),
      by rw [show EF env (.n 1009) = qv inp (.HB 3 5) from g1270,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 5 2 (by decide) (by decide)]; rfl⟩
  | 3, 5, 3, _, _, _ => exact ⟨EF env (.n 1008), outCell_sound _ σ K201 119 1008 3 (by decide),
      by rw [show EF env (.n 1008) = qv inp (.HB 3 5) from g1271,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 5 3 (by decide) (by decide)]; rfl⟩
  | 3, 6, 0, _, _, _ => exact ⟨EF env (.n 1007), outCell_sound _ σ K201 120 1007 0 (by decide),
      by rw [show EF env (.n 1007) = qv inp (.HB 3 6) from g1272,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 6 0 (by decide) (by decide)]; rfl⟩
  | 3, 6, 1, _, _, _ => exact ⟨EF env (.n 1006), outCell_sound _ σ K201 121 1006 1 (by decide),
      by rw [show EF env (.n 1006) = qv inp (.HB 3 6) from g1273,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 6 1 (by decide) (by decide)]; rfl⟩
  | 3, 6, 2, _, _, _ => exact ⟨EF env (.n 1005), outCell_sound _ σ K201 122 1005 2 (by decide),
      by rw [show EF env (.n 1005) = qv inp (.HB 3 6) from g1274,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 6 2 (by decide) (by decide)]; rfl⟩
  | 3, 6, 3, _, _, _ => exact ⟨EF env (.n 1004), outCell_sound _ σ K201 123 1004 3 (by decide),
      by rw [show EF env (.n 1004) = qv inp (.HB 3 6) from g1275,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 6 3 (by decide) (by decide)]; rfl⟩
  | 3, 7, 0, _, _, _ => exact ⟨EF env (.n 1003), outCell_sound _ σ K201 124 1003 0 (by decide),
      by rw [show EF env (.n 1003) = qv inp (.HB 3 7) from g1276,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 7 0 (by decide) (by decide)]; rfl⟩
  | 3, 7, 1, _, _, _ => exact ⟨EF env (.n 1002), outCell_sound _ σ K201 125 1002 1 (by decide),
      by rw [show EF env (.n 1002) = qv inp (.HB 3 7) from g1277,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 7 1 (by decide) (by decide)]; rfl⟩
  | 3, 7, 2, _, _, _ => exact ⟨EF env (.n 1001), outCell_sound _ σ K201 126 1001 2 (by decide),
      by rw [show EF env (.n 1001) = qv inp (.HB 3 7) from g1278,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 7 2 (by decide) (by decide)]; rfl⟩
  | 3, 7, 3, _, _, _ => exact ⟨EF env (.n 1000), outCell_sound _ σ K201 127 1000 3 (by decide),
      by rw [show EF env (.n 1000) = qv inp (.HB 3 7) from g1279,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 7 3 (by decide) (by decide)]; rfl⟩
  | _ + 4, _, _, hn, _, _ => omega
  | _, _ + 8, _, _, hi, _ => omega
  | _, _, _ + 4, _, _, hb => omega


/-- Every write of the exit slice ends in the output region or below the entry stack offset. -/
theorem K201_logB : K201.mem.all logOkB = true := by
  decide +kernel

theorem K201_log (p : Addr Lin × Cell E Lin) (hp : p ∈ K201.mem) :
    p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off.c = [] ∧ p.1.off.k < 24) := by
  have h : logOkB p = true := List.all_eq_true.mp K201_logB p hp
  by_cases h1 : p.1.region = rOut
  · exact Or.inl h1
  by_cases h2 : p.1.region = rStack
  · right
    have hd : decide (p.1.off.c = ([] : List Int) ∧ p.1.off.k < 24) = true := by
      rw [logOkB, if_neg h1, if_pos h2] at h
      exact h
    exact ⟨h2, of_decide_eq_true hd⟩
  · exfalso
    rw [logOkB, if_neg h1, if_neg h2] at h
    cases h

/-- The exit cut's log, after substituting the concrete symbols, still satisfies `OutLog`. -/
theorem outLog_map_K201 (σ : Nat → Int) (e : Key → W32) :
    OutLog (K201.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases K201_log q hq with h | ⟨h, hc, hk⟩
  · left
    simpa [mapAddr] using h
  · right
    have hreg : (mapAddr σ q.1).region = rStack := by simpa [mapAddr] using h
    refine ⟨hreg, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k := by
      simp [Lin.eval, hc, dotC]
    show q.1.off.eval σ < 24
    rw [hoff]
    exact hk

/-- `HMem` for an environment restarted through a log, from concrete input cells at `σ 0`. -/
theorem hmem_view (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (σ0 : Int)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ0 + (o : Int)⟩ = .dat ((inp o).zeroExtend 32) 0)
    (e : Key → W32) (σ' : Nat → Int) (h0 : σ' 0 = σ0) (M : CLog) (hM : OutLog M) :
    HMem 256 inp (ecomb e σ' (view M mem0c)) := by
  intro o _
  simp only [ecomb]
  rw [view_other M mem0c _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
    fun h => absurd (show rIn = rStack from h) (by decide)⟩)]
  have ha : (⟨rIn, (⟨(o : Int), [1]⟩ : Lin).eval σ'⟩ : Addr Int) =
      ⟨rIn, σ0 + (o : Int)⟩ := by
    simp only [Lin.eval, dotC, Addr.mk.injEq, true_and]; omega
  rw [ha, hin o]; rfl

/-! ## The last batch behind an accumulated log -/

/-- The last batch at a residual count `s ∈ [4, 8)` behind an accumulated output log: head
slice, body and exit slice, with the batch's 128 output bytes. -/
theorem exit_batch (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (σ : Nat → Int) (e : Key → W32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + (o : Int)⟩ = .dat ((inp o).zeroExtend 32) 0)
    (M : CLog) (hM : OutLog M)
    (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∃ e', run prog 4 mem0c orcC (68 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (fr M (mapState e σ KHL2)) =
        fr M (mapState e' σ K201) ∧
      OutLog (K201.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) ∧
      ∀ n i b, n < 4 → i < 8 → b < 4 → ∃ x,
        lookup (⟨rOut, σ 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)
            (K201.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) =
          .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32 := by
  let E : Key → W32 := ecomb e σ (view M mem0c)
  have kq : MemKeyed m0q := by rw [m0q_eq]; exact mem0s_keyed 4 rodata 24
  have hrel : Mem0Rel E σ m0q (view M mem0c) := by
    rw [m0q_eq]
    exact mem0Rel_of_wf 4 rodata 24 E σ (view M mem0c)
      (wf_view rodata mem0c M hM hw) (envMem_ecomb E σ (view M mem0c))
  have hE : HMem 256 inp E := hmem_view inp mem0c (σ 0) hin e σ rfl M hM
  have hrun : run prog 4 mem0c orcC (68 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (fr M (mapState e σ KHL2)) =
      fr M (mapState (EF E) σ K201) := by
    rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) KHL2 KHL2_nOnly,
      run_finalS E σ (view M mem0c) orcC hrel hge hlt]
  have hout := out_finalS inp E σ (view M mem0c) orcC hrel hge hlt hE
  rw [run_finalS E σ (view M mem0c) orcC hrel hge hlt] at hout
  refine ⟨EF E, hrun, outLog_app (outLog_map_K201 σ (EF E)) hM, ?_⟩
  intro n i b hn hi hb
  obtain ⟨x, hx, hv⟩ := hout n i b hn hi hb
  exact ⟨x, lookup_app_left _ _ _ _ hx, hv⟩

/-! ## The count at the loop head shifts by the substitution -/

theorem sigmaOf_tau0 (σ : Nat → Int) : sigmaOf tau σ 0 = σ 0 + 256 := by
  unfold sigmaOf tauAt tau
  split <;> simp [Lin.eval, dotC] <;> omega

theorem sigmaOf_tau1 (σ : Nat → Int) : sigmaOf tau σ 1 = σ 1 + 128 := by
  unfold sigmaOf tauAt tau
  split <;> simp [Lin.eval, dotC] <;> omega

theorem sIt_0 (j : Nat) (σ : Nat → Int) : sIt j σ 0 = σ 0 + 256 * (j : Int) := by
  induction j generalizing σ with
  | zero => simp [sIt]
  | succ j ih =>
    rw [show sIt (j + 1) σ = sIt j (sigmaOf tau σ) from rfl, ih (sigmaOf tau σ), sigmaOf_tau0]
    omega

theorem sIt_1 (j : Nat) (σ : Nat → Int) : sIt j σ 1 = σ 1 + 128 * (j : Int) := by
  induction j generalizing σ with
  | zero => simp [sIt]
  | succ j ih =>
    rw [show sIt (j + 1) σ = sIt j (sigmaOf tau σ) from rfl, ih (sigmaOf tau σ), sigmaOf_tau1]
    omega

theorem sIt_2 (j : Nat) (σ : Nat → Int) : sIt j σ 2 = σ 2 - 4 * (j : Int) := by
  induction j generalizing σ with
  | zero => simp [sIt]
  | succ j ih =>
    rw [show sIt (j + 1) σ = sIt j (sigmaOf tau σ) from rfl, ih (sigmaOf tau σ), tau_count]
    omega

/-- Blocks of the batch at turn `j`: the batch input window is the four blocks `4j .. 4j+3`. -/
theorem blk_shift4 (inp : Nat → Byte) (j n : Nat) :
    blk (fun o => inp (256 * j + o)) n = blk inp (4 * j + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-! ## Every count for avx_x4, in S mode -/

/-- **avx_x4 at every count, from a loop invariant head.**  `j` full turns leave a residual
count `s ∈ [4, 8)`, and the last batch (head, body, exit slice) produces the outputs of the
blocks `4j .. 4j+3`; behind an accumulated output log. -/
theorem x4_all (inp : Nat → Byte) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (σ : Nat → Int) (e : Key → W32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + (o : Int)⟩ = .dat ((inp o).zeroExtend 32) 0)
    (M : CLog) (hM : OutLog M) (j s : Nat) (hs : 4 ≤ s) (hs8 : s < 8)
    (hσ : σ 2 = 4 * (j : Int) + (s : Int)) :
    ∃ e' M', run prog 4 mem0c orcC (j * TURNLEN + (68 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))) (fr M (mapState e σ KHL2)) =
        fr M' (mapState e' (sIt j σ) K201) ∧
      OutLog (K201.mem.map (fun p => (mapAddr (sIt j σ) p.1, mapCell e' (sIt j σ) p.2)) ++ M') ∧
      ∀ n i b, n < 4 → i < 8 → b < 4 → ∃ x,
        lookup (⟨rOut, (sIt j σ) 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int)
            (K201.mem.map (fun p => (mapAddr (sIt j σ) p.1, mapCell e' (sIt j σ) p.2)) ++ M') =
          .ok (some (.dat x b)) ∧
        byteOf x b = ((node (blk inp (4 * j + n))).getD (4 * i + b) 0).zeroExtend 32 := by
  obtain ⟨e1, M1, hrun1, hM1⟩ := loop mem0c orcC hw s hs hs8 j e σ M hσ hM
  have h2 : sIt j σ 2 = (s : Int) := by rw [sIt_2]; omega
  have hge1 : 4 ≤ sIt j σ 2 := by rw [h2]; omega
  have hlt1 : sIt j σ 2 < 8 := by rw [h2]; omega
  have hin1 : ∀ o : Nat, mem0c ⟨rIn, sIt j σ 0 + (o : Int)⟩ =
      .dat ((inp (256 * j + o)).zeroExtend 32) 0 := by
    intro o
    have hcast : ((256 * j + o : Nat) : Int) = 256 * (j : Int) + (o : Int) := by
      push_cast; omega
    rw [sIt_0, Int.add_assoc, ← hcast]
    exact hin (256 * j + o)
  obtain ⟨e2, hE2, hLog2, hout2⟩ :=
    exit_batch (fun o => inp (256 * j + o)) mem0c orcC hw (sIt j σ) e1 hin1 M1 hM1 hge1 hlt1
  refine ⟨e2, M1, ?_, hLog2, ?_⟩
  · rw [run_add, hrun1]
    exact hE2
  · intro n i b hn hi hb
    obtain ⟨x, hx, hv⟩ := hout2 n i b hn hi hb
    refine ⟨x, hx, ?_⟩
    rw [blk_shift4 inp j n] at hv
    exact hv

end Hashtree.Proofs.AvxX4Exit
