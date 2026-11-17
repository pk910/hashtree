import Hashtree.Proofs.WinWrapperMach
import Hashtree.Asm.SpecQ
import Hashtree.Spec
import Hashtree.Kernels.X86Win.Shani
import Hashtree.Kernels.X86Win.Avx512X16
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Kernels.X86Win.AvxX1

/-!
# R5: the windows/amd64 Go wrapper `HashtreeHash`, composed with a kernel

This file proves the machine-level composition promised for the windows wrapper: from the
wrapper's ABI0 entry state (`wEntryW`), through the assembler prologue, the argument loads,
`MOVQ SP, BX ; ADDQ $2048, SP ; ANDQ $-32, SP`, the `CALL` (a return marker pushed at the
aligned call `rsp`), the kernel (its windows contract `KSpecW`), and the epilogue
`MOVQ BX, SP ; MOVQ R12, R8 ; ADDQ $F, SP ; POPQ BP ; RET`, the wrapper returns to its caller
with the ABI0 stack restored (`rsp = SPe + 8`), the caller's `rbp` in `rbp`, the caller's `r8`
restored from `r12`, and every output byte the SHA-256 byte of its input block.

Two frame sizes are modelled (`Kernels/X86Win/WrapperWindows`):

* `fixedFrame` (`$2048`, branch `fix/windows-wrapper-frame`): the text's `ADDQ $2048, SP`
  matches the declared frame, so the aligned call `rsp` is inside the wrapper's own frame
  (identical geometry to the linux wrapper).  `wrapper_kernelW_fixed` gives the clean
  Go-facing contract: writes are output bytes or bytes of `[SPe - 2056, SPe)`.

* `shippedFrame` (`$1024`, the shipped source): the text still adds 2048, so the aligned call
  `rsp` (and therefore the pushed return marker, and the kernel's stack) lies 985..1016 bytes
  *above* the wrapper's entry `rsp`, in the caller's frame.  `wrapper_kernelW_shipped` proves the
  machine still returns correctly *provided* the kernel's own stack writes start above
  `SPe + 8` (`hD9`, i.e. `D ≤ σ10 - σ9 - 8`), records that the call writes the return marker
  above `SPe` (a witness), and proves that the linux-style footprint claim
  `Foot (σ 9) 2056 ...` is *false* for the shipped frame.  In the shipped layout the wrapper is
  therefore only safe for kernels whose stack depth is below the distance the alignment leaves
  above `SPe`; see `formal/notes/R5.md`.

U6 (the avx512_x16 stream never saves/restores `xmm6`-`xmm15`) is not assumed away: `KSpecW`
takes no xmm preservation, the wrapper itself does not read any vector register, and the defect
is recorded by `WinAvx512.u6_witness` / `WinAvx512.win_no_rsp`.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinWrapper
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Proofs.WrapperAmd64 (m0W m0W_rel l10 l10_eval sAt_eval getG_of pushRet callK
  argCells lkIs lkIs_sound)

/-! ## Shared specifications (local copies)

`Proofs/WrapperAmd64` and `Proofs/ShaniW` also import the linux kernels' proof modules (and
through them the `Gen` proof data); the windows file keeps only the parts it composes with, so
the two shapes it needs are restated here.  `Foot` is the linux wrapper's footprint claim,
used below only to state (and, for the shipped frame, refute) the corresponding claim. -/

/-- Every logged write is an output byte in `[ob, ob + len)` or a stack byte in `[sp - D, sp)`. -/
def Foot (sp : Int) (D : Nat) (ob : Int) (len : Nat) (M : CLog) : Prop :=
  ∀ p ∈ M, (p.1.region = rOut ∧ ob ≤ p.1.off ∧ p.1.off < ob + len) ∨
    (p.1.region = rStack ∧ sp - D ≤ p.1.off ∧ p.1.off < sp)

/-- The output blocks hold the SHA-256 bytes of the input blocks. -/
def OutOk (inp : Nat → Byte) (ob : Int) (nblk : Nat) (M : CLog) : Prop :=
  ∀ n i b, n < nblk → i < 8 → b < 4 → ∃ x,
    lookup (⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M = .ok (some (.dat x b)) ∧
      byteOf x b = ((node (blk inp n)).getD (4 * i + b) 0).zeroExtend 32

theorem lin10_eval (σ : Nat → Int) (l : Lin) (h : l.c = List.replicate 10 0 ++ [1]) : l.eval σ = l.k + σ 10 := by
  obtain ⟨k, c⟩ := l; simp only at h; subst h; exact l10_eval σ k

theorem linS_eval (σ : Nat → Int) (l : Lin) (h : l.c = stkC) : l.eval σ = l.k + σ 9 := by
  obtain ⟨k, c⟩ := l; simp only at h; subst h; exact sAt_eval σ k

theorem readCell_some (m : Addr Int → Cell W32 Int) (s : CState) (a : Addr Int) (c : Cell W32 Int)
    (h : lookup a s.mem = .ok (some c)) : readCell m s a = .ok c := by simp [readCell, h]

theorem readCell_none (m : Addr Int → Cell W32 Int) (s : CState) (a : Addr Int)
    (h : lookup a s.mem = .ok none) : readCell m s a = .ok (m a) := by simp [readCell, h]

theorem plusI_nat (r : Region) (o : Int) (k : Nat) : (⟨r, o⟩ : Addr Int).plusI k = ⟨r, o + k⟩ := by
  simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]

/-! ## The windows kernel contract -/

/-- Win64 callee-saved registers hold their entry values through the kernel (`rbx`, `rbp` the
wrapper's frame pointers, `r12` the wrapper's saved incoming `r8` (tagged `rNum`), `r13`/`r15`
the caller's integers, `r14` = g), and `rsp` is the kernel's entry `rsp` + 8 (the return marker
was popped).  The vector registers are deliberately not mentioned: U6. -/
def RegsOkW (σ : Nat → Int) (s : CState) : Prop :=
  s.gpr[3]? = some (.ptr ⟨rStack, σ 5⟩) ∧ s.gpr[5]? = some (.ptr ⟨rStack, σ 6⟩) ∧
    s.gpr[12]? = some (.ptr ⟨rNum, σ 7⟩) ∧ s.gpr[13]? = some (.ptr ⟨rNum, σ 11⟩) ∧
    s.gpr[14]? = some (.ptr ⟨rG, σ 8⟩) ∧ s.gpr[15]? = some (.ptr ⟨rNum, σ 12⟩) ∧
    s.gpr[4]? = some (.ptr ⟨rStack, σ 9 + 8⟩)

/-- A windows kernel's contract at the wrapper's call state `entryWin`: for every count, from
`entryWin` on a memory with its rodata, the return address at `σ 9` and the input bytes, it
returns after `steps c` instructions without a model error, its writes are output bytes and
stack bytes `[σ 9 - D, σ 9)`, the outputs are SHA-256 of the blocks, and the Win64 callee-saved
registers and `rsp` are restored (`RegsOkW`). -/
def KSpecW (kprog : Array Instr) (rodata : List Nat) (steps : Nat → Nat) (D : Nat) : Prop :=
  ∀ (c : Nat) (inp : Nat → Spec.Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool), WfMemW rodata [] env0 σ mem0c →
    EnvMem env0 σ mem0c → σ 2 = c →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let fin := run kprog 4 mem0c orcC (steps c) (mapState env0 σ entryWin)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ Foot (σ 9) D (σ 1) (32 * c) fin.mem ∧
      OutOk inp (σ 1) c fin.mem ∧ RegsOkW σ fin

/-- The whole wrapper call for declared frame `Fr` and a given kernel. -/
def wrapRunW (Fr : Int) (kprog : Array Instr) (N : Nat) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (s : CState) : CState :=
  run (post Fr) 4 m orc 5 (callK kprog N m orc (alignStep m orc (run (pre Fr) 4 m orc 9 s)))

/-! ## The composition -/

/-- **The wrapper call with a kernel meeting `KSpecW`** (frame `Fr` generic).  `hsepM` says the
aligned call marker is entirely below or above the wrapper's `[SPe-8, SPe+8)` slot pair;
`hsepK` says the kernel's stack writes are entirely below or above it.  The conclusion keeps the
kernel, marker and saved-`rbp` write ranges separate so both frame geometries can be read off. -/
theorem wrapper_kernelW_core (Fr : Int) (kprog : Array Instr) (rodata : List Nat)
    (steps : Nat → Nat) (D : Nat) (hk : KSpecW kprog rodata steps D)
    (hlenK : (KpreW Fr).gpr.length = 16)
    (hshape : { KCW Fr with mem := [], assume := [] } = entryWin.substL (tauCW Fr))
    (hsplit : (KCW Fr).mem = (KCW Fr).mem.take 8 ++ (KpreW Fr).mem)
    (hmarker : ∀ p ∈ (KCW Fr).mem.take 8, p.1.region = rStack ∧
      p.1.off.c = List.replicate 10 0 ++ [1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 8)
    (hmlk : ∀ k : Nat, k < 8 →
      lkIs ⟨rStack, l10 k⟩ (KCW Fr).mem (.pb ⟨rRet, Lin.ofInt 0⟩ k) = true)
    (hbpf : ∀ p ∈ (KpreW Fr).mem, p.1.region = rStack ∧ p.1.off.c = stkC ∧
      -8 ≤ p.1.off.k ∧ p.1.off.k < 0)
    (hbplk : ∀ k : Nat, k < 8 →
      lkIs ⟨rStack, sAt (-8 + k)⟩ (KpreW Fr).mem (.pb ⟨rStack, Lin.sym 6⟩ k) = true)
    (hhead : ((⟨rStack, l10 0⟩ : Addr Lin), Cell.pb ⟨rRet, Lin.ofInt 0⟩ 0) ∈
      (KCW Fr).mem.take 8)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (eP : Key → W32)
    (hP : run (pre Fr) 4 mem0c orc 9 (mapState env σ wEntryW) = mapState eP σ (KpreW Fr))
    (hA : alignStep mem0c orc (mapState eP σ (KpreW Fr)) = mapState eP σ (KalW Fr))
    (hsepM : σ 10 + 8 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10)
    (hsepK : σ 10 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 - (D : Int))
    (hw : WfMemW rodata argCells env σ mem0c) (_he : EnvMem env σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := wrapRunW Fr kprog (steps c) mem0c orc (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      (∀ p ∈ fin.mem, (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * c) ∨
        (p.1.region = rStack ∧ ((σ 10 - (D : Int) ≤ p.1.off ∧ p.1.off < σ 10) ∨
          (σ 10 ≤ p.1.off ∧ p.1.off < σ 10 + 8) ∨ (σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9)))) ∧
      OutOk inp (σ 1) c fin.mem ∧
      (σ 9 ≤ σ 10 → ∃ p ∈ fin.mem, p.1.region = rStack ∧ p.1.off = σ 10) := by
  let σK := sigmaOf (tauCW Fr) σ
  have k0 : σK 0 = σ 0 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k1 : σK 1 = σ 1 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k2 : σK 2 = σ 2 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k7 : σK 7 = σ 13 := by simp [σK, sigmaOf, tauAt, tauCW, Lin.eval_sym]
  have k5 : σK 5 = σ 9 - 8 - Fr := by simp [σK, sigmaOf, tauAt, tauCW, sAt_eval]; omega
  have k9 : σK 9 = σ 10 := by simp [σK, sigmaOf, tauAt, tauCW, l10_eval]
  let f := fun (p : Addr Lin × Cell E Lin) => (mapAddr σ p.1, mapCell eP σ p.2)
  let Lm := (KCW Fr).mem.take 8 |>.map f
  let Lb := (KpreW Fr).mem.map f
  have hLw : (KCW Fr).mem.map f = Lm ++ Lb := by
    show (KCW Fr).mem.map f = ((KCW Fr).mem.take 8).map f ++ (KpreW Fr).mem.map f
    rw [← List.map_append, ← hsplit]
  have hcall : { pushRet (alignStep mem0c orc (run (pre Fr) 4 mem0c orc 9
        (mapState env σ wEntryW))) with pc := 0 } =
      fr (Lm ++ Lb) (mapState eP σK entryWin) := by
    rw [hP, hA, push_homW Fr eP σ hlenK, mapState_reached eP σ (KCW Fr) entryWin (tauCW Fr) hshape]
    show fr ((KCW Fr).mem.map f) _ = _
    rw [hLw]
  -- the call log: marker cells and the saved `rbp`
  have hLm : ∀ p ∈ Lm, p.1.region = rStack ∧ σ 10 ≤ p.1.off ∧ p.1.off < σ 10 + 8 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := hmarker q hq
    simp only [f, mapAddr, lin10_eval σ _ h2, h1]
    exact ⟨trivial, by omega, by omega⟩
  have hLb : ∀ p ∈ Lb, p.1.region = rStack ∧ σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := hbpf q hq
    simp only [f, mapAddr, linS_eval σ _ h2, h1]
    exact ⟨trivial, by omega, by omega⟩
  have hLw3 : ∀ p ∈ Lm ++ Lb, p.1.region = rStack := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact (hLm p h).1
    · exact (hLb p h).1
  have ne3 : ∀ (a : Addr Int), a.region ≠ rStack → ∀ p ∈ Lm ++ Lb, p.1 ≠ a := by
    intro a ha p hp heq; rw [← heq] at ha; exact ha (hLw3 p hp)
  let mK := view (Lm ++ Lb) mem0c
  have hmK4 : ∀ o, mK ⟨4, o⟩ = mem0c ⟨4, o⟩ := fun o =>
    view_other _ _ _ (ne3 ⟨4, o⟩ (by decide : (4 : Region) ≠ rStack))
  have hmKI : ∀ o, mK ⟨rIn, o⟩ = mem0c ⟨rIn, o⟩ := fun o =>
    view_other _ _ _ (ne3 ⟨rIn, o⟩ (by decide : rIn ≠ rStack))
  have hmKR : ∀ k : Int, 0 ≤ k → k < 8 → mK ⟨rStack, σK 9 + k⟩ = .pb ⟨rRet, 0⟩ k.toNat := by
    intro k h1 h2
    have hk' := hmlk k.toNat (by omega)
    have hl := lookup_hom eP σ _ (KCW Fr).mem _ (lkIs_sound _ _ _ hk')
    have ha : mapAddr σ (⟨rStack, l10 k.toNat⟩ : Addr Lin) = ⟨rStack, σK 9 + k⟩ := by
      simp only [mapAddr, l10_eval, k9]; congr 1; omega
    have hc0 : mapCell eP σ (Cell.pb ⟨rRet, Lin.ofInt 0⟩ k.toNat) = .pb ⟨rRet, 0⟩ k.toNat := by
      simp [mapCell, mapAddr, Lin.ofInt, Lin.eval, dotC]
    rw [ha, show (KCW Fr).mem.map (fun p => (mapAddr σ p.1, mapCell eP σ p.2)) = Lm ++ Lb from hLw,
      Option.map_some, hc0] at hl
    simp only [mK, view, hl]
  have hwK : WfMemW rodata [] (ecomb eP σK mK) σK mK := by
    obtain ⟨hro, _, hinw, _⟩ := hw
    refine ⟨fun o => (hmK4 o).trans (hro o), hmKR, fun o => ?_, fun k c hl => by simp [plookup] at hl⟩
    rw [hmKI]; exact hinw o
  have hinK : ∀ o : Nat, mK ⟨rIn, σK 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
    intro o; rw [hmKI, k0]; exact hin o
  obtain ⟨kh, ke, kt, kfoot, kout, kregs⟩ :=
    hk c inp (ecomb eP σK mK) σK mK orc hwK (envMem_ecomb _ _ _) (by rw [k2]; exact hc) hinK
  generalize hF : run kprog 4 mK orc (steps c) (mapState (ecomb eP σK mK) σK entryWin) = F
    at kh ke kt kfoot kout kregs
  have hcK : callK kprog (steps c) mem0c orc (alignStep mem0c orc (run (pre Fr) 4 mem0c orc 9
        (mapState env σ wEntryW))) =
      { fr (Lm ++ Lb) F with pc := 0, halted := false } := by
    simp only [callK]
    rw [hcall, run_fr, mapState_nOnly eP (ecomb eP σK mK) σK (fun _ => rfl) entryWin entryWin_nOnly]
    show { fr (Lm ++ Lb) (run kprog 4 mK orc (steps c) _) with pc := 0, halted := false } = _
    rw [hF]
  -- the epilogue
  obtain ⟨hr3, hr5, hr12, hr13, hr14, hr15, hr4⟩ := kregs
  have hlen : 12 < F.gpr.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hr12; omega
  let S : CState := { fr (Lm ++ Lb) F with pc := 0, halted := false }
  -- the kernel's writes avoid the wrapper's saved `rbp` and return-address slots
  have hFsep : ∀ p ∈ F.mem, p.1.region = rStack → ¬(σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 9 + 8) := by
    intro p hp hreg h
    rcases kfoot p hp with ⟨ho, _, _⟩ | ⟨hs, hlo, hhi⟩
    · rw [ho] at hreg; exact absurd hreg (by decide)
    · rw [k9] at hhi
      rcases hsepK with hk | hk <;> omega
  have hbp : ∀ k : Nat, k < 8 → readCell mem0c S ((⟨rStack, σK 5 + Fr⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rStack, σ 6⟩ k) := by
    intro k hk8
    apply readCell_some
    show lookup _ (F.mem ++ (Lm ++ Lb)) = _
    rw [plusI_nat, lookup_app_right _ _ _ (by
      intro p hp heq
      have hoff : p.1.off = σ 9 - 8 + (k : Int) := by rw [heq]; dsimp only; omega
      refine hFsep p hp ?_ ⟨by omega, by omega⟩
      rw [heq])]
    rw [lookup_app_right _ _ _ (by
      intro p hp heq
      obtain ⟨_, hlo, hhi⟩ := hLm p hp
      have hoff : p.1.off = σ 9 - 8 + (k : Int) := by rw [heq]; dsimp only; omega
      rcases hsepM with hs | hs <;> omega)]
    have hl := lookup_hom eP σ _ (KpreW Fr).mem _ (lkIs_sound _ _ _ (hbplk k hk8))
    simp only [mapAddr, sAt_eval, Option.map_some, mapCell, Lin.eval_sym] at hl
    rw [show (⟨rStack, σK 5 + Fr + (k : Int)⟩ : Addr Int) = ⟨rStack, -8 + (k : Int) + σ 9⟩ by
      congr 1; omega]
    exact hl
  have hret : ∀ k : Nat, k < 8 →
      readCell mem0c S ((⟨rStack, σK 5 + Fr + 8⟩ : Addr Int).plusI k) =
      .ok (.pb ⟨rRet, 0⟩ k) := by
    intro k hk8
    rw [plusI_nat, readCell_none]
    · obtain ⟨_, hret0, _, _⟩ := hw
      rw [show (⟨rStack, σK 5 + Fr + 8 + (k : Int)⟩ : Addr Int) = ⟨rStack, σ 9 + (k : Int)⟩ by
        congr 1; omega]
      rw [hret0 k (by omega) (by omega)]; rfl
    · show lookup _ (F.mem ++ (Lm ++ Lb)) = _
      rw [lookup_app_right _ _ _ (by
        intro p hp heq
        have hoff : p.1.off = σ 9 + (k : Int) := by rw [heq]; dsimp only; omega
        refine hFsep p hp ?_ ⟨by omega, by omega⟩
        rw [heq])]
      apply lookup_none_ne
      intro p hp heq
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨_, hlo, hhi⟩ := hLm p h
        have hoff : p.1.off = σ 9 + (k : Int) := by rw [heq]; dsimp only; omega
        rcases hsepM with hs | hs <;> omega
      · obtain ⟨_, hlo, hhi⟩ := hLb p h
        have hoff : p.1.off = σ 9 + (k : Int) := by rw [heq]; dsimp only; omega
        omega
  have h3S : S.getG 3 = .ptr ⟨rStack, σK 5⟩ := by
    show F.getG 3 = _
    rw [getG_of _ _ _ hr3]
  have h12S : S.getG 12 = .ptr ⟨rNum, σ 13⟩ := by
    show F.getG 12 = _
    rw [getG_of _ _ _ hr12]
    simp only [k7]
  obtain ⟨ph, pe, pt, pm, p4, p5, p8⟩ := post_runW mem0c orc S (σK 5) Fr ⟨rStack, σ 6⟩
    (.ptr ⟨rNum, σ 13⟩) rfl rfl hlen h3S h12S hbp hret
  have hw' : wrapRunW Fr kprog (steps c) mem0c orc (mapState env σ wEntryW) =
      run (post Fr) 4 mem0c orc 5 S := by
    simp only [wrapRunW]; rw [hcK]
  rw [hw']
  refine ⟨ph, pe.trans ke, pt.trans kt, ?_, p5, p8, ?_, ?_, ?_⟩
  · rw [p4]; congr 2; omega
  · rw [pm]
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases kfoot p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, by rw [k1] at h2; exact h2, by rw [k1] at h3; exact h3⟩
      · exact Or.inr ⟨h1, Or.inl ⟨by rw [k9] at h2; exact h2, by rw [k9] at h3; exact h3⟩⟩
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨a, b, d⟩ := hLm p h'; exact Or.inr ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩
      · obtain ⟨a, b, d⟩ := hLb p h'; exact Or.inr ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩
  · rw [pm]
    intro n i b hn hi hb
    obtain ⟨x, hx, hv⟩ := kout n i b hn hi hb
    rw [k1] at hx
    exact ⟨x, lookup_app_left _ _ _ _ hx, hv⟩
  · intro h9
    refine ⟨f ((⟨rStack, l10 0⟩ : Addr Lin), Cell.pb ⟨rRet, Lin.ofInt 0⟩ 0), ?_, ?_, ?_⟩
    · rw [pm]
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hhead))
    · simp only [f, mapAddr]
    · simp only [f, mapAddr, l10_eval]; omega

/-! ## The two frame geometries -/

/-- **The wrapper call with a kernel meeting `KSpecW`, fixed frame (`$2048`).**  This is the
Go-facing contract of `HashtreeHash`: the kernel's stack (`D ≤ 2009`) and the wrapper's own frame
and saved `rbp` all lie in `[SPe - 2056, SPe)`, the caller's frame is untouched, and the outputs
are SHA-256 of the input blocks. -/
theorem wrapper_kernelW_fixed (kprog : Array Instr) (rodata : List Nat) (steps : Nat → Nat)
    (D : Nat) (hk : KSpecW kprog rodata steps D) (hD : D ≤ 2009)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW rodata argCells env σ mem0c) (he : EnvMem env σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32) :
    let fin := wrapRunW fixedFrame kprog (steps c) mem0c orc (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
      OutOk inp (σ 1) c fin.mem := by
  let eP := envAbs env (run (pre fixedFrame) 4 m0W (fun _ => false) 9 wEntryW)
  have hP := (slice_sound env σ m0W mem0c (m0W_rel rodata env σ mem0c hw he)
    (pre fixedFrame) 4 (fun _ => false) orc 9 wEntryW (KpreW fixedFrame) [] slicePreW_fixed rfl
    (fun p hp => by rw [KpreW_fixed_assume] at hp; cases hp)).1
  have hAe : alignStep mem0c orc (mapState eP σ (KpreW fixedFrame)) =
      mapState eP σ (KalW fixedFrame) := align_homW_fixed eP σ mem0c orc hA
  have hsepM : σ 10 + 8 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 := by left; omega
  have hsepK : σ 10 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 - (D : Int) := by left; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ :=
    wrapper_kernelW_core fixedFrame kprog rodata steps D hk (KpreW_fixed_len) KCW_shape_fixed
      KCW_mem_split_fixed markerW_facts_fixed markerW_lk_fixed bpW_facts_fixed bpW_lk_fixed
      KCW_head_fixed c inp env σ mem0c orc eP hP hAe hsepM hsepK hw he hc hin
  have hA1 : σ 10 + 8 ≤ σ 9 - 8 := by omega
  have hA2 : σ 9 - 47 ≤ σ 10 := by omega
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8⟩
  intro p hp
  rcases h7 p hp with ⟨ho, a, b⟩ | ⟨hs, h⟩
  · exact Or.inl ⟨ho, a, b⟩
  · rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨hs, by omega, by omega⟩
    · exact Or.inr ⟨hs, by omega, by omega⟩
    · exact Or.inr ⟨hs, by omega, by omega⟩

/-- **The wrapper call with a kernel meeting `KSpecW`, shipped frame (`$1024`).**  Because the
assembler text still adds 2048, the aligned call `rsp` is `SPe + 985 .. SPe + 1016`: the return
marker and the kernel's stack are above the wrapper's entry `rsp`.  The machine still returns
correctly (`hD9`: the kernel's stack writes start at or above `SPe + 8`; otherwise the wrapper's
return address slot `[SPe, SPe+8)` is at risk), the call's writes are output bytes or bytes of
`[SPe - 8, σ10 + 8)` (the saved `rbp` and the caller's frame above `SPe`), the return marker is a
write above `SPe` (witness), and the linux-style footprint claim `Foot (SPe) 2056` is false. -/
theorem wrapper_kernelW_shipped (kprog : Array Instr) (rodata : List Nat) (steps : Nat → Nat)
    (D : Nat) (hk : KSpecW kprog rodata steps D)
    (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hw : WfMemW rodata argCells env σ mem0c) (he : EnvMem env σ mem0c) (hc : σ 2 = c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hA : σ 10 + 8 = (σ 9 + 1016) - (σ 9 + 1016) % 32)
    (hD9 : σ 9 + 8 ≤ σ 10 - (D : Int)) :
    let fin := wrapRunW shippedFrame kprog (steps c) mem0c orc (mapState env σ wEntryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
      fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
      (∀ p ∈ fin.mem, (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * c) ∨
        (p.1.region = rStack ∧ σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 10 + 8)) ∧
      OutOk inp (σ 1) c fin.mem ∧
      (∃ p ∈ fin.mem, p.1.region = rStack ∧ σ 9 ≤ p.1.off) ∧
      ¬ Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem := by
  let eP := envAbs env (run (pre shippedFrame) 4 m0W (fun _ => false) 9 wEntryW)
  have hP := (slice_sound env σ m0W mem0c (m0W_rel rodata env σ mem0c hw he)
    (pre shippedFrame) 4 (fun _ => false) orc 9 wEntryW (KpreW shippedFrame) [] slicePreW_shipped rfl
    (fun p hp => by rw [KpreW_shipped_assume] at hp; cases hp)).1
  have hAe : alignStep mem0c orc (mapState eP σ (KpreW shippedFrame)) =
      mapState eP σ (KalW shippedFrame) := align_homW_shipped eP σ mem0c orc hA
  have hsepM : σ 10 + 8 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 := by right; omega
  have hsepK : σ 10 ≤ σ 9 - 8 ∨ σ 9 + 8 ≤ σ 10 - (D : Int) := by right; exact hD9
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hwit⟩ :=
    wrapper_kernelW_core shippedFrame kprog rodata steps D hk (KpreW_shipped_len) KCW_shape_shipped
      KCW_mem_split_shipped markerW_facts_shipped markerW_lk_shipped bpW_facts_shipped bpW_lk_shipped
      KCW_head_shipped c inp env σ mem0c orc eP hP hAe hsepM hsepK hw he hc hin
  have h9le : σ 9 ≤ σ 10 := by omega
  have hwit' := hwit h9le
  have hfoot : ∀ p ∈ (wrapRunW shippedFrame kprog (steps c) mem0c orc
      (mapState env σ wEntryW)).mem,
      (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * c) ∨
        (p.1.region = rStack ∧ σ 9 - 8 ≤ p.1.off ∧ p.1.off < σ 10 + 8) := by
    intro p hp
    rcases h7 p hp with ⟨ho, a, b⟩ | ⟨hs, h⟩
    · exact Or.inl ⟨ho, a, b⟩
    · rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inr ⟨hs, by omega, by omega⟩
      · exact Or.inr ⟨hs, by omega, by omega⟩
      · exact Or.inr ⟨hs, by omega, by omega⟩
  have hnot : ¬ Foot (σ 9) 2056 (σ 1) (32 * c)
      (wrapRunW shippedFrame kprog (steps c) mem0c orc (mapState env σ wEntryW)).mem := by
    intro hF
    obtain ⟨p, hp, hreg, hoff⟩ := hwit'
    have h := hF p hp
    rcases h with ⟨ho, _, _⟩ | ⟨hs, _, hlt⟩
    · rw [hreg] at ho; exact absurd ho (by decide)
    · omega
  exact ⟨h1, h2, h3, h4, h5, h6, hfoot, h8, ⟨hwit'.choose, hwit'.choose_spec.1,
    hwit'.choose_spec.2.1, by omega⟩, hnot⟩

/-! ## The dispatch -/

def kprogOfW : Kern → Array Instr
  | .shani => Kernels.X86Win.Shani.prog | .avx512 => Kernels.X86Win.Avx512X16.prog
  | .avx2 => Kernels.X86Win.Avx2X8.prog | .avx1 => Kernels.X86Win.AvxX1.prog

def krodataOfW : Kern → List Nat
  | .shani => Kernels.X86Win.Shani.rodata | .avx512 => Kernels.X86Win.Avx512X16.rodata
  | .avx2 => Kernels.X86Win.Avx2X8.rodata | .avx1 => Kernels.X86Win.AvxX1.rodata

/-- A windows kernel's contract at the wrapper's call state, with a step count and a stack depth
that fits the wrapper's frame. -/
def FitsW (k : Kern) : Prop :=
  ∃ (steps : Nat → Nat) (D : Nat), D ≤ 2009 ∧ KSpecW (kprogOfW k) (krodataOfW k) steps D

/-- **`HashtreeHash` (windows/amd64, fixed frame) is correct** for whichever kernel the three
feature bytes select, given the windows contracts of the four kernels (`hShani`, `hAvx512`,
`hAvx2`, `hAvx1`).  The per-kernel windows functional contracts at `entryWin` are the open gap
(see `formal/notes/R5.md` section 6); the avx512 stream's contract must not assume `xmm6`-`xmm15`
(U6, `WinAvx512.u6_witness`). -/
theorem wrapper_correctW (hasShani hasAVX512 hasAVX2 : Bool)
    (hShani : FitsW .shani) (hAvx512 : FitsW .avx512) (hAvx2 : FitsW .avx2)
    (hAvx1 : FitsW .avx1) :
    let k := pick hasShani hasAVX512 hasAVX2
    ∃ steps : Nat → Nat, ∀ (c : Nat) (inp : Nat → Spec.Byte) (env : Key → W32)
      (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool),
      WfMemW (krodataOfW k) argCells env σ mem0c → EnvMem env σ mem0c → σ 2 = c →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      σ 10 + 8 = (σ 9 - 8) - (σ 9 - 8) % 32 →
      let fin := wrapRunW fixedFrame (kprogOfW k) (steps c) mem0c orc (mapState env σ wEntryW)
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
        fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧
        fin.getG 8 = .ptr ⟨rNum, σ 13⟩ ∧
        Foot (σ 9) 2056 (σ 1) (32 * c) fin.mem ∧
        OutOk inp (σ 1) c fin.mem := by
  intro k
  have hf : FitsW k := by
    simp only [k, pick]
    split
    · exact hShani
    · split
      · exact hAvx512
      · split
        · exact hAvx2
        · exact hAvx1
  obtain ⟨steps, D, hD, hs⟩ := hf
  exact ⟨steps, fun c inp env σ mem0c orc hw he hc hin hA =>
    wrapper_kernelW_fixed _ _ steps D hs hD c inp env σ mem0c orc hw he hc hin hA⟩

end Hashtree.Proofs.WinWrapper
