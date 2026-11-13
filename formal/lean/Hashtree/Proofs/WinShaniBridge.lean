import Hashtree.Proofs.WinShaniSeedAlign
import Hashtree.Proofs.WinShaniExit
import Hashtree.Proofs.ShaniW
import Hashtree.Proofs.WinWrapper
import Hashtree.Asm.RunExit
import Hashtree.Asm.X86RunHom
import Hashtree.Asm.X86Loop

/-!
# R5: the positive `shani_x2` bridge — the windows seed runs like the linux certificate

`WinShaniSeedAlign` proved that the windows body seed `seedSt st a` is not the certificate start
state `mapState e σ entryW` (constructors differ on registers the body never reads).  This module
closes checkpoint (a): on the registers the body can read before writing (`[2, 6, 4, 7]`, the
entry live set of the linux program) the seed agrees with the certificate's state after its
`sub rsp, 88`, so `RunAgree.run_agree` carries the certificate's conclusions (halted, no error,
no tail call, the write log) over to the seed run, and `RunExit` locates the body exit.

The windows save log (the ten `movdqa [rsp+16k], xmm(6+k)` of the prologue) is below the linux
frame; `X86Frame.run_fr` moves it into the initial memory (`view`), where `ShaniW.wfW_view` shows
the certificate's memory hypotheses still hold.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Hashtree.Proofs.WinShaniBridge

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.BodyReads
open Hashtree.Asm.RunAgree Hashtree.Asm.RunExit
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinShaniCall (seedSt seedSt_getG seedSt_gpr_len)
open Hashtree.Proofs.WinShani (F G)
open Hashtree.Proofs.WinShaniFront (saveLog laneLog saveSt)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG linuxLive shani_linux_cert shani_linux_live_entry_eq)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Shani.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog
abbrev rodata : List Nat := Hashtree.Kernels.X86.Shani.rodata
abbrev mem0S : Addr Lin → Cell E Lin := mem0sW 4 rodata []

/-! ## The certificate's state after `sub rsp, 88`, symbolically -/

/-- One symbolic step of the linux program from the certificate start state. -/
def E1 : State E Lin := run linuxProg 4 mem0S (fun _ => false) 1 entryW

theorem E1_err : E1.err = none := by decide +kernel
theorem E1_assume : E1.assume = [] := by decide +kernel
theorem E1_pc : E1.pc = 1 := by decide +kernel
theorem E1_halted : E1.halted = false := by decide +kernel
theorem E1_tail : E1.tail = none := by decide +kernel
theorem E1_mem : E1.mem = [] := by decide +kernel
theorem E1_vr : E1.vr = entryW.vr := by decide +kernel
theorem E1_len : E1.gpr.length = 16 := by decide +kernel
theorem E1_flags : E1.flags = some (sAt 0, Lin.ofInt 88) := by decide +kernel
theorem E1_gpr2 : E1.gpr[2]? = some (.ptr ⟨rNum, Lin.sym 2⟩) := by decide +kernel
theorem E1_gpr6 : E1.gpr[6]? = some (.ptr ⟨rIn, Lin.sym 0⟩) := by decide +kernel
theorem E1_gpr7 : E1.gpr[7]? = some (.ptr ⟨rOut, Lin.sym 1⟩) := by decide +kernel
theorem E1_gpr4 : E1.gpr[4]? = some (.ptr ⟨rStack, sAt (-88)⟩) := by decide +kernel

theorem E1_assumeOk (σ : Nat → Int) : AssumeOk σ E1 := by
  intro p hp; rw [E1_assume] at hp; cases hp

/-- The certificate's concrete state after one step is the image of `E1`. -/
theorem run1_eq (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel e σ mem0S m) :
    run linuxProg 4 m orcC 1 (mapState e σ entryW) = mapState e σ E1 :=
  run_hom e σ mem0S m h0 linuxProg 4 (fun _ => false) orcC 1 entryW rfl E1_err (E1_assumeOk σ)

/-! ## The windows call state and the seed -/

section Seed
variable (env : Key → W32) (σ : Nat → Int)

/-- The windows kernel call state, concretely. -/
def stW : State W32 Int := mapState env σ entryWin
/-- The return-address pointer (the kernel's entry `rsp`). -/
def aW : Addr Int := ⟨rStack, σ 9⟩
/-- The windows prologue's save log (the ten `xmm6`-`xmm15` slots below the linux frame). -/
def M : CLog := saveLog (stW env σ) ((aW σ).plusI (-248)) 10 []
/-- The linux body seed without the save log. -/
def s0 : State W32 Int := { seedSt (stW env σ) (aW σ) with mem := [] }

theorem stW_mem : (stW env σ).mem = [] := rfl
theorem stW_halted : (stW env σ).halted = false := rfl
theorem stW_len : (stW env σ).gpr.length = 16 := by
  show (entryWin.gpr.map _).length = 16
  rw [List.length_map]; decide +kernel

theorem entryWin_gpr4 : entryWin.gpr[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel
theorem entryWin_gpr1 : entryWin.gpr[1]? = some (.ptr ⟨rOut, Lin.sym 1⟩) := by decide +kernel
theorem entryWin_gpr2 : entryWin.gpr[2]? = some (.ptr ⟨rIn, Lin.sym 0⟩) := by decide +kernel
theorem entryWin_gpr8 : entryWin.gpr[8]? = some (.ptr ⟨rNum, Lin.sym 2⟩) := by decide +kernel

theorem stW_rsp : (stW env σ).getG rsp = .ptr (aW σ) := by
  show (mapState env σ entryWin).getG 4 = _
  rw [mapState_getG entryWin_gpr4]
  simp only [mapVal, mapAddr, sAt_eval, aW, Int.zero_add]

theorem seed_fr : seedSt (stW env σ) (aW σ) = fr (M env σ) (s0 env σ) := by
  simp only [fr, s0, M, seedSt, stW_mem, List.nil_append]

/-! ### The save log lives in `[σ 9 - 248, σ 9 - 88)` -/

theorem laneLog_upper (a : Addr Int) (xs : List W32) (p : Addr Int × Cell W32 Int)
    (hp : p ∈ laneLog a xs) : p.1.off < a.off + 4 * xs.length := by
  induction xs generalizing a with
  | nil => simp only [laneLog, List.not_mem_nil] at hp
  | cons x xs ih =>
    simp only [laneLog, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hp
    rcases hp with hp | hp | hp | hp | hp
    · have := ih _ hp
      simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, List.length_cons] at this ⊢
      omega
    all_goals (subst hp; simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, List.length_cons]; omega)

theorem saveLog_bounds (st : State W32 Int) (r : Addr Int) :
    ∀ (n : Nat) (p : Addr Int × Cell W32 Int), p ∈ saveLog st r n [] →
      p.1.region = r.region ∧ r.off ≤ p.1.off ∧ p.1.off < r.off + 16 * n
  | 0, p, hp => by simp only [saveLog, List.not_mem_nil] at hp
  | n + 1, p, hp => by
    simp only [saveLog, List.mem_append] at hp
    rcases hp with hp | hp
    · have h1 := Hashtree.Proofs.WinShaniEpi.laneLog_bounds _ _ p hp
      have h2 := laneLog_upper _ _ p hp
      have hl : ((st.getV (6 + n)).take 4).length ≤ 4 := by
        rw [List.length_take]; omega
      simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq] at h1 h2
      refine ⟨h1.1, by omega, by omega⟩
    · have := saveLog_bounds st r n p hp
      refine ⟨this.1, this.2.1, by omega⟩

theorem M_bounds (p : Addr Int × Cell W32 Int) (hp : p ∈ M env σ) :
    p.1.region = rStack ∧ σ 9 - 248 ≤ p.1.off ∧ p.1.off < σ 9 - 88 := by
  have := saveLog_bounds _ _ 10 p hp
  simp only [aW, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq] at this
  exact ⟨this.1, by omega, by omega⟩

theorem M_outLog : Hashtree.Proofs.ShaniW.OutLogW (σ 9) (M env σ) := by
  intro p hp
  have := M_bounds env σ p hp
  exact Or.inr ⟨this.1, by omega⟩

/-- The save log does not touch an address outside its range. -/
theorem M_ne (a : Addr Int) (ha : a.region ≠ rStack ∨ a.off < σ 9 - 248 ∨ σ 9 - 88 ≤ a.off) :
    ∀ p ∈ M env σ, p.1 ≠ a := by
  intro p hp heq
  have := M_bounds env σ p hp
  rw [heq] at this
  rcases ha with ha | ha | ha
  · exact ha this.1
  · omega
  · omega

theorem view_M (m : Addr Int → Cell W32 Int) (a : Addr Int)
    (ha : a.region ≠ rStack ∨ a.off < σ 9 - 248 ∨ σ 9 - 88 ≤ a.off) : view (M env σ) m a = m a :=
  view_other _ m a (M_ne env σ a ha)

/-! ### The certificate environment -/

/-- The certificate's symbol environment: the windows one on numbered symbols, the viewed memory
on memory symbols. -/
def eOf (m : Addr Int → Cell W32 Int) : Key → W32 := fun k => match k with
  | .n i => env (.n i)
  | .m r off => cellX (m ⟨r, off.eval σ⟩)

theorem envMem_eOf (m : Addr Int → Cell W32 Int) : EnvMem (eOf env σ m) σ m := fun _ _ => rfl

theorem wf_view (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata [] env σ m) :
    WfMemW rodata [] (eOf env σ (view (M env σ) m)) σ (view (M env σ) m) :=
  Hashtree.Proofs.ShaniW.wfW_view env _ σ σ rfl m (M env σ) (M_outLog env σ) hw

theorem hin_view (m : Addr Int → Cell W32 Int) (inp : Nat → Spec.Byte)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, view (M env σ) m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
  intro o
  rw [view_M env σ m _ (Or.inl (show rIn ≠ rStack by decide))]
  exact hin o

theorem vr_eq (m : Addr Int → Cell W32 Int) :
    E1.vr.map (·.map (E.eval (eOf env σ m))) = entryWin.vr.map (·.map (E.eval env)) := by
  rw [E1_vr]
  show entryW.vr.map _ = entryW.vr.map _
  apply List.map_congr_left
  intro v hv
  simp only [entryW, List.mem_map, List.mem_range] at hv
  obtain ⟨i, _, rfl⟩ := hv
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  rfl

/-! ## The alignment: the seed agrees with the certificate on the entry live set -/

theorem seed_agree (m : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel (eOf env σ m) σ mem0S m) :
    Agree [2, 6, 4, 7] (s0 env σ) (run linuxProg 4 m orcC 1 (mapState (eOf env σ m) σ entryW)) := by
  rw [run1_eq _ _ _ _ h0]
  have hs0 : ∀ j, (s0 env σ).getG j = (seedSt (stW env σ) (aW σ)).getG j := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rw [hs0]
    rcases hr with rfl | rfl | rfl | rfl
    · rw [seedSt_getG _ _ 2 (by omega), ite_eq_right (by decide), show F 2 = 8 from rfl]
      show (mapState env σ entryWin).getG 8 = _
      rw [mapState_getG entryWin_gpr8, mapState_getG E1_gpr2]; simp only [mapVal]
    · rw [seedSt_getG _ _ 6 (by omega), ite_eq_right (by decide), show F 6 = 2 from rfl]
      show (mapState env σ entryWin).getG 2 = _
      rw [mapState_getG entryWin_gpr2, mapState_getG E1_gpr6]; simp only [mapVal]
    · rw [seedSt_getG _ _ 4 (by omega), ite_eq_left rfl, mapState_getG E1_gpr4]
      simp only [mapVal, mapAddr, sAt_eval, aW, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]
      rw [Int.add_comm]
    · rw [seedSt_getG _ _ 7 (by omega), ite_eq_right (by decide), show F 7 = 1 from rfl]
      show (mapState env σ entryWin).getG 1 = _
      rw [mapState_getG entryWin_gpr1, mapState_getG E1_gpr7]; simp only [mapVal]
  · show (seedSt (stW env σ) (aW σ)).gpr.length = (E1.gpr.map _).length
    rw [seedSt_gpr_len, List.length_map, E1_len]
  · show (entryWin.vr.map _) = E1.vr.map _
    exact (vr_eq env σ m).symm
  · have h1 : (s0 env σ).flags = some ((aW σ).off, (88 : Int)) := rfl
    have h2 : (mapState (eOf env σ m) σ E1).flags =
        E1.flags.map (fun p => (p.1.eval σ, p.2.eval σ)) := rfl
    rw [h1, h2, E1_flags]
    simp only [Option.map_some, sAt_eval, aW, Int.zero_add, show Lin.eval σ (Lin.ofInt 88) = 88 from rfl]
  · have h2 : (mapState (eOf env σ m) σ E1).mem =
        E1.mem.map (fun p => (mapAddr σ p.1, mapCell (eOf env σ m) σ p.2)) := rfl
    show ([] : CLog) = _
    rw [h2, E1_mem]; rfl
  · show 1 = E1.pc
    rw [E1_pc]
  · show false = E1.halted
    rw [E1_halted]
  · show none = E1.tail
    rw [E1_tail]
  · show none = E1.err
    rw [E1_err]

end Seed

/-! ## The linux body region and its never-written registers -/

/-- Kernel scan: pcs 1..668 form a body with exit 669, and never write rsp, nor the linux
homes of the Win64 callee-saved registers (`G 3 = 8`, `G 5 = 3`, 12, 13, 14, 15). -/
theorem linux_bodyScan : bodyScan linuxProg 1 669 [4, 8, 3, 12, 13, 14, 15] = true := by
  decide +kernel

theorem linux_body : Body linuxProg 1 669 := (bodyScan_sound linux_bodyScan).1

theorem linux_unwritten (r : Nat) (hr : r ∈ [4, 8, 3, 12, 13, 14, 15]) :
    ∀ p i, 1 ≤ p → p < 669 → linuxProg[p]? = some i → r ∉ dsts i :=
  (bodyScan_sound linux_bodyScan).2 r hr

theorem linux_669 : linuxProg[669]? = some (.alu .add 64 4 (.imm 88)) := by decide +kernel
theorem linux_670 : linuxProg[670]? = some .ret := by decide +kernel

theorem rodata_eq : Hashtree.Kernels.X86Win.Shani.rodata = rodata := by decide +kernel

/-! ## Reading rodata and the return marker -/

theorem plusI_nat' (r : Region) (o : Int) (k : Nat) : (⟨r, o⟩ : Addr Int).plusI k = ⟨r, o + k⟩ := by
  simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]

theorem isPb_self (p : Addr Int) (k : Nat) : isPb p k (.pb p k : Cell W32 Int) = true := by
  simp [isPb, AddrEq.same]

/-- Four data cells load as a lane. -/
theorem loadLane_ok (m : Addr Int → Cell W32 Int) (s : State W32 Int) (r : Region) (o : Int)
    (h : ∀ k : Int, 0 ≤ k → k < 4 → ∃ x, readCell m s ⟨r, o + k⟩ = .ok (.dat x 0)) :
    ∃ v, loadLane m s ⟨r, o⟩ = .ok v := by
  obtain ⟨x0, h0⟩ := h 0 (by decide) (by decide)
  obtain ⟨x1, h1⟩ := h 1 (by decide) (by decide)
  obtain ⟨x2, h2⟩ := h 2 (by decide) (by decide)
  obtain ⟨x3, h3⟩ := h 3 (by decide) (by decide)
  rw [Int.add_zero] at h0
  simp only [loadLane, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, h0, h1, h2, h3, bind,
    Except.bind, lanePat, cellData, pure, Except.pure]
  exact ⟨_, rfl⟩

theorem loadLanes_ok (m : Addr Int → Cell W32 Int) (s : State W32 Int) (r : Region) :
    ∀ (n : Nat) (o : Int), (∀ k : Int, 0 ≤ k → k < 4 * n → ∃ x, readCell m s ⟨r, o + k⟩ = .ok (.dat x 0)) →
      ∃ v, loadLanes m s ⟨r, o⟩ n = .ok v
  | 0, o, _ => ⟨[], rfl⟩
  | n + 1, o, h => by
    obtain ⟨x, hx⟩ := loadLane_ok m s r o (fun k hk0 hk => h k hk0 (by omega))
    obtain ⟨xs, hxs⟩ := loadLanes_ok m s r n (o + 4) (fun k hk0 hk => by
      have := h (k + 4) (by omega) (by omega)
      rwa [show o + (k + 4) = o + 4 + k by omega] at this)
    refine ⟨x :: xs, ?_⟩
    simp only [loadLanes, hx, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, hxs, bind, Except.bind,
      pure, Except.pure]

/-- The eight pointer bytes of the return marker load as the return pointer. -/
theorem loadVal_marker (m : Addr Int → Cell W32 Int) (s : State W32 Int) (b : Int)
    (hc0 : readCell m s ⟨rStack, b⟩ = .ok (.pb ⟨rRet, 0⟩ 0))
    (hcell : ∀ k : Nat, k < 8 → readCell m s ((⟨rStack, b⟩ : Addr Int).plusI k) = .ok (.pb ⟨rRet, 0⟩ k)) :
    loadVal m s ⟨rStack, b⟩ = .ok (.ptr ⟨rRet, 0⟩) := by
  simp only [loadVal, hc0, bind, Except.bind, pbRest, hcell 1 (by omega), hcell 2 (by omega),
    hcell 3 (by omega), hcell 4 (by omega), hcell 5 (by omega), hcell 6 (by omega), hcell 7 (by omega),
    isPb_self, ite_true, pure, Except.pure]

/-! ## The epilogue keeps `err` and `tail` -/

theorem epiSt_err (s st : State W32 Int) : ∀ k, (Hashtree.Proofs.WinShaniEpi.epiSt s st k).err = s.err
  | 0 => rfl
  | k + 1 => by
    rw [Hashtree.Proofs.WinShaniEpi.epiSt_succ]
    simp only [State.next, setVec, State.setV]
    exact epiSt_err s st k

theorem epiSt_tail (s st : State W32 Int) : ∀ k, (Hashtree.Proofs.WinShaniEpi.epiSt s st k).tail = s.tail
  | 0 => rfl
  | k + 1 => by
    rw [Hashtree.Proofs.WinShaniEpi.epiSt_succ]
    simp only [State.next, setVec, State.setV]
    exact epiSt_tail s st k

theorem epiSt_gpr_len (s st : State W32 Int) : ∀ k, (Hashtree.Proofs.WinShaniEpi.epiSt s st k).gpr.length = s.gpr.length
  | 0 => rfl
  | k + 1 => by
    rw [Hashtree.Proofs.WinShaniEpi.epiSt_succ]
    simp only [State.next, setVec, State.setV]
    exact epiSt_gpr_len s st k

theorem epiFinal_err (t0 st : State W32 Int) (r : Addr Int) :
    (Hashtree.Proofs.WinShaniEpi.epiFinal t0 st r).err = t0.err := by
  show (Hashtree.Proofs.WinShaniEpi.epiSt t0 st 10).err = t0.err
  exact epiSt_err t0 st 10

theorem epiFinal_tail (t0 st : State W32 Int) (r : Addr Int) :
    (Hashtree.Proofs.WinShaniEpi.epiFinal t0 st r).tail = t0.tail := by
  show (Hashtree.Proofs.WinShaniEpi.epiSt t0 st 10).tail = t0.tail
  exact epiSt_tail t0 st 10

theorem epiFinal_gpr_len (t0 st : State W32 Int) (r : Addr Int) :
    (Hashtree.Proofs.WinShaniEpi.epiFinal t0 st r).gpr.length = t0.gpr.length := by
  show ((Hashtree.Proofs.WinShaniEpi.epiSt t0 st 10).gpr.set rsp _).length = t0.gpr.length
  rw [List.length_set]; exact epiSt_gpr_len t0 st 10

theorem getElem?_of_getG (s : State W32 Int) (j : Nat) (hj : j < s.gpr.length) :
    s.gpr[j]? = some (s.getG j) := by
  rw [List.getElem?_eq_getElem hj]
  simp only [State.getG, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem entryWin_getV_len : ∀ k, k < 10 → (entryWin.getV (6 + k)).length = 16 := by decide +kernel

/-! ## The main theorem: the windows call from the linux certificate -/

section Main
variable (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
  (c : Nat) (inp : Nat → Spec.Byte)

/-- The viewed memory (the save log folded into the initial memory). -/
abbrev mV : Addr Int → Cell W32 Int := view (M env σ) m
/-- The certificate environment on the viewed memory. -/
abbrev eV : Key → W32 := eOf env σ (mV env σ m)
/-- The body fuel: the certificate's step count minus the `sub rsp, 88`. -/
abbrev N : Nat := Hashtree.Proofs.ShaniW.steps c - 1
/-- The seed run at the certificate's fuel. -/
abbrev finS : State W32 Int := run linuxProg 4 (mV env σ m) orcC (N c) (s0 env σ)

theorem steps_pos : Hashtree.Proofs.ShaniW.steps c = 1 + N c := by
  simp only [N, Hashtree.Proofs.ShaniW.steps]; omega

/-- The agreement of the seed run with the certificate run, every fuel. -/
theorem run_agree_fuel (hw : WfMemW rodata [] env σ m) (k : Nat) :
    Agree (linuxLive.getD (run linuxProg 4 (mV env σ m) orcC k (s0 env σ)).pc [])
      (run linuxProg 4 (mV env σ m) orcC k (s0 env σ))
      (run linuxProg 4 (mV env σ m) orcC k
        (run linuxProg 4 (mV env σ m) orcC 1 (mapState (eV env σ m) σ entryW))) := by
  apply run_agree linuxProg 4 (mV env σ m) orcC shani_linux_cert k
  show Agree (linuxLive.getD 1 []) _ _
  rw [shani_linux_live_entry_eq]
  exact seed_agree env σ (mV env σ m) orcC
    (mem0RelW_of_wf rodata [] _ σ _ (wf_view env σ m hw) (envMem_eOf env σ _))

/-- The certificate's run, split after its first step. -/
theorem cert_split :
    run linuxProg 4 (mV env σ m) orcC (Hashtree.Proofs.ShaniW.steps c) (mapState (eV env σ m) σ entryW)
      = run linuxProg 4 (mV env σ m) orcC (N c)
          (run linuxProg 4 (mV env σ m) orcC 1 (mapState (eV env σ m) σ entryW)) := by
  rw [steps_pos c, run_add]

/-- What the certificate gives at the viewed memory. -/
theorem cert (hw : WfMemW rodata [] env σ m) (hc : σ 2 = c)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (finS env σ m orcC c).halted = true ∧ (finS env σ m orcC c).err = none ∧
      (finS env σ m orcC c).tail = none ∧
      Hashtree.Proofs.ShaniW.InRange (σ 9) (σ 1) (32 * c) (finS env σ m orcC c).mem ∧
      Hashtree.Proofs.ShaniW.OutOk inp (σ 1) c (finS env σ m orcC c).mem := by
  have hcert := Hashtree.Proofs.ShaniW.correctW c inp (eV env σ m) σ (mV env σ m) orcC
    (wf_view env σ m hw) (envMem_eOf env σ _) hc (hin_view env σ m inp hin)
  obtain ⟨hH, hE, hT, hIR, hOO, _⟩ := hcert
  rw [cert_split] at hH hE hT hIR hOO
  have hA := run_agree_fuel env σ m orcC hw (N c)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hA.halted]; exact hH
  · rw [hA.err]; exact hE
  · rw [hA.tail]; exact hT
  · rw [hA.mem]; exact hIR
  · rw [hA.mem]; exact hOO

/-- The body exit of the seed run: a fuel `n ≤ N` at which the linux body reaches pc 669 unhalted,
inside before, with the registers the body never writes intact and the log of the whole run. -/
theorem exit (hw : WfMemW rodata [] env σ m) (hc : σ 2 = c)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ n, n ≤ N c ∧
      (∀ k, k < n → 1 ≤ (run linuxProg 4 (mV env σ m) orcC k (s0 env σ)).pc ∧
        (run linuxProg 4 (mV env σ m) orcC k (s0 env σ)).pc < 669 ∧
        (run linuxProg 4 (mV env σ m) orcC k (s0 env σ)).halted = false) ∧
      (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)).pc = 669 ∧
      (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)).halted = false ∧
      (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)).err = none ∧
      (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)).tail = none ∧
      (∀ r, r ∈ [4, 8, 3, 12, 13, 14, 15] →
        (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)).getG r = (s0 env σ).getG r) ∧
      (run linuxProg 4 (mV env σ m) orcC (N c) (s0 env σ)).mem
        = (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)).mem := by
  obtain ⟨hH, hE, _, _, _⟩ := cert env σ m orcC c inp hw hc hin
  simp only [finS] at hH hE
  obtain ⟨n, hn, hk, hpc, hnh⟩ := run_exit linuxProg 4 (mV env σ m) orcC linux_body (N c) (s0 env σ)
    (by show 1 ≤ 1; omega) (by show 1 < 669; omega) rfl hH hE
  have herr : ∀ k, k ≤ N c → (run linuxProg 4 (mV env σ m) orcC k (s0 env σ)).err = none :=
    run_err_none linuxProg 4 (mV env σ m) orcC (N c) (s0 env σ) hE
  refine ⟨n, hn, hk, hpc, hnh, herr n hn, ?_, ?_, ?_⟩
  · rw [run_tail linuxProg 4 (mV env σ m) orcC n (s0 env σ) hnh]; rfl
  · intro r hr
    exact run_preserve linuxProg 4 (mV env σ m) orcC r (linux_unwritten r hr) n (s0 env σ) hk (herr n hn)
  · -- the tail: `add rsp, 88` at 669 then `ret` at 670, then halted
    have hsplit : run linuxProg 4 (mV env σ m) orcC (N c) (s0 env σ)
        = run linuxProg 4 (mV env σ m) orcC (N c - n) (run linuxProg 4 (mV env σ m) orcC n (s0 env σ)) := by
      rw [← run_add, Nat.add_sub_cancel' hn]
    have herrS : ∀ k, k ≤ N c - n →
        (run linuxProg 4 (mV env σ m) orcC k (run linuxProg 4 (mV env σ m) orcC n (s0 env σ))).err = none := by
      intro k hk'; rw [← run_add]; exact herr (n + k) (by omega)
    rw [hsplit] at hH ⊢
    generalize hS : run linuxProg 4 (mV env σ m) orcC n (s0 env σ) = S at hpc hnh herrS hH ⊢
    -- step 1: add
    have h1 := exec_shape 4 (mV env σ m) orcC (.alu .add 64 4 (.imm 88)) S hnh
    have hs1 : run linuxProg 4 (mV env σ m) orcC 1 S = exec 4 (mV env σ m) orcC (.alu .add 64 4 (.imm 88)) S := by
      rw [run_succ linuxProg 4 (mV env σ m) orcC 0 S hnh _ (by rw [hpc]; exact linux_669)]; rfl
    have hN1 : 1 ≤ N c - n := by
      rcases Nat.lt_or_ge (N c - n) 1 with hlt | hge
      · exfalso
        have : N c - n = 0 := by omega
        rw [this] at hH
        simp only [run] at hH
        rw [hnh] at hH; cases hH
      · exact hge
    have he1 : (exec 4 (mV env σ m) orcC (.alu .add 64 4 (.imm 88)) S).err = none := by
      rw [← hs1]; exact herrS 1 hN1
    rcases h1 with ⟨h1e, _⟩ | ⟨_, h1h, _, h1m, _, _, h1pc⟩
    · exact absurd he1 h1e
    generalize hS1 : exec 4 (mV env σ m) orcC (.alu .add 64 4 (.imm 88)) S = S1 at hs1 h1h h1m h1pc he1
    have h1h' : S1.halted = false := by
      rcases h1h with h | h
      · rw [h]; exact hnh
      · simp [halts] at h
    have h1pc' : S1.pc = 670 := by
      rcases h1pc with h | h
      · simpa [succs, hpc] using h
      · rw [h1h'] at h; cases h
    have h1m' : S1.mem = S.mem := h1m rfl
    -- step 2: ret
    have h2 := exec_shape 4 (mV env σ m) orcC .ret S1 h1h'
    have hs2 : run linuxProg 4 (mV env σ m) orcC 2 S = exec 4 (mV env σ m) orcC .ret S1 := by
      rw [run_succ linuxProg 4 (mV env σ m) orcC 1 S hnh _ (by rw [hpc]; exact linux_669), hS1]
      rw [run_succ linuxProg 4 (mV env σ m) orcC 0 S1 h1h' _ (by rw [h1pc']; exact linux_670)]; rfl
    have hN2 : 2 ≤ N c - n := by
      rcases Nat.lt_or_ge (N c - n) 2 with hlt | hge
      · exfalso
        have : N c - n = 1 := by omega
        rw [this, hs1] at hH
        rw [h1h'] at hH; cases hH
      · exact hge
    have he2 : (exec 4 (mV env σ m) orcC .ret S1).err = none := by
      rw [← hs2]; exact herrS 2 hN2
    rcases h2 with ⟨h2e, _⟩ | ⟨_, _, _, h2m, h2halt, _, _⟩
    · exact absurd he2 h2e
    have h2h' : (exec 4 (mV env σ m) orcC .ret S1).halted = true := h2halt rfl
    have h2m' : (exec 4 (mV env σ m) orcC .ret S1).mem = S1.mem := h2m rfl
    have hrest : run linuxProg 4 (mV env σ m) orcC (N c - n) S
        = run linuxProg 4 (mV env σ m) orcC (N c - n - 2) (exec 4 (mV env σ m) orcC .ret S1) := by
      rw [← hs2, ← run_add, Nat.add_sub_cancel' hN2]
    rw [hrest, run_halted_eq _ _ _ _ _ _ h2h', h2m', h1m']

end Main


end Hashtree.Proofs.WinShaniBridge
