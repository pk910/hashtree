import Hashtree.Proofs.WinShaniWrite
import Hashtree.Proofs.WinNs
import Hashtree.Proofs.WinShaniCall

/-!
# R5: discharging the body-exit stack facts of the windows `shani_x2` call

`WinShaniCall.shani_call` ends in the epilogue from a linux body-exit state, taking three
stack facts as hypotheses: `hrsp` (`rsp` is still the body value `a - 88`), and `hW`/`hmem` (the
body's stack image is the prologue save log under a prefix `W` outside the 160-byte save area).

This module proves them from the shipped streams:

* `exec_rsp_ns` -- an `nsSafe` instruction does not write `rsp`; `run_rsp` -- hence a run of a body
  slice leaves `rsp` alone.
* `shani_linux_ns`, `shani_linux_ws` -- kernel-checked scans of the 668-instruction linux body
  (`nsSafeB`, and `wSafeB 160` where the save-area base is `a - 248` and `rsp = a - 88`).
* `shani_body_log` -- the `WinShaniWrite` engine applied to the linux body run: the memory at
  body exit is `W ++ saveLog st (a - 248) 10 st.mem` with `Outside (a - 248) 160 W`.
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Hashtree.Proofs.WinShaniExit

open Hashtree.Proofs.WinShaniEpi (Outside plusI_off plusI_region plusI_zero plusI_add)
open Hashtree.Proofs.WinShani (F)
open Hashtree.Proofs.WinShaniCall (seedSt seedSt_getG seedSt_gpr_len bodyExit shani_call)
open Hashtree.Proofs.WinShaniFront (saveLog saveSt)
open Hashtree.Proofs.WinShaniEpi (epiFinal)
open Hashtree.Proofs.WinShaniFlags (m256)
open Hashtree.Proofs.WinShani (winProg)

open Hashtree.Proofs.WinShaniWrite (wSafe wSafeB wSafeB_iff exec_write_log run_write_log
  outside_nil outside_app)

/-! ## `rsp` is not written by an `nsSafe` instruction -/

theorem exec_rsp_ns {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (i : Instr) (s : State W32 Int) (hn : nsSafe i) :
    (exec ro mem0 orc i s).getG 4 = s.getG 4 := by
  cases hs : s.halted with
  | true => simp only [exec, hs, ite_true]
  | false =>
  simp only [exec, hs, Bool.false_eq_true, ite_false]
  cases i with
  | nop =>
    dsimp only
    simp only [getG_next]
  | vop op vex w dv s1 s2 =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun b => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | vshift k vex w dv src n =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | vshiftq vex w dv src n =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | vror w dv src n =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | vtern w dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | vload vex w dv src =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun v => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | vstore w m src =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun a => ?_)
    simp only [okOr_pure, getG_storeLanes, getG_next]
  | pshufd vex dv src imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | pshufb vex w dv src mask =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun r => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | palignr vex dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | pblendw dv src imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | shufps w dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | perm2f128 dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | inserti128 dv s1 m imm =>
    dsimp only
    refine okOr_bind2_getG s 4 _ _ _ (fun a x => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | inserti64x4 dv s1 m imm =>
    dsimp only
    refine okOr_bind2_getG s 4 _ _ _ (fun a x => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | permi2d dv s1 s2 =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun x => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | permi2q dv s1 s2 =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun x => ?_)
    simp only [okOr_pure, getG_setVec, getG_next]
  | sha256rnds2 dv src =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | sha256msg1 dv src =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | sha256msg2 dv src =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
  | mov w d src =>
    dsimp only
    obtain ⟨hw32, hd16, hd4⟩ : w = 32 ∧ d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 64
    · exact absurd (hw32.symm.trans hw) (by decide)
    · simp only [if_neg hw]
      cases hm : gData32 ro mem0 s src with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_next]
        rw [getG_setData32_ne s d 4 x (by omega)]
  | movst w m src =>
    dsimp only
    refine okOr_bind_getG s 4 _ _ (fun a => ?_)
    by_cases hw : w = 64
    · simp only [if_pos hw, okOr_pure, getG_storeVal, getG_next]
    · simp only [if_neg hw]
      cases hg : s.getG src with
      | num lo hi => simp only [hg, okOr_pure, getG_storeLane, getG_next]
      | ptr q => exact okOr_throw_getG s 4 _
  | alu op w d src =>
    dsimp only
    obtain ⟨hd16, hd4, hw, hsg⟩ : d < 16 ∧ d ≠ 4 ∧ (w = 32 ∨ (w = 64 ∧ op = LOp.add))
      ∧ gsRegSafe src := hn
    by_cases hw64 : w = 64
    · have hop : op = LOp.add := by
        rcases hw with h32 | ⟨h64, ha⟩
        · exact absurd (h32.symm.trans hw64) (by decide)
        · exact ha
      subst hop
      simp only [if_pos hw64]
      have hz : ¬ (LOp.add = LOp.xor ∧ src = .reg d) := fun h => absurd h.1 (by decide)
      simp only [if_neg hz]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]
        | ok b =>
          by_cases hc : b.region = rNum ∨ a.region = rNum
          · simp only [if_pos hc, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
            rw [getG_setG_ne' s d 4 _ (by omega)]
          · simp only [bind_ok_eq, if_neg hc]
            rw [okOr_throw_getG s 4]
    · simp only [if_neg hw64]
      by_cases hz : op = .xor ∧ src = .reg d
      · simp only [if_pos hz, okOr_pure, getG_clearFlags, getG_next]
        rw [getG_setData32_ne s d 4 (Lane.const 0) (by omega)]
      · simp only [if_neg hz]
        cases ha : gData32 ro mem0 s (.reg d) with
        | error e => simp only [bind_error_eq, okOr_error, getG_fail]
        | ok x =>
          cases hb : gData32 ro mem0 s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]
          | ok y =>
            simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
            rw [getG_setData32_ne s d 4 _ (by omega)]
  | sub w d src =>
    dsimp only
    obtain ⟨hd16, hd4, hs⟩ : d < 16 ∧ d ≠ 4 ∧ gsRegSafe src := hn
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]
        | ok b =>
          by_cases hc : b.region = rNum
          · simp only [if_pos hc, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
            rw [getG_setG_ne' s d 4 _ (by omega)]
          · simp only [bind_ok_eq, if_neg hc]
            rw [okOr_throw_getG s 4]
    · simp only [if_neg hw]
      rw [okOr_throw_getG s 4]
  | lea d m =>
    dsimp only
    obtain ⟨hd16, hd4, hb, hi, hr⟩ : d < 16 ∧ d ≠ 4 ∧ m.base = none ∧ m.index = none
      ∧ m.ro ≠ none := hn
    cases he : effAddr ro s m with
    | error e => simp only [bind_error_eq, okOr_error, getG_fail]
    | ok a =>
      simp only [bind_ok_eq, okOr_pure, getG_next]
      rw [getG_setG_ne' s d 4 _ (by omega)]
  | ror w d n =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 32
    · simp only [if_pos hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
        rw [getG_setData32_ne s d 4 _ (by omega)]
    · simp only [if_neg hw]
      rw [okOr_throw_getG s 4]
  | shld w d src n =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 32
    · simp only [if_pos hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        cases hb : gData32 ro mem0 s (.reg src) with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]
        | ok y =>
          simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
          rw [getG_setData32_ne s d 4 _ (by omega)]
    · simp only [if_neg hw]
      rw [okOr_throw_getG s 4]
  | shl w d n =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok a =>
        simp only [bind_ok_eq]
        by_cases hr : a.region = rNum
        · simp only [if_pos hr, okOr_pure, getG_clearFlags, getG_next]
          rw [getG_setG_ne' s d 4 _ (by omega)]
        · simp only [bind_ok_eq, if_neg hr]
          rw [okOr_throw_getG s 4]
    · simp only [if_neg hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
        rw [getG_setData32_ne s d 4 _ (by omega)]
  | bswap w d =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 32
    · simp only [if_pos hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_next]
        rw [getG_setData32_ne s d 4 _ (by omega)]
    · simp only [if_neg hw]
      rw [okOr_throw_getG s 4]
  | push r => exact hn.elim
  | pop r => exact hn.elim
  | cmp w a b =>
    dsimp only
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        cases hy : gCtl s b with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]
        | ok y =>
          by_cases hc : y.region = rNum ∨ y.region = x.region
          · simp only [if_pos hc, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
          · simp only [bind_ok_eq, if_neg hc]
            rw [okOr_throw_getG s 4]
    · simp only [if_neg hw]
      rw [okOr_throw_getG s 4]
  | test w a b =>
    dsimp only
    by_cases hc : w = 64 ∧ a = b
    · simp only [if_pos hc]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]
      | ok x =>
        by_cases hr : x.region = rNum
        · simp only [if_pos hr, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
        · simp only [bind_ok_eq, if_neg hr]
          rw [okOr_throw_getG s 4]
    · simp only [if_neg hc]
      rw [okOr_throw_getG s 4]
  | jcc c t =>
    dsimp only
    cases hf : s.flags with
    | none =>
      rw [okOr_throw_getG s 4]
    | some q =>
      obtain ⟨x, y⟩ := q
      dsimp only
      simp only [okOr_pure, getG_branch]
  | jmp t =>
    dsimp only
    rfl
  | jccTail c name => exact hn.elim
  | jmpTail name => exact hn.elim
  | ret => exact hn.elim


/-! ## `rsp` over a whole slice -/

section BodyLog
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

theorem run_rsp {prog : Array Instr} {base L : Nat}
    (hnsI : ∀ pc i, base ≤ pc → pc < base + L → prog[pc]? = some i → nsSafe i)
    (hL : base + L ≤ prog.size) :
    ∀ (n : Nat) (s : State W32 Int),
    (∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨
      (base ≤ (run prog ro mem0 orc k s).pc ∧
        (run prog ro mem0 orc k s).pc < base + L)) →
    (run prog ro mem0 orc n s).getG 4 = s.getG 4 := by
  intro n
  induction n with
  | zero =>
    intro s hcond
    rfl
  | succ n ih =>
    intro s hcond
    by_cases hh : s.halted = true
    · rw [run_halted prog ro mem0 orc (n + 1) s hh]
    · have hf : s.halted = false := by simpa using hh
      have h0c := hcond 0 (Nat.zero_lt_succ n)
      have hpc : base ≤ s.pc ∧ s.pc < base + L := by
        rcases h0c with h' | h'
        · exact absurd h' (by
            rw [show run prog ro mem0 orc 0 s = s from rfl]
            simp [hf])
        · exact h'
      have hlt : s.pc < prog.size := by omega
      have hx : prog[s.pc]? = some prog[s.pc] := Array.getElem?_eq_getElem hlt
      have step : ∀ m, run prog ro mem0 orc (m + 1) s
          = run prog ro mem0 orc m (exec ro mem0 orc prog[s.pc] s) := by
        intro m
        simp only [run, hf, Bool.false_eq_true, ite_false, hx]
      have hcond' : ∀ k', k' < n →
          (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).halted = true ∨
          (base ≤ (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).pc ∧
            (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).pc < base + L) := by
        intro k' hk'
        have h1 := hcond (k' + 1) (Nat.succ_lt_succ hk')
        rwa [step k'] at h1
      rw [step n]
      rw [ih (exec ro mem0 orc prog[s.pc] s) hcond']
      exact exec_rsp_ns prog[s.pc] s (hnsI s.pc prog[s.pc] hpc.1 hpc.2 hx)

/-! ## Kernel-checked scans of the linux body -/

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Shani.prog

/-- Every instruction of the linux `shani_x2` body preserves the "no stack pointer in a
register" invariant. -/
theorem shani_linux_ns : ((linuxProg.toList.drop 1).take 668).all nsSafeB = true := by
  decide +kernel

/-- Every instruction of the linux `shani_x2` body is write-safe for the windows save area: with
`rsp = (a - 248) + 160`, no store writes into `[a - 248, a - 88)`. -/
theorem shani_linux_ws : ((linuxProg.toList.drop 1).take 668).all (wSafeB 160) = true := by
  decide +kernel

theorem shani_hnsI : ∀ pc i, 1 ≤ pc → pc < 1 + 668 → linuxProg[pc]? = some i → nsSafe i := by
  intro pc i h1 h2 hp
  have hget : nsSafeB i = true :=
    all_slice_get linuxProg.toList 1 668 nsSafeB shani_linux_ns (pc - 1) (by omega) i (by
      rw [show 1 + (pc - 1) = pc from by omega]
      simpa using hp)
  exact (nsSafeB_iff i).mp hget

theorem shani_hwsI : ∀ pc i, 1 ≤ pc → pc < 1 + 668 → linuxProg[pc]? = some i → wSafe 160 i := by
  intro pc i h1 h2 hp
  have hget : wSafeB 160 i = true :=
    all_slice_get linuxProg.toList 1 668 (wSafeB 160) shani_linux_ws (pc - 1) (by omega) i (by
      rw [show 1 + (pc - 1) = pc from by omega]
      simpa using hp)
  exact (wSafeB_iff 160 i).mp hget

/-! ## The entry seed satisfies the invariants -/

theorem f_ne4 : ∀ j, j < 16 → j ≠ 4 → F j ≠ 4 := by
  apply Hashtree.Proofs.WinShani.all_fin
  decide

/-- The linux body-entry seed has no stack pointer in a non-`rsp` register, when the ABI entry
state has none. -/
theorem seed_ns (st : State W32 Int) (a : Addr Int)
    (hns0 : ∀ j, j ≠ 4 → NoStackVal (st.getG j)) :
    ∀ j, j ≠ 4 → NoStackVal ((seedSt st a).getG j) := by
  intro j hj
  by_cases hj16 : j < 16
  · rw [seedSt_getG st a j hj16]
    rw [ite_eq_right (by omega)]
    exact hns0 (F j) (f_ne4 j hj16 hj)
  · have hlen : (seedSt st a).gpr.length = 16 := seedSt_gpr_len st a
    have hg : (seedSt st a).getG j = Val.num (Lane.const 0) (Lane.const 0) := by
      simp only [State.getG, List.getD_eq_getElem?_getD]
      rw [show (seedSt st a).gpr[j]? = none from
        List.getElem?_eq_none (by rw [hlen]; omega)]
      rfl
    rw [hg]
    exact noStack_num _ _

/-- The linux body-entry seed has `rsp = a - 88 = (a - 248) + 160`. -/
theorem seed_rsp (st : State W32 Int) (a : Addr Int) :
    (seedSt st a).getG 4 = .ptr ((a.plusI (-248)).plusI 160) := by
  rw [seedSt_getG st a 4 (by omega)]
  rw [ite_eq_left (show (4 : Nat) = 4 from rfl)]
  rw [plusI_add]
  rw [show (-248 : Int) + 160 = -88 from by decide]

/-! ## The body-exit stack facts -/

/-- The linux body of `shani_x2` only prepends cells outside the windows save area to the prologue
save log, and leaves `rsp` at `a - 88`.  This is `hW`, `hmem` and `hrsp` of
`WinShaniCall.shani_call`. -/
theorem shani_body_log (hro : ro ≠ rStack) (st : State W32 Int) (a : Addr Int) (n : Nat)
    (hnst : ∀ j, j ≠ 4 → NoStackVal (st.getG j))
    (hr : a.region = rStack)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 1 + 668)) :
    ∃ W, Outside (a.plusI (-248)) 160 W ∧
      (run linuxProg ro mem0 orc n (seedSt st a)).mem
        = W ++ saveLog st (a.plusI (-248)) 10 st.mem := by
  have hL : 1 + 668 ≤ linuxProg.size := by
    have h := Hashtree.Proofs.WinShaniTransfer.hi_le
    omega
  have hlen : (seedSt st a).gpr.length = 16 := seedSt_gpr_len st a
  have hsp : ∀ k, k ≤ n →
      (run linuxProg ro mem0 orc k (seedSt st a)).getG 4
        = .ptr ((a.plusI (-248)).plusI 160) := by
    intro k hk
    rw [run_rsp (prog := linuxProg) (base := 1) (L := 668) shani_hnsI hL k (seedSt st a)
      (fun k' hk' => hcond k' (by omega))]
    exact seed_rsp st a
  have hns : ∀ k, k ≤ n → ∀ j, j ≠ 4 →
      NoStackVal ((run linuxProg ro mem0 orc k (seedSt st a)).getG j) :=
    run_ns (prog := linuxProg) (base := 1) (L := 668) hro shani_hnsI hL n (seedSt st a) hlen
      (seed_ns st a hnst) (fun k' hk' => hcond k' hk')
  obtain ⟨W, hW, hmem⟩ :=
    run_write_log (prog := linuxProg) (base := 1) (L := 668) 160 shani_hwsI hL n
      (seedSt st a) (a.plusI (-248)) hr hsp hns hcond
  exact ⟨W, hmem, hW⟩

/-- `WinShaniCall.shani_call` with the three stack facts discharged by `shani_body_log`: the only
remaining hypotheses are the entry ABI facts, the slice condition, and the body-exit
`pc`/halt/`ret` facts (which the flat model cannot compute). -/
theorem shani_call_mem (st : State W32 Int) (a : Addr Int) (n : Nat)
    (v : List W32) (x : Addr Int)
    (hlen : st.gpr.length = 16) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 669))
    (hpc : (run linuxProg ro mem0 orc n (seedSt st a)).pc = 669)
    (hnh : (run linuxProg ro mem0 orc n (seedSt st a)).halted = false)
    (hnst : ∀ j, j ≠ 4 → NoStackVal (st.getG j))
    (ha : a.region = rStack) (hro : ro ≠ rStack)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 (run linuxProg ro mem0 orc n (seedSt st a))
      ((a.plusI (-248)).plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    run winProg ro mem0 orc (11 + (n + 12)) { st with pc := 0 }
      = epiFinal (bodyExit (run linuxProg ro mem0 orc n (seedSt st a))) st (a.plusI (-248)) := by
  have hL : 1 + 668 ≤ linuxProg.size := by
    have h := Hashtree.Proofs.WinShaniTransfer.hi_le
    omega
  obtain ⟨W, hW, hmem⟩ := shani_body_log hro st a n hnst ha hcond
  have hrsp : (run linuxProg ro mem0 orc n (seedSt st a)).getG rsp = .ptr (a.plusI (-88)) := by
    rw [show rsp = 4 from rfl,
      run_rsp (prog := linuxProg) (base := 1) (L := 668) shani_hnsI hL n (seedSt st a) hcond,
      seed_rsp]
    rw [plusI_add]
    rw [show (-248 : Int) + 160 = -88 from by decide]
  exact shani_call st a n st.mem W v x hlen hh h4 hv hx hcond hpc hnh hrsp hW hmem hvlen hret

end BodyLog

end Hashtree.Proofs.WinShaniExit
