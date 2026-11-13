import Hashtree.Proofs.WinShaniCall
import Hashtree.Proofs.WinWrapperPre
import Hashtree.Proofs.ShaniAll
import Hashtree.Asm.X86SymW
import Hashtree.Asm.BodyReads
import Hashtree.Asm.RunAgree

/-!
# R5: the windows `shani_x2` seed versus the linux certificate start states

`WinShaniCall.seedSt` is the linux-named state from which the windows body run is proved to be
the translated linux body run (`shani_seed_eq`, `shani_body_transfer`).  To reuse a linux
functional certificate the run must start from exactly that seed, so the seed would have to be
`mapState env sigma entryS` (`ShaniAll.shani_correct`) or `mapState env sigma entryW`
(`ShaniW.correctW`).

This module records, machine-checked, the exact reason the first does not line up, and the
register table behind it.  At the windows kernel call state `entryWin` the linux register `3`
(`rbx`) of the seed holds the Win64 `rbp`, which the wrapper sets to a stack pointer
(`ptr (rStack, sigma 6)`), while `X86Sym.entryS` has `rbx` as an arbitrary number
(`num (.var (.n (gId 3 0))) (.var (.n (gId 3 1)))`).  `mapVal` preserves the constructor, so no
choice of the certificate symbols can make the two states equal.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinShaniSeedAlign

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinShaniCall (seedSt seedSt_getG)
open Hashtree.Proofs.WinShani (F)
open Hashtree.Proofs.WrapperAmd64 (getG_of)

/-! ## The general `mapState` register lemma -/

theorem mapState_getG {e : Key → W32} {σ : Nat → Int} {s : State E Lin} {i : Nat} {v : Val E Lin}
    (h : s.gpr[i]? = some v) :
    (mapState e σ s).getG i = mapVal e σ v := by
  apply getG_of
  simp only [mapState, List.getElem?_map, h, Option.map_some]

/-! ## The windows seed `rbx` -/

theorem entryWin_gpr5 : entryWin.gpr[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by
  decide +kernel

theorem seed_gpr3 (env : Key → W32) (σ : Nat → Int) (a : Addr Int) :
    (seedSt (mapState env σ entryWin) a).getG 3 = .ptr ⟨rStack, σ 6⟩ := by
  rw [seedSt_getG _ a 3 (by omega)]
  rw [ite_eq_right (show (3 : Nat) ≠ 4 from by decide)]
  show (mapState env σ entryWin).getG (F 3) = _
  rw [show F 3 = 5 from rfl]
  rw [mapState_getG entryWin_gpr5]
  simp only [mapVal, mapAddr, Lin.eval_sym]

/-! ## The start state of `ShaniAll`, register `rbx` -/

theorem entryS24_gpr3 : (entryS 24).gpr[3]? =
    some (.num (.var (.n (gId 3 0))) (.var (.n (gId 3 1)))) := by
  decide +kernel

theorem entryS_gpr3 (e : Key → W32) (σ' : Nat → Int) :
    (mapState e σ' (entryS 24)).getG 3 = .num (e (.n (gId 3 0))) (e (.n (gId 3 1))) := by
  rw [mapState_getG entryS24_gpr3]
  simp only [mapVal, E.eval]

/-- The windows seed is not the linux certificate start state for any choice of the
certificate symbols: `rbx` is a stack pointer in the seed and a number on the certificate
side. -/
theorem seed_ne_entryS (env : Key → W32) (σ : Nat → Int) (a : Addr Int)
    (e : Key → W32) (σ' : Nat → Int) :
    seedSt (mapState env σ entryWin) a ≠ mapState e σ' (entryS 24) := by
  intro h
  have h1 := congrArg (fun s => s.getG 3) h
  rw [seed_gpr3, entryS_gpr3] at h1
  cases h1

/-! ## The closer certificate `ShaniW.correctW`: `X86SymW.entryW`

`entryW` is the linux Go wrapper call state.  It has an arbitrary entry stack pointer, so it is
the closest certificate, but it still disagrees with the windows seed on the constructor of
several registers, independently of the symbol choice.  We record two of them. -/

section EntryW
open Hashtree.Asm.X86SymW

theorem entryW_gpr5 : entryW.gpr[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by
  decide +kernel

theorem entryW_gpr8 : entryW.gpr[8]? =
    some (.num (.var (.n (gId 8 0))) (.var (.n (gId 8 1)))) := by
  decide +kernel

/-- The seed `rbp` is a number (the Win64 caller data in `rdi`), not a stack pointer. -/
theorem seed_gpr5 (env : Key → W32) (σ : Nat → Int) (a : Addr Int) :
    (seedSt (mapState env σ entryWin) a).getG 5 =
      .num (env (.n (gId 7 0))) (env (.n (gId 7 1))) := by
  rw [seedSt_getG _ a 5 (by omega)]
  rw [ite_eq_right (show (5 : Nat) ≠ 4 from by decide)]
  show (mapState env σ entryWin).getG (F 5) = _
  rw [show F 5 = 7 from rfl]
  have h : entryWin.gpr[7]? = some (.num (.var (.n (gId 7 0))) (.var (.n (gId 7 1)))) := by
    decide +kernel
  rw [mapState_getG h]
  simp only [mapVal, E.eval]

/-- The seed `r8` is a stack pointer (the Win64 `rbx`), not a number. -/
theorem seed_gpr8 (env : Key → W32) (σ : Nat → Int) (a : Addr Int) :
    (seedSt (mapState env σ entryWin) a).getG 8 = .ptr ⟨rStack, σ 5⟩ := by
  rw [seedSt_getG _ a 8 (by omega)]
  rw [ite_eq_right (show (8 : Nat) ≠ 4 from by decide)]
  show (mapState env σ entryWin).getG (F 8) = _
  rw [show F 8 = 3 from rfl]
  have h : entryWin.gpr[3]? = some (.ptr ⟨rStack, Lin.sym 5⟩) := by
    decide +kernel
  rw [mapState_getG h]
  simp only [mapVal, mapAddr, Lin.eval_sym]

theorem entryW_getG5 (e : Key → W32) (σ' : Nat → Int) :
    (mapState e σ' entryW).getG 5 = .ptr ⟨rStack, σ' 6⟩ := by
  rw [mapState_getG entryW_gpr5]
  simp only [mapVal, mapAddr, Lin.eval_sym]

theorem entryW_getG8 (e : Key → W32) (σ' : Nat → Int) :
    (mapState e σ' entryW).getG 8 = .num (e (.n (gId 8 0))) (e (.n (gId 8 1))) := by
  rw [mapState_getG entryW_gpr8]
  simp only [mapVal, E.eval]

theorem seed_ne_entryW (env : Key → W32) (σ : Nat → Int) (a : Addr Int)
    (e : Key → W32) (σ' : Nat → Int) :
    seedSt (mapState env σ entryWin) a ≠ mapState e σ' entryW := by
  intro h
  have h1 := congrArg (fun s => s.getG 8) h
  rw [seed_gpr8, entryW_getG8] at h1
  cases h1

end EntryW


/-! ## The body read set: registers read before their first write

The invariance question is decided by which general registers the body reads *before* writing
them: those entry values are the only ones that can influence the run.  The scan below walks the
668-instruction shared body (linux pcs 1..668, windows pcs 11..678), treating an ALU/sub/ror/shld
destination as read (read-modify-write) and a memory operand base as a read, and drops any read
after the register was written. -/

section ReadSet
open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Asm.BodyReads

abbrev linuxBody : List Instr := (Hashtree.Kernels.X86.Shani.prog.toList.drop 1).take 668
abbrev winBody : List Instr := (Hashtree.Kernels.X86Win.Shani.prog.toList.drop 11).take 668

/-- The linux body reads before first write only `rdx` (count), `rsi` (input), `rsp` and `rdi`
(output). -/
theorem shani_body_rbw_linux : rbw linuxBody = [2, 6, 4, 7] := by decide +kernel

/-- The windows body is the same instruction stream under the register permutation `F`:
`r8` (count), `rdx` (input), `rsp`, `rcx` (output). -/
theorem shani_body_rbw_windows : rbw winBody = [8, 2, 4, 1] := by decide +kernel

end ReadSet

/-! ## The run-invariance certificates

`rbw` is the read set of the straight-line stream; the body loops (windows pc 445 `jmp 14`, 15
`jl 446`, 447 `je 679`), so the per-pc sets the engine of `Asm/RunAgree` consumes are the
live-variable fixpoints `linuxLive`/`winLive`, certified by `certB` (`decide +kernel`).  The entry
live sets are exactly the `rbw` tables above: linux pc 1 (after `sub rsp, 88`) reads
`[2, 6, 4, 7]`, windows pc 11 (after the prologue) reads `[8, 2, 4, 1]`. -/

section Live
open Hashtree.Asm.BodyReads Hashtree.Asm.RunAgree

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Shani.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

/-- Per-pc live register sets of the linux `shani_x2` program. -/
def linuxLive : List (List Nat) := live linuxProg
/-- Per-pc live register sets of the windows `shani_x2` program. -/
def winLive : List (List Nat) := live winProg
/-- Per-pc flags live-in bits. -/
def linuxLiveF : List Bool := liveF linuxProg
def winLiveF : List Bool := liveF winProg

theorem shani_linux_certB : certB linuxProg linuxLive linuxLiveF = true := by decide +kernel
theorem shani_windows_certB : certB winProg winLive winLiveF = true := by decide +kernel

/-- The certificate `run_agree` consumes for the linux program. -/
theorem shani_linux_cert : Cert linuxProg (fun p => linuxLive.getD p []) (fun p => linuxLiveF.getD p false) :=
  Cert_of_certB shani_linux_certB

/-- The certificate `run_agree` consumes for the windows program. -/
theorem shani_windows_cert : Cert winProg (fun p => winLive.getD p []) (fun p => winLiveF.getD p false) :=
  Cert_of_certB shani_windows_certB

/-- The flags are not live at the body entries (each body compares before it branches). -/
theorem shani_linux_liveF_entry : linuxLiveF.getD 1 false = false := by decide +kernel
theorem shani_windows_liveF_entry : winLiveF.getD 11 false = false := by decide +kernel

/-- Closure: the linux body entry live set (pc 1) is inside the read set `[2, 6, 4, 7]`. -/
theorem shani_linux_live_entry_eq : linuxLive.getD 1 [] = [2, 6, 4, 7] := by decide +kernel
theorem shani_windows_live_entry_eq : winLive.getD 11 [] = [8, 2, 4, 1] := by decide +kernel

theorem shani_linux_live_entry : ∀ r, r ∈ linuxLive.getD 1 [] → r ∈ [2, 6, 4, 7] := by
  rw [shani_linux_live_entry_eq]; exact fun _ h => h

/-- Closure: the windows body entry live set (pc 11) is inside the read set `[8, 2, 4, 1]`. -/
theorem shani_windows_live_entry : ∀ r, r ∈ winLive.getD 11 [] → r ∈ [8, 2, 4, 1] := by
  rw [shani_windows_live_entry_eq]; exact fun _ h => h

end Live

end Hashtree.Proofs.WinShaniSeedAlign
