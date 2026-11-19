import Hashtree.Proofs.WinAvx2X8WShift
import Hashtree.Gen.WinAvx2X8P.D2
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinAvx2X8W

/-!
# The windows avx2_x8 loop cuts for the second and later passes: the saved cells stripped

The windows `avx2_x8` prologue pushes `rbp` and `rsi` and saves `r12..r15` and `ymm6..15` into
its frame: 368 cells (`rbp` pointer bytes at `sAt (-8) ..`, the `rsi` data bytes at
`sAt (-16) ..`, the `r12..r15` pointer bytes at `sAt (-368 - r) ..`, the 320 `ymm` data bytes at
`sAt (-336 - r) ..`), so from the loop head `K3` on every pilot cut carries them at the (oldest)
end of its write log.  A loop invariant head must have an empty log, which the pass-1 cuts
cannot provide.  For the second and later passes the cuts are therefore stripped of those cells
(`strip368`, `stripK8 r`), and the cells move into the symbolic initial memory's push list
(`pushC r`, `m8P r := mem0qW 4 roC (pushC r)`): pointer bytes as in the linux `avx2_x8` loop
(`Avx2X8WStrip`), data bytes address-keyed as in the windows `avx_x4` loop (`WinAvxX4WStrip`).
At the concrete level they are in the log the first pass accumulated, and nothing later
overwrites them (every later write is an output cell or a frame cell below `sAt (-368 - r)`).
The body never reads them; the exit path (`KTEs r`) restores `ymm6..15`, `r12..r15` and pops
`rsi`, `rbp` from them, which the symbolic executor serves from the push list.

`KHs r` is the stripped invariant head (`K3` with all sixteen loop-carried `ymm` and the dead
`rsi` at the tail's table pointer), `KH4s r`/`KH5s r` the replayed cuts with the still-unloaded
`ymm7..15` / `ymm14, ymm15`, `KTs r` the turn's end and `KTEs r` the exit, all over `m8P r`.
-/

namespace Hashtree.Proofs.WinAvx2X8WStrip

/-! ## The saved cells as a push list -/

/-- The saved cells at residue `r` (generated). -/
def pushC (r : Nat) : List (Int × Cell E Lin) :=
  [((-8 + 0 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 0 : Cell E Lin)),
   ((-8 + 1 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 1 : Cell E Lin)),
   ((-8 + 2 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 2 : Cell E Lin)),
   ((-8 + 3 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 3 : Cell E Lin)),
   ((-8 + 4 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 4 : Cell E Lin)),
   ((-8 + 5 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 5 : Cell E Lin)),
   ((-8 + 6 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 6 : Cell E Lin)),
   ((-8 + 7 : Int), (.pb ⟨rStack, Lin.sym 6⟩ 7 : Cell E Lin)),
   ((-16 + 0 : Int), (.dat (.var (.m rStack (sAt (-16 + 0)))) 0 : Cell E Lin)),
   ((-16 + 1 : Int), (.dat (.var (.m rStack (sAt (-16 + 1)))) 1 : Cell E Lin)),
   ((-16 + 2 : Int), (.dat (.var (.m rStack (sAt (-16 + 2)))) 2 : Cell E Lin)),
   ((-16 + 3 : Int), (.dat (.var (.m rStack (sAt (-16 + 3)))) 3 : Cell E Lin)),
   ((-16 + 4 : Int), (.dat (.var (.m rStack (sAt (-16 + 4)))) 0 : Cell E Lin)),
   ((-16 + 5 : Int), (.dat (.var (.m rStack (sAt (-16 + 5)))) 1 : Cell E Lin)),
   ((-16 + 6 : Int), (.dat (.var (.m rStack (sAt (-16 + 6)))) 2 : Cell E Lin)),
   ((-16 + 7 : Int), (.dat (.var (.m rStack (sAt (-16 + 7)))) 3 : Cell E Lin)),
   ((-368 - (r : Int) + 0), (.pb ⟨rNum, Lin.sym 7⟩ 0 : Cell E Lin)),
   ((-368 - (r : Int) + 1), (.pb ⟨rNum, Lin.sym 7⟩ 1 : Cell E Lin)),
   ((-368 - (r : Int) + 2), (.pb ⟨rNum, Lin.sym 7⟩ 2 : Cell E Lin)),
   ((-368 - (r : Int) + 3), (.pb ⟨rNum, Lin.sym 7⟩ 3 : Cell E Lin)),
   ((-368 - (r : Int) + 4), (.pb ⟨rNum, Lin.sym 7⟩ 4 : Cell E Lin)),
   ((-368 - (r : Int) + 5), (.pb ⟨rNum, Lin.sym 7⟩ 5 : Cell E Lin)),
   ((-368 - (r : Int) + 6), (.pb ⟨rNum, Lin.sym 7⟩ 6 : Cell E Lin)),
   ((-368 - (r : Int) + 7), (.pb ⟨rNum, Lin.sym 7⟩ 7 : Cell E Lin)),
   ((-368 - (r : Int) + 8), (.pb ⟨rNum, Lin.sym 11⟩ 0 : Cell E Lin)),
   ((-368 - (r : Int) + 9), (.pb ⟨rNum, Lin.sym 11⟩ 1 : Cell E Lin)),
   ((-368 - (r : Int) + 10), (.pb ⟨rNum, Lin.sym 11⟩ 2 : Cell E Lin)),
   ((-368 - (r : Int) + 11), (.pb ⟨rNum, Lin.sym 11⟩ 3 : Cell E Lin)),
   ((-368 - (r : Int) + 12), (.pb ⟨rNum, Lin.sym 11⟩ 4 : Cell E Lin)),
   ((-368 - (r : Int) + 13), (.pb ⟨rNum, Lin.sym 11⟩ 5 : Cell E Lin)),
   ((-368 - (r : Int) + 14), (.pb ⟨rNum, Lin.sym 11⟩ 6 : Cell E Lin)),
   ((-368 - (r : Int) + 15), (.pb ⟨rNum, Lin.sym 11⟩ 7 : Cell E Lin)),
   ((-368 - (r : Int) + 16), (.pb ⟨rG, Lin.sym 8⟩ 0 : Cell E Lin)),
   ((-368 - (r : Int) + 17), (.pb ⟨rG, Lin.sym 8⟩ 1 : Cell E Lin)),
   ((-368 - (r : Int) + 18), (.pb ⟨rG, Lin.sym 8⟩ 2 : Cell E Lin)),
   ((-368 - (r : Int) + 19), (.pb ⟨rG, Lin.sym 8⟩ 3 : Cell E Lin)),
   ((-368 - (r : Int) + 20), (.pb ⟨rG, Lin.sym 8⟩ 4 : Cell E Lin)),
   ((-368 - (r : Int) + 21), (.pb ⟨rG, Lin.sym 8⟩ 5 : Cell E Lin)),
   ((-368 - (r : Int) + 22), (.pb ⟨rG, Lin.sym 8⟩ 6 : Cell E Lin)),
   ((-368 - (r : Int) + 23), (.pb ⟨rG, Lin.sym 8⟩ 7 : Cell E Lin)),
   ((-368 - (r : Int) + 24), (.pb ⟨rNum, Lin.sym 12⟩ 0 : Cell E Lin)),
   ((-368 - (r : Int) + 25), (.pb ⟨rNum, Lin.sym 12⟩ 1 : Cell E Lin)),
   ((-368 - (r : Int) + 26), (.pb ⟨rNum, Lin.sym 12⟩ 2 : Cell E Lin)),
   ((-368 - (r : Int) + 27), (.pb ⟨rNum, Lin.sym 12⟩ 3 : Cell E Lin)),
   ((-368 - (r : Int) + 28), (.pb ⟨rNum, Lin.sym 12⟩ 4 : Cell E Lin)),
   ((-368 - (r : Int) + 29), (.pb ⟨rNum, Lin.sym 12⟩ 5 : Cell E Lin)),
   ((-368 - (r : Int) + 30), (.pb ⟨rNum, Lin.sym 12⟩ 6 : Cell E Lin)),
   ((-368 - (r : Int) + 31), (.pb ⟨rNum, Lin.sym 12⟩ 7 : Cell E Lin)),
   ((-336 - (r : Int) + 0), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 0)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 1), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 1)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 2), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 2)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 3), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 3)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 4), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 4)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 5), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 5)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 6), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 6)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 7), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 7)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 8), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 8)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 9), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 9)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 10), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 10)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 11), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 11)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 12), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 12)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 13), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 13)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 14), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 14)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 15), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 15)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 16), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 16)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 17), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 17)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 18), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 18)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 19), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 19)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 20), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 20)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 21), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 21)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 22), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 22)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 23), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 23)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 24), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 24)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 25), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 25)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 26), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 26)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 27), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 27)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 28), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 28)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 29), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 29)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 30), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 30)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 31), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 31)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 32), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 32)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 33), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 33)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 34), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 34)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 35), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 35)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 36), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 36)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 37), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 37)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 38), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 38)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 39), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 39)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 40), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 40)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 41), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 41)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 42), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 42)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 43), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 43)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 44), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 44)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 45), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 45)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 46), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 46)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 47), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 47)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 48), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 48)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 49), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 49)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 50), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 50)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 51), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 51)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 52), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 52)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 53), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 53)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 54), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 54)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 55), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 55)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 56), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 56)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 57), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 57)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 58), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 58)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 59), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 59)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 60), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 60)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 61), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 61)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 62), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 62)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 63), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 63)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 64), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 64)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 65), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 65)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 66), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 66)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 67), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 67)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 68), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 68)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 69), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 69)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 70), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 70)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 71), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 71)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 72), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 72)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 73), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 73)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 74), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 74)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 75), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 75)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 76), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 76)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 77), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 77)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 78), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 78)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 79), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 79)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 80), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 80)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 81), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 81)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 82), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 82)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 83), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 83)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 84), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 84)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 85), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 85)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 86), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 86)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 87), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 87)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 88), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 88)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 89), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 89)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 90), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 90)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 91), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 91)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 92), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 92)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 93), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 93)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 94), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 94)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 95), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 95)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 96), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 96)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 97), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 97)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 98), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 98)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 99), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 99)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 100), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 100)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 101), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 101)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 102), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 102)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 103), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 103)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 104), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 104)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 105), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 105)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 106), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 106)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 107), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 107)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 108), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 108)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 109), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 109)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 110), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 110)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 111), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 111)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 112), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 112)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 113), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 113)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 114), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 114)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 115), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 115)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 116), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 116)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 117), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 117)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 118), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 118)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 119), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 119)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 120), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 120)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 121), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 121)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 122), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 122)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 123), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 123)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 124), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 124)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 125), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 125)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 126), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 126)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 127), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 127)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 128), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 128)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 129), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 129)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 130), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 130)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 131), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 131)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 132), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 132)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 133), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 133)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 134), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 134)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 135), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 135)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 136), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 136)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 137), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 137)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 138), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 138)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 139), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 139)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 140), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 140)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 141), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 141)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 142), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 142)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 143), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 143)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 144), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 144)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 145), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 145)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 146), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 146)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 147), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 147)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 148), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 148)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 149), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 149)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 150), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 150)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 151), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 151)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 152), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 152)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 153), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 153)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 154), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 154)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 155), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 155)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 156), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 156)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 157), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 157)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 158), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 158)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 159), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 159)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 160), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 160)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 161), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 161)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 162), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 162)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 163), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 163)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 164), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 164)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 165), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 165)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 166), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 166)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 167), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 167)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 168), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 168)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 169), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 169)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 170), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 170)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 171), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 171)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 172), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 172)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 173), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 173)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 174), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 174)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 175), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 175)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 176), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 176)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 177), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 177)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 178), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 178)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 179), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 179)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 180), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 180)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 181), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 181)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 182), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 182)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 183), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 183)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 184), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 184)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 185), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 185)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 186), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 186)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 187), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 187)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 188), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 188)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 189), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 189)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 190), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 190)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 191), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 191)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 192), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 192)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 193), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 193)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 194), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 194)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 195), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 195)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 196), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 196)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 197), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 197)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 198), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 198)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 199), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 199)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 200), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 200)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 201), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 201)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 202), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 202)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 203), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 203)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 204), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 204)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 205), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 205)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 206), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 206)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 207), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 207)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 208), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 208)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 209), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 209)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 210), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 210)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 211), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 211)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 212), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 212)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 213), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 213)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 214), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 214)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 215), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 215)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 216), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 216)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 217), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 217)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 218), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 218)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 219), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 219)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 220), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 220)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 221), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 221)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 222), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 222)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 223), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 223)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 224), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 224)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 225), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 225)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 226), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 226)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 227), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 227)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 228), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 228)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 229), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 229)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 230), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 230)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 231), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 231)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 232), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 232)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 233), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 233)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 234), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 234)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 235), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 235)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 236), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 236)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 237), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 237)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 238), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 238)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 239), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 239)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 240), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 240)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 241), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 241)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 242), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 242)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 243), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 243)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 244), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 244)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 245), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 245)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 246), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 246)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 247), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 247)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 248), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 248)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 249), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 249)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 250), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 250)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 251), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 251)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 252), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 252)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 253), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 253)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 254), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 254)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 255), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 255)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 256), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 256)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 257), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 257)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 258), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 258)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 259), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 259)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 260), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 260)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 261), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 261)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 262), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 262)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 263), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 263)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 264), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 264)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 265), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 265)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 266), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 266)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 267), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 267)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 268), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 268)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 269), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 269)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 270), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 270)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 271), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 271)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 272), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 272)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 273), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 273)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 274), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 274)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 275), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 275)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 276), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 276)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 277), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 277)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 278), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 278)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 279), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 279)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 280), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 280)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 281), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 281)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 282), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 282)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 283), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 283)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 284), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 284)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 285), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 285)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 286), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 286)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 287), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 287)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 288), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 288)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 289), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 289)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 290), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 290)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 291), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 291)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 292), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 292)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 293), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 293)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 294), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 294)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 295), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 295)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 296), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 296)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 297), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 297)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 298), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 298)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 299), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 299)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 300), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 300)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 301), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 301)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 302), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 302)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 303), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 303)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 304), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 304)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 305), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 305)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 306), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 306)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 307), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 307)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 308), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 308)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 309), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 309)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 310), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 310)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 311), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 311)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 312), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 312)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 313), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 313)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 314), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 314)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 315), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 315)))) 3 : Cell E Lin)),
   ((-336 - (r : Int) + 316), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 316)))) 0 : Cell E Lin)),
   ((-336 - (r : Int) + 317), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 317)))) 1 : Cell E Lin)),
   ((-336 - (r : Int) + 318), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 318)))) 2 : Cell E Lin)),
   ((-336 - (r : Int) + 319), (.dat (.var (.m rStack (sAt (-336 - (r : Int) + 319)))) 3 : Cell E Lin))]

/-- The symbolic memory of a later pass: the table, the marker, and the saved cells. -/
def m8P (r : Nat) : Addr Lin → Cell E Lin := mem0qW 4 roC (pushC r)

theorem m8P_eq (r : Nat) : m8P r = mem0sW 4 rodata (pushC r) :=
  mem0qW_eq 4 rodata (pushC r) roC 70 roC_eq (by decide +kernel)

/-- `lookup a log` yields exactly the cell `c` (a decidable form of the symbolic lookup). -/
def lookupIs (a : Addr Lin) (log : List (Addr Lin × Cell E Lin)) (c : Cell E Lin) : Bool :=
  match lookup a log with
  | .ok (some c') => decide (c' = c)
  | _ => false

theorem lookupIs_eq {a : Addr Lin} {log : List (Addr Lin × Cell E Lin)} {c : Cell E Lin}
    (h : lookupIs a log c = true) : lookup a log = .ok (some c) := by
  unfold lookupIs at h
  split at h
  · rename_i c' heq
    rw [heq, of_decide_eq_true h]
  · cases h

/-- `lookup a log` yields a data byte with index `j`. -/
def lookupDat (a : Addr Lin) (log : List (Addr Lin × Cell E Lin)) (j : Nat) : Bool :=
  match lookup a log with
  | .ok (some (.dat _ j')) => j' == j
  | _ => false

theorem lookupDat_eq {a : Addr Lin} {log : List (Addr Lin × Cell E Lin)} {j : Nat}
    (h : lookupDat a log j = true) : ∃ x, lookup a log = .ok (some (.dat x j)) := by
  unfold lookupDat at h
  split at h
  · rename_i x j' heq
    exact ⟨x, by rw [heq, beq_iff_eq.mp h]⟩
  · cases h

/-- A saved cell is in a log: a pointer byte exactly, a data byte by its index. -/
def savedIn (log : List (Addr Lin × Cell E Lin)) (p : Int × Cell E Lin) : Bool :=
  match p.2 with
  | .pb _ _ => lookupIs (⟨rStack, sAt p.1⟩ : Addr Lin) log p.2
  | .dat _ j => lookupDat (⟨rStack, sAt p.1⟩ : Addr Lin) log j

/-! ## The stripped cuts -/

/-- Drop the 368 oldest log entries (the saved cells). -/
def strip368 (K : State E Lin) : State E Lin := { K with mem := K.mem.take (K.mem.length - 368) }

/-- A pilot cut rebased at residue `r` and stripped of the saved cells. -/
def stripK8 (r : Nat) (K : State E Lin) : State E Lin := strip368 (shiftK8 r K)

/-- The turn's end of a later pass (the 24-instruction loop tail from the stripped `K211`). -/
def KTs (r : Nat) : State E Lin := abstract (run prog 4 (m8P r) orcB 24 (stripK8 r K211))

/-- Overwrite the vector registers in `rs` with the values a turn leaves in them. -/
def vfixAtS (r : Nat) (rs : List Nat) (vr : List (List E)) : List (List E) :=
  rs.foldl (fun vr i => vr.set i ((KTs r).vr.getD i [])) vr

def wfixSS (r : Nat) (rs : List Nat) (s : State E Lin) : State E Lin :=
  { s with vr := vfixAtS r rs s.vr }

/-- The stripped loop invariant head: `K3` with the sixteen loop-carried `ymm`, the dead `rsi`
on the table (`lea rsi` at pc 25 overwrites it), empty log. -/
def KHs (r : Nat) : State E Lin :=
  wfixSS r [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    { stripK8 r K3 with gpr := (stripK8 r K3).gpr.set 6 (.ptr ⟨4, ⟨2048, []⟩⟩) }

/-- The second replayed cut: `K4` with the still-unloaded `ymm7..15`. -/
def KH4s (r : Nat) : State E Lin := wfixSS r [7, 8, 9, 10, 11, 12, 13, 14, 15] (stripK8 r K4)

/-- The third replayed cut: `K5` with the still-unloaded `ymm14, ymm15`. -/
def KH5s (r : Nat) : State E Lin := wfixSS r [14, 15] (stripK8 r K5)

/-- The exit of a later pass: the tail with `jb` taken, the restores (served from the push
list), `mov rsp,rbp; pop rsi; pop rbp; jmp avx_x4`. -/
def KTEs (r : Nat) : State E Lin := abstract (run prog 4 (m8P r) orcEx 42 (stripK8 r K211))

theorem pushKeyed_8 : pushKeyed (pushC 8) = true := by decide +kernel
theorem pushKeyed_24 : pushKeyed (pushC 24) = true := by decide +kernel

theorem m8P_keyed_8 : MemKeyed (m8P 8) :=
  mem0qW_keyed 4 rodata (pushC 8) roC 70 roC_eq (by decide +kernel) pushKeyed_8
theorem m8P_keyed_24 : MemKeyed (m8P 24) :=
  mem0qW_keyed 4 rodata (pushC 24) roC 70 roC_eq (by decide +kernel) pushKeyed_24

/-! ## The kernel checks at the two ABI residues

All facts about the cuts of one residue are one boolean, so that the kernel evaluates the
turn's end `KTs r` and the exit `KTEs r` once per residue; the named facts are read off it. -/

def stripOk (r : Nat) : Bool :=
  decide ((stripK8 r K3).mem = []) &&
  sliceCheck prog 4 (m8P r) orcB 8 (KHs r) (KH4s r) T3 &&
  sliceCheck prog 4 (m8P r) orcB 8 (KH4s r) (KH5s r) T4 &&
  sliceCheck prog 4 (m8P r) orcB 8 (KH5s r) (stripK8 r K6) T5 &&
  sliceCheck prog 4 (m8P r) orcB 24 (stripK8 r K211) (KTs r) [] &&
  sliceCheck prog 4 (m8P r) orcEx 42 (stripK8 r K211) (KTEs r) [] &&
  decide (({ KTs r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8) &&
  decide ((KTs r).pc = 25) && decide ((KTs r).assume = AT) && (KTs r).mem.all logOkBW &&
  (KHs r).nOnly &&
  decide ((KTEs r).tail = some "hashtree_sha256_avx_x4") && decide ((KTEs r).err = none) &&
  decide ((KTEs r).halted = true) && decide ((KTEs r).pc = 6103) &&
  decide ((KTEs r).assume = AX) && (KTEs r).mem.all logOkBW && decide ((KTEs r).gpr = exitGprW) &&
  -- the first pass: its end is the stripped head too, and its log holds the saved cells
  decide (({ KT r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8) &&
  (pushC r).all (savedIn (KT r).mem) &&
  -- a later pass never writes a saved cell
  (KTs r).mem.all (fun p => decide (p.1.region ≠ rStack ∨ p.1.off.k < -368 - (r : Int)))

/-- The facts of one residue, as a conjunction. -/
theorem stripFacts (r : Nat) (h : stripOk r = true) :
    (stripK8 r K3).mem = [] ∧
    sliceCheck prog 4 (m8P r) orcB 8 (KHs r) (KH4s r) T3 = true ∧
    sliceCheck prog 4 (m8P r) orcB 8 (KH4s r) (KH5s r) T4 = true ∧
    sliceCheck prog 4 (m8P r) orcB 8 (KH5s r) (stripK8 r K6) T5 = true ∧
    sliceCheck prog 4 (m8P r) orcB 24 (stripK8 r K211) (KTs r) [] = true ∧
    sliceCheck prog 4 (m8P r) orcEx 42 (stripK8 r K211) (KTEs r) [] = true ∧
    ({ KTs r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8 ∧
    (KTs r).pc = 25 ∧ (KTs r).assume = AT ∧ (KTs r).mem.all logOkBW = true ∧
    (KHs r).nOnly = true ∧
    (KTEs r).tail = some "hashtree_sha256_avx_x4" ∧ (KTEs r).err = none ∧
    (KTEs r).halted = true ∧ (KTEs r).pc = 6103 ∧ (KTEs r).assume = AX ∧
    (KTEs r).mem.all logOkBW = true ∧ (KTEs r).gpr = exitGprW ∧
    ({ KT r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8 ∧
    (pushC r).all (savedIn (KT r).mem) = true ∧
    (KTs r).mem.all (fun p => decide (p.1.region ≠ rStack ∨ p.1.off.k < -368 - (r : Int))) = true := by
  simp only [stripOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩

end Hashtree.Proofs.WinAvx2X8WStrip
