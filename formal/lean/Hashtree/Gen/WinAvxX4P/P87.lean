import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D87
import Hashtree.Gen.WinAvxX4P.D86

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice87 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 25 K87 K88 T87 = true := by
  decide +kernel

theorem core87_327 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1227) = V (.W 3 0 35))
    (h1 : env (.n 1226) = V (.W 3 0 35))
    (h2 : env (.n 1225) = V (.W 3 0 35))
    (h3 : env (.n 1224) = V (.W 3 0 35))
    (h4 : env (.n 1243) = V (.W 3 0 34))
    (h5 : env (.n 1242) = V (.W 3 0 34))
    (h6 : env (.n 1241) = V (.W 3 0 34))
    (h7 : env (.n 1240) = V (.W 3 0 34))
    (h8 : env (.n 1019) = V (.W 3 0 48))
    (h9 : env (.n 1018) = V (.W 3 0 48))
    (h10 : env (.n 1017) = V (.W 3 0 48))
    (h11 : env (.n 1016) = V (.W 3 0 48))
    (h12 : env (.n 1099) = V (.W 3 0 43))
    (h13 : env (.n 1098) = V (.W 3 0 43))
    (h14 : env (.n 1097) = V (.W 3 0 43))
    (h15 : env (.n 1096) = V (.W 3 0 43))
    (h16 : V (.W 3 0 50) = sigma1 (V (.W 3 0 48)) + V (.M2 3 0 34))
    (h17 : V (.M2 3 0 34) = V (.M1 3 0 34) + V (.W 3 0 43))
    (h18 : V (.M1 3 0 34) = V (.W 3 0 34) + sigma0 (V (.W 3 0 35))) :
    E.eval env (.add (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24)))) 7) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24)))) 25)) (.shr (.or (.or (.and (.shr (.var (.n 1227)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1226)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1225)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1224)) 24) (.const 255)) 24))) 3)) (.or (.or (.and (.shr (.var (.n 1243)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1242)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1241)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1240)) 24) (.const 255)) 24)))) (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 17) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 15)) (.shr (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24))) 10)) (.or (.or (.and (.shr (.var (.n 1099)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1098)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1097)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1096)) 24) (.const 255)) 24))))) = V (.W 3 0 50) :=
  shape33 (env (.n 1227)) (env (.n 1226)) (env (.n 1225)) (env (.n 1224)) (env (.n 1243)) (env (.n 1242)) (env (.n 1241)) (env (.n 1240)) (env (.n 1019)) (env (.n 1018)) (env (.n 1017)) (env (.n 1016)) (env (.n 1099)) (env (.n 1098)) (env (.n 1097)) (env (.n 1096)) (V (.W 3 0 35)) (V (.W 3 0 34)) (V (.W 3 0 48)) (V (.W 3 0 43)) (V (.W 3 0 50)) (V (.M2 3 0 34)) (V (.M1 3 0 34)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

theorem core87_326 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1231) = V (.W 2 0 35))
    (h1 : env (.n 1230) = V (.W 2 0 35))
    (h2 : env (.n 1229) = V (.W 2 0 35))
    (h3 : env (.n 1228) = V (.W 2 0 35))
    (h4 : env (.n 1247) = V (.W 2 0 34))
    (h5 : env (.n 1246) = V (.W 2 0 34))
    (h6 : env (.n 1245) = V (.W 2 0 34))
    (h7 : env (.n 1244) = V (.W 2 0 34))
    (h8 : env (.n 1023) = V (.W 2 0 48))
    (h9 : env (.n 1022) = V (.W 2 0 48))
    (h10 : env (.n 1021) = V (.W 2 0 48))
    (h11 : env (.n 1020) = V (.W 2 0 48))
    (h12 : env (.n 1103) = V (.W 2 0 43))
    (h13 : env (.n 1102) = V (.W 2 0 43))
    (h14 : env (.n 1101) = V (.W 2 0 43))
    (h15 : env (.n 1100) = V (.W 2 0 43))
    (h16 : V (.W 2 0 50) = sigma1 (V (.W 2 0 48)) + V (.M2 2 0 34))
    (h17 : V (.M2 2 0 34) = V (.M1 2 0 34) + V (.W 2 0 43))
    (h18 : V (.M1 2 0 34) = V (.W 2 0 34) + sigma0 (V (.W 2 0 35))) :
    E.eval env (.add (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24)))) 7) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24)))) 25)) (.shr (.or (.or (.and (.shr (.var (.n 1231)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1230)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1229)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1228)) 24) (.const 255)) 24))) 3)) (.or (.or (.and (.shr (.var (.n 1247)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1246)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1245)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1244)) 24) (.const 255)) 24)))) (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 17) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 15)) (.shr (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24))) 10)) (.or (.or (.and (.shr (.var (.n 1103)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1102)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1101)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1100)) 24) (.const 255)) 24))))) = V (.W 2 0 50) :=
  shape33 (env (.n 1231)) (env (.n 1230)) (env (.n 1229)) (env (.n 1228)) (env (.n 1247)) (env (.n 1246)) (env (.n 1245)) (env (.n 1244)) (env (.n 1023)) (env (.n 1022)) (env (.n 1021)) (env (.n 1020)) (env (.n 1103)) (env (.n 1102)) (env (.n 1101)) (env (.n 1100)) (V (.W 2 0 35)) (V (.W 2 0 34)) (V (.W 2 0 48)) (V (.W 2 0 43)) (V (.W 2 0 50)) (V (.M2 2 0 34)) (V (.M1 2 0 34)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

theorem core87_325 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1235) = V (.W 1 0 35))
    (h1 : env (.n 1234) = V (.W 1 0 35))
    (h2 : env (.n 1233) = V (.W 1 0 35))
    (h3 : env (.n 1232) = V (.W 1 0 35))
    (h4 : env (.n 1251) = V (.W 1 0 34))
    (h5 : env (.n 1250) = V (.W 1 0 34))
    (h6 : env (.n 1249) = V (.W 1 0 34))
    (h7 : env (.n 1248) = V (.W 1 0 34))
    (h8 : env (.n 1027) = V (.W 1 0 48))
    (h9 : env (.n 1026) = V (.W 1 0 48))
    (h10 : env (.n 1025) = V (.W 1 0 48))
    (h11 : env (.n 1024) = V (.W 1 0 48))
    (h12 : env (.n 1107) = V (.W 1 0 43))
    (h13 : env (.n 1106) = V (.W 1 0 43))
    (h14 : env (.n 1105) = V (.W 1 0 43))
    (h15 : env (.n 1104) = V (.W 1 0 43))
    (h16 : V (.W 1 0 50) = sigma1 (V (.W 1 0 48)) + V (.M2 1 0 34))
    (h17 : V (.M2 1 0 34) = V (.M1 1 0 34) + V (.W 1 0 43))
    (h18 : V (.M1 1 0 34) = V (.W 1 0 34) + sigma0 (V (.W 1 0 35))) :
    E.eval env (.add (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24)))) 7) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24)))) 25)) (.shr (.or (.or (.and (.shr (.var (.n 1235)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1234)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1233)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1232)) 24) (.const 255)) 24))) 3)) (.or (.or (.and (.shr (.var (.n 1251)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1250)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1249)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1248)) 24) (.const 255)) 24)))) (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 17) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 15)) (.shr (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24))) 10)) (.or (.or (.and (.shr (.var (.n 1107)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1106)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1105)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1104)) 24) (.const 255)) 24))))) = V (.W 1 0 50) :=
  shape33 (env (.n 1235)) (env (.n 1234)) (env (.n 1233)) (env (.n 1232)) (env (.n 1251)) (env (.n 1250)) (env (.n 1249)) (env (.n 1248)) (env (.n 1027)) (env (.n 1026)) (env (.n 1025)) (env (.n 1024)) (env (.n 1107)) (env (.n 1106)) (env (.n 1105)) (env (.n 1104)) (V (.W 1 0 35)) (V (.W 1 0 34)) (V (.W 1 0 48)) (V (.W 1 0 43)) (V (.W 1 0 50)) (V (.M2 1 0 34)) (V (.M1 1 0 34)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

theorem core87_324 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (h0 : env (.n 1239) = V (.W 0 0 35))
    (h1 : env (.n 1238) = V (.W 0 0 35))
    (h2 : env (.n 1237) = V (.W 0 0 35))
    (h3 : env (.n 1236) = V (.W 0 0 35))
    (h4 : env (.n 1255) = V (.W 0 0 34))
    (h5 : env (.n 1254) = V (.W 0 0 34))
    (h6 : env (.n 1253) = V (.W 0 0 34))
    (h7 : env (.n 1252) = V (.W 0 0 34))
    (h8 : env (.n 1031) = V (.W 0 0 48))
    (h9 : env (.n 1030) = V (.W 0 0 48))
    (h10 : env (.n 1029) = V (.W 0 0 48))
    (h11 : env (.n 1028) = V (.W 0 0 48))
    (h12 : env (.n 1111) = V (.W 0 0 43))
    (h13 : env (.n 1110) = V (.W 0 0 43))
    (h14 : env (.n 1109) = V (.W 0 0 43))
    (h15 : env (.n 1108) = V (.W 0 0 43))
    (h16 : V (.W 0 0 50) = sigma1 (V (.W 0 0 48)) + V (.M2 0 0 34))
    (h17 : V (.M2 0 0 34) = V (.M1 0 0 34) + V (.W 0 0 43))
    (h18 : V (.M1 0 0 34) = V (.W 0 0 34) + sigma0 (V (.W 0 0 35))) :
    E.eval env (.add (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24)))) 7) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24))) 11) (.shl (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24))) 21)) (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24)))) 25)) (.shr (.or (.or (.and (.shr (.var (.n 1239)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1238)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1237)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1236)) 24) (.const 255)) 24))) 3)) (.or (.or (.and (.shr (.var (.n 1255)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1254)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1253)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1252)) 24) (.const 255)) 24)))) (.add (.xor (.or (.shr (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 17) (.shl (.xor (.or (.shr (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24))) 2) (.shl (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24))) 30)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 15)) (.shr (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24))) 10)) (.or (.or (.and (.shr (.var (.n 1111)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1110)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1109)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1108)) 24) (.const 255)) 24))))) = V (.W 0 0 50) :=
  shape33 (env (.n 1239)) (env (.n 1238)) (env (.n 1237)) (env (.n 1236)) (env (.n 1255)) (env (.n 1254)) (env (.n 1253)) (env (.n 1252)) (env (.n 1031)) (env (.n 1030)) (env (.n 1029)) (env (.n 1028)) (env (.n 1111)) (env (.n 1110)) (env (.n 1109)) (env (.n 1108)) (V (.W 0 0 35)) (V (.W 0 0 34)) (V (.W 0 0 48)) (V (.W 0 0 43)) (V (.W 0 0 50)) (V (.M2 0 0 34)) (V (.M1 0 0 34)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

theorem step87 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L87) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 25 K87)) L88 := by
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
  have h160 := hI.1; have hI := hI.2
  have h161 := hI.1; have hI := hI.2
  have h162 := hI.1; have hI := hI.2
  have h163 := hI.1; have hI := hI.2
  have h164 := hI.1; have hI := hI.2
  have h165 := hI.1; have hI := hI.2
  have h166 := hI.1; have hI := hI.2
  have h167 := hI.1; have hI := hI.2
  have h168 := hI.1; have hI := hI.2
  have h169 := hI.1; have hI := hI.2
  have h170 := hI.1; have hI := hI.2
  have h171 := hI.1; have hI := hI.2
  have h172 := hI.1; have hI := hI.2
  have h173 := hI.1; have hI := hI.2
  have h174 := hI.1; have hI := hI.2
  have h175 := hI.1; have hI := hI.2
  have h176 := hI.1; have hI := hI.2
  have h177 := hI.1; have hI := hI.2
  have h178 := hI.1; have hI := hI.2
  have h179 := hI.1; have hI := hI.2
  have h180 := hI.1; have hI := hI.2
  have h181 := hI.1; have hI := hI.2
  have h182 := hI.1; have hI := hI.2
  have h183 := hI.1; have hI := hI.2
  have h184 := hI.1; have hI := hI.2
  have h185 := hI.1; have hI := hI.2
  have h186 := hI.1; have hI := hI.2
  have h187 := hI.1; have hI := hI.2
  have h188 := hI.1; have hI := hI.2
  have h189 := hI.1; have hI := hI.2
  have h190 := hI.1; have hI := hI.2
  have h191 := hI.1; have hI := hI.2
  have h192 := hI.1; have hI := hI.2
  have h193 := hI.1; have hI := hI.2
  have h194 := hI.1; have hI := hI.2
  have h195 := hI.1; have hI := hI.2
  have h196 := hI.1; have hI := hI.2
  have h197 := hI.1; have hI := hI.2
  have h198 := hI.1; have hI := hI.2
  have h199 := hI.1; have hI := hI.2
  have h200 := hI.1; have hI := hI.2
  have h201 := hI.1; have hI := hI.2
  have h202 := hI.1; have hI := hI.2
  have h203 := hI.1; have hI := hI.2
  have h204 := hI.1; have hI := hI.2
  have h205 := hI.1; have hI := hI.2
  have h206 := hI.1; have hI := hI.2
  have h207 := hI.1; have hI := hI.2
  have h208 := hI.1; have hI := hI.2
  have h209 := hI.1; have hI := hI.2
  have h210 := hI.1; have hI := hI.2
  have h211 := hI.1; have hI := hI.2
  have h212 := hI.1; have hI := hI.2
  have h213 := hI.1; have hI := hI.2
  have h214 := hI.1; have hI := hI.2
  have h215 := hI.1; have hI := hI.2
  have h216 := hI.1; have hI := hI.2
  have h217 := hI.1; have hI := hI.2
  have h218 := hI.1; have hI := hI.2
  have h219 := hI.1; have hI := hI.2
  have h220 := hI.1; have hI := hI.2
  have h221 := hI.1; have hI := hI.2
  have h222 := hI.1; have hI := hI.2
  have h223 := hI.1; have hI := hI.2
  have h224 := hI.1; have hI := hI.2
  have h225 := hI.1; have hI := hI.2
  have h226 := hI.1; have hI := hI.2
  have h227 := hI.1; have hI := hI.2
  have h228 := hI.1; have hI := hI.2
  have h229 := hI.1; have hI := hI.2
  have h230 := hI.1; have hI := hI.2
  have h231 := hI.1; have hI := hI.2
  have h232 := hI.1; have hI := hI.2
  have h233 := hI.1; have hI := hI.2
  have h234 := hI.1; have hI := hI.2
  have h235 := hI.1; have hI := hI.2
  have h236 := hI.1; have hI := hI.2
  have h237 := hI.1; have hI := hI.2
  have h238 := hI.1; have hI := hI.2
  have h239 := hI.1; have hI := hI.2
  have h240 := hI.1; have hI := hI.2
  have h241 := hI.1; have hI := hI.2
  have h242 := hI.1; have hI := hI.2
  have h243 := hI.1; have hI := hI.2
  have h244 := hI.1; have hI := hI.2
  have h245 := hI.1; have hI := hI.2
  have h246 := hI.1; have hI := hI.2
  have h247 := hI.1; have hI := hI.2
  have h248 := hI.1; have hI := hI.2
  have h249 := hI.1; have hI := hI.2
  have h250 := hI.1; have hI := hI.2
  have h251 := hI.1; have hI := hI.2
  have h252 := hI.1; have hI := hI.2
  have h253 := hI.1; have hI := hI.2
  have h254 := hI.1; have hI := hI.2
  have h255 := hI.1; have hI := hI.2
  have h256 := hI.1; have hI := hI.2
  have h257 := hI.1; have hI := hI.2
  have h258 := hI.1; have hI := hI.2
  have h259 := hI.1; have hI := hI.2
  have h260 := hI.1; have hI := hI.2
  have h261 := hI.1; have hI := hI.2
  have h262 := hI.1; have hI := hI.2
  have h263 := hI.1; have hI := hI.2
  have h264 := hI.1; have hI := hI.2
  have h265 := hI.1; have hI := hI.2
  have h266 := hI.1; have hI := hI.2
  have h267 := hI.1; have hI := hI.2
  have h268 := hI.1; have hI := hI.2
  have h269 := hI.1; have hI := hI.2
  have h270 := hI.1; have hI := hI.2
  have h271 := hI.1; have hI := hI.2
  have h272 := hI.1; have hI := hI.2
  have h273 := hI.1; have hI := hI.2
  have h274 := hI.1; have hI := hI.2
  have h275 := hI.1; have hI := hI.2
  have h276 := hI.1; have hI := hI.2
  have h277 := hI.1; have hI := hI.2
  have h278 := hI.1; have hI := hI.2
  have h279 := hI.1; have hI := hI.2
  have h280 := hI.1; have hI := hI.2
  have h281 := hI.1; have hI := hI.2
  have h282 := hI.1; have hI := hI.2
  have h283 := hI.1; have hI := hI.2
  have h284 := hI.1; have hI := hI.2
  have h285 := hI.1; have hI := hI.2
  have h286 := hI.1; have hI := hI.2
  have h287 := hI.1; have hI := hI.2
  exact invC_of_trees inp env _ T87 L88 (slice_trees_mem prog 4 _ _ 25 K87 K88 T87 slice87 env)
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
      (And.intro ⟨rfl, h128⟩
      (And.intro ⟨rfl, h129⟩
      (And.intro ⟨rfl, h130⟩
      (And.intro ⟨rfl, h131⟩
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
      (And.intro ⟨rfl, h144⟩
      (And.intro ⟨rfl, h145⟩
      (And.intro ⟨rfl, h146⟩
      (And.intro ⟨rfl, h147⟩
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
      (And.intro ⟨rfl, h160⟩
      (And.intro ⟨rfl, h161⟩
      (And.intro ⟨rfl, h162⟩
      (And.intro ⟨rfl, h163⟩
      (And.intro ⟨rfl, h164⟩
      (And.intro ⟨rfl, h165⟩
      (And.intro ⟨rfl, h166⟩
      (And.intro ⟨rfl, h167⟩
      (And.intro ⟨rfl, h168⟩
      (And.intro ⟨rfl, h169⟩
      (And.intro ⟨rfl, h170⟩
      (And.intro ⟨rfl, h171⟩
      (And.intro ⟨rfl, h172⟩
      (And.intro ⟨rfl, h173⟩
      (And.intro ⟨rfl, h174⟩
      (And.intro ⟨rfl, h175⟩
      (And.intro ⟨rfl, h176⟩
      (And.intro ⟨rfl, h177⟩
      (And.intro ⟨rfl, h178⟩
      (And.intro ⟨rfl, h179⟩
      (And.intro ⟨rfl, h180⟩
      (And.intro ⟨rfl, h181⟩
      (And.intro ⟨rfl, h182⟩
      (And.intro ⟨rfl, h183⟩
      (And.intro ⟨rfl, h184⟩
      (And.intro ⟨rfl, h185⟩
      (And.intro ⟨rfl, h186⟩
      (And.intro ⟨rfl, h187⟩
      (And.intro ⟨rfl, h188⟩
      (And.intro ⟨rfl, h189⟩
      (And.intro ⟨rfl, h190⟩
      (And.intro ⟨rfl, h191⟩
      (And.intro ⟨rfl, h192⟩
      (And.intro ⟨rfl, h193⟩
      (And.intro ⟨rfl, h194⟩
      (And.intro ⟨rfl, h195⟩
      (And.intro ⟨rfl, h196⟩
      (And.intro ⟨rfl, h197⟩
      (And.intro ⟨rfl, h198⟩
      (And.intro ⟨rfl, h199⟩
      (And.intro ⟨rfl, h200⟩
      (And.intro ⟨rfl, h201⟩
      (And.intro ⟨rfl, h202⟩
      (And.intro ⟨rfl, h203⟩
      (And.intro ⟨rfl, h204⟩
      (And.intro ⟨rfl, h205⟩
      (And.intro ⟨rfl, h206⟩
      (And.intro ⟨rfl, h207⟩
      (And.intro ⟨rfl, h208⟩
      (And.intro ⟨rfl, h209⟩
      (And.intro ⟨rfl, h210⟩
      (And.intro ⟨rfl, h211⟩
      (And.intro ⟨rfl, h212⟩
      (And.intro ⟨rfl, h213⟩
      (And.intro ⟨rfl, h214⟩
      (And.intro ⟨rfl, h215⟩
      (And.intro ⟨rfl, h216⟩
      (And.intro ⟨rfl, h217⟩
      (And.intro ⟨rfl, h218⟩
      (And.intro ⟨rfl, h219⟩
      (And.intro ⟨rfl, h220⟩
      (And.intro ⟨rfl, h221⟩
      (And.intro ⟨rfl, h222⟩
      (And.intro ⟨rfl, h223⟩
      (And.intro ⟨rfl, h224⟩
      (And.intro ⟨rfl, h225⟩
      (And.intro ⟨rfl, h226⟩
      (And.intro ⟨rfl, h227⟩
      (And.intro ⟨rfl, h228⟩
      (And.intro ⟨rfl, h229⟩
      (And.intro ⟨rfl, h230⟩
      (And.intro ⟨rfl, h231⟩
      (And.intro ⟨rfl, h232⟩
      (And.intro ⟨rfl, h233⟩
      (And.intro ⟨rfl, h234⟩
      (And.intro ⟨rfl, h235⟩
      (And.intro ⟨rfl, h236⟩
      (And.intro ⟨rfl, h237⟩
      (And.intro ⟨rfl, h238⟩
      (And.intro ⟨rfl, h239⟩
      (And.intro ⟨rfl, h240⟩
      (And.intro ⟨rfl, h241⟩
      (And.intro ⟨rfl, h242⟩
      (And.intro ⟨rfl, h243⟩
      (And.intro ⟨rfl, h244⟩
      (And.intro ⟨rfl, h245⟩
      (And.intro ⟨rfl, h246⟩
      (And.intro ⟨rfl, h247⟩
      (And.intro ⟨rfl, h248⟩
      (And.intro ⟨rfl, h249⟩
      (And.intro ⟨rfl, h250⟩
      (And.intro ⟨rfl, h251⟩
      (And.intro ⟨rfl, h252⟩
      (And.intro ⟨rfl, h253⟩
      (And.intro ⟨rfl, h254⟩
      (And.intro ⟨rfl, h255⟩
      (And.intro ⟨rfl, core87_327 (qv inp) inp env h28 h29 h30 h31 h12 h13 h14 h15 h236 h237 h238 h239 h156 h157 h158 h159 (qW_recM2 inp 3 0 50 (by decide) (by decide)) (qM2 inp 3 0 34) (qM1 inp 3 0 34)⟩
      (And.intro ⟨rfl, core87_326 (qv inp) inp env h24 h25 h26 h27 h8 h9 h10 h11 h232 h233 h234 h235 h152 h153 h154 h155 (qW_recM2 inp 2 0 50 (by decide) (by decide)) (qM2 inp 2 0 34) (qM1 inp 2 0 34)⟩
      (And.intro ⟨rfl, core87_325 (qv inp) inp env h20 h21 h22 h23 h4 h5 h6 h7 h228 h229 h230 h231 h148 h149 h150 h151 (qW_recM2 inp 1 0 50 (by decide) (by decide)) (qM2 inp 1 0 34) (qM1 inp 1 0 34)⟩
      (And.intro ⟨rfl, core87_324 (qv inp) inp env h16 h17 h18 h19 h0 h1 h2 h3 h224 h225 h226 h227 h144 h145 h146 h147 (qW_recM2 inp 0 0 50 (by decide) (by decide)) (qM2 inp 0 0 34) (qM1 inp 0 0 34)⟩
      (And.intro ⟨rfl, h256⟩
      (And.intro ⟨rfl, h257⟩
      (And.intro ⟨rfl, h258⟩
      (And.intro ⟨rfl, h259⟩
      (And.intro ⟨rfl, h260⟩
      (And.intro ⟨rfl, h261⟩
      (And.intro ⟨rfl, h262⟩
      (And.intro ⟨rfl, h263⟩
      (And.intro ⟨rfl, h264⟩
      (And.intro ⟨rfl, h265⟩
      (And.intro ⟨rfl, h266⟩
      (And.intro ⟨rfl, h267⟩
      (And.intro ⟨rfl, h268⟩
      (And.intro ⟨rfl, h269⟩
      (And.intro ⟨rfl, h270⟩
      (And.intro ⟨rfl, h271⟩
      (And.intro ⟨rfl, h272⟩
      (And.intro ⟨rfl, h273⟩
      (And.intro ⟨rfl, h274⟩
      (And.intro ⟨rfl, h275⟩
      (And.intro ⟨rfl, h276⟩
      (And.intro ⟨rfl, h277⟩
      (And.intro ⟨rfl, h278⟩
      (And.intro ⟨rfl, h279⟩
      (And.intro ⟨rfl, h280⟩
      (And.intro ⟨rfl, h281⟩
      (And.intro ⟨rfl, h282⟩
      (And.intro ⟨rfl, h283⟩
      (And.intro ⟨rfl, h284⟩
      (And.intro ⟨rfl, h285⟩
      (And.intro ⟨rfl, h286⟩
      (And.intro ⟨rfl, h287⟩
      trivial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hashtree.Gen.WinAvxX4P
