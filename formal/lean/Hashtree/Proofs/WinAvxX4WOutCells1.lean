import Hashtree.Proofs.WinAvxX4WShift

/-! R2c windows x4 — the tail cuts' log shapes and output-cell tables, part 1 (generated; one `decide +kernel` per fact). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4 Hashtree.Gen.WinAvxX4P
open Hashtree.Proofs.WinAvxX4W (m0W shiftKW orcB orcEx KT KTE)

namespace Hashtree.Proofs.WinAvxX4WOut

/-- Every logged cell of a tail cut is an output cell at `sym 1 + o`, `o < 128`, or a stack
cell `sAt k`, `-568 ≤ k < 0` (the kernel's own frame). -/
def outShapeW4 (K : State E Lin) : Bool :=
  K.mem.all fun p =>
    (p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 128)) ||
    (p.1.region == rStack && p.1.off.c == Hashtree.Asm.X86SymW.stkC && decide (-568 ≤ p.1.off.k) && decide (p.1.off.k < 0))

/-- The 128 `(o, id, b)` output cells of a tail cut (the pilot's `out_final` table). -/
def w4tab : List (Nat × Nat × Nat) := [(0, 1127, 0), (1, 1126, 1), (2, 1125, 2), (3, 1124, 3), (4, 1123, 0), (5, 1122, 1), (6, 1121, 2), (7, 1120, 3), (8, 1119, 0), (9, 1118, 1), (10, 1117, 2), (11, 1116, 3), (12, 1115, 0), (13, 1114, 1), (14, 1113, 2), (15, 1112, 3), (16, 1111, 0), (17, 1110, 1), (18, 1109, 2), (19, 1108, 3), (20, 1107, 0), (21, 1106, 1), (22, 1105, 2), (23, 1104, 3), (24, 1103, 0), (25, 1102, 1), (26, 1101, 2), (27, 1100, 3), (28, 1099, 0), (29, 1098, 1), (30, 1097, 2), (31, 1096, 3), (32, 1095, 0), (33, 1094, 1), (34, 1093, 2), (35, 1092, 3), (36, 1091, 0), (37, 1090, 1), (38, 1089, 2), (39, 1088, 3), (40, 1087, 0), (41, 1086, 1), (42, 1085, 2), (43, 1084, 3), (44, 1083, 0), (45, 1082, 1), (46, 1081, 2), (47, 1080, 3), (48, 1079, 0), (49, 1078, 1), (50, 1077, 2), (51, 1076, 3), (52, 1075, 0), (53, 1074, 1), (54, 1073, 2), (55, 1072, 3), (56, 1071, 0), (57, 1070, 1), (58, 1069, 2), (59, 1068, 3), (60, 1067, 0), (61, 1066, 1), (62, 1065, 2), (63, 1064, 3), (64, 1063, 0), (65, 1062, 1), (66, 1061, 2), (67, 1060, 3), (68, 1059, 0), (69, 1058, 1), (70, 1057, 2), (71, 1056, 3), (72, 1055, 0), (73, 1054, 1), (74, 1053, 2), (75, 1052, 3), (76, 1051, 0), (77, 1050, 1), (78, 1049, 2), (79, 1048, 3), (80, 1047, 0), (81, 1046, 1), (82, 1045, 2), (83, 1044, 3), (84, 1043, 0), (85, 1042, 1), (86, 1041, 2), (87, 1040, 3), (88, 1039, 0), (89, 1038, 1), (90, 1037, 2), (91, 1036, 3), (92, 1035, 0), (93, 1034, 1), (94, 1033, 2), (95, 1032, 3), (96, 1031, 0), (97, 1030, 1), (98, 1029, 2), (99, 1028, 3), (100, 1027, 0), (101, 1026, 1), (102, 1025, 2), (103, 1024, 3), (104, 1023, 0), (105, 1022, 1), (106, 1021, 2), (107, 1020, 3), (108, 1019, 0), (109, 1018, 1), (110, 1017, 2), (111, 1016, 3), (112, 1015, 0), (113, 1014, 1), (114, 1013, 2), (115, 1012, 3), (116, 1011, 0), (117, 1010, 1), (118, 1009, 2), (119, 1008, 3), (120, 1007, 0), (121, 1006, 1), (122, 1005, 2), (123, 1004, 3), (124, 1003, 0), (125, 1002, 1), (126, 1001, 2), (127, 1000, 3)]

theorem w4shape_KT : outShapeW4 KT = true := by decide +kernel

theorem w4cells_KT : w4tab.all (fun t => outCell KT t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem w4cell_KT (o id b : Nat) (h : (o, id, b) ∈ w4tab) : outCell KT o id b = true :=
  List.all_eq_true.mp w4cells_KT (o, id, b) h

theorem w4shape_KTE : outShapeW4 KTE = true := by decide +kernel

theorem w4cells_KTE : w4tab.all (fun t => outCell KTE t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem w4cell_KTE (o id b : Nat) (h : (o, id, b) ∈ w4tab) : outCell KTE o id b = true :=
  List.all_eq_true.mp w4cells_KTE (o, id, b) h

end Hashtree.Proofs.WinAvxX4WOut
