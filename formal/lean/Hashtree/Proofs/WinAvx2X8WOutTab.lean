import Hashtree.Proofs.Avx512X16WOutBase
import Hashtree.Proofs.WinLogW
import Hashtree.Gen.WinAvx2X8P.D211

/-! R2c windows x8 — the 256 output cells of a pass, the shape of a pass's log, and the eight digests from
the invariant at the pilot's last labels, for any cut whose cells are the pilot's (generated from the pilot's `out_final`). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.Avx512X16WOut (OutOk)

namespace Hashtree.Proofs.WinAvx2X8WOut

/-- The 256 `(o, id, b)` output cells of the pilot's final cut `K212`. -/
def tab8w : List (Nat × Nat × Nat) := [(0, 1255, 0), (1, 1254, 1), (2, 1253, 2), (3, 1252, 3), (4, 1251, 0), (5, 1250, 1), (6, 1249, 2), (7, 1248, 3), (8, 1247, 0), (9, 1246, 1), (10, 1245, 2), (11, 1244, 3), (12, 1243, 0), (13, 1242, 1), (14, 1241, 2), (15, 1240, 3), (16, 1239, 0), (17, 1238, 1), (18, 1237, 2), (19, 1236, 3), (20, 1235, 0), (21, 1234, 1), (22, 1233, 2), (23, 1232, 3), (24, 1231, 0), (25, 1230, 1), (26, 1229, 2), (27, 1228, 3), (28, 1227, 0), (29, 1226, 1), (30, 1225, 2), (31, 1224, 3), (32, 1223, 0), (33, 1222, 1), (34, 1221, 2), (35, 1220, 3), (36, 1219, 0), (37, 1218, 1), (38, 1217, 2), (39, 1216, 3), (40, 1215, 0), (41, 1214, 1), (42, 1213, 2), (43, 1212, 3), (44, 1211, 0), (45, 1210, 1), (46, 1209, 2), (47, 1208, 3), (48, 1207, 0), (49, 1206, 1), (50, 1205, 2), (51, 1204, 3), (52, 1203, 0), (53, 1202, 1), (54, 1201, 2), (55, 1200, 3), (56, 1199, 0), (57, 1198, 1), (58, 1197, 2), (59, 1196, 3), (60, 1195, 0), (61, 1194, 1), (62, 1193, 2), (63, 1192, 3), (64, 1191, 0), (65, 1190, 1), (66, 1189, 2), (67, 1188, 3), (68, 1187, 0), (69, 1186, 1), (70, 1185, 2), (71, 1184, 3), (72, 1183, 0), (73, 1182, 1), (74, 1181, 2), (75, 1180, 3), (76, 1179, 0), (77, 1178, 1), (78, 1177, 2), (79, 1176, 3), (80, 1175, 0), (81, 1174, 1), (82, 1173, 2), (83, 1172, 3), (84, 1171, 0), (85, 1170, 1), (86, 1169, 2), (87, 1168, 3), (88, 1167, 0), (89, 1166, 1), (90, 1165, 2), (91, 1164, 3), (92, 1163, 0), (93, 1162, 1), (94, 1161, 2), (95, 1160, 3), (96, 1159, 0), (97, 1158, 1), (98, 1157, 2), (99, 1156, 3), (100, 1155, 0), (101, 1154, 1), (102, 1153, 2), (103, 1152, 3), (104, 1151, 0), (105, 1150, 1), (106, 1149, 2), (107, 1148, 3), (108, 1147, 0), (109, 1146, 1), (110, 1145, 2), (111, 1144, 3), (112, 1143, 0), (113, 1142, 1), (114, 1141, 2), (115, 1140, 3), (116, 1139, 0), (117, 1138, 1), (118, 1137, 2), (119, 1136, 3), (120, 1135, 0), (121, 1134, 1), (122, 1133, 2), (123, 1132, 3), (124, 1131, 0), (125, 1130, 1), (126, 1129, 2), (127, 1128, 3), (128, 1127, 0), (129, 1126, 1), (130, 1125, 2), (131, 1124, 3), (132, 1123, 0), (133, 1122, 1), (134, 1121, 2), (135, 1120, 3), (136, 1119, 0), (137, 1118, 1), (138, 1117, 2), (139, 1116, 3), (140, 1115, 0), (141, 1114, 1), (142, 1113, 2), (143, 1112, 3), (144, 1111, 0), (145, 1110, 1), (146, 1109, 2), (147, 1108, 3), (148, 1107, 0), (149, 1106, 1), (150, 1105, 2), (151, 1104, 3), (152, 1103, 0), (153, 1102, 1), (154, 1101, 2), (155, 1100, 3), (156, 1099, 0), (157, 1098, 1), (158, 1097, 2), (159, 1096, 3), (160, 1095, 0), (161, 1094, 1), (162, 1093, 2), (163, 1092, 3), (164, 1091, 0), (165, 1090, 1), (166, 1089, 2), (167, 1088, 3), (168, 1087, 0), (169, 1086, 1), (170, 1085, 2), (171, 1084, 3), (172, 1083, 0), (173, 1082, 1), (174, 1081, 2), (175, 1080, 3), (176, 1079, 0), (177, 1078, 1), (178, 1077, 2), (179, 1076, 3), (180, 1075, 0), (181, 1074, 1), (182, 1073, 2), (183, 1072, 3), (184, 1071, 0), (185, 1070, 1), (186, 1069, 2), (187, 1068, 3), (188, 1067, 0), (189, 1066, 1), (190, 1065, 2), (191, 1064, 3), (192, 1063, 0), (193, 1062, 1), (194, 1061, 2), (195, 1060, 3), (196, 1059, 0), (197, 1058, 1), (198, 1057, 2), (199, 1056, 3), (200, 1055, 0), (201, 1054, 1), (202, 1053, 2), (203, 1052, 3), (204, 1051, 0), (205, 1050, 1), (206, 1049, 2), (207, 1048, 3), (208, 1047, 0), (209, 1046, 1), (210, 1045, 2), (211, 1044, 3), (212, 1043, 0), (213, 1042, 1), (214, 1041, 2), (215, 1040, 3), (216, 1039, 0), (217, 1038, 1), (218, 1037, 2), (219, 1036, 3), (220, 1035, 0), (221, 1034, 1), (222, 1033, 2), (223, 1032, 3), (224, 1031, 0), (225, 1030, 1), (226, 1029, 2), (227, 1028, 3), (228, 1027, 0), (229, 1026, 1), (230, 1025, 2), (231, 1024, 3), (232, 1023, 0), (233, 1022, 1), (234, 1021, 2), (235, 1020, 3), (236, 1019, 0), (237, 1018, 1), (238, 1017, 2), (239, 1016, 3), (240, 1015, 0), (241, 1014, 1), (242, 1013, 2), (243, 1012, 3), (244, 1011, 0), (245, 1010, 1), (246, 1009, 2), (247, 1008, 3), (248, 1007, 0), (249, 1006, 1), (250, 1005, 2), (251, 1004, 3), (252, 1003, 0), (253, 1002, 1), (254, 1001, 2), (255, 1000, 3)]

/-- Every logged cell is an output cell at `sym 1 + o`, `o < 256`, or a stack cell `sAt k`,
`-1296 ≤ k < 0` (the kernel's frame). -/
def outShape8W (K : State E Lin) : Bool :=
  K.mem.all fun p =>
    (p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 256)) ||
    (p.1.region == rStack && p.1.off.c == Hashtree.Asm.X86SymW.stkC && decide (-1296 ≤ p.1.off.k) && decide (p.1.off.k < 0))

theorem out_eval8w (σ : Nat → Int) (k : Int) : (⟨k, [0, 1]⟩ : Lin).eval σ = σ 1 + k := by
  show k + (0 * σ 0 + (1 * σ (0 + 1) + 0)) = σ 1 + k
  rw [show (0 + 1 : Nat) = 1 from rfl]
  omega

theorem outShape8W_sound (K : State E Lin) (h : outShape8W K = true) (e : Key → W32) (σ : Nat → Int) :
    ∀ p ∈ (mapState e σ K).mem,
      (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
      (p.1.region = rStack ∧ σ 9 - 1296 ≤ p.1.off ∧ p.1.off < σ 9) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [outShape8W, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨qr, qk, qc⟩, qcell⟩ := q
  rcases h _ hq with ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩ | ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    left
    show rOut = rOut ∧ σ 1 ≤ (⟨qk, [0, 1]⟩ : Lin).eval σ ∧ (⟨qk, [0, 1]⟩ : Lin).eval σ < σ 1 + 256
    rw [out_eval8w]
    exact ⟨rfl, by omega, by omega⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    right
    show rStack = rStack ∧ σ 9 - 1296 ≤ (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ ∧
      (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ < σ 9
    rw [Hashtree.Proofs.WinLogW.sAtW_eval]
    exact ⟨rfl, by omega, by omega⟩

/-- **The eight digests.**  A cut whose output cells are the pilot's (`tab8w`), at an environment
satisfying the pilot's final invariant (`L212`), holds the SHA-256 bytes of the 8 input blocks. -/
theorem outOk_tab8w (K : State E Lin) (hK : tab8w.all (fun t => outCell K t.1 t.2.1 t.2.2) = true)
    (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L212) :
    OutOk inp (σ 1) 8 (mapState e σ K).mem := by
  have hc : ∀ o id b, (o, id, b) ∈ tab8w → outCell K o id b = true :=
    fun o id b h => List.all_eq_true.mp hK (o, id, b) h
  have hF := hI
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
  intro n i b hn hi hb
  match n, i, b, hn, hi, hb with
  | 0, 0, 0, _, _, _ => exact ⟨e (.n 1255), outCell_sound _ σ K 0 1255 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1255) = qv inp (.HB 0 0) from g896,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 0 0 (by decide) (by decide)]; rfl⟩
  | 0, 0, 1, _, _, _ => exact ⟨e (.n 1254), outCell_sound _ σ K 1 1254 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1254) = qv inp (.HB 0 0) from g897,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 0 1 (by decide) (by decide)]; rfl⟩
  | 0, 0, 2, _, _, _ => exact ⟨e (.n 1253), outCell_sound _ σ K 2 1253 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1253) = qv inp (.HB 0 0) from g898,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 0 2 (by decide) (by decide)]; rfl⟩
  | 0, 0, 3, _, _, _ => exact ⟨e (.n 1252), outCell_sound _ σ K 3 1252 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1252) = qv inp (.HB 0 0) from g899,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 0 3 (by decide) (by decide)]; rfl⟩
  | 0, 1, 0, _, _, _ => exact ⟨e (.n 1251), outCell_sound _ σ K 4 1251 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1251) = qv inp (.HB 0 1) from g900,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 1 0 (by decide) (by decide)]; rfl⟩
  | 0, 1, 1, _, _, _ => exact ⟨e (.n 1250), outCell_sound _ σ K 5 1250 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1250) = qv inp (.HB 0 1) from g901,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 1 1 (by decide) (by decide)]; rfl⟩
  | 0, 1, 2, _, _, _ => exact ⟨e (.n 1249), outCell_sound _ σ K 6 1249 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1249) = qv inp (.HB 0 1) from g902,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 1 2 (by decide) (by decide)]; rfl⟩
  | 0, 1, 3, _, _, _ => exact ⟨e (.n 1248), outCell_sound _ σ K 7 1248 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1248) = qv inp (.HB 0 1) from g903,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 1 3 (by decide) (by decide)]; rfl⟩
  | 0, 2, 0, _, _, _ => exact ⟨e (.n 1247), outCell_sound _ σ K 8 1247 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1247) = qv inp (.HB 0 2) from g904,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 2 0 (by decide) (by decide)]; rfl⟩
  | 0, 2, 1, _, _, _ => exact ⟨e (.n 1246), outCell_sound _ σ K 9 1246 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1246) = qv inp (.HB 0 2) from g905,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 2 1 (by decide) (by decide)]; rfl⟩
  | 0, 2, 2, _, _, _ => exact ⟨e (.n 1245), outCell_sound _ σ K 10 1245 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1245) = qv inp (.HB 0 2) from g906,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 2 2 (by decide) (by decide)]; rfl⟩
  | 0, 2, 3, _, _, _ => exact ⟨e (.n 1244), outCell_sound _ σ K 11 1244 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1244) = qv inp (.HB 0 2) from g907,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 2 3 (by decide) (by decide)]; rfl⟩
  | 0, 3, 0, _, _, _ => exact ⟨e (.n 1243), outCell_sound _ σ K 12 1243 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1243) = qv inp (.HB 0 3) from g908,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 3 0 (by decide) (by decide)]; rfl⟩
  | 0, 3, 1, _, _, _ => exact ⟨e (.n 1242), outCell_sound _ σ K 13 1242 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1242) = qv inp (.HB 0 3) from g909,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 3 1 (by decide) (by decide)]; rfl⟩
  | 0, 3, 2, _, _, _ => exact ⟨e (.n 1241), outCell_sound _ σ K 14 1241 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1241) = qv inp (.HB 0 3) from g910,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 3 2 (by decide) (by decide)]; rfl⟩
  | 0, 3, 3, _, _, _ => exact ⟨e (.n 1240), outCell_sound _ σ K 15 1240 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1240) = qv inp (.HB 0 3) from g911,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 3 3 (by decide) (by decide)]; rfl⟩
  | 0, 4, 0, _, _, _ => exact ⟨e (.n 1239), outCell_sound _ σ K 16 1239 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1239) = qv inp (.HB 0 4) from g912,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 4 0 (by decide) (by decide)]; rfl⟩
  | 0, 4, 1, _, _, _ => exact ⟨e (.n 1238), outCell_sound _ σ K 17 1238 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1238) = qv inp (.HB 0 4) from g913,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 4 1 (by decide) (by decide)]; rfl⟩
  | 0, 4, 2, _, _, _ => exact ⟨e (.n 1237), outCell_sound _ σ K 18 1237 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1237) = qv inp (.HB 0 4) from g914,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 4 2 (by decide) (by decide)]; rfl⟩
  | 0, 4, 3, _, _, _ => exact ⟨e (.n 1236), outCell_sound _ σ K 19 1236 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1236) = qv inp (.HB 0 4) from g915,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 4 3 (by decide) (by decide)]; rfl⟩
  | 0, 5, 0, _, _, _ => exact ⟨e (.n 1235), outCell_sound _ σ K 20 1235 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1235) = qv inp (.HB 0 5) from g916,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 5 0 (by decide) (by decide)]; rfl⟩
  | 0, 5, 1, _, _, _ => exact ⟨e (.n 1234), outCell_sound _ σ K 21 1234 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1234) = qv inp (.HB 0 5) from g917,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 5 1 (by decide) (by decide)]; rfl⟩
  | 0, 5, 2, _, _, _ => exact ⟨e (.n 1233), outCell_sound _ σ K 22 1233 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1233) = qv inp (.HB 0 5) from g918,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 5 2 (by decide) (by decide)]; rfl⟩
  | 0, 5, 3, _, _, _ => exact ⟨e (.n 1232), outCell_sound _ σ K 23 1232 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1232) = qv inp (.HB 0 5) from g919,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 5 3 (by decide) (by decide)]; rfl⟩
  | 0, 6, 0, _, _, _ => exact ⟨e (.n 1231), outCell_sound _ σ K 24 1231 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1231) = qv inp (.HB 0 6) from g920,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 6 0 (by decide) (by decide)]; rfl⟩
  | 0, 6, 1, _, _, _ => exact ⟨e (.n 1230), outCell_sound _ σ K 25 1230 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1230) = qv inp (.HB 0 6) from g921,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 6 1 (by decide) (by decide)]; rfl⟩
  | 0, 6, 2, _, _, _ => exact ⟨e (.n 1229), outCell_sound _ σ K 26 1229 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1229) = qv inp (.HB 0 6) from g922,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 6 2 (by decide) (by decide)]; rfl⟩
  | 0, 6, 3, _, _, _ => exact ⟨e (.n 1228), outCell_sound _ σ K 27 1228 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1228) = qv inp (.HB 0 6) from g923,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 6 3 (by decide) (by decide)]; rfl⟩
  | 0, 7, 0, _, _, _ => exact ⟨e (.n 1227), outCell_sound _ σ K 28 1227 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1227) = qv inp (.HB 0 7) from g924,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 7 0 (by decide) (by decide)]; rfl⟩
  | 0, 7, 1, _, _, _ => exact ⟨e (.n 1226), outCell_sound _ σ K 29 1226 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1226) = qv inp (.HB 0 7) from g925,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 7 1 (by decide) (by decide)]; rfl⟩
  | 0, 7, 2, _, _, _ => exact ⟨e (.n 1225), outCell_sound _ σ K 30 1225 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1225) = qv inp (.HB 0 7) from g926,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 7 2 (by decide) (by decide)]; rfl⟩
  | 0, 7, 3, _, _, _ => exact ⟨e (.n 1224), outCell_sound _ σ K 31 1224 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1224) = qv inp (.HB 0 7) from g927,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 7 3 (by decide) (by decide)]; rfl⟩
  | 1, 0, 0, _, _, _ => exact ⟨e (.n 1223), outCell_sound _ σ K 32 1223 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1223) = qv inp (.HB 1 0) from g928,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 0 0 (by decide) (by decide)]; rfl⟩
  | 1, 0, 1, _, _, _ => exact ⟨e (.n 1222), outCell_sound _ σ K 33 1222 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1222) = qv inp (.HB 1 0) from g929,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 0 1 (by decide) (by decide)]; rfl⟩
  | 1, 0, 2, _, _, _ => exact ⟨e (.n 1221), outCell_sound _ σ K 34 1221 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1221) = qv inp (.HB 1 0) from g930,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 0 2 (by decide) (by decide)]; rfl⟩
  | 1, 0, 3, _, _, _ => exact ⟨e (.n 1220), outCell_sound _ σ K 35 1220 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1220) = qv inp (.HB 1 0) from g931,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 0 3 (by decide) (by decide)]; rfl⟩
  | 1, 1, 0, _, _, _ => exact ⟨e (.n 1219), outCell_sound _ σ K 36 1219 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1219) = qv inp (.HB 1 1) from g932,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 1 0 (by decide) (by decide)]; rfl⟩
  | 1, 1, 1, _, _, _ => exact ⟨e (.n 1218), outCell_sound _ σ K 37 1218 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1218) = qv inp (.HB 1 1) from g933,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 1 1 (by decide) (by decide)]; rfl⟩
  | 1, 1, 2, _, _, _ => exact ⟨e (.n 1217), outCell_sound _ σ K 38 1217 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1217) = qv inp (.HB 1 1) from g934,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 1 2 (by decide) (by decide)]; rfl⟩
  | 1, 1, 3, _, _, _ => exact ⟨e (.n 1216), outCell_sound _ σ K 39 1216 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1216) = qv inp (.HB 1 1) from g935,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 1 3 (by decide) (by decide)]; rfl⟩
  | 1, 2, 0, _, _, _ => exact ⟨e (.n 1215), outCell_sound _ σ K 40 1215 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1215) = qv inp (.HB 1 2) from g936,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 2 0 (by decide) (by decide)]; rfl⟩
  | 1, 2, 1, _, _, _ => exact ⟨e (.n 1214), outCell_sound _ σ K 41 1214 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1214) = qv inp (.HB 1 2) from g937,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 2 1 (by decide) (by decide)]; rfl⟩
  | 1, 2, 2, _, _, _ => exact ⟨e (.n 1213), outCell_sound _ σ K 42 1213 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1213) = qv inp (.HB 1 2) from g938,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 2 2 (by decide) (by decide)]; rfl⟩
  | 1, 2, 3, _, _, _ => exact ⟨e (.n 1212), outCell_sound _ σ K 43 1212 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1212) = qv inp (.HB 1 2) from g939,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 2 3 (by decide) (by decide)]; rfl⟩
  | 1, 3, 0, _, _, _ => exact ⟨e (.n 1211), outCell_sound _ σ K 44 1211 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1211) = qv inp (.HB 1 3) from g940,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 3 0 (by decide) (by decide)]; rfl⟩
  | 1, 3, 1, _, _, _ => exact ⟨e (.n 1210), outCell_sound _ σ K 45 1210 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1210) = qv inp (.HB 1 3) from g941,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 3 1 (by decide) (by decide)]; rfl⟩
  | 1, 3, 2, _, _, _ => exact ⟨e (.n 1209), outCell_sound _ σ K 46 1209 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1209) = qv inp (.HB 1 3) from g942,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 3 2 (by decide) (by decide)]; rfl⟩
  | 1, 3, 3, _, _, _ => exact ⟨e (.n 1208), outCell_sound _ σ K 47 1208 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1208) = qv inp (.HB 1 3) from g943,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 3 3 (by decide) (by decide)]; rfl⟩
  | 1, 4, 0, _, _, _ => exact ⟨e (.n 1207), outCell_sound _ σ K 48 1207 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1207) = qv inp (.HB 1 4) from g944,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 4 0 (by decide) (by decide)]; rfl⟩
  | 1, 4, 1, _, _, _ => exact ⟨e (.n 1206), outCell_sound _ σ K 49 1206 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1206) = qv inp (.HB 1 4) from g945,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 4 1 (by decide) (by decide)]; rfl⟩
  | 1, 4, 2, _, _, _ => exact ⟨e (.n 1205), outCell_sound _ σ K 50 1205 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1205) = qv inp (.HB 1 4) from g946,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 4 2 (by decide) (by decide)]; rfl⟩
  | 1, 4, 3, _, _, _ => exact ⟨e (.n 1204), outCell_sound _ σ K 51 1204 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1204) = qv inp (.HB 1 4) from g947,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 4 3 (by decide) (by decide)]; rfl⟩
  | 1, 5, 0, _, _, _ => exact ⟨e (.n 1203), outCell_sound _ σ K 52 1203 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1203) = qv inp (.HB 1 5) from g948,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 5 0 (by decide) (by decide)]; rfl⟩
  | 1, 5, 1, _, _, _ => exact ⟨e (.n 1202), outCell_sound _ σ K 53 1202 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1202) = qv inp (.HB 1 5) from g949,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 5 1 (by decide) (by decide)]; rfl⟩
  | 1, 5, 2, _, _, _ => exact ⟨e (.n 1201), outCell_sound _ σ K 54 1201 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1201) = qv inp (.HB 1 5) from g950,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 5 2 (by decide) (by decide)]; rfl⟩
  | 1, 5, 3, _, _, _ => exact ⟨e (.n 1200), outCell_sound _ σ K 55 1200 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1200) = qv inp (.HB 1 5) from g951,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 5 3 (by decide) (by decide)]; rfl⟩
  | 1, 6, 0, _, _, _ => exact ⟨e (.n 1199), outCell_sound _ σ K 56 1199 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1199) = qv inp (.HB 1 6) from g952,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 6 0 (by decide) (by decide)]; rfl⟩
  | 1, 6, 1, _, _, _ => exact ⟨e (.n 1198), outCell_sound _ σ K 57 1198 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1198) = qv inp (.HB 1 6) from g953,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 6 1 (by decide) (by decide)]; rfl⟩
  | 1, 6, 2, _, _, _ => exact ⟨e (.n 1197), outCell_sound _ σ K 58 1197 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1197) = qv inp (.HB 1 6) from g954,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 6 2 (by decide) (by decide)]; rfl⟩
  | 1, 6, 3, _, _, _ => exact ⟨e (.n 1196), outCell_sound _ σ K 59 1196 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1196) = qv inp (.HB 1 6) from g955,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 6 3 (by decide) (by decide)]; rfl⟩
  | 1, 7, 0, _, _, _ => exact ⟨e (.n 1195), outCell_sound _ σ K 60 1195 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1195) = qv inp (.HB 1 7) from g956,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 7 0 (by decide) (by decide)]; rfl⟩
  | 1, 7, 1, _, _, _ => exact ⟨e (.n 1194), outCell_sound _ σ K 61 1194 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1194) = qv inp (.HB 1 7) from g957,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 7 1 (by decide) (by decide)]; rfl⟩
  | 1, 7, 2, _, _, _ => exact ⟨e (.n 1193), outCell_sound _ σ K 62 1193 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1193) = qv inp (.HB 1 7) from g958,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 7 2 (by decide) (by decide)]; rfl⟩
  | 1, 7, 3, _, _, _ => exact ⟨e (.n 1192), outCell_sound _ σ K 63 1192 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1192) = qv inp (.HB 1 7) from g959,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 7 3 (by decide) (by decide)]; rfl⟩
  | 2, 0, 0, _, _, _ => exact ⟨e (.n 1191), outCell_sound _ σ K 64 1191 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1191) = qv inp (.HB 2 0) from g960,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 0 0 (by decide) (by decide)]; rfl⟩
  | 2, 0, 1, _, _, _ => exact ⟨e (.n 1190), outCell_sound _ σ K 65 1190 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1190) = qv inp (.HB 2 0) from g961,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 0 1 (by decide) (by decide)]; rfl⟩
  | 2, 0, 2, _, _, _ => exact ⟨e (.n 1189), outCell_sound _ σ K 66 1189 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1189) = qv inp (.HB 2 0) from g962,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 0 2 (by decide) (by decide)]; rfl⟩
  | 2, 0, 3, _, _, _ => exact ⟨e (.n 1188), outCell_sound _ σ K 67 1188 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1188) = qv inp (.HB 2 0) from g963,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 0 3 (by decide) (by decide)]; rfl⟩
  | 2, 1, 0, _, _, _ => exact ⟨e (.n 1187), outCell_sound _ σ K 68 1187 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1187) = qv inp (.HB 2 1) from g964,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 1 0 (by decide) (by decide)]; rfl⟩
  | 2, 1, 1, _, _, _ => exact ⟨e (.n 1186), outCell_sound _ σ K 69 1186 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1186) = qv inp (.HB 2 1) from g965,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 1 1 (by decide) (by decide)]; rfl⟩
  | 2, 1, 2, _, _, _ => exact ⟨e (.n 1185), outCell_sound _ σ K 70 1185 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1185) = qv inp (.HB 2 1) from g966,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 1 2 (by decide) (by decide)]; rfl⟩
  | 2, 1, 3, _, _, _ => exact ⟨e (.n 1184), outCell_sound _ σ K 71 1184 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1184) = qv inp (.HB 2 1) from g967,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 1 3 (by decide) (by decide)]; rfl⟩
  | 2, 2, 0, _, _, _ => exact ⟨e (.n 1183), outCell_sound _ σ K 72 1183 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1183) = qv inp (.HB 2 2) from g968,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 2 0 (by decide) (by decide)]; rfl⟩
  | 2, 2, 1, _, _, _ => exact ⟨e (.n 1182), outCell_sound _ σ K 73 1182 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1182) = qv inp (.HB 2 2) from g969,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 2 1 (by decide) (by decide)]; rfl⟩
  | 2, 2, 2, _, _, _ => exact ⟨e (.n 1181), outCell_sound _ σ K 74 1181 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1181) = qv inp (.HB 2 2) from g970,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 2 2 (by decide) (by decide)]; rfl⟩
  | 2, 2, 3, _, _, _ => exact ⟨e (.n 1180), outCell_sound _ σ K 75 1180 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1180) = qv inp (.HB 2 2) from g971,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 2 3 (by decide) (by decide)]; rfl⟩
  | 2, 3, 0, _, _, _ => exact ⟨e (.n 1179), outCell_sound _ σ K 76 1179 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1179) = qv inp (.HB 2 3) from g972,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 3 0 (by decide) (by decide)]; rfl⟩
  | 2, 3, 1, _, _, _ => exact ⟨e (.n 1178), outCell_sound _ σ K 77 1178 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1178) = qv inp (.HB 2 3) from g973,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 3 1 (by decide) (by decide)]; rfl⟩
  | 2, 3, 2, _, _, _ => exact ⟨e (.n 1177), outCell_sound _ σ K 78 1177 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1177) = qv inp (.HB 2 3) from g974,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 3 2 (by decide) (by decide)]; rfl⟩
  | 2, 3, 3, _, _, _ => exact ⟨e (.n 1176), outCell_sound _ σ K 79 1176 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1176) = qv inp (.HB 2 3) from g975,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 3 3 (by decide) (by decide)]; rfl⟩
  | 2, 4, 0, _, _, _ => exact ⟨e (.n 1175), outCell_sound _ σ K 80 1175 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1175) = qv inp (.HB 2 4) from g976,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 4 0 (by decide) (by decide)]; rfl⟩
  | 2, 4, 1, _, _, _ => exact ⟨e (.n 1174), outCell_sound _ σ K 81 1174 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1174) = qv inp (.HB 2 4) from g977,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 4 1 (by decide) (by decide)]; rfl⟩
  | 2, 4, 2, _, _, _ => exact ⟨e (.n 1173), outCell_sound _ σ K 82 1173 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1173) = qv inp (.HB 2 4) from g978,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 4 2 (by decide) (by decide)]; rfl⟩
  | 2, 4, 3, _, _, _ => exact ⟨e (.n 1172), outCell_sound _ σ K 83 1172 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1172) = qv inp (.HB 2 4) from g979,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 4 3 (by decide) (by decide)]; rfl⟩
  | 2, 5, 0, _, _, _ => exact ⟨e (.n 1171), outCell_sound _ σ K 84 1171 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1171) = qv inp (.HB 2 5) from g980,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 5 0 (by decide) (by decide)]; rfl⟩
  | 2, 5, 1, _, _, _ => exact ⟨e (.n 1170), outCell_sound _ σ K 85 1170 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1170) = qv inp (.HB 2 5) from g981,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 5 1 (by decide) (by decide)]; rfl⟩
  | 2, 5, 2, _, _, _ => exact ⟨e (.n 1169), outCell_sound _ σ K 86 1169 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1169) = qv inp (.HB 2 5) from g982,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 5 2 (by decide) (by decide)]; rfl⟩
  | 2, 5, 3, _, _, _ => exact ⟨e (.n 1168), outCell_sound _ σ K 87 1168 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1168) = qv inp (.HB 2 5) from g983,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 5 3 (by decide) (by decide)]; rfl⟩
  | 2, 6, 0, _, _, _ => exact ⟨e (.n 1167), outCell_sound _ σ K 88 1167 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1167) = qv inp (.HB 2 6) from g984,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 6 0 (by decide) (by decide)]; rfl⟩
  | 2, 6, 1, _, _, _ => exact ⟨e (.n 1166), outCell_sound _ σ K 89 1166 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1166) = qv inp (.HB 2 6) from g985,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 6 1 (by decide) (by decide)]; rfl⟩
  | 2, 6, 2, _, _, _ => exact ⟨e (.n 1165), outCell_sound _ σ K 90 1165 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1165) = qv inp (.HB 2 6) from g986,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 6 2 (by decide) (by decide)]; rfl⟩
  | 2, 6, 3, _, _, _ => exact ⟨e (.n 1164), outCell_sound _ σ K 91 1164 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1164) = qv inp (.HB 2 6) from g987,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 6 3 (by decide) (by decide)]; rfl⟩
  | 2, 7, 0, _, _, _ => exact ⟨e (.n 1163), outCell_sound _ σ K 92 1163 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1163) = qv inp (.HB 2 7) from g988,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 7 0 (by decide) (by decide)]; rfl⟩
  | 2, 7, 1, _, _, _ => exact ⟨e (.n 1162), outCell_sound _ σ K 93 1162 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1162) = qv inp (.HB 2 7) from g989,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 7 1 (by decide) (by decide)]; rfl⟩
  | 2, 7, 2, _, _, _ => exact ⟨e (.n 1161), outCell_sound _ σ K 94 1161 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1161) = qv inp (.HB 2 7) from g990,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 7 2 (by decide) (by decide)]; rfl⟩
  | 2, 7, 3, _, _, _ => exact ⟨e (.n 1160), outCell_sound _ σ K 95 1160 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1160) = qv inp (.HB 2 7) from g991,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 7 3 (by decide) (by decide)]; rfl⟩
  | 3, 0, 0, _, _, _ => exact ⟨e (.n 1159), outCell_sound _ σ K 96 1159 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1159) = qv inp (.HB 3 0) from g992,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 0 0 (by decide) (by decide)]; rfl⟩
  | 3, 0, 1, _, _, _ => exact ⟨e (.n 1158), outCell_sound _ σ K 97 1158 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1158) = qv inp (.HB 3 0) from g993,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 0 1 (by decide) (by decide)]; rfl⟩
  | 3, 0, 2, _, _, _ => exact ⟨e (.n 1157), outCell_sound _ σ K 98 1157 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1157) = qv inp (.HB 3 0) from g994,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 0 2 (by decide) (by decide)]; rfl⟩
  | 3, 0, 3, _, _, _ => exact ⟨e (.n 1156), outCell_sound _ σ K 99 1156 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1156) = qv inp (.HB 3 0) from g995,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 0 3 (by decide) (by decide)]; rfl⟩
  | 3, 1, 0, _, _, _ => exact ⟨e (.n 1155), outCell_sound _ σ K 100 1155 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1155) = qv inp (.HB 3 1) from g996,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 1 0 (by decide) (by decide)]; rfl⟩
  | 3, 1, 1, _, _, _ => exact ⟨e (.n 1154), outCell_sound _ σ K 101 1154 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1154) = qv inp (.HB 3 1) from g997,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 1 1 (by decide) (by decide)]; rfl⟩
  | 3, 1, 2, _, _, _ => exact ⟨e (.n 1153), outCell_sound _ σ K 102 1153 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1153) = qv inp (.HB 3 1) from g998,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 1 2 (by decide) (by decide)]; rfl⟩
  | 3, 1, 3, _, _, _ => exact ⟨e (.n 1152), outCell_sound _ σ K 103 1152 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1152) = qv inp (.HB 3 1) from g999,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 1 3 (by decide) (by decide)]; rfl⟩
  | 3, 2, 0, _, _, _ => exact ⟨e (.n 1151), outCell_sound _ σ K 104 1151 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1151) = qv inp (.HB 3 2) from g1000,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 2 0 (by decide) (by decide)]; rfl⟩
  | 3, 2, 1, _, _, _ => exact ⟨e (.n 1150), outCell_sound _ σ K 105 1150 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1150) = qv inp (.HB 3 2) from g1001,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 2 1 (by decide) (by decide)]; rfl⟩
  | 3, 2, 2, _, _, _ => exact ⟨e (.n 1149), outCell_sound _ σ K 106 1149 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1149) = qv inp (.HB 3 2) from g1002,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 2 2 (by decide) (by decide)]; rfl⟩
  | 3, 2, 3, _, _, _ => exact ⟨e (.n 1148), outCell_sound _ σ K 107 1148 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1148) = qv inp (.HB 3 2) from g1003,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 2 3 (by decide) (by decide)]; rfl⟩
  | 3, 3, 0, _, _, _ => exact ⟨e (.n 1147), outCell_sound _ σ K 108 1147 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1147) = qv inp (.HB 3 3) from g1004,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 3 0 (by decide) (by decide)]; rfl⟩
  | 3, 3, 1, _, _, _ => exact ⟨e (.n 1146), outCell_sound _ σ K 109 1146 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1146) = qv inp (.HB 3 3) from g1005,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 3 1 (by decide) (by decide)]; rfl⟩
  | 3, 3, 2, _, _, _ => exact ⟨e (.n 1145), outCell_sound _ σ K 110 1145 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1145) = qv inp (.HB 3 3) from g1006,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 3 2 (by decide) (by decide)]; rfl⟩
  | 3, 3, 3, _, _, _ => exact ⟨e (.n 1144), outCell_sound _ σ K 111 1144 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1144) = qv inp (.HB 3 3) from g1007,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 3 3 (by decide) (by decide)]; rfl⟩
  | 3, 4, 0, _, _, _ => exact ⟨e (.n 1143), outCell_sound _ σ K 112 1143 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1143) = qv inp (.HB 3 4) from g1008,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 4 0 (by decide) (by decide)]; rfl⟩
  | 3, 4, 1, _, _, _ => exact ⟨e (.n 1142), outCell_sound _ σ K 113 1142 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1142) = qv inp (.HB 3 4) from g1009,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 4 1 (by decide) (by decide)]; rfl⟩
  | 3, 4, 2, _, _, _ => exact ⟨e (.n 1141), outCell_sound _ σ K 114 1141 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1141) = qv inp (.HB 3 4) from g1010,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 4 2 (by decide) (by decide)]; rfl⟩
  | 3, 4, 3, _, _, _ => exact ⟨e (.n 1140), outCell_sound _ σ K 115 1140 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1140) = qv inp (.HB 3 4) from g1011,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 4 3 (by decide) (by decide)]; rfl⟩
  | 3, 5, 0, _, _, _ => exact ⟨e (.n 1139), outCell_sound _ σ K 116 1139 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1139) = qv inp (.HB 3 5) from g1012,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 5 0 (by decide) (by decide)]; rfl⟩
  | 3, 5, 1, _, _, _ => exact ⟨e (.n 1138), outCell_sound _ σ K 117 1138 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1138) = qv inp (.HB 3 5) from g1013,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 5 1 (by decide) (by decide)]; rfl⟩
  | 3, 5, 2, _, _, _ => exact ⟨e (.n 1137), outCell_sound _ σ K 118 1137 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1137) = qv inp (.HB 3 5) from g1014,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 5 2 (by decide) (by decide)]; rfl⟩
  | 3, 5, 3, _, _, _ => exact ⟨e (.n 1136), outCell_sound _ σ K 119 1136 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1136) = qv inp (.HB 3 5) from g1015,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 5 3 (by decide) (by decide)]; rfl⟩
  | 3, 6, 0, _, _, _ => exact ⟨e (.n 1135), outCell_sound _ σ K 120 1135 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1135) = qv inp (.HB 3 6) from g1016,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 6 0 (by decide) (by decide)]; rfl⟩
  | 3, 6, 1, _, _, _ => exact ⟨e (.n 1134), outCell_sound _ σ K 121 1134 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1134) = qv inp (.HB 3 6) from g1017,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 6 1 (by decide) (by decide)]; rfl⟩
  | 3, 6, 2, _, _, _ => exact ⟨e (.n 1133), outCell_sound _ σ K 122 1133 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1133) = qv inp (.HB 3 6) from g1018,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 6 2 (by decide) (by decide)]; rfl⟩
  | 3, 6, 3, _, _, _ => exact ⟨e (.n 1132), outCell_sound _ σ K 123 1132 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1132) = qv inp (.HB 3 6) from g1019,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 6 3 (by decide) (by decide)]; rfl⟩
  | 3, 7, 0, _, _, _ => exact ⟨e (.n 1131), outCell_sound _ σ K 124 1131 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1131) = qv inp (.HB 3 7) from g1020,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 7 0 (by decide) (by decide)]; rfl⟩
  | 3, 7, 1, _, _, _ => exact ⟨e (.n 1130), outCell_sound _ σ K 125 1130 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1130) = qv inp (.HB 3 7) from g1021,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 7 1 (by decide) (by decide)]; rfl⟩
  | 3, 7, 2, _, _, _ => exact ⟨e (.n 1129), outCell_sound _ σ K 126 1129 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1129) = qv inp (.HB 3 7) from g1022,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 7 2 (by decide) (by decide)]; rfl⟩
  | 3, 7, 3, _, _, _ => exact ⟨e (.n 1128), outCell_sound _ σ K 127 1128 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1128) = qv inp (.HB 3 7) from g1023,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 7 3 (by decide) (by decide)]; rfl⟩
  | 4, 0, 0, _, _, _ => exact ⟨e (.n 1127), outCell_sound _ σ K 128 1127 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1127) = qv inp (.HB 4 0) from g1024,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 0 0 (by decide) (by decide)]; rfl⟩
  | 4, 0, 1, _, _, _ => exact ⟨e (.n 1126), outCell_sound _ σ K 129 1126 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1126) = qv inp (.HB 4 0) from g1025,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 0 1 (by decide) (by decide)]; rfl⟩
  | 4, 0, 2, _, _, _ => exact ⟨e (.n 1125), outCell_sound _ σ K 130 1125 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1125) = qv inp (.HB 4 0) from g1026,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 0 2 (by decide) (by decide)]; rfl⟩
  | 4, 0, 3, _, _, _ => exact ⟨e (.n 1124), outCell_sound _ σ K 131 1124 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1124) = qv inp (.HB 4 0) from g1027,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 0 3 (by decide) (by decide)]; rfl⟩
  | 4, 1, 0, _, _, _ => exact ⟨e (.n 1123), outCell_sound _ σ K 132 1123 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1123) = qv inp (.HB 4 1) from g1028,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 1 0 (by decide) (by decide)]; rfl⟩
  | 4, 1, 1, _, _, _ => exact ⟨e (.n 1122), outCell_sound _ σ K 133 1122 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1122) = qv inp (.HB 4 1) from g1029,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 1 1 (by decide) (by decide)]; rfl⟩
  | 4, 1, 2, _, _, _ => exact ⟨e (.n 1121), outCell_sound _ σ K 134 1121 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1121) = qv inp (.HB 4 1) from g1030,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 1 2 (by decide) (by decide)]; rfl⟩
  | 4, 1, 3, _, _, _ => exact ⟨e (.n 1120), outCell_sound _ σ K 135 1120 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1120) = qv inp (.HB 4 1) from g1031,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 1 3 (by decide) (by decide)]; rfl⟩
  | 4, 2, 0, _, _, _ => exact ⟨e (.n 1119), outCell_sound _ σ K 136 1119 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1119) = qv inp (.HB 4 2) from g1032,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 2 0 (by decide) (by decide)]; rfl⟩
  | 4, 2, 1, _, _, _ => exact ⟨e (.n 1118), outCell_sound _ σ K 137 1118 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1118) = qv inp (.HB 4 2) from g1033,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 2 1 (by decide) (by decide)]; rfl⟩
  | 4, 2, 2, _, _, _ => exact ⟨e (.n 1117), outCell_sound _ σ K 138 1117 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1117) = qv inp (.HB 4 2) from g1034,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 2 2 (by decide) (by decide)]; rfl⟩
  | 4, 2, 3, _, _, _ => exact ⟨e (.n 1116), outCell_sound _ σ K 139 1116 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1116) = qv inp (.HB 4 2) from g1035,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 2 3 (by decide) (by decide)]; rfl⟩
  | 4, 3, 0, _, _, _ => exact ⟨e (.n 1115), outCell_sound _ σ K 140 1115 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1115) = qv inp (.HB 4 3) from g1036,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 3 0 (by decide) (by decide)]; rfl⟩
  | 4, 3, 1, _, _, _ => exact ⟨e (.n 1114), outCell_sound _ σ K 141 1114 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1114) = qv inp (.HB 4 3) from g1037,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 3 1 (by decide) (by decide)]; rfl⟩
  | 4, 3, 2, _, _, _ => exact ⟨e (.n 1113), outCell_sound _ σ K 142 1113 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1113) = qv inp (.HB 4 3) from g1038,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 3 2 (by decide) (by decide)]; rfl⟩
  | 4, 3, 3, _, _, _ => exact ⟨e (.n 1112), outCell_sound _ σ K 143 1112 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1112) = qv inp (.HB 4 3) from g1039,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 3 3 (by decide) (by decide)]; rfl⟩
  | 4, 4, 0, _, _, _ => exact ⟨e (.n 1111), outCell_sound _ σ K 144 1111 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1111) = qv inp (.HB 4 4) from g1040,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 4 0 (by decide) (by decide)]; rfl⟩
  | 4, 4, 1, _, _, _ => exact ⟨e (.n 1110), outCell_sound _ σ K 145 1110 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1110) = qv inp (.HB 4 4) from g1041,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 4 1 (by decide) (by decide)]; rfl⟩
  | 4, 4, 2, _, _, _ => exact ⟨e (.n 1109), outCell_sound _ σ K 146 1109 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1109) = qv inp (.HB 4 4) from g1042,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 4 2 (by decide) (by decide)]; rfl⟩
  | 4, 4, 3, _, _, _ => exact ⟨e (.n 1108), outCell_sound _ σ K 147 1108 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1108) = qv inp (.HB 4 4) from g1043,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 4 3 (by decide) (by decide)]; rfl⟩
  | 4, 5, 0, _, _, _ => exact ⟨e (.n 1107), outCell_sound _ σ K 148 1107 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1107) = qv inp (.HB 4 5) from g1044,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 5 0 (by decide) (by decide)]; rfl⟩
  | 4, 5, 1, _, _, _ => exact ⟨e (.n 1106), outCell_sound _ σ K 149 1106 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1106) = qv inp (.HB 4 5) from g1045,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 5 1 (by decide) (by decide)]; rfl⟩
  | 4, 5, 2, _, _, _ => exact ⟨e (.n 1105), outCell_sound _ σ K 150 1105 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1105) = qv inp (.HB 4 5) from g1046,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 5 2 (by decide) (by decide)]; rfl⟩
  | 4, 5, 3, _, _, _ => exact ⟨e (.n 1104), outCell_sound _ σ K 151 1104 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1104) = qv inp (.HB 4 5) from g1047,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 5 3 (by decide) (by decide)]; rfl⟩
  | 4, 6, 0, _, _, _ => exact ⟨e (.n 1103), outCell_sound _ σ K 152 1103 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1103) = qv inp (.HB 4 6) from g1048,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 6 0 (by decide) (by decide)]; rfl⟩
  | 4, 6, 1, _, _, _ => exact ⟨e (.n 1102), outCell_sound _ σ K 153 1102 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1102) = qv inp (.HB 4 6) from g1049,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 6 1 (by decide) (by decide)]; rfl⟩
  | 4, 6, 2, _, _, _ => exact ⟨e (.n 1101), outCell_sound _ σ K 154 1101 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1101) = qv inp (.HB 4 6) from g1050,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 6 2 (by decide) (by decide)]; rfl⟩
  | 4, 6, 3, _, _, _ => exact ⟨e (.n 1100), outCell_sound _ σ K 155 1100 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1100) = qv inp (.HB 4 6) from g1051,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 6 3 (by decide) (by decide)]; rfl⟩
  | 4, 7, 0, _, _, _ => exact ⟨e (.n 1099), outCell_sound _ σ K 156 1099 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1099) = qv inp (.HB 4 7) from g1052,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 7 0 (by decide) (by decide)]; rfl⟩
  | 4, 7, 1, _, _, _ => exact ⟨e (.n 1098), outCell_sound _ σ K 157 1098 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1098) = qv inp (.HB 4 7) from g1053,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 7 1 (by decide) (by decide)]; rfl⟩
  | 4, 7, 2, _, _, _ => exact ⟨e (.n 1097), outCell_sound _ σ K 158 1097 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1097) = qv inp (.HB 4 7) from g1054,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 7 2 (by decide) (by decide)]; rfl⟩
  | 4, 7, 3, _, _, _ => exact ⟨e (.n 1096), outCell_sound _ σ K 159 1096 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1096) = qv inp (.HB 4 7) from g1055,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 7 3 (by decide) (by decide)]; rfl⟩
  | 5, 0, 0, _, _, _ => exact ⟨e (.n 1095), outCell_sound _ σ K 160 1095 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1095) = qv inp (.HB 5 0) from g1056,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 0 0 (by decide) (by decide)]; rfl⟩
  | 5, 0, 1, _, _, _ => exact ⟨e (.n 1094), outCell_sound _ σ K 161 1094 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1094) = qv inp (.HB 5 0) from g1057,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 0 1 (by decide) (by decide)]; rfl⟩
  | 5, 0, 2, _, _, _ => exact ⟨e (.n 1093), outCell_sound _ σ K 162 1093 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1093) = qv inp (.HB 5 0) from g1058,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 0 2 (by decide) (by decide)]; rfl⟩
  | 5, 0, 3, _, _, _ => exact ⟨e (.n 1092), outCell_sound _ σ K 163 1092 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1092) = qv inp (.HB 5 0) from g1059,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 0 3 (by decide) (by decide)]; rfl⟩
  | 5, 1, 0, _, _, _ => exact ⟨e (.n 1091), outCell_sound _ σ K 164 1091 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1091) = qv inp (.HB 5 1) from g1060,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 1 0 (by decide) (by decide)]; rfl⟩
  | 5, 1, 1, _, _, _ => exact ⟨e (.n 1090), outCell_sound _ σ K 165 1090 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1090) = qv inp (.HB 5 1) from g1061,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 1 1 (by decide) (by decide)]; rfl⟩
  | 5, 1, 2, _, _, _ => exact ⟨e (.n 1089), outCell_sound _ σ K 166 1089 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1089) = qv inp (.HB 5 1) from g1062,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 1 2 (by decide) (by decide)]; rfl⟩
  | 5, 1, 3, _, _, _ => exact ⟨e (.n 1088), outCell_sound _ σ K 167 1088 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1088) = qv inp (.HB 5 1) from g1063,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 1 3 (by decide) (by decide)]; rfl⟩
  | 5, 2, 0, _, _, _ => exact ⟨e (.n 1087), outCell_sound _ σ K 168 1087 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1087) = qv inp (.HB 5 2) from g1064,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 2 0 (by decide) (by decide)]; rfl⟩
  | 5, 2, 1, _, _, _ => exact ⟨e (.n 1086), outCell_sound _ σ K 169 1086 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1086) = qv inp (.HB 5 2) from g1065,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 2 1 (by decide) (by decide)]; rfl⟩
  | 5, 2, 2, _, _, _ => exact ⟨e (.n 1085), outCell_sound _ σ K 170 1085 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1085) = qv inp (.HB 5 2) from g1066,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 2 2 (by decide) (by decide)]; rfl⟩
  | 5, 2, 3, _, _, _ => exact ⟨e (.n 1084), outCell_sound _ σ K 171 1084 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1084) = qv inp (.HB 5 2) from g1067,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 2 3 (by decide) (by decide)]; rfl⟩
  | 5, 3, 0, _, _, _ => exact ⟨e (.n 1083), outCell_sound _ σ K 172 1083 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1083) = qv inp (.HB 5 3) from g1068,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 3 0 (by decide) (by decide)]; rfl⟩
  | 5, 3, 1, _, _, _ => exact ⟨e (.n 1082), outCell_sound _ σ K 173 1082 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1082) = qv inp (.HB 5 3) from g1069,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 3 1 (by decide) (by decide)]; rfl⟩
  | 5, 3, 2, _, _, _ => exact ⟨e (.n 1081), outCell_sound _ σ K 174 1081 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1081) = qv inp (.HB 5 3) from g1070,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 3 2 (by decide) (by decide)]; rfl⟩
  | 5, 3, 3, _, _, _ => exact ⟨e (.n 1080), outCell_sound _ σ K 175 1080 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1080) = qv inp (.HB 5 3) from g1071,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 3 3 (by decide) (by decide)]; rfl⟩
  | 5, 4, 0, _, _, _ => exact ⟨e (.n 1079), outCell_sound _ σ K 176 1079 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1079) = qv inp (.HB 5 4) from g1072,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 4 0 (by decide) (by decide)]; rfl⟩
  | 5, 4, 1, _, _, _ => exact ⟨e (.n 1078), outCell_sound _ σ K 177 1078 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1078) = qv inp (.HB 5 4) from g1073,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 4 1 (by decide) (by decide)]; rfl⟩
  | 5, 4, 2, _, _, _ => exact ⟨e (.n 1077), outCell_sound _ σ K 178 1077 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1077) = qv inp (.HB 5 4) from g1074,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 4 2 (by decide) (by decide)]; rfl⟩
  | 5, 4, 3, _, _, _ => exact ⟨e (.n 1076), outCell_sound _ σ K 179 1076 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1076) = qv inp (.HB 5 4) from g1075,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 4 3 (by decide) (by decide)]; rfl⟩
  | 5, 5, 0, _, _, _ => exact ⟨e (.n 1075), outCell_sound _ σ K 180 1075 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1075) = qv inp (.HB 5 5) from g1076,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 5 0 (by decide) (by decide)]; rfl⟩
  | 5, 5, 1, _, _, _ => exact ⟨e (.n 1074), outCell_sound _ σ K 181 1074 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1074) = qv inp (.HB 5 5) from g1077,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 5 1 (by decide) (by decide)]; rfl⟩
  | 5, 5, 2, _, _, _ => exact ⟨e (.n 1073), outCell_sound _ σ K 182 1073 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1073) = qv inp (.HB 5 5) from g1078,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 5 2 (by decide) (by decide)]; rfl⟩
  | 5, 5, 3, _, _, _ => exact ⟨e (.n 1072), outCell_sound _ σ K 183 1072 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1072) = qv inp (.HB 5 5) from g1079,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 5 3 (by decide) (by decide)]; rfl⟩
  | 5, 6, 0, _, _, _ => exact ⟨e (.n 1071), outCell_sound _ σ K 184 1071 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1071) = qv inp (.HB 5 6) from g1080,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 6 0 (by decide) (by decide)]; rfl⟩
  | 5, 6, 1, _, _, _ => exact ⟨e (.n 1070), outCell_sound _ σ K 185 1070 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1070) = qv inp (.HB 5 6) from g1081,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 6 1 (by decide) (by decide)]; rfl⟩
  | 5, 6, 2, _, _, _ => exact ⟨e (.n 1069), outCell_sound _ σ K 186 1069 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1069) = qv inp (.HB 5 6) from g1082,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 6 2 (by decide) (by decide)]; rfl⟩
  | 5, 6, 3, _, _, _ => exact ⟨e (.n 1068), outCell_sound _ σ K 187 1068 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1068) = qv inp (.HB 5 6) from g1083,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 6 3 (by decide) (by decide)]; rfl⟩
  | 5, 7, 0, _, _, _ => exact ⟨e (.n 1067), outCell_sound _ σ K 188 1067 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1067) = qv inp (.HB 5 7) from g1084,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 7 0 (by decide) (by decide)]; rfl⟩
  | 5, 7, 1, _, _, _ => exact ⟨e (.n 1066), outCell_sound _ σ K 189 1066 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1066) = qv inp (.HB 5 7) from g1085,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 7 1 (by decide) (by decide)]; rfl⟩
  | 5, 7, 2, _, _, _ => exact ⟨e (.n 1065), outCell_sound _ σ K 190 1065 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1065) = qv inp (.HB 5 7) from g1086,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 7 2 (by decide) (by decide)]; rfl⟩
  | 5, 7, 3, _, _, _ => exact ⟨e (.n 1064), outCell_sound _ σ K 191 1064 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1064) = qv inp (.HB 5 7) from g1087,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 7 3 (by decide) (by decide)]; rfl⟩
  | 6, 0, 0, _, _, _ => exact ⟨e (.n 1063), outCell_sound _ σ K 192 1063 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1063) = qv inp (.HB 6 0) from g1088,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 0 0 (by decide) (by decide)]; rfl⟩
  | 6, 0, 1, _, _, _ => exact ⟨e (.n 1062), outCell_sound _ σ K 193 1062 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1062) = qv inp (.HB 6 0) from g1089,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 0 1 (by decide) (by decide)]; rfl⟩
  | 6, 0, 2, _, _, _ => exact ⟨e (.n 1061), outCell_sound _ σ K 194 1061 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1061) = qv inp (.HB 6 0) from g1090,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 0 2 (by decide) (by decide)]; rfl⟩
  | 6, 0, 3, _, _, _ => exact ⟨e (.n 1060), outCell_sound _ σ K 195 1060 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1060) = qv inp (.HB 6 0) from g1091,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 0 3 (by decide) (by decide)]; rfl⟩
  | 6, 1, 0, _, _, _ => exact ⟨e (.n 1059), outCell_sound _ σ K 196 1059 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1059) = qv inp (.HB 6 1) from g1092,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 1 0 (by decide) (by decide)]; rfl⟩
  | 6, 1, 1, _, _, _ => exact ⟨e (.n 1058), outCell_sound _ σ K 197 1058 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1058) = qv inp (.HB 6 1) from g1093,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 1 1 (by decide) (by decide)]; rfl⟩
  | 6, 1, 2, _, _, _ => exact ⟨e (.n 1057), outCell_sound _ σ K 198 1057 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1057) = qv inp (.HB 6 1) from g1094,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 1 2 (by decide) (by decide)]; rfl⟩
  | 6, 1, 3, _, _, _ => exact ⟨e (.n 1056), outCell_sound _ σ K 199 1056 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1056) = qv inp (.HB 6 1) from g1095,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 1 3 (by decide) (by decide)]; rfl⟩
  | 6, 2, 0, _, _, _ => exact ⟨e (.n 1055), outCell_sound _ σ K 200 1055 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1055) = qv inp (.HB 6 2) from g1096,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 2 0 (by decide) (by decide)]; rfl⟩
  | 6, 2, 1, _, _, _ => exact ⟨e (.n 1054), outCell_sound _ σ K 201 1054 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1054) = qv inp (.HB 6 2) from g1097,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 2 1 (by decide) (by decide)]; rfl⟩
  | 6, 2, 2, _, _, _ => exact ⟨e (.n 1053), outCell_sound _ σ K 202 1053 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1053) = qv inp (.HB 6 2) from g1098,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 2 2 (by decide) (by decide)]; rfl⟩
  | 6, 2, 3, _, _, _ => exact ⟨e (.n 1052), outCell_sound _ σ K 203 1052 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1052) = qv inp (.HB 6 2) from g1099,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 2 3 (by decide) (by decide)]; rfl⟩
  | 6, 3, 0, _, _, _ => exact ⟨e (.n 1051), outCell_sound _ σ K 204 1051 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1051) = qv inp (.HB 6 3) from g1100,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 3 0 (by decide) (by decide)]; rfl⟩
  | 6, 3, 1, _, _, _ => exact ⟨e (.n 1050), outCell_sound _ σ K 205 1050 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1050) = qv inp (.HB 6 3) from g1101,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 3 1 (by decide) (by decide)]; rfl⟩
  | 6, 3, 2, _, _, _ => exact ⟨e (.n 1049), outCell_sound _ σ K 206 1049 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1049) = qv inp (.HB 6 3) from g1102,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 3 2 (by decide) (by decide)]; rfl⟩
  | 6, 3, 3, _, _, _ => exact ⟨e (.n 1048), outCell_sound _ σ K 207 1048 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1048) = qv inp (.HB 6 3) from g1103,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 3 3 (by decide) (by decide)]; rfl⟩
  | 6, 4, 0, _, _, _ => exact ⟨e (.n 1047), outCell_sound _ σ K 208 1047 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1047) = qv inp (.HB 6 4) from g1104,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 4 0 (by decide) (by decide)]; rfl⟩
  | 6, 4, 1, _, _, _ => exact ⟨e (.n 1046), outCell_sound _ σ K 209 1046 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1046) = qv inp (.HB 6 4) from g1105,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 4 1 (by decide) (by decide)]; rfl⟩
  | 6, 4, 2, _, _, _ => exact ⟨e (.n 1045), outCell_sound _ σ K 210 1045 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1045) = qv inp (.HB 6 4) from g1106,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 4 2 (by decide) (by decide)]; rfl⟩
  | 6, 4, 3, _, _, _ => exact ⟨e (.n 1044), outCell_sound _ σ K 211 1044 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1044) = qv inp (.HB 6 4) from g1107,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 4 3 (by decide) (by decide)]; rfl⟩
  | 6, 5, 0, _, _, _ => exact ⟨e (.n 1043), outCell_sound _ σ K 212 1043 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1043) = qv inp (.HB 6 5) from g1108,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 5 0 (by decide) (by decide)]; rfl⟩
  | 6, 5, 1, _, _, _ => exact ⟨e (.n 1042), outCell_sound _ σ K 213 1042 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1042) = qv inp (.HB 6 5) from g1109,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 5 1 (by decide) (by decide)]; rfl⟩
  | 6, 5, 2, _, _, _ => exact ⟨e (.n 1041), outCell_sound _ σ K 214 1041 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1041) = qv inp (.HB 6 5) from g1110,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 5 2 (by decide) (by decide)]; rfl⟩
  | 6, 5, 3, _, _, _ => exact ⟨e (.n 1040), outCell_sound _ σ K 215 1040 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1040) = qv inp (.HB 6 5) from g1111,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 5 3 (by decide) (by decide)]; rfl⟩
  | 6, 6, 0, _, _, _ => exact ⟨e (.n 1039), outCell_sound _ σ K 216 1039 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1039) = qv inp (.HB 6 6) from g1112,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 6 0 (by decide) (by decide)]; rfl⟩
  | 6, 6, 1, _, _, _ => exact ⟨e (.n 1038), outCell_sound _ σ K 217 1038 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1038) = qv inp (.HB 6 6) from g1113,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 6 1 (by decide) (by decide)]; rfl⟩
  | 6, 6, 2, _, _, _ => exact ⟨e (.n 1037), outCell_sound _ σ K 218 1037 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1037) = qv inp (.HB 6 6) from g1114,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 6 2 (by decide) (by decide)]; rfl⟩
  | 6, 6, 3, _, _, _ => exact ⟨e (.n 1036), outCell_sound _ σ K 219 1036 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1036) = qv inp (.HB 6 6) from g1115,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 6 3 (by decide) (by decide)]; rfl⟩
  | 6, 7, 0, _, _, _ => exact ⟨e (.n 1035), outCell_sound _ σ K 220 1035 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1035) = qv inp (.HB 6 7) from g1116,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 7 0 (by decide) (by decide)]; rfl⟩
  | 6, 7, 1, _, _, _ => exact ⟨e (.n 1034), outCell_sound _ σ K 221 1034 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1034) = qv inp (.HB 6 7) from g1117,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 7 1 (by decide) (by decide)]; rfl⟩
  | 6, 7, 2, _, _, _ => exact ⟨e (.n 1033), outCell_sound _ σ K 222 1033 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1033) = qv inp (.HB 6 7) from g1118,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 7 2 (by decide) (by decide)]; rfl⟩
  | 6, 7, 3, _, _, _ => exact ⟨e (.n 1032), outCell_sound _ σ K 223 1032 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1032) = qv inp (.HB 6 7) from g1119,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 7 3 (by decide) (by decide)]; rfl⟩
  | 7, 0, 0, _, _, _ => exact ⟨e (.n 1031), outCell_sound _ σ K 224 1031 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1031) = qv inp (.HB 7 0) from g1120,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 0 0 (by decide) (by decide)]; rfl⟩
  | 7, 0, 1, _, _, _ => exact ⟨e (.n 1030), outCell_sound _ σ K 225 1030 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1030) = qv inp (.HB 7 0) from g1121,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 0 1 (by decide) (by decide)]; rfl⟩
  | 7, 0, 2, _, _, _ => exact ⟨e (.n 1029), outCell_sound _ σ K 226 1029 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1029) = qv inp (.HB 7 0) from g1122,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 0 2 (by decide) (by decide)]; rfl⟩
  | 7, 0, 3, _, _, _ => exact ⟨e (.n 1028), outCell_sound _ σ K 227 1028 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1028) = qv inp (.HB 7 0) from g1123,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 0 3 (by decide) (by decide)]; rfl⟩
  | 7, 1, 0, _, _, _ => exact ⟨e (.n 1027), outCell_sound _ σ K 228 1027 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1027) = qv inp (.HB 7 1) from g1124,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 1 0 (by decide) (by decide)]; rfl⟩
  | 7, 1, 1, _, _, _ => exact ⟨e (.n 1026), outCell_sound _ σ K 229 1026 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1026) = qv inp (.HB 7 1) from g1125,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 1 1 (by decide) (by decide)]; rfl⟩
  | 7, 1, 2, _, _, _ => exact ⟨e (.n 1025), outCell_sound _ σ K 230 1025 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1025) = qv inp (.HB 7 1) from g1126,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 1 2 (by decide) (by decide)]; rfl⟩
  | 7, 1, 3, _, _, _ => exact ⟨e (.n 1024), outCell_sound _ σ K 231 1024 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1024) = qv inp (.HB 7 1) from g1127,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 1 3 (by decide) (by decide)]; rfl⟩
  | 7, 2, 0, _, _, _ => exact ⟨e (.n 1023), outCell_sound _ σ K 232 1023 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1023) = qv inp (.HB 7 2) from g1128,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 2 0 (by decide) (by decide)]; rfl⟩
  | 7, 2, 1, _, _, _ => exact ⟨e (.n 1022), outCell_sound _ σ K 233 1022 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1022) = qv inp (.HB 7 2) from g1129,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 2 1 (by decide) (by decide)]; rfl⟩
  | 7, 2, 2, _, _, _ => exact ⟨e (.n 1021), outCell_sound _ σ K 234 1021 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1021) = qv inp (.HB 7 2) from g1130,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 2 2 (by decide) (by decide)]; rfl⟩
  | 7, 2, 3, _, _, _ => exact ⟨e (.n 1020), outCell_sound _ σ K 235 1020 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1020) = qv inp (.HB 7 2) from g1131,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 2 3 (by decide) (by decide)]; rfl⟩
  | 7, 3, 0, _, _, _ => exact ⟨e (.n 1019), outCell_sound _ σ K 236 1019 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1019) = qv inp (.HB 7 3) from g1132,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 3 0 (by decide) (by decide)]; rfl⟩
  | 7, 3, 1, _, _, _ => exact ⟨e (.n 1018), outCell_sound _ σ K 237 1018 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1018) = qv inp (.HB 7 3) from g1133,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 3 1 (by decide) (by decide)]; rfl⟩
  | 7, 3, 2, _, _, _ => exact ⟨e (.n 1017), outCell_sound _ σ K 238 1017 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1017) = qv inp (.HB 7 3) from g1134,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 3 2 (by decide) (by decide)]; rfl⟩
  | 7, 3, 3, _, _, _ => exact ⟨e (.n 1016), outCell_sound _ σ K 239 1016 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1016) = qv inp (.HB 7 3) from g1135,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 3 3 (by decide) (by decide)]; rfl⟩
  | 7, 4, 0, _, _, _ => exact ⟨e (.n 1015), outCell_sound _ σ K 240 1015 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1015) = qv inp (.HB 7 4) from g1136,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 4 0 (by decide) (by decide)]; rfl⟩
  | 7, 4, 1, _, _, _ => exact ⟨e (.n 1014), outCell_sound _ σ K 241 1014 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1014) = qv inp (.HB 7 4) from g1137,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 4 1 (by decide) (by decide)]; rfl⟩
  | 7, 4, 2, _, _, _ => exact ⟨e (.n 1013), outCell_sound _ σ K 242 1013 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1013) = qv inp (.HB 7 4) from g1138,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 4 2 (by decide) (by decide)]; rfl⟩
  | 7, 4, 3, _, _, _ => exact ⟨e (.n 1012), outCell_sound _ σ K 243 1012 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1012) = qv inp (.HB 7 4) from g1139,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 4 3 (by decide) (by decide)]; rfl⟩
  | 7, 5, 0, _, _, _ => exact ⟨e (.n 1011), outCell_sound _ σ K 244 1011 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1011) = qv inp (.HB 7 5) from g1140,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 5 0 (by decide) (by decide)]; rfl⟩
  | 7, 5, 1, _, _, _ => exact ⟨e (.n 1010), outCell_sound _ σ K 245 1010 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1010) = qv inp (.HB 7 5) from g1141,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 5 1 (by decide) (by decide)]; rfl⟩
  | 7, 5, 2, _, _, _ => exact ⟨e (.n 1009), outCell_sound _ σ K 246 1009 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1009) = qv inp (.HB 7 5) from g1142,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 5 2 (by decide) (by decide)]; rfl⟩
  | 7, 5, 3, _, _, _ => exact ⟨e (.n 1008), outCell_sound _ σ K 247 1008 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1008) = qv inp (.HB 7 5) from g1143,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 5 3 (by decide) (by decide)]; rfl⟩
  | 7, 6, 0, _, _, _ => exact ⟨e (.n 1007), outCell_sound _ σ K 248 1007 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1007) = qv inp (.HB 7 6) from g1144,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 6 0 (by decide) (by decide)]; rfl⟩
  | 7, 6, 1, _, _, _ => exact ⟨e (.n 1006), outCell_sound _ σ K 249 1006 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1006) = qv inp (.HB 7 6) from g1145,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 6 1 (by decide) (by decide)]; rfl⟩
  | 7, 6, 2, _, _, _ => exact ⟨e (.n 1005), outCell_sound _ σ K 250 1005 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1005) = qv inp (.HB 7 6) from g1146,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 6 2 (by decide) (by decide)]; rfl⟩
  | 7, 6, 3, _, _, _ => exact ⟨e (.n 1004), outCell_sound _ σ K 251 1004 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1004) = qv inp (.HB 7 6) from g1147,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 6 3 (by decide) (by decide)]; rfl⟩
  | 7, 7, 0, _, _, _ => exact ⟨e (.n 1003), outCell_sound _ σ K 252 1003 0 (hc _ _ _ (by decide)),
      by rw [show e (.n 1003) = qv inp (.HB 7 7) from g1148,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 7 0 (by decide) (by decide)]; rfl⟩
  | 7, 7, 1, _, _, _ => exact ⟨e (.n 1002), outCell_sound _ σ K 253 1002 1 (hc _ _ _ (by decide)),
      by rw [show e (.n 1002) = qv inp (.HB 7 7) from g1149,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 7 1 (by decide) (by decide)]; rfl⟩
  | 7, 7, 2, _, _, _ => exact ⟨e (.n 1001), outCell_sound _ σ K 254 1001 2 (hc _ _ _ (by decide)),
      by rw [show e (.n 1001) = qv inp (.HB 7 7) from g1150,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 7 2 (by decide) (by decide)]; rfl⟩
  | 7, 7, 3, _, _, _ => exact ⟨e (.n 1000), outCell_sound _ σ K 255 1000 3 (hc _ _ _ (by decide)),
      by rw [show e (.n 1000) = qv inp (.HB 7 7) from g1151,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 7 3 (by decide) (by decide)]; rfl⟩
  | _ + 8, _, _, hn, _, _ => omega
  | _, _ + 8, _, _, hi, _ => omega
  | _, _, _ + 4, _, _, hb => omega

end Hashtree.Proofs.WinAvx2X8WOut
