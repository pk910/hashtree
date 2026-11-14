import Hashtree.Proofs.Avx512X16WOutInv
import Hashtree.Proofs.Avx512X16WTurn

/-!
# R2c — the loop tails with the pilot's trees, and one turn's output

* `sliceT_turn` / `sliceT_exit`: the two 22-instruction tails of `Avx512X16WEntry`
  (`wcutH K216` to `KT` / `KTE`) re-checked **with** the pilot's tree list `T216` (R2b checked
  them with `[]`), so the pilot's last invariant step `step216` lifts through them
  (`stepT_turn` / `stepT_exit`: `InvC … L216 → InvC … L217`).
* `outShape`: a turn's symbolic write log is exactly output cells at `sym 1 + o`, `o < 512`
  (`KT_outShape` / `KTE_outShape`, `decide`), and its concrete meaning (`outShape_sound`).
* `outOk_KT` / `outOk_KTE`: the 16 digests of a turn from the invariant at `L217`, the pilot's
  `out_final` case table with the W cut and a generic environment.  Generated.
-/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.Avx512X16 Hashtree.Gen.Avx512X16P
open Hashtree.Proofs.Avx512X16WBody (mW wcutH)
open Hashtree.Proofs.Avx512X16WEntry (KT KTE orcNone orcExit)

namespace Hashtree.Proofs.Avx512X16WOut

/-! ## The tails with trees -/

theorem sliceT_turn : sliceCheck prog 4 mW orcNone 22 (wcutH K216) KT T216 = true := by
  decide +kernel

theorem sliceT_exit : sliceCheck prog 4 mW orcExit 22 (wcutH K216) KTE T216 = true := by
  decide +kernel

theorem stepT_turn (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L216) (hm : HMem 1024 inp env) :
    InvC inp (envAbs env (run prog 4 mW orcNone 22 (wcutH K216))) L217 :=
  invC_lift inp env prog 4 m0q mW _ _ 22 K216 K217 (wcutH K216) KT T216 L217
    slice216 sliceT_turn lab_216 (step216 inp env hI hm)

theorem stepT_exit (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L216) (hm : HMem 1024 inp env) :
    InvC inp (envAbs env (run prog 4 mW orcExit 22 (wcutH K216))) L217 :=
  invC_lift inp env prog 4 m0q mW _ _ 22 K216 K217 (wcutH K216) KTE T216 L217
    slice216 sliceT_exit lab_216 (step216 inp env hI hm)

/-! ## The shape of a turn's write log -/

/-- Every logged cell is an output cell at `sym 1 + o` with `o < 512`. -/
def outShape (K : State E Lin) : Bool :=
  K.mem.all fun p => p.1.region == rOut && p.1.off.c == [0, 1] && decide (0 ≤ p.1.off.k) && decide (p.1.off.k < 512)

theorem KT_outShape : outShape KT = true := by decide +kernel
theorem KTE_outShape : outShape KTE = true := by decide +kernel

theorem out_eval (σ : Nat → Int) (k : Int) : (⟨k, [0, 1]⟩ : Lin).eval σ = σ 1 + k := by
  show k + (0 * σ 0 + (1 * σ (0 + 1) + 0)) = σ 1 + k
  rw [show (0 + 1 : Nat) = 1 from rfl]
  omega

theorem outShape_sound (K : State E Lin) (h : outShape K = true) (e : Key → W32) (σ : Nat → Int) :
    ∀ p ∈ (mapState e σ K).mem, p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 512 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [outShape, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩ := h q hq
  obtain ⟨⟨qr, qk, qc⟩, qcell⟩ := q
  simp only at hr hc h0 h1
  subst hr; subst hc
  show rOut = rOut ∧ σ 1 ≤ (⟨qk, [0, 1]⟩ : Lin).eval σ ∧ (⟨qk, [0, 1]⟩ : Lin).eval σ < σ 1 + 512
  rw [out_eval]
  exact ⟨rfl, by omega, by omega⟩


/-- The 512 `(o, id, b)` output cells of `KT`, checked once. -/
def KT_tab : List (Nat × Nat × Nat) := [(0, 1511, 0), (1, 1510, 1), (2, 1509, 2), (3, 1508, 3), (4, 1507, 0), (5, 1506, 1), (6, 1505, 2), (7, 1504, 3), (8, 1503, 0), (9, 1502, 1), (10, 1501, 2), (11, 1500, 3), (12, 1499, 0), (13, 1498, 1), (14, 1497, 2), (15, 1496, 3), (16, 1495, 0), (17, 1494, 1), (18, 1493, 2), (19, 1492, 3), (20, 1491, 0), (21, 1490, 1), (22, 1489, 2), (23, 1488, 3), (24, 1487, 0), (25, 1486, 1), (26, 1485, 2), (27, 1484, 3), (28, 1483, 0), (29, 1482, 1), (30, 1481, 2), (31, 1480, 3), (32, 1479, 0), (33, 1478, 1), (34, 1477, 2), (35, 1476, 3), (36, 1475, 0), (37, 1474, 1), (38, 1473, 2), (39, 1472, 3), (40, 1471, 0), (41, 1470, 1), (42, 1469, 2), (43, 1468, 3), (44, 1467, 0), (45, 1466, 1), (46, 1465, 2), (47, 1464, 3), (48, 1463, 0), (49, 1462, 1), (50, 1461, 2), (51, 1460, 3), (52, 1459, 0), (53, 1458, 1), (54, 1457, 2), (55, 1456, 3), (56, 1455, 0), (57, 1454, 1), (58, 1453, 2), (59, 1452, 3), (60, 1451, 0), (61, 1450, 1), (62, 1449, 2), (63, 1448, 3), (64, 1447, 0), (65, 1446, 1), (66, 1445, 2), (67, 1444, 3), (68, 1443, 0), (69, 1442, 1), (70, 1441, 2), (71, 1440, 3), (72, 1439, 0), (73, 1438, 1), (74, 1437, 2), (75, 1436, 3), (76, 1435, 0), (77, 1434, 1), (78, 1433, 2), (79, 1432, 3), (80, 1431, 0), (81, 1430, 1), (82, 1429, 2), (83, 1428, 3), (84, 1427, 0), (85, 1426, 1), (86, 1425, 2), (87, 1424, 3), (88, 1423, 0), (89, 1422, 1), (90, 1421, 2), (91, 1420, 3), (92, 1419, 0), (93, 1418, 1), (94, 1417, 2), (95, 1416, 3), (96, 1415, 0), (97, 1414, 1), (98, 1413, 2), (99, 1412, 3), (100, 1411, 0), (101, 1410, 1), (102, 1409, 2), (103, 1408, 3), (104, 1407, 0), (105, 1406, 1), (106, 1405, 2), (107, 1404, 3), (108, 1403, 0), (109, 1402, 1), (110, 1401, 2), (111, 1400, 3), (112, 1399, 0), (113, 1398, 1), (114, 1397, 2), (115, 1396, 3), (116, 1395, 0), (117, 1394, 1), (118, 1393, 2), (119, 1392, 3), (120, 1391, 0), (121, 1390, 1), (122, 1389, 2), (123, 1388, 3), (124, 1387, 0), (125, 1386, 1), (126, 1385, 2), (127, 1384, 3), (128, 1383, 0), (129, 1382, 1), (130, 1381, 2), (131, 1380, 3), (132, 1379, 0), (133, 1378, 1), (134, 1377, 2), (135, 1376, 3), (136, 1375, 0), (137, 1374, 1), (138, 1373, 2), (139, 1372, 3), (140, 1371, 0), (141, 1370, 1), (142, 1369, 2), (143, 1368, 3), (144, 1367, 0), (145, 1366, 1), (146, 1365, 2), (147, 1364, 3), (148, 1363, 0), (149, 1362, 1), (150, 1361, 2), (151, 1360, 3), (152, 1359, 0), (153, 1358, 1), (154, 1357, 2), (155, 1356, 3), (156, 1355, 0), (157, 1354, 1), (158, 1353, 2), (159, 1352, 3), (160, 1351, 0), (161, 1350, 1), (162, 1349, 2), (163, 1348, 3), (164, 1347, 0), (165, 1346, 1), (166, 1345, 2), (167, 1344, 3), (168, 1343, 0), (169, 1342, 1), (170, 1341, 2), (171, 1340, 3), (172, 1339, 0), (173, 1338, 1), (174, 1337, 2), (175, 1336, 3), (176, 1335, 0), (177, 1334, 1), (178, 1333, 2), (179, 1332, 3), (180, 1331, 0), (181, 1330, 1), (182, 1329, 2), (183, 1328, 3), (184, 1327, 0), (185, 1326, 1), (186, 1325, 2), (187, 1324, 3), (188, 1323, 0), (189, 1322, 1), (190, 1321, 2), (191, 1320, 3), (192, 1319, 0), (193, 1318, 1), (194, 1317, 2), (195, 1316, 3), (196, 1315, 0), (197, 1314, 1), (198, 1313, 2), (199, 1312, 3), (200, 1311, 0), (201, 1310, 1), (202, 1309, 2), (203, 1308, 3), (204, 1307, 0), (205, 1306, 1), (206, 1305, 2), (207, 1304, 3), (208, 1303, 0), (209, 1302, 1), (210, 1301, 2), (211, 1300, 3), (212, 1299, 0), (213, 1298, 1), (214, 1297, 2), (215, 1296, 3), (216, 1295, 0), (217, 1294, 1), (218, 1293, 2), (219, 1292, 3), (220, 1291, 0), (221, 1290, 1), (222, 1289, 2), (223, 1288, 3), (224, 1287, 0), (225, 1286, 1), (226, 1285, 2), (227, 1284, 3), (228, 1283, 0), (229, 1282, 1), (230, 1281, 2), (231, 1280, 3), (232, 1279, 0), (233, 1278, 1), (234, 1277, 2), (235, 1276, 3), (236, 1275, 0), (237, 1274, 1), (238, 1273, 2), (239, 1272, 3), (240, 1271, 0), (241, 1270, 1), (242, 1269, 2), (243, 1268, 3), (244, 1267, 0), (245, 1266, 1), (246, 1265, 2), (247, 1264, 3), (248, 1263, 0), (249, 1262, 1), (250, 1261, 2), (251, 1260, 3), (252, 1259, 0), (253, 1258, 1), (254, 1257, 2), (255, 1256, 3), (256, 1255, 0), (257, 1254, 1), (258, 1253, 2), (259, 1252, 3), (260, 1251, 0), (261, 1250, 1), (262, 1249, 2), (263, 1248, 3), (264, 1247, 0), (265, 1246, 1), (266, 1245, 2), (267, 1244, 3), (268, 1243, 0), (269, 1242, 1), (270, 1241, 2), (271, 1240, 3), (272, 1239, 0), (273, 1238, 1), (274, 1237, 2), (275, 1236, 3), (276, 1235, 0), (277, 1234, 1), (278, 1233, 2), (279, 1232, 3), (280, 1231, 0), (281, 1230, 1), (282, 1229, 2), (283, 1228, 3), (284, 1227, 0), (285, 1226, 1), (286, 1225, 2), (287, 1224, 3), (288, 1223, 0), (289, 1222, 1), (290, 1221, 2), (291, 1220, 3), (292, 1219, 0), (293, 1218, 1), (294, 1217, 2), (295, 1216, 3), (296, 1215, 0), (297, 1214, 1), (298, 1213, 2), (299, 1212, 3), (300, 1211, 0), (301, 1210, 1), (302, 1209, 2), (303, 1208, 3), (304, 1207, 0), (305, 1206, 1), (306, 1205, 2), (307, 1204, 3), (308, 1203, 0), (309, 1202, 1), (310, 1201, 2), (311, 1200, 3), (312, 1199, 0), (313, 1198, 1), (314, 1197, 2), (315, 1196, 3), (316, 1195, 0), (317, 1194, 1), (318, 1193, 2), (319, 1192, 3), (320, 1191, 0), (321, 1190, 1), (322, 1189, 2), (323, 1188, 3), (324, 1187, 0), (325, 1186, 1), (326, 1185, 2), (327, 1184, 3), (328, 1183, 0), (329, 1182, 1), (330, 1181, 2), (331, 1180, 3), (332, 1179, 0), (333, 1178, 1), (334, 1177, 2), (335, 1176, 3), (336, 1175, 0), (337, 1174, 1), (338, 1173, 2), (339, 1172, 3), (340, 1171, 0), (341, 1170, 1), (342, 1169, 2), (343, 1168, 3), (344, 1167, 0), (345, 1166, 1), (346, 1165, 2), (347, 1164, 3), (348, 1163, 0), (349, 1162, 1), (350, 1161, 2), (351, 1160, 3), (352, 1159, 0), (353, 1158, 1), (354, 1157, 2), (355, 1156, 3), (356, 1155, 0), (357, 1154, 1), (358, 1153, 2), (359, 1152, 3), (360, 1151, 0), (361, 1150, 1), (362, 1149, 2), (363, 1148, 3), (364, 1147, 0), (365, 1146, 1), (366, 1145, 2), (367, 1144, 3), (368, 1143, 0), (369, 1142, 1), (370, 1141, 2), (371, 1140, 3), (372, 1139, 0), (373, 1138, 1), (374, 1137, 2), (375, 1136, 3), (376, 1135, 0), (377, 1134, 1), (378, 1133, 2), (379, 1132, 3), (380, 1131, 0), (381, 1130, 1), (382, 1129, 2), (383, 1128, 3), (384, 1127, 0), (385, 1126, 1), (386, 1125, 2), (387, 1124, 3), (388, 1123, 0), (389, 1122, 1), (390, 1121, 2), (391, 1120, 3), (392, 1119, 0), (393, 1118, 1), (394, 1117, 2), (395, 1116, 3), (396, 1115, 0), (397, 1114, 1), (398, 1113, 2), (399, 1112, 3), (400, 1111, 0), (401, 1110, 1), (402, 1109, 2), (403, 1108, 3), (404, 1107, 0), (405, 1106, 1), (406, 1105, 2), (407, 1104, 3), (408, 1103, 0), (409, 1102, 1), (410, 1101, 2), (411, 1100, 3), (412, 1099, 0), (413, 1098, 1), (414, 1097, 2), (415, 1096, 3), (416, 1095, 0), (417, 1094, 1), (418, 1093, 2), (419, 1092, 3), (420, 1091, 0), (421, 1090, 1), (422, 1089, 2), (423, 1088, 3), (424, 1087, 0), (425, 1086, 1), (426, 1085, 2), (427, 1084, 3), (428, 1083, 0), (429, 1082, 1), (430, 1081, 2), (431, 1080, 3), (432, 1079, 0), (433, 1078, 1), (434, 1077, 2), (435, 1076, 3), (436, 1075, 0), (437, 1074, 1), (438, 1073, 2), (439, 1072, 3), (440, 1071, 0), (441, 1070, 1), (442, 1069, 2), (443, 1068, 3), (444, 1067, 0), (445, 1066, 1), (446, 1065, 2), (447, 1064, 3), (448, 1063, 0), (449, 1062, 1), (450, 1061, 2), (451, 1060, 3), (452, 1059, 0), (453, 1058, 1), (454, 1057, 2), (455, 1056, 3), (456, 1055, 0), (457, 1054, 1), (458, 1053, 2), (459, 1052, 3), (460, 1051, 0), (461, 1050, 1), (462, 1049, 2), (463, 1048, 3), (464, 1047, 0), (465, 1046, 1), (466, 1045, 2), (467, 1044, 3), (468, 1043, 0), (469, 1042, 1), (470, 1041, 2), (471, 1040, 3), (472, 1039, 0), (473, 1038, 1), (474, 1037, 2), (475, 1036, 3), (476, 1035, 0), (477, 1034, 1), (478, 1033, 2), (479, 1032, 3), (480, 1031, 0), (481, 1030, 1), (482, 1029, 2), (483, 1028, 3), (484, 1027, 0), (485, 1026, 1), (486, 1025, 2), (487, 1024, 3), (488, 1023, 0), (489, 1022, 1), (490, 1021, 2), (491, 1020, 3), (492, 1019, 0), (493, 1018, 1), (494, 1017, 2), (495, 1016, 3), (496, 1015, 0), (497, 1014, 1), (498, 1013, 2), (499, 1012, 3), (500, 1011, 0), (501, 1010, 1), (502, 1009, 2), (503, 1008, 3), (504, 1007, 0), (505, 1006, 1), (506, 1005, 2), (507, 1004, 3), (508, 1003, 0), (509, 1002, 1), (510, 1001, 2), (511, 1000, 3)]

theorem KT_cells : KT_tab.all (fun t => outCell KT t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem KT_cell (o id b : Nat) (h : (o, id, b) ∈ KT_tab) : outCell KT o id b = true :=
  List.all_eq_true.mp KT_cells (o, id, b) h

/-- The write log of a turn ending in `KT` holds the 16 digests, from the invariant at `L217`. -/
theorem outOk_KT (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L217) :
    OutOk inp (σ 1) 16 (mapState e σ KT).mem := by
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
  intro n i b hn hi hb
  match n, i, b, hn, hi, hb with
  | 0, 0, 0, _, _, _ => exact ⟨e (.n 1511), outCell_sound _ σ KT 0 1511 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1511) = qv inp (.HB 0 0) from g0,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 0 0 (by decide) (by decide)]; rfl⟩
  | 0, 0, 1, _, _, _ => exact ⟨e (.n 1510), outCell_sound _ σ KT 1 1510 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1510) = qv inp (.HB 0 0) from g1,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 0 1 (by decide) (by decide)]; rfl⟩
  | 0, 0, 2, _, _, _ => exact ⟨e (.n 1509), outCell_sound _ σ KT 2 1509 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1509) = qv inp (.HB 0 0) from g2,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 0 2 (by decide) (by decide)]; rfl⟩
  | 0, 0, 3, _, _, _ => exact ⟨e (.n 1508), outCell_sound _ σ KT 3 1508 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1508) = qv inp (.HB 0 0) from g3,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 0 3 (by decide) (by decide)]; rfl⟩
  | 0, 1, 0, _, _, _ => exact ⟨e (.n 1507), outCell_sound _ σ KT 4 1507 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1507) = qv inp (.HB 0 1) from g4,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 1 0 (by decide) (by decide)]; rfl⟩
  | 0, 1, 1, _, _, _ => exact ⟨e (.n 1506), outCell_sound _ σ KT 5 1506 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1506) = qv inp (.HB 0 1) from g5,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 1 1 (by decide) (by decide)]; rfl⟩
  | 0, 1, 2, _, _, _ => exact ⟨e (.n 1505), outCell_sound _ σ KT 6 1505 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1505) = qv inp (.HB 0 1) from g6,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 1 2 (by decide) (by decide)]; rfl⟩
  | 0, 1, 3, _, _, _ => exact ⟨e (.n 1504), outCell_sound _ σ KT 7 1504 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1504) = qv inp (.HB 0 1) from g7,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 1 3 (by decide) (by decide)]; rfl⟩
  | 0, 2, 0, _, _, _ => exact ⟨e (.n 1503), outCell_sound _ σ KT 8 1503 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1503) = qv inp (.HB 0 2) from g8,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 2 0 (by decide) (by decide)]; rfl⟩
  | 0, 2, 1, _, _, _ => exact ⟨e (.n 1502), outCell_sound _ σ KT 9 1502 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1502) = qv inp (.HB 0 2) from g9,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 2 1 (by decide) (by decide)]; rfl⟩
  | 0, 2, 2, _, _, _ => exact ⟨e (.n 1501), outCell_sound _ σ KT 10 1501 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1501) = qv inp (.HB 0 2) from g10,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 2 2 (by decide) (by decide)]; rfl⟩
  | 0, 2, 3, _, _, _ => exact ⟨e (.n 1500), outCell_sound _ σ KT 11 1500 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1500) = qv inp (.HB 0 2) from g11,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 2 3 (by decide) (by decide)]; rfl⟩
  | 0, 3, 0, _, _, _ => exact ⟨e (.n 1499), outCell_sound _ σ KT 12 1499 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1499) = qv inp (.HB 0 3) from g12,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 3 0 (by decide) (by decide)]; rfl⟩
  | 0, 3, 1, _, _, _ => exact ⟨e (.n 1498), outCell_sound _ σ KT 13 1498 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1498) = qv inp (.HB 0 3) from g13,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 3 1 (by decide) (by decide)]; rfl⟩
  | 0, 3, 2, _, _, _ => exact ⟨e (.n 1497), outCell_sound _ σ KT 14 1497 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1497) = qv inp (.HB 0 3) from g14,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 3 2 (by decide) (by decide)]; rfl⟩
  | 0, 3, 3, _, _, _ => exact ⟨e (.n 1496), outCell_sound _ σ KT 15 1496 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1496) = qv inp (.HB 0 3) from g15,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 3 3 (by decide) (by decide)]; rfl⟩
  | 0, 4, 0, _, _, _ => exact ⟨e (.n 1495), outCell_sound _ σ KT 16 1495 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1495) = qv inp (.HB 0 4) from g16,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 4 0 (by decide) (by decide)]; rfl⟩
  | 0, 4, 1, _, _, _ => exact ⟨e (.n 1494), outCell_sound _ σ KT 17 1494 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1494) = qv inp (.HB 0 4) from g17,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 4 1 (by decide) (by decide)]; rfl⟩
  | 0, 4, 2, _, _, _ => exact ⟨e (.n 1493), outCell_sound _ σ KT 18 1493 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1493) = qv inp (.HB 0 4) from g18,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 4 2 (by decide) (by decide)]; rfl⟩
  | 0, 4, 3, _, _, _ => exact ⟨e (.n 1492), outCell_sound _ σ KT 19 1492 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1492) = qv inp (.HB 0 4) from g19,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 4 3 (by decide) (by decide)]; rfl⟩
  | 0, 5, 0, _, _, _ => exact ⟨e (.n 1491), outCell_sound _ σ KT 20 1491 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1491) = qv inp (.HB 0 5) from g20,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 5 0 (by decide) (by decide)]; rfl⟩
  | 0, 5, 1, _, _, _ => exact ⟨e (.n 1490), outCell_sound _ σ KT 21 1490 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1490) = qv inp (.HB 0 5) from g21,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 5 1 (by decide) (by decide)]; rfl⟩
  | 0, 5, 2, _, _, _ => exact ⟨e (.n 1489), outCell_sound _ σ KT 22 1489 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1489) = qv inp (.HB 0 5) from g22,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 5 2 (by decide) (by decide)]; rfl⟩
  | 0, 5, 3, _, _, _ => exact ⟨e (.n 1488), outCell_sound _ σ KT 23 1488 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1488) = qv inp (.HB 0 5) from g23,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 5 3 (by decide) (by decide)]; rfl⟩
  | 0, 6, 0, _, _, _ => exact ⟨e (.n 1487), outCell_sound _ σ KT 24 1487 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1487) = qv inp (.HB 0 6) from g24,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 6 0 (by decide) (by decide)]; rfl⟩
  | 0, 6, 1, _, _, _ => exact ⟨e (.n 1486), outCell_sound _ σ KT 25 1486 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1486) = qv inp (.HB 0 6) from g25,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 6 1 (by decide) (by decide)]; rfl⟩
  | 0, 6, 2, _, _, _ => exact ⟨e (.n 1485), outCell_sound _ σ KT 26 1485 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1485) = qv inp (.HB 0 6) from g26,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 6 2 (by decide) (by decide)]; rfl⟩
  | 0, 6, 3, _, _, _ => exact ⟨e (.n 1484), outCell_sound _ σ KT 27 1484 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1484) = qv inp (.HB 0 6) from g27,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 6 3 (by decide) (by decide)]; rfl⟩
  | 0, 7, 0, _, _, _ => exact ⟨e (.n 1483), outCell_sound _ σ KT 28 1483 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1483) = qv inp (.HB 0 7) from g28,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 7 0 (by decide) (by decide)]; rfl⟩
  | 0, 7, 1, _, _, _ => exact ⟨e (.n 1482), outCell_sound _ σ KT 29 1482 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1482) = qv inp (.HB 0 7) from g29,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 7 1 (by decide) (by decide)]; rfl⟩
  | 0, 7, 2, _, _, _ => exact ⟨e (.n 1481), outCell_sound _ σ KT 30 1481 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1481) = qv inp (.HB 0 7) from g30,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 7 2 (by decide) (by decide)]; rfl⟩
  | 0, 7, 3, _, _, _ => exact ⟨e (.n 1480), outCell_sound _ σ KT 31 1480 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1480) = qv inp (.HB 0 7) from g31,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 7 3 (by decide) (by decide)]; rfl⟩
  | 1, 0, 0, _, _, _ => exact ⟨e (.n 1479), outCell_sound _ σ KT 32 1479 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1479) = qv inp (.HB 1 0) from g32,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 0 0 (by decide) (by decide)]; rfl⟩
  | 1, 0, 1, _, _, _ => exact ⟨e (.n 1478), outCell_sound _ σ KT 33 1478 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1478) = qv inp (.HB 1 0) from g33,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 0 1 (by decide) (by decide)]; rfl⟩
  | 1, 0, 2, _, _, _ => exact ⟨e (.n 1477), outCell_sound _ σ KT 34 1477 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1477) = qv inp (.HB 1 0) from g34,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 0 2 (by decide) (by decide)]; rfl⟩
  | 1, 0, 3, _, _, _ => exact ⟨e (.n 1476), outCell_sound _ σ KT 35 1476 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1476) = qv inp (.HB 1 0) from g35,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 0 3 (by decide) (by decide)]; rfl⟩
  | 1, 1, 0, _, _, _ => exact ⟨e (.n 1475), outCell_sound _ σ KT 36 1475 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1475) = qv inp (.HB 1 1) from g36,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 1 0 (by decide) (by decide)]; rfl⟩
  | 1, 1, 1, _, _, _ => exact ⟨e (.n 1474), outCell_sound _ σ KT 37 1474 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1474) = qv inp (.HB 1 1) from g37,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 1 1 (by decide) (by decide)]; rfl⟩
  | 1, 1, 2, _, _, _ => exact ⟨e (.n 1473), outCell_sound _ σ KT 38 1473 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1473) = qv inp (.HB 1 1) from g38,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 1 2 (by decide) (by decide)]; rfl⟩
  | 1, 1, 3, _, _, _ => exact ⟨e (.n 1472), outCell_sound _ σ KT 39 1472 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1472) = qv inp (.HB 1 1) from g39,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 1 3 (by decide) (by decide)]; rfl⟩
  | 1, 2, 0, _, _, _ => exact ⟨e (.n 1471), outCell_sound _ σ KT 40 1471 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1471) = qv inp (.HB 1 2) from g40,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 2 0 (by decide) (by decide)]; rfl⟩
  | 1, 2, 1, _, _, _ => exact ⟨e (.n 1470), outCell_sound _ σ KT 41 1470 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1470) = qv inp (.HB 1 2) from g41,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 2 1 (by decide) (by decide)]; rfl⟩
  | 1, 2, 2, _, _, _ => exact ⟨e (.n 1469), outCell_sound _ σ KT 42 1469 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1469) = qv inp (.HB 1 2) from g42,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 2 2 (by decide) (by decide)]; rfl⟩
  | 1, 2, 3, _, _, _ => exact ⟨e (.n 1468), outCell_sound _ σ KT 43 1468 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1468) = qv inp (.HB 1 2) from g43,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 2 3 (by decide) (by decide)]; rfl⟩
  | 1, 3, 0, _, _, _ => exact ⟨e (.n 1467), outCell_sound _ σ KT 44 1467 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1467) = qv inp (.HB 1 3) from g44,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 3 0 (by decide) (by decide)]; rfl⟩
  | 1, 3, 1, _, _, _ => exact ⟨e (.n 1466), outCell_sound _ σ KT 45 1466 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1466) = qv inp (.HB 1 3) from g45,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 3 1 (by decide) (by decide)]; rfl⟩
  | 1, 3, 2, _, _, _ => exact ⟨e (.n 1465), outCell_sound _ σ KT 46 1465 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1465) = qv inp (.HB 1 3) from g46,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 3 2 (by decide) (by decide)]; rfl⟩
  | 1, 3, 3, _, _, _ => exact ⟨e (.n 1464), outCell_sound _ σ KT 47 1464 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1464) = qv inp (.HB 1 3) from g47,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 3 3 (by decide) (by decide)]; rfl⟩
  | 1, 4, 0, _, _, _ => exact ⟨e (.n 1463), outCell_sound _ σ KT 48 1463 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1463) = qv inp (.HB 1 4) from g48,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 4 0 (by decide) (by decide)]; rfl⟩
  | 1, 4, 1, _, _, _ => exact ⟨e (.n 1462), outCell_sound _ σ KT 49 1462 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1462) = qv inp (.HB 1 4) from g49,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 4 1 (by decide) (by decide)]; rfl⟩
  | 1, 4, 2, _, _, _ => exact ⟨e (.n 1461), outCell_sound _ σ KT 50 1461 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1461) = qv inp (.HB 1 4) from g50,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 4 2 (by decide) (by decide)]; rfl⟩
  | 1, 4, 3, _, _, _ => exact ⟨e (.n 1460), outCell_sound _ σ KT 51 1460 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1460) = qv inp (.HB 1 4) from g51,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 4 3 (by decide) (by decide)]; rfl⟩
  | 1, 5, 0, _, _, _ => exact ⟨e (.n 1459), outCell_sound _ σ KT 52 1459 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1459) = qv inp (.HB 1 5) from g52,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 5 0 (by decide) (by decide)]; rfl⟩
  | 1, 5, 1, _, _, _ => exact ⟨e (.n 1458), outCell_sound _ σ KT 53 1458 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1458) = qv inp (.HB 1 5) from g53,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 5 1 (by decide) (by decide)]; rfl⟩
  | 1, 5, 2, _, _, _ => exact ⟨e (.n 1457), outCell_sound _ σ KT 54 1457 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1457) = qv inp (.HB 1 5) from g54,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 5 2 (by decide) (by decide)]; rfl⟩
  | 1, 5, 3, _, _, _ => exact ⟨e (.n 1456), outCell_sound _ σ KT 55 1456 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1456) = qv inp (.HB 1 5) from g55,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 5 3 (by decide) (by decide)]; rfl⟩
  | 1, 6, 0, _, _, _ => exact ⟨e (.n 1455), outCell_sound _ σ KT 56 1455 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1455) = qv inp (.HB 1 6) from g56,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 6 0 (by decide) (by decide)]; rfl⟩
  | 1, 6, 1, _, _, _ => exact ⟨e (.n 1454), outCell_sound _ σ KT 57 1454 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1454) = qv inp (.HB 1 6) from g57,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 6 1 (by decide) (by decide)]; rfl⟩
  | 1, 6, 2, _, _, _ => exact ⟨e (.n 1453), outCell_sound _ σ KT 58 1453 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1453) = qv inp (.HB 1 6) from g58,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 6 2 (by decide) (by decide)]; rfl⟩
  | 1, 6, 3, _, _, _ => exact ⟨e (.n 1452), outCell_sound _ σ KT 59 1452 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1452) = qv inp (.HB 1 6) from g59,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 6 3 (by decide) (by decide)]; rfl⟩
  | 1, 7, 0, _, _, _ => exact ⟨e (.n 1451), outCell_sound _ σ KT 60 1451 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1451) = qv inp (.HB 1 7) from g60,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 7 0 (by decide) (by decide)]; rfl⟩
  | 1, 7, 1, _, _, _ => exact ⟨e (.n 1450), outCell_sound _ σ KT 61 1450 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1450) = qv inp (.HB 1 7) from g61,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 7 1 (by decide) (by decide)]; rfl⟩
  | 1, 7, 2, _, _, _ => exact ⟨e (.n 1449), outCell_sound _ σ KT 62 1449 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1449) = qv inp (.HB 1 7) from g62,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 7 2 (by decide) (by decide)]; rfl⟩
  | 1, 7, 3, _, _, _ => exact ⟨e (.n 1448), outCell_sound _ σ KT 63 1448 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1448) = qv inp (.HB 1 7) from g63,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 7 3 (by decide) (by decide)]; rfl⟩
  | 2, 0, 0, _, _, _ => exact ⟨e (.n 1447), outCell_sound _ σ KT 64 1447 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1447) = qv inp (.HB 2 0) from g64,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 0 0 (by decide) (by decide)]; rfl⟩
  | 2, 0, 1, _, _, _ => exact ⟨e (.n 1446), outCell_sound _ σ KT 65 1446 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1446) = qv inp (.HB 2 0) from g65,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 0 1 (by decide) (by decide)]; rfl⟩
  | 2, 0, 2, _, _, _ => exact ⟨e (.n 1445), outCell_sound _ σ KT 66 1445 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1445) = qv inp (.HB 2 0) from g66,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 0 2 (by decide) (by decide)]; rfl⟩
  | 2, 0, 3, _, _, _ => exact ⟨e (.n 1444), outCell_sound _ σ KT 67 1444 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1444) = qv inp (.HB 2 0) from g67,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 0 3 (by decide) (by decide)]; rfl⟩
  | 2, 1, 0, _, _, _ => exact ⟨e (.n 1443), outCell_sound _ σ KT 68 1443 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1443) = qv inp (.HB 2 1) from g68,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 1 0 (by decide) (by decide)]; rfl⟩
  | 2, 1, 1, _, _, _ => exact ⟨e (.n 1442), outCell_sound _ σ KT 69 1442 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1442) = qv inp (.HB 2 1) from g69,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 1 1 (by decide) (by decide)]; rfl⟩
  | 2, 1, 2, _, _, _ => exact ⟨e (.n 1441), outCell_sound _ σ KT 70 1441 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1441) = qv inp (.HB 2 1) from g70,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 1 2 (by decide) (by decide)]; rfl⟩
  | 2, 1, 3, _, _, _ => exact ⟨e (.n 1440), outCell_sound _ σ KT 71 1440 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1440) = qv inp (.HB 2 1) from g71,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 1 3 (by decide) (by decide)]; rfl⟩
  | 2, 2, 0, _, _, _ => exact ⟨e (.n 1439), outCell_sound _ σ KT 72 1439 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1439) = qv inp (.HB 2 2) from g72,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 2 0 (by decide) (by decide)]; rfl⟩
  | 2, 2, 1, _, _, _ => exact ⟨e (.n 1438), outCell_sound _ σ KT 73 1438 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1438) = qv inp (.HB 2 2) from g73,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 2 1 (by decide) (by decide)]; rfl⟩
  | 2, 2, 2, _, _, _ => exact ⟨e (.n 1437), outCell_sound _ σ KT 74 1437 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1437) = qv inp (.HB 2 2) from g74,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 2 2 (by decide) (by decide)]; rfl⟩
  | 2, 2, 3, _, _, _ => exact ⟨e (.n 1436), outCell_sound _ σ KT 75 1436 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1436) = qv inp (.HB 2 2) from g75,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 2 3 (by decide) (by decide)]; rfl⟩
  | 2, 3, 0, _, _, _ => exact ⟨e (.n 1435), outCell_sound _ σ KT 76 1435 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1435) = qv inp (.HB 2 3) from g76,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 3 0 (by decide) (by decide)]; rfl⟩
  | 2, 3, 1, _, _, _ => exact ⟨e (.n 1434), outCell_sound _ σ KT 77 1434 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1434) = qv inp (.HB 2 3) from g77,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 3 1 (by decide) (by decide)]; rfl⟩
  | 2, 3, 2, _, _, _ => exact ⟨e (.n 1433), outCell_sound _ σ KT 78 1433 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1433) = qv inp (.HB 2 3) from g78,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 3 2 (by decide) (by decide)]; rfl⟩
  | 2, 3, 3, _, _, _ => exact ⟨e (.n 1432), outCell_sound _ σ KT 79 1432 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1432) = qv inp (.HB 2 3) from g79,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 3 3 (by decide) (by decide)]; rfl⟩
  | 2, 4, 0, _, _, _ => exact ⟨e (.n 1431), outCell_sound _ σ KT 80 1431 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1431) = qv inp (.HB 2 4) from g80,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 4 0 (by decide) (by decide)]; rfl⟩
  | 2, 4, 1, _, _, _ => exact ⟨e (.n 1430), outCell_sound _ σ KT 81 1430 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1430) = qv inp (.HB 2 4) from g81,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 4 1 (by decide) (by decide)]; rfl⟩
  | 2, 4, 2, _, _, _ => exact ⟨e (.n 1429), outCell_sound _ σ KT 82 1429 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1429) = qv inp (.HB 2 4) from g82,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 4 2 (by decide) (by decide)]; rfl⟩
  | 2, 4, 3, _, _, _ => exact ⟨e (.n 1428), outCell_sound _ σ KT 83 1428 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1428) = qv inp (.HB 2 4) from g83,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 4 3 (by decide) (by decide)]; rfl⟩
  | 2, 5, 0, _, _, _ => exact ⟨e (.n 1427), outCell_sound _ σ KT 84 1427 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1427) = qv inp (.HB 2 5) from g84,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 5 0 (by decide) (by decide)]; rfl⟩
  | 2, 5, 1, _, _, _ => exact ⟨e (.n 1426), outCell_sound _ σ KT 85 1426 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1426) = qv inp (.HB 2 5) from g85,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 5 1 (by decide) (by decide)]; rfl⟩
  | 2, 5, 2, _, _, _ => exact ⟨e (.n 1425), outCell_sound _ σ KT 86 1425 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1425) = qv inp (.HB 2 5) from g86,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 5 2 (by decide) (by decide)]; rfl⟩
  | 2, 5, 3, _, _, _ => exact ⟨e (.n 1424), outCell_sound _ σ KT 87 1424 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1424) = qv inp (.HB 2 5) from g87,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 5 3 (by decide) (by decide)]; rfl⟩
  | 2, 6, 0, _, _, _ => exact ⟨e (.n 1423), outCell_sound _ σ KT 88 1423 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1423) = qv inp (.HB 2 6) from g88,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 6 0 (by decide) (by decide)]; rfl⟩
  | 2, 6, 1, _, _, _ => exact ⟨e (.n 1422), outCell_sound _ σ KT 89 1422 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1422) = qv inp (.HB 2 6) from g89,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 6 1 (by decide) (by decide)]; rfl⟩
  | 2, 6, 2, _, _, _ => exact ⟨e (.n 1421), outCell_sound _ σ KT 90 1421 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1421) = qv inp (.HB 2 6) from g90,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 6 2 (by decide) (by decide)]; rfl⟩
  | 2, 6, 3, _, _, _ => exact ⟨e (.n 1420), outCell_sound _ σ KT 91 1420 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1420) = qv inp (.HB 2 6) from g91,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 6 3 (by decide) (by decide)]; rfl⟩
  | 2, 7, 0, _, _, _ => exact ⟨e (.n 1419), outCell_sound _ σ KT 92 1419 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1419) = qv inp (.HB 2 7) from g92,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 7 0 (by decide) (by decide)]; rfl⟩
  | 2, 7, 1, _, _, _ => exact ⟨e (.n 1418), outCell_sound _ σ KT 93 1418 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1418) = qv inp (.HB 2 7) from g93,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 7 1 (by decide) (by decide)]; rfl⟩
  | 2, 7, 2, _, _, _ => exact ⟨e (.n 1417), outCell_sound _ σ KT 94 1417 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1417) = qv inp (.HB 2 7) from g94,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 7 2 (by decide) (by decide)]; rfl⟩
  | 2, 7, 3, _, _, _ => exact ⟨e (.n 1416), outCell_sound _ σ KT 95 1416 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1416) = qv inp (.HB 2 7) from g95,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 7 3 (by decide) (by decide)]; rfl⟩
  | 3, 0, 0, _, _, _ => exact ⟨e (.n 1415), outCell_sound _ σ KT 96 1415 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1415) = qv inp (.HB 3 0) from g96,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 0 0 (by decide) (by decide)]; rfl⟩
  | 3, 0, 1, _, _, _ => exact ⟨e (.n 1414), outCell_sound _ σ KT 97 1414 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1414) = qv inp (.HB 3 0) from g97,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 0 1 (by decide) (by decide)]; rfl⟩
  | 3, 0, 2, _, _, _ => exact ⟨e (.n 1413), outCell_sound _ σ KT 98 1413 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1413) = qv inp (.HB 3 0) from g98,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 0 2 (by decide) (by decide)]; rfl⟩
  | 3, 0, 3, _, _, _ => exact ⟨e (.n 1412), outCell_sound _ σ KT 99 1412 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1412) = qv inp (.HB 3 0) from g99,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 0 3 (by decide) (by decide)]; rfl⟩
  | 3, 1, 0, _, _, _ => exact ⟨e (.n 1411), outCell_sound _ σ KT 100 1411 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1411) = qv inp (.HB 3 1) from g100,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 1 0 (by decide) (by decide)]; rfl⟩
  | 3, 1, 1, _, _, _ => exact ⟨e (.n 1410), outCell_sound _ σ KT 101 1410 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1410) = qv inp (.HB 3 1) from g101,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 1 1 (by decide) (by decide)]; rfl⟩
  | 3, 1, 2, _, _, _ => exact ⟨e (.n 1409), outCell_sound _ σ KT 102 1409 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1409) = qv inp (.HB 3 1) from g102,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 1 2 (by decide) (by decide)]; rfl⟩
  | 3, 1, 3, _, _, _ => exact ⟨e (.n 1408), outCell_sound _ σ KT 103 1408 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1408) = qv inp (.HB 3 1) from g103,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 1 3 (by decide) (by decide)]; rfl⟩
  | 3, 2, 0, _, _, _ => exact ⟨e (.n 1407), outCell_sound _ σ KT 104 1407 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1407) = qv inp (.HB 3 2) from g104,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 2 0 (by decide) (by decide)]; rfl⟩
  | 3, 2, 1, _, _, _ => exact ⟨e (.n 1406), outCell_sound _ σ KT 105 1406 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1406) = qv inp (.HB 3 2) from g105,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 2 1 (by decide) (by decide)]; rfl⟩
  | 3, 2, 2, _, _, _ => exact ⟨e (.n 1405), outCell_sound _ σ KT 106 1405 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1405) = qv inp (.HB 3 2) from g106,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 2 2 (by decide) (by decide)]; rfl⟩
  | 3, 2, 3, _, _, _ => exact ⟨e (.n 1404), outCell_sound _ σ KT 107 1404 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1404) = qv inp (.HB 3 2) from g107,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 2 3 (by decide) (by decide)]; rfl⟩
  | 3, 3, 0, _, _, _ => exact ⟨e (.n 1403), outCell_sound _ σ KT 108 1403 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1403) = qv inp (.HB 3 3) from g108,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 3 0 (by decide) (by decide)]; rfl⟩
  | 3, 3, 1, _, _, _ => exact ⟨e (.n 1402), outCell_sound _ σ KT 109 1402 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1402) = qv inp (.HB 3 3) from g109,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 3 1 (by decide) (by decide)]; rfl⟩
  | 3, 3, 2, _, _, _ => exact ⟨e (.n 1401), outCell_sound _ σ KT 110 1401 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1401) = qv inp (.HB 3 3) from g110,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 3 2 (by decide) (by decide)]; rfl⟩
  | 3, 3, 3, _, _, _ => exact ⟨e (.n 1400), outCell_sound _ σ KT 111 1400 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1400) = qv inp (.HB 3 3) from g111,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 3 3 (by decide) (by decide)]; rfl⟩
  | 3, 4, 0, _, _, _ => exact ⟨e (.n 1399), outCell_sound _ σ KT 112 1399 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1399) = qv inp (.HB 3 4) from g112,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 4 0 (by decide) (by decide)]; rfl⟩
  | 3, 4, 1, _, _, _ => exact ⟨e (.n 1398), outCell_sound _ σ KT 113 1398 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1398) = qv inp (.HB 3 4) from g113,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 4 1 (by decide) (by decide)]; rfl⟩
  | 3, 4, 2, _, _, _ => exact ⟨e (.n 1397), outCell_sound _ σ KT 114 1397 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1397) = qv inp (.HB 3 4) from g114,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 4 2 (by decide) (by decide)]; rfl⟩
  | 3, 4, 3, _, _, _ => exact ⟨e (.n 1396), outCell_sound _ σ KT 115 1396 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1396) = qv inp (.HB 3 4) from g115,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 4 3 (by decide) (by decide)]; rfl⟩
  | 3, 5, 0, _, _, _ => exact ⟨e (.n 1395), outCell_sound _ σ KT 116 1395 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1395) = qv inp (.HB 3 5) from g116,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 5 0 (by decide) (by decide)]; rfl⟩
  | 3, 5, 1, _, _, _ => exact ⟨e (.n 1394), outCell_sound _ σ KT 117 1394 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1394) = qv inp (.HB 3 5) from g117,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 5 1 (by decide) (by decide)]; rfl⟩
  | 3, 5, 2, _, _, _ => exact ⟨e (.n 1393), outCell_sound _ σ KT 118 1393 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1393) = qv inp (.HB 3 5) from g118,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 5 2 (by decide) (by decide)]; rfl⟩
  | 3, 5, 3, _, _, _ => exact ⟨e (.n 1392), outCell_sound _ σ KT 119 1392 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1392) = qv inp (.HB 3 5) from g119,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 5 3 (by decide) (by decide)]; rfl⟩
  | 3, 6, 0, _, _, _ => exact ⟨e (.n 1391), outCell_sound _ σ KT 120 1391 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1391) = qv inp (.HB 3 6) from g120,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 6 0 (by decide) (by decide)]; rfl⟩
  | 3, 6, 1, _, _, _ => exact ⟨e (.n 1390), outCell_sound _ σ KT 121 1390 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1390) = qv inp (.HB 3 6) from g121,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 6 1 (by decide) (by decide)]; rfl⟩
  | 3, 6, 2, _, _, _ => exact ⟨e (.n 1389), outCell_sound _ σ KT 122 1389 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1389) = qv inp (.HB 3 6) from g122,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 6 2 (by decide) (by decide)]; rfl⟩
  | 3, 6, 3, _, _, _ => exact ⟨e (.n 1388), outCell_sound _ σ KT 123 1388 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1388) = qv inp (.HB 3 6) from g123,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 6 3 (by decide) (by decide)]; rfl⟩
  | 3, 7, 0, _, _, _ => exact ⟨e (.n 1387), outCell_sound _ σ KT 124 1387 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1387) = qv inp (.HB 3 7) from g124,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 7 0 (by decide) (by decide)]; rfl⟩
  | 3, 7, 1, _, _, _ => exact ⟨e (.n 1386), outCell_sound _ σ KT 125 1386 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1386) = qv inp (.HB 3 7) from g125,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 7 1 (by decide) (by decide)]; rfl⟩
  | 3, 7, 2, _, _, _ => exact ⟨e (.n 1385), outCell_sound _ σ KT 126 1385 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1385) = qv inp (.HB 3 7) from g126,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 7 2 (by decide) (by decide)]; rfl⟩
  | 3, 7, 3, _, _, _ => exact ⟨e (.n 1384), outCell_sound _ σ KT 127 1384 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1384) = qv inp (.HB 3 7) from g127,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 7 3 (by decide) (by decide)]; rfl⟩
  | 4, 0, 0, _, _, _ => exact ⟨e (.n 1383), outCell_sound _ σ KT 128 1383 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1383) = qv inp (.HB 4 0) from g128,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 0 0 (by decide) (by decide)]; rfl⟩
  | 4, 0, 1, _, _, _ => exact ⟨e (.n 1382), outCell_sound _ σ KT 129 1382 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1382) = qv inp (.HB 4 0) from g129,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 0 1 (by decide) (by decide)]; rfl⟩
  | 4, 0, 2, _, _, _ => exact ⟨e (.n 1381), outCell_sound _ σ KT 130 1381 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1381) = qv inp (.HB 4 0) from g130,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 0 2 (by decide) (by decide)]; rfl⟩
  | 4, 0, 3, _, _, _ => exact ⟨e (.n 1380), outCell_sound _ σ KT 131 1380 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1380) = qv inp (.HB 4 0) from g131,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 0 3 (by decide) (by decide)]; rfl⟩
  | 4, 1, 0, _, _, _ => exact ⟨e (.n 1379), outCell_sound _ σ KT 132 1379 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1379) = qv inp (.HB 4 1) from g132,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 1 0 (by decide) (by decide)]; rfl⟩
  | 4, 1, 1, _, _, _ => exact ⟨e (.n 1378), outCell_sound _ σ KT 133 1378 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1378) = qv inp (.HB 4 1) from g133,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 1 1 (by decide) (by decide)]; rfl⟩
  | 4, 1, 2, _, _, _ => exact ⟨e (.n 1377), outCell_sound _ σ KT 134 1377 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1377) = qv inp (.HB 4 1) from g134,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 1 2 (by decide) (by decide)]; rfl⟩
  | 4, 1, 3, _, _, _ => exact ⟨e (.n 1376), outCell_sound _ σ KT 135 1376 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1376) = qv inp (.HB 4 1) from g135,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 1 3 (by decide) (by decide)]; rfl⟩
  | 4, 2, 0, _, _, _ => exact ⟨e (.n 1375), outCell_sound _ σ KT 136 1375 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1375) = qv inp (.HB 4 2) from g136,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 2 0 (by decide) (by decide)]; rfl⟩
  | 4, 2, 1, _, _, _ => exact ⟨e (.n 1374), outCell_sound _ σ KT 137 1374 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1374) = qv inp (.HB 4 2) from g137,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 2 1 (by decide) (by decide)]; rfl⟩
  | 4, 2, 2, _, _, _ => exact ⟨e (.n 1373), outCell_sound _ σ KT 138 1373 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1373) = qv inp (.HB 4 2) from g138,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 2 2 (by decide) (by decide)]; rfl⟩
  | 4, 2, 3, _, _, _ => exact ⟨e (.n 1372), outCell_sound _ σ KT 139 1372 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1372) = qv inp (.HB 4 2) from g139,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 2 3 (by decide) (by decide)]; rfl⟩
  | 4, 3, 0, _, _, _ => exact ⟨e (.n 1371), outCell_sound _ σ KT 140 1371 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1371) = qv inp (.HB 4 3) from g140,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 3 0 (by decide) (by decide)]; rfl⟩
  | 4, 3, 1, _, _, _ => exact ⟨e (.n 1370), outCell_sound _ σ KT 141 1370 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1370) = qv inp (.HB 4 3) from g141,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 3 1 (by decide) (by decide)]; rfl⟩
  | 4, 3, 2, _, _, _ => exact ⟨e (.n 1369), outCell_sound _ σ KT 142 1369 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1369) = qv inp (.HB 4 3) from g142,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 3 2 (by decide) (by decide)]; rfl⟩
  | 4, 3, 3, _, _, _ => exact ⟨e (.n 1368), outCell_sound _ σ KT 143 1368 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1368) = qv inp (.HB 4 3) from g143,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 3 3 (by decide) (by decide)]; rfl⟩
  | 4, 4, 0, _, _, _ => exact ⟨e (.n 1367), outCell_sound _ σ KT 144 1367 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1367) = qv inp (.HB 4 4) from g144,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 4 0 (by decide) (by decide)]; rfl⟩
  | 4, 4, 1, _, _, _ => exact ⟨e (.n 1366), outCell_sound _ σ KT 145 1366 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1366) = qv inp (.HB 4 4) from g145,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 4 1 (by decide) (by decide)]; rfl⟩
  | 4, 4, 2, _, _, _ => exact ⟨e (.n 1365), outCell_sound _ σ KT 146 1365 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1365) = qv inp (.HB 4 4) from g146,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 4 2 (by decide) (by decide)]; rfl⟩
  | 4, 4, 3, _, _, _ => exact ⟨e (.n 1364), outCell_sound _ σ KT 147 1364 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1364) = qv inp (.HB 4 4) from g147,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 4 3 (by decide) (by decide)]; rfl⟩
  | 4, 5, 0, _, _, _ => exact ⟨e (.n 1363), outCell_sound _ σ KT 148 1363 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1363) = qv inp (.HB 4 5) from g148,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 5 0 (by decide) (by decide)]; rfl⟩
  | 4, 5, 1, _, _, _ => exact ⟨e (.n 1362), outCell_sound _ σ KT 149 1362 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1362) = qv inp (.HB 4 5) from g149,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 5 1 (by decide) (by decide)]; rfl⟩
  | 4, 5, 2, _, _, _ => exact ⟨e (.n 1361), outCell_sound _ σ KT 150 1361 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1361) = qv inp (.HB 4 5) from g150,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 5 2 (by decide) (by decide)]; rfl⟩
  | 4, 5, 3, _, _, _ => exact ⟨e (.n 1360), outCell_sound _ σ KT 151 1360 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1360) = qv inp (.HB 4 5) from g151,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 5 3 (by decide) (by decide)]; rfl⟩
  | 4, 6, 0, _, _, _ => exact ⟨e (.n 1359), outCell_sound _ σ KT 152 1359 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1359) = qv inp (.HB 4 6) from g152,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 6 0 (by decide) (by decide)]; rfl⟩
  | 4, 6, 1, _, _, _ => exact ⟨e (.n 1358), outCell_sound _ σ KT 153 1358 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1358) = qv inp (.HB 4 6) from g153,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 6 1 (by decide) (by decide)]; rfl⟩
  | 4, 6, 2, _, _, _ => exact ⟨e (.n 1357), outCell_sound _ σ KT 154 1357 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1357) = qv inp (.HB 4 6) from g154,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 6 2 (by decide) (by decide)]; rfl⟩
  | 4, 6, 3, _, _, _ => exact ⟨e (.n 1356), outCell_sound _ σ KT 155 1356 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1356) = qv inp (.HB 4 6) from g155,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 6 3 (by decide) (by decide)]; rfl⟩
  | 4, 7, 0, _, _, _ => exact ⟨e (.n 1355), outCell_sound _ σ KT 156 1355 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1355) = qv inp (.HB 4 7) from g156,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 7 0 (by decide) (by decide)]; rfl⟩
  | 4, 7, 1, _, _, _ => exact ⟨e (.n 1354), outCell_sound _ σ KT 157 1354 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1354) = qv inp (.HB 4 7) from g157,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 7 1 (by decide) (by decide)]; rfl⟩
  | 4, 7, 2, _, _, _ => exact ⟨e (.n 1353), outCell_sound _ σ KT 158 1353 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1353) = qv inp (.HB 4 7) from g158,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 7 2 (by decide) (by decide)]; rfl⟩
  | 4, 7, 3, _, _, _ => exact ⟨e (.n 1352), outCell_sound _ σ KT 159 1352 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1352) = qv inp (.HB 4 7) from g159,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 7 3 (by decide) (by decide)]; rfl⟩
  | 5, 0, 0, _, _, _ => exact ⟨e (.n 1351), outCell_sound _ σ KT 160 1351 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1351) = qv inp (.HB 5 0) from g160,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 0 0 (by decide) (by decide)]; rfl⟩
  | 5, 0, 1, _, _, _ => exact ⟨e (.n 1350), outCell_sound _ σ KT 161 1350 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1350) = qv inp (.HB 5 0) from g161,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 0 1 (by decide) (by decide)]; rfl⟩
  | 5, 0, 2, _, _, _ => exact ⟨e (.n 1349), outCell_sound _ σ KT 162 1349 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1349) = qv inp (.HB 5 0) from g162,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 0 2 (by decide) (by decide)]; rfl⟩
  | 5, 0, 3, _, _, _ => exact ⟨e (.n 1348), outCell_sound _ σ KT 163 1348 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1348) = qv inp (.HB 5 0) from g163,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 0 3 (by decide) (by decide)]; rfl⟩
  | 5, 1, 0, _, _, _ => exact ⟨e (.n 1347), outCell_sound _ σ KT 164 1347 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1347) = qv inp (.HB 5 1) from g164,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 1 0 (by decide) (by decide)]; rfl⟩
  | 5, 1, 1, _, _, _ => exact ⟨e (.n 1346), outCell_sound _ σ KT 165 1346 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1346) = qv inp (.HB 5 1) from g165,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 1 1 (by decide) (by decide)]; rfl⟩
  | 5, 1, 2, _, _, _ => exact ⟨e (.n 1345), outCell_sound _ σ KT 166 1345 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1345) = qv inp (.HB 5 1) from g166,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 1 2 (by decide) (by decide)]; rfl⟩
  | 5, 1, 3, _, _, _ => exact ⟨e (.n 1344), outCell_sound _ σ KT 167 1344 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1344) = qv inp (.HB 5 1) from g167,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 1 3 (by decide) (by decide)]; rfl⟩
  | 5, 2, 0, _, _, _ => exact ⟨e (.n 1343), outCell_sound _ σ KT 168 1343 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1343) = qv inp (.HB 5 2) from g168,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 2 0 (by decide) (by decide)]; rfl⟩
  | 5, 2, 1, _, _, _ => exact ⟨e (.n 1342), outCell_sound _ σ KT 169 1342 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1342) = qv inp (.HB 5 2) from g169,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 2 1 (by decide) (by decide)]; rfl⟩
  | 5, 2, 2, _, _, _ => exact ⟨e (.n 1341), outCell_sound _ σ KT 170 1341 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1341) = qv inp (.HB 5 2) from g170,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 2 2 (by decide) (by decide)]; rfl⟩
  | 5, 2, 3, _, _, _ => exact ⟨e (.n 1340), outCell_sound _ σ KT 171 1340 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1340) = qv inp (.HB 5 2) from g171,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 2 3 (by decide) (by decide)]; rfl⟩
  | 5, 3, 0, _, _, _ => exact ⟨e (.n 1339), outCell_sound _ σ KT 172 1339 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1339) = qv inp (.HB 5 3) from g172,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 3 0 (by decide) (by decide)]; rfl⟩
  | 5, 3, 1, _, _, _ => exact ⟨e (.n 1338), outCell_sound _ σ KT 173 1338 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1338) = qv inp (.HB 5 3) from g173,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 3 1 (by decide) (by decide)]; rfl⟩
  | 5, 3, 2, _, _, _ => exact ⟨e (.n 1337), outCell_sound _ σ KT 174 1337 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1337) = qv inp (.HB 5 3) from g174,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 3 2 (by decide) (by decide)]; rfl⟩
  | 5, 3, 3, _, _, _ => exact ⟨e (.n 1336), outCell_sound _ σ KT 175 1336 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1336) = qv inp (.HB 5 3) from g175,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 3 3 (by decide) (by decide)]; rfl⟩
  | 5, 4, 0, _, _, _ => exact ⟨e (.n 1335), outCell_sound _ σ KT 176 1335 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1335) = qv inp (.HB 5 4) from g176,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 4 0 (by decide) (by decide)]; rfl⟩
  | 5, 4, 1, _, _, _ => exact ⟨e (.n 1334), outCell_sound _ σ KT 177 1334 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1334) = qv inp (.HB 5 4) from g177,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 4 1 (by decide) (by decide)]; rfl⟩
  | 5, 4, 2, _, _, _ => exact ⟨e (.n 1333), outCell_sound _ σ KT 178 1333 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1333) = qv inp (.HB 5 4) from g178,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 4 2 (by decide) (by decide)]; rfl⟩
  | 5, 4, 3, _, _, _ => exact ⟨e (.n 1332), outCell_sound _ σ KT 179 1332 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1332) = qv inp (.HB 5 4) from g179,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 4 3 (by decide) (by decide)]; rfl⟩
  | 5, 5, 0, _, _, _ => exact ⟨e (.n 1331), outCell_sound _ σ KT 180 1331 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1331) = qv inp (.HB 5 5) from g180,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 5 0 (by decide) (by decide)]; rfl⟩
  | 5, 5, 1, _, _, _ => exact ⟨e (.n 1330), outCell_sound _ σ KT 181 1330 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1330) = qv inp (.HB 5 5) from g181,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 5 1 (by decide) (by decide)]; rfl⟩
  | 5, 5, 2, _, _, _ => exact ⟨e (.n 1329), outCell_sound _ σ KT 182 1329 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1329) = qv inp (.HB 5 5) from g182,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 5 2 (by decide) (by decide)]; rfl⟩
  | 5, 5, 3, _, _, _ => exact ⟨e (.n 1328), outCell_sound _ σ KT 183 1328 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1328) = qv inp (.HB 5 5) from g183,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 5 3 (by decide) (by decide)]; rfl⟩
  | 5, 6, 0, _, _, _ => exact ⟨e (.n 1327), outCell_sound _ σ KT 184 1327 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1327) = qv inp (.HB 5 6) from g184,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 6 0 (by decide) (by decide)]; rfl⟩
  | 5, 6, 1, _, _, _ => exact ⟨e (.n 1326), outCell_sound _ σ KT 185 1326 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1326) = qv inp (.HB 5 6) from g185,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 6 1 (by decide) (by decide)]; rfl⟩
  | 5, 6, 2, _, _, _ => exact ⟨e (.n 1325), outCell_sound _ σ KT 186 1325 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1325) = qv inp (.HB 5 6) from g186,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 6 2 (by decide) (by decide)]; rfl⟩
  | 5, 6, 3, _, _, _ => exact ⟨e (.n 1324), outCell_sound _ σ KT 187 1324 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1324) = qv inp (.HB 5 6) from g187,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 6 3 (by decide) (by decide)]; rfl⟩
  | 5, 7, 0, _, _, _ => exact ⟨e (.n 1323), outCell_sound _ σ KT 188 1323 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1323) = qv inp (.HB 5 7) from g188,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 7 0 (by decide) (by decide)]; rfl⟩
  | 5, 7, 1, _, _, _ => exact ⟨e (.n 1322), outCell_sound _ σ KT 189 1322 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1322) = qv inp (.HB 5 7) from g189,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 7 1 (by decide) (by decide)]; rfl⟩
  | 5, 7, 2, _, _, _ => exact ⟨e (.n 1321), outCell_sound _ σ KT 190 1321 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1321) = qv inp (.HB 5 7) from g190,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 7 2 (by decide) (by decide)]; rfl⟩
  | 5, 7, 3, _, _, _ => exact ⟨e (.n 1320), outCell_sound _ σ KT 191 1320 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1320) = qv inp (.HB 5 7) from g191,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 7 3 (by decide) (by decide)]; rfl⟩
  | 6, 0, 0, _, _, _ => exact ⟨e (.n 1319), outCell_sound _ σ KT 192 1319 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1319) = qv inp (.HB 6 0) from g192,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 0 0 (by decide) (by decide)]; rfl⟩
  | 6, 0, 1, _, _, _ => exact ⟨e (.n 1318), outCell_sound _ σ KT 193 1318 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1318) = qv inp (.HB 6 0) from g193,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 0 1 (by decide) (by decide)]; rfl⟩
  | 6, 0, 2, _, _, _ => exact ⟨e (.n 1317), outCell_sound _ σ KT 194 1317 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1317) = qv inp (.HB 6 0) from g194,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 0 2 (by decide) (by decide)]; rfl⟩
  | 6, 0, 3, _, _, _ => exact ⟨e (.n 1316), outCell_sound _ σ KT 195 1316 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1316) = qv inp (.HB 6 0) from g195,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 0 3 (by decide) (by decide)]; rfl⟩
  | 6, 1, 0, _, _, _ => exact ⟨e (.n 1315), outCell_sound _ σ KT 196 1315 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1315) = qv inp (.HB 6 1) from g196,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 1 0 (by decide) (by decide)]; rfl⟩
  | 6, 1, 1, _, _, _ => exact ⟨e (.n 1314), outCell_sound _ σ KT 197 1314 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1314) = qv inp (.HB 6 1) from g197,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 1 1 (by decide) (by decide)]; rfl⟩
  | 6, 1, 2, _, _, _ => exact ⟨e (.n 1313), outCell_sound _ σ KT 198 1313 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1313) = qv inp (.HB 6 1) from g198,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 1 2 (by decide) (by decide)]; rfl⟩
  | 6, 1, 3, _, _, _ => exact ⟨e (.n 1312), outCell_sound _ σ KT 199 1312 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1312) = qv inp (.HB 6 1) from g199,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 1 3 (by decide) (by decide)]; rfl⟩
  | 6, 2, 0, _, _, _ => exact ⟨e (.n 1311), outCell_sound _ σ KT 200 1311 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1311) = qv inp (.HB 6 2) from g200,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 2 0 (by decide) (by decide)]; rfl⟩
  | 6, 2, 1, _, _, _ => exact ⟨e (.n 1310), outCell_sound _ σ KT 201 1310 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1310) = qv inp (.HB 6 2) from g201,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 2 1 (by decide) (by decide)]; rfl⟩
  | 6, 2, 2, _, _, _ => exact ⟨e (.n 1309), outCell_sound _ σ KT 202 1309 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1309) = qv inp (.HB 6 2) from g202,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 2 2 (by decide) (by decide)]; rfl⟩
  | 6, 2, 3, _, _, _ => exact ⟨e (.n 1308), outCell_sound _ σ KT 203 1308 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1308) = qv inp (.HB 6 2) from g203,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 2 3 (by decide) (by decide)]; rfl⟩
  | 6, 3, 0, _, _, _ => exact ⟨e (.n 1307), outCell_sound _ σ KT 204 1307 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1307) = qv inp (.HB 6 3) from g204,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 3 0 (by decide) (by decide)]; rfl⟩
  | 6, 3, 1, _, _, _ => exact ⟨e (.n 1306), outCell_sound _ σ KT 205 1306 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1306) = qv inp (.HB 6 3) from g205,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 3 1 (by decide) (by decide)]; rfl⟩
  | 6, 3, 2, _, _, _ => exact ⟨e (.n 1305), outCell_sound _ σ KT 206 1305 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1305) = qv inp (.HB 6 3) from g206,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 3 2 (by decide) (by decide)]; rfl⟩
  | 6, 3, 3, _, _, _ => exact ⟨e (.n 1304), outCell_sound _ σ KT 207 1304 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1304) = qv inp (.HB 6 3) from g207,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 3 3 (by decide) (by decide)]; rfl⟩
  | 6, 4, 0, _, _, _ => exact ⟨e (.n 1303), outCell_sound _ σ KT 208 1303 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1303) = qv inp (.HB 6 4) from g208,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 4 0 (by decide) (by decide)]; rfl⟩
  | 6, 4, 1, _, _, _ => exact ⟨e (.n 1302), outCell_sound _ σ KT 209 1302 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1302) = qv inp (.HB 6 4) from g209,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 4 1 (by decide) (by decide)]; rfl⟩
  | 6, 4, 2, _, _, _ => exact ⟨e (.n 1301), outCell_sound _ σ KT 210 1301 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1301) = qv inp (.HB 6 4) from g210,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 4 2 (by decide) (by decide)]; rfl⟩
  | 6, 4, 3, _, _, _ => exact ⟨e (.n 1300), outCell_sound _ σ KT 211 1300 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1300) = qv inp (.HB 6 4) from g211,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 4 3 (by decide) (by decide)]; rfl⟩
  | 6, 5, 0, _, _, _ => exact ⟨e (.n 1299), outCell_sound _ σ KT 212 1299 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1299) = qv inp (.HB 6 5) from g212,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 5 0 (by decide) (by decide)]; rfl⟩
  | 6, 5, 1, _, _, _ => exact ⟨e (.n 1298), outCell_sound _ σ KT 213 1298 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1298) = qv inp (.HB 6 5) from g213,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 5 1 (by decide) (by decide)]; rfl⟩
  | 6, 5, 2, _, _, _ => exact ⟨e (.n 1297), outCell_sound _ σ KT 214 1297 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1297) = qv inp (.HB 6 5) from g214,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 5 2 (by decide) (by decide)]; rfl⟩
  | 6, 5, 3, _, _, _ => exact ⟨e (.n 1296), outCell_sound _ σ KT 215 1296 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1296) = qv inp (.HB 6 5) from g215,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 5 3 (by decide) (by decide)]; rfl⟩
  | 6, 6, 0, _, _, _ => exact ⟨e (.n 1295), outCell_sound _ σ KT 216 1295 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1295) = qv inp (.HB 6 6) from g216,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 6 0 (by decide) (by decide)]; rfl⟩
  | 6, 6, 1, _, _, _ => exact ⟨e (.n 1294), outCell_sound _ σ KT 217 1294 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1294) = qv inp (.HB 6 6) from g217,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 6 1 (by decide) (by decide)]; rfl⟩
  | 6, 6, 2, _, _, _ => exact ⟨e (.n 1293), outCell_sound _ σ KT 218 1293 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1293) = qv inp (.HB 6 6) from g218,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 6 2 (by decide) (by decide)]; rfl⟩
  | 6, 6, 3, _, _, _ => exact ⟨e (.n 1292), outCell_sound _ σ KT 219 1292 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1292) = qv inp (.HB 6 6) from g219,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 6 3 (by decide) (by decide)]; rfl⟩
  | 6, 7, 0, _, _, _ => exact ⟨e (.n 1291), outCell_sound _ σ KT 220 1291 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1291) = qv inp (.HB 6 7) from g220,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 7 0 (by decide) (by decide)]; rfl⟩
  | 6, 7, 1, _, _, _ => exact ⟨e (.n 1290), outCell_sound _ σ KT 221 1290 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1290) = qv inp (.HB 6 7) from g221,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 7 1 (by decide) (by decide)]; rfl⟩
  | 6, 7, 2, _, _, _ => exact ⟨e (.n 1289), outCell_sound _ σ KT 222 1289 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1289) = qv inp (.HB 6 7) from g222,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 7 2 (by decide) (by decide)]; rfl⟩
  | 6, 7, 3, _, _, _ => exact ⟨e (.n 1288), outCell_sound _ σ KT 223 1288 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1288) = qv inp (.HB 6 7) from g223,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 7 3 (by decide) (by decide)]; rfl⟩
  | 7, 0, 0, _, _, _ => exact ⟨e (.n 1287), outCell_sound _ σ KT 224 1287 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1287) = qv inp (.HB 7 0) from g224,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 0 0 (by decide) (by decide)]; rfl⟩
  | 7, 0, 1, _, _, _ => exact ⟨e (.n 1286), outCell_sound _ σ KT 225 1286 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1286) = qv inp (.HB 7 0) from g225,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 0 1 (by decide) (by decide)]; rfl⟩
  | 7, 0, 2, _, _, _ => exact ⟨e (.n 1285), outCell_sound _ σ KT 226 1285 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1285) = qv inp (.HB 7 0) from g226,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 0 2 (by decide) (by decide)]; rfl⟩
  | 7, 0, 3, _, _, _ => exact ⟨e (.n 1284), outCell_sound _ σ KT 227 1284 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1284) = qv inp (.HB 7 0) from g227,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 0 3 (by decide) (by decide)]; rfl⟩
  | 7, 1, 0, _, _, _ => exact ⟨e (.n 1283), outCell_sound _ σ KT 228 1283 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1283) = qv inp (.HB 7 1) from g228,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 1 0 (by decide) (by decide)]; rfl⟩
  | 7, 1, 1, _, _, _ => exact ⟨e (.n 1282), outCell_sound _ σ KT 229 1282 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1282) = qv inp (.HB 7 1) from g229,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 1 1 (by decide) (by decide)]; rfl⟩
  | 7, 1, 2, _, _, _ => exact ⟨e (.n 1281), outCell_sound _ σ KT 230 1281 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1281) = qv inp (.HB 7 1) from g230,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 1 2 (by decide) (by decide)]; rfl⟩
  | 7, 1, 3, _, _, _ => exact ⟨e (.n 1280), outCell_sound _ σ KT 231 1280 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1280) = qv inp (.HB 7 1) from g231,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 1 3 (by decide) (by decide)]; rfl⟩
  | 7, 2, 0, _, _, _ => exact ⟨e (.n 1279), outCell_sound _ σ KT 232 1279 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1279) = qv inp (.HB 7 2) from g232,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 2 0 (by decide) (by decide)]; rfl⟩
  | 7, 2, 1, _, _, _ => exact ⟨e (.n 1278), outCell_sound _ σ KT 233 1278 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1278) = qv inp (.HB 7 2) from g233,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 2 1 (by decide) (by decide)]; rfl⟩
  | 7, 2, 2, _, _, _ => exact ⟨e (.n 1277), outCell_sound _ σ KT 234 1277 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1277) = qv inp (.HB 7 2) from g234,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 2 2 (by decide) (by decide)]; rfl⟩
  | 7, 2, 3, _, _, _ => exact ⟨e (.n 1276), outCell_sound _ σ KT 235 1276 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1276) = qv inp (.HB 7 2) from g235,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 2 3 (by decide) (by decide)]; rfl⟩
  | 7, 3, 0, _, _, _ => exact ⟨e (.n 1275), outCell_sound _ σ KT 236 1275 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1275) = qv inp (.HB 7 3) from g236,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 3 0 (by decide) (by decide)]; rfl⟩
  | 7, 3, 1, _, _, _ => exact ⟨e (.n 1274), outCell_sound _ σ KT 237 1274 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1274) = qv inp (.HB 7 3) from g237,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 3 1 (by decide) (by decide)]; rfl⟩
  | 7, 3, 2, _, _, _ => exact ⟨e (.n 1273), outCell_sound _ σ KT 238 1273 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1273) = qv inp (.HB 7 3) from g238,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 3 2 (by decide) (by decide)]; rfl⟩
  | 7, 3, 3, _, _, _ => exact ⟨e (.n 1272), outCell_sound _ σ KT 239 1272 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1272) = qv inp (.HB 7 3) from g239,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 3 3 (by decide) (by decide)]; rfl⟩
  | 7, 4, 0, _, _, _ => exact ⟨e (.n 1271), outCell_sound _ σ KT 240 1271 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1271) = qv inp (.HB 7 4) from g240,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 4 0 (by decide) (by decide)]; rfl⟩
  | 7, 4, 1, _, _, _ => exact ⟨e (.n 1270), outCell_sound _ σ KT 241 1270 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1270) = qv inp (.HB 7 4) from g241,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 4 1 (by decide) (by decide)]; rfl⟩
  | 7, 4, 2, _, _, _ => exact ⟨e (.n 1269), outCell_sound _ σ KT 242 1269 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1269) = qv inp (.HB 7 4) from g242,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 4 2 (by decide) (by decide)]; rfl⟩
  | 7, 4, 3, _, _, _ => exact ⟨e (.n 1268), outCell_sound _ σ KT 243 1268 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1268) = qv inp (.HB 7 4) from g243,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 4 3 (by decide) (by decide)]; rfl⟩
  | 7, 5, 0, _, _, _ => exact ⟨e (.n 1267), outCell_sound _ σ KT 244 1267 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1267) = qv inp (.HB 7 5) from g244,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 5 0 (by decide) (by decide)]; rfl⟩
  | 7, 5, 1, _, _, _ => exact ⟨e (.n 1266), outCell_sound _ σ KT 245 1266 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1266) = qv inp (.HB 7 5) from g245,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 5 1 (by decide) (by decide)]; rfl⟩
  | 7, 5, 2, _, _, _ => exact ⟨e (.n 1265), outCell_sound _ σ KT 246 1265 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1265) = qv inp (.HB 7 5) from g246,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 5 2 (by decide) (by decide)]; rfl⟩
  | 7, 5, 3, _, _, _ => exact ⟨e (.n 1264), outCell_sound _ σ KT 247 1264 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1264) = qv inp (.HB 7 5) from g247,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 5 3 (by decide) (by decide)]; rfl⟩
  | 7, 6, 0, _, _, _ => exact ⟨e (.n 1263), outCell_sound _ σ KT 248 1263 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1263) = qv inp (.HB 7 6) from g248,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 6 0 (by decide) (by decide)]; rfl⟩
  | 7, 6, 1, _, _, _ => exact ⟨e (.n 1262), outCell_sound _ σ KT 249 1262 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1262) = qv inp (.HB 7 6) from g249,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 6 1 (by decide) (by decide)]; rfl⟩
  | 7, 6, 2, _, _, _ => exact ⟨e (.n 1261), outCell_sound _ σ KT 250 1261 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1261) = qv inp (.HB 7 6) from g250,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 6 2 (by decide) (by decide)]; rfl⟩
  | 7, 6, 3, _, _, _ => exact ⟨e (.n 1260), outCell_sound _ σ KT 251 1260 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1260) = qv inp (.HB 7 6) from g251,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 6 3 (by decide) (by decide)]; rfl⟩
  | 7, 7, 0, _, _, _ => exact ⟨e (.n 1259), outCell_sound _ σ KT 252 1259 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1259) = qv inp (.HB 7 7) from g252,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 7 0 (by decide) (by decide)]; rfl⟩
  | 7, 7, 1, _, _, _ => exact ⟨e (.n 1258), outCell_sound _ σ KT 253 1258 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1258) = qv inp (.HB 7 7) from g253,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 7 1 (by decide) (by decide)]; rfl⟩
  | 7, 7, 2, _, _, _ => exact ⟨e (.n 1257), outCell_sound _ σ KT 254 1257 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1257) = qv inp (.HB 7 7) from g254,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 7 2 (by decide) (by decide)]; rfl⟩
  | 7, 7, 3, _, _, _ => exact ⟨e (.n 1256), outCell_sound _ σ KT 255 1256 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1256) = qv inp (.HB 7 7) from g255,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 7 3 (by decide) (by decide)]; rfl⟩
  | 8, 0, 0, _, _, _ => exact ⟨e (.n 1255), outCell_sound _ σ KT 256 1255 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1255) = qv inp (.HB 8 0) from g256,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 0 0 (by decide) (by decide)]; rfl⟩
  | 8, 0, 1, _, _, _ => exact ⟨e (.n 1254), outCell_sound _ σ KT 257 1254 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1254) = qv inp (.HB 8 0) from g257,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 0 1 (by decide) (by decide)]; rfl⟩
  | 8, 0, 2, _, _, _ => exact ⟨e (.n 1253), outCell_sound _ σ KT 258 1253 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1253) = qv inp (.HB 8 0) from g258,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 0 2 (by decide) (by decide)]; rfl⟩
  | 8, 0, 3, _, _, _ => exact ⟨e (.n 1252), outCell_sound _ σ KT 259 1252 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1252) = qv inp (.HB 8 0) from g259,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 0 3 (by decide) (by decide)]; rfl⟩
  | 8, 1, 0, _, _, _ => exact ⟨e (.n 1251), outCell_sound _ σ KT 260 1251 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1251) = qv inp (.HB 8 1) from g260,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 1 0 (by decide) (by decide)]; rfl⟩
  | 8, 1, 1, _, _, _ => exact ⟨e (.n 1250), outCell_sound _ σ KT 261 1250 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1250) = qv inp (.HB 8 1) from g261,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 1 1 (by decide) (by decide)]; rfl⟩
  | 8, 1, 2, _, _, _ => exact ⟨e (.n 1249), outCell_sound _ σ KT 262 1249 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1249) = qv inp (.HB 8 1) from g262,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 1 2 (by decide) (by decide)]; rfl⟩
  | 8, 1, 3, _, _, _ => exact ⟨e (.n 1248), outCell_sound _ σ KT 263 1248 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1248) = qv inp (.HB 8 1) from g263,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 1 3 (by decide) (by decide)]; rfl⟩
  | 8, 2, 0, _, _, _ => exact ⟨e (.n 1247), outCell_sound _ σ KT 264 1247 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1247) = qv inp (.HB 8 2) from g264,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 2 0 (by decide) (by decide)]; rfl⟩
  | 8, 2, 1, _, _, _ => exact ⟨e (.n 1246), outCell_sound _ σ KT 265 1246 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1246) = qv inp (.HB 8 2) from g265,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 2 1 (by decide) (by decide)]; rfl⟩
  | 8, 2, 2, _, _, _ => exact ⟨e (.n 1245), outCell_sound _ σ KT 266 1245 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1245) = qv inp (.HB 8 2) from g266,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 2 2 (by decide) (by decide)]; rfl⟩
  | 8, 2, 3, _, _, _ => exact ⟨e (.n 1244), outCell_sound _ σ KT 267 1244 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1244) = qv inp (.HB 8 2) from g267,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 2 3 (by decide) (by decide)]; rfl⟩
  | 8, 3, 0, _, _, _ => exact ⟨e (.n 1243), outCell_sound _ σ KT 268 1243 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1243) = qv inp (.HB 8 3) from g268,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 3 0 (by decide) (by decide)]; rfl⟩
  | 8, 3, 1, _, _, _ => exact ⟨e (.n 1242), outCell_sound _ σ KT 269 1242 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1242) = qv inp (.HB 8 3) from g269,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 3 1 (by decide) (by decide)]; rfl⟩
  | 8, 3, 2, _, _, _ => exact ⟨e (.n 1241), outCell_sound _ σ KT 270 1241 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1241) = qv inp (.HB 8 3) from g270,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 3 2 (by decide) (by decide)]; rfl⟩
  | 8, 3, 3, _, _, _ => exact ⟨e (.n 1240), outCell_sound _ σ KT 271 1240 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1240) = qv inp (.HB 8 3) from g271,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 3 3 (by decide) (by decide)]; rfl⟩
  | 8, 4, 0, _, _, _ => exact ⟨e (.n 1239), outCell_sound _ σ KT 272 1239 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1239) = qv inp (.HB 8 4) from g272,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 4 0 (by decide) (by decide)]; rfl⟩
  | 8, 4, 1, _, _, _ => exact ⟨e (.n 1238), outCell_sound _ σ KT 273 1238 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1238) = qv inp (.HB 8 4) from g273,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 4 1 (by decide) (by decide)]; rfl⟩
  | 8, 4, 2, _, _, _ => exact ⟨e (.n 1237), outCell_sound _ σ KT 274 1237 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1237) = qv inp (.HB 8 4) from g274,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 4 2 (by decide) (by decide)]; rfl⟩
  | 8, 4, 3, _, _, _ => exact ⟨e (.n 1236), outCell_sound _ σ KT 275 1236 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1236) = qv inp (.HB 8 4) from g275,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 4 3 (by decide) (by decide)]; rfl⟩
  | 8, 5, 0, _, _, _ => exact ⟨e (.n 1235), outCell_sound _ σ KT 276 1235 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1235) = qv inp (.HB 8 5) from g276,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 5 0 (by decide) (by decide)]; rfl⟩
  | 8, 5, 1, _, _, _ => exact ⟨e (.n 1234), outCell_sound _ σ KT 277 1234 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1234) = qv inp (.HB 8 5) from g277,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 5 1 (by decide) (by decide)]; rfl⟩
  | 8, 5, 2, _, _, _ => exact ⟨e (.n 1233), outCell_sound _ σ KT 278 1233 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1233) = qv inp (.HB 8 5) from g278,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 5 2 (by decide) (by decide)]; rfl⟩
  | 8, 5, 3, _, _, _ => exact ⟨e (.n 1232), outCell_sound _ σ KT 279 1232 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1232) = qv inp (.HB 8 5) from g279,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 5 3 (by decide) (by decide)]; rfl⟩
  | 8, 6, 0, _, _, _ => exact ⟨e (.n 1231), outCell_sound _ σ KT 280 1231 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1231) = qv inp (.HB 8 6) from g280,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 6 0 (by decide) (by decide)]; rfl⟩
  | 8, 6, 1, _, _, _ => exact ⟨e (.n 1230), outCell_sound _ σ KT 281 1230 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1230) = qv inp (.HB 8 6) from g281,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 6 1 (by decide) (by decide)]; rfl⟩
  | 8, 6, 2, _, _, _ => exact ⟨e (.n 1229), outCell_sound _ σ KT 282 1229 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1229) = qv inp (.HB 8 6) from g282,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 6 2 (by decide) (by decide)]; rfl⟩
  | 8, 6, 3, _, _, _ => exact ⟨e (.n 1228), outCell_sound _ σ KT 283 1228 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1228) = qv inp (.HB 8 6) from g283,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 6 3 (by decide) (by decide)]; rfl⟩
  | 8, 7, 0, _, _, _ => exact ⟨e (.n 1227), outCell_sound _ σ KT 284 1227 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1227) = qv inp (.HB 8 7) from g284,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 7 0 (by decide) (by decide)]; rfl⟩
  | 8, 7, 1, _, _, _ => exact ⟨e (.n 1226), outCell_sound _ σ KT 285 1226 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1226) = qv inp (.HB 8 7) from g285,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 7 1 (by decide) (by decide)]; rfl⟩
  | 8, 7, 2, _, _, _ => exact ⟨e (.n 1225), outCell_sound _ σ KT 286 1225 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1225) = qv inp (.HB 8 7) from g286,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 7 2 (by decide) (by decide)]; rfl⟩
  | 8, 7, 3, _, _, _ => exact ⟨e (.n 1224), outCell_sound _ σ KT 287 1224 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1224) = qv inp (.HB 8 7) from g287,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 7 3 (by decide) (by decide)]; rfl⟩
  | 9, 0, 0, _, _, _ => exact ⟨e (.n 1223), outCell_sound _ σ KT 288 1223 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1223) = qv inp (.HB 9 0) from g288,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 0 0 (by decide) (by decide)]; rfl⟩
  | 9, 0, 1, _, _, _ => exact ⟨e (.n 1222), outCell_sound _ σ KT 289 1222 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1222) = qv inp (.HB 9 0) from g289,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 0 1 (by decide) (by decide)]; rfl⟩
  | 9, 0, 2, _, _, _ => exact ⟨e (.n 1221), outCell_sound _ σ KT 290 1221 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1221) = qv inp (.HB 9 0) from g290,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 0 2 (by decide) (by decide)]; rfl⟩
  | 9, 0, 3, _, _, _ => exact ⟨e (.n 1220), outCell_sound _ σ KT 291 1220 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1220) = qv inp (.HB 9 0) from g291,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 0 3 (by decide) (by decide)]; rfl⟩
  | 9, 1, 0, _, _, _ => exact ⟨e (.n 1219), outCell_sound _ σ KT 292 1219 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1219) = qv inp (.HB 9 1) from g292,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 1 0 (by decide) (by decide)]; rfl⟩
  | 9, 1, 1, _, _, _ => exact ⟨e (.n 1218), outCell_sound _ σ KT 293 1218 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1218) = qv inp (.HB 9 1) from g293,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 1 1 (by decide) (by decide)]; rfl⟩
  | 9, 1, 2, _, _, _ => exact ⟨e (.n 1217), outCell_sound _ σ KT 294 1217 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1217) = qv inp (.HB 9 1) from g294,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 1 2 (by decide) (by decide)]; rfl⟩
  | 9, 1, 3, _, _, _ => exact ⟨e (.n 1216), outCell_sound _ σ KT 295 1216 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1216) = qv inp (.HB 9 1) from g295,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 1 3 (by decide) (by decide)]; rfl⟩
  | 9, 2, 0, _, _, _ => exact ⟨e (.n 1215), outCell_sound _ σ KT 296 1215 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1215) = qv inp (.HB 9 2) from g296,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 2 0 (by decide) (by decide)]; rfl⟩
  | 9, 2, 1, _, _, _ => exact ⟨e (.n 1214), outCell_sound _ σ KT 297 1214 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1214) = qv inp (.HB 9 2) from g297,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 2 1 (by decide) (by decide)]; rfl⟩
  | 9, 2, 2, _, _, _ => exact ⟨e (.n 1213), outCell_sound _ σ KT 298 1213 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1213) = qv inp (.HB 9 2) from g298,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 2 2 (by decide) (by decide)]; rfl⟩
  | 9, 2, 3, _, _, _ => exact ⟨e (.n 1212), outCell_sound _ σ KT 299 1212 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1212) = qv inp (.HB 9 2) from g299,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 2 3 (by decide) (by decide)]; rfl⟩
  | 9, 3, 0, _, _, _ => exact ⟨e (.n 1211), outCell_sound _ σ KT 300 1211 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1211) = qv inp (.HB 9 3) from g300,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 3 0 (by decide) (by decide)]; rfl⟩
  | 9, 3, 1, _, _, _ => exact ⟨e (.n 1210), outCell_sound _ σ KT 301 1210 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1210) = qv inp (.HB 9 3) from g301,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 3 1 (by decide) (by decide)]; rfl⟩
  | 9, 3, 2, _, _, _ => exact ⟨e (.n 1209), outCell_sound _ σ KT 302 1209 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1209) = qv inp (.HB 9 3) from g302,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 3 2 (by decide) (by decide)]; rfl⟩
  | 9, 3, 3, _, _, _ => exact ⟨e (.n 1208), outCell_sound _ σ KT 303 1208 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1208) = qv inp (.HB 9 3) from g303,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 3 3 (by decide) (by decide)]; rfl⟩
  | 9, 4, 0, _, _, _ => exact ⟨e (.n 1207), outCell_sound _ σ KT 304 1207 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1207) = qv inp (.HB 9 4) from g304,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 4 0 (by decide) (by decide)]; rfl⟩
  | 9, 4, 1, _, _, _ => exact ⟨e (.n 1206), outCell_sound _ σ KT 305 1206 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1206) = qv inp (.HB 9 4) from g305,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 4 1 (by decide) (by decide)]; rfl⟩
  | 9, 4, 2, _, _, _ => exact ⟨e (.n 1205), outCell_sound _ σ KT 306 1205 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1205) = qv inp (.HB 9 4) from g306,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 4 2 (by decide) (by decide)]; rfl⟩
  | 9, 4, 3, _, _, _ => exact ⟨e (.n 1204), outCell_sound _ σ KT 307 1204 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1204) = qv inp (.HB 9 4) from g307,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 4 3 (by decide) (by decide)]; rfl⟩
  | 9, 5, 0, _, _, _ => exact ⟨e (.n 1203), outCell_sound _ σ KT 308 1203 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1203) = qv inp (.HB 9 5) from g308,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 5 0 (by decide) (by decide)]; rfl⟩
  | 9, 5, 1, _, _, _ => exact ⟨e (.n 1202), outCell_sound _ σ KT 309 1202 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1202) = qv inp (.HB 9 5) from g309,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 5 1 (by decide) (by decide)]; rfl⟩
  | 9, 5, 2, _, _, _ => exact ⟨e (.n 1201), outCell_sound _ σ KT 310 1201 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1201) = qv inp (.HB 9 5) from g310,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 5 2 (by decide) (by decide)]; rfl⟩
  | 9, 5, 3, _, _, _ => exact ⟨e (.n 1200), outCell_sound _ σ KT 311 1200 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1200) = qv inp (.HB 9 5) from g311,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 5 3 (by decide) (by decide)]; rfl⟩
  | 9, 6, 0, _, _, _ => exact ⟨e (.n 1199), outCell_sound _ σ KT 312 1199 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1199) = qv inp (.HB 9 6) from g312,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 6 0 (by decide) (by decide)]; rfl⟩
  | 9, 6, 1, _, _, _ => exact ⟨e (.n 1198), outCell_sound _ σ KT 313 1198 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1198) = qv inp (.HB 9 6) from g313,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 6 1 (by decide) (by decide)]; rfl⟩
  | 9, 6, 2, _, _, _ => exact ⟨e (.n 1197), outCell_sound _ σ KT 314 1197 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1197) = qv inp (.HB 9 6) from g314,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 6 2 (by decide) (by decide)]; rfl⟩
  | 9, 6, 3, _, _, _ => exact ⟨e (.n 1196), outCell_sound _ σ KT 315 1196 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1196) = qv inp (.HB 9 6) from g315,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 6 3 (by decide) (by decide)]; rfl⟩
  | 9, 7, 0, _, _, _ => exact ⟨e (.n 1195), outCell_sound _ σ KT 316 1195 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1195) = qv inp (.HB 9 7) from g316,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 7 0 (by decide) (by decide)]; rfl⟩
  | 9, 7, 1, _, _, _ => exact ⟨e (.n 1194), outCell_sound _ σ KT 317 1194 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1194) = qv inp (.HB 9 7) from g317,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 7 1 (by decide) (by decide)]; rfl⟩
  | 9, 7, 2, _, _, _ => exact ⟨e (.n 1193), outCell_sound _ σ KT 318 1193 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1193) = qv inp (.HB 9 7) from g318,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 7 2 (by decide) (by decide)]; rfl⟩
  | 9, 7, 3, _, _, _ => exact ⟨e (.n 1192), outCell_sound _ σ KT 319 1192 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1192) = qv inp (.HB 9 7) from g319,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 7 3 (by decide) (by decide)]; rfl⟩
  | 10, 0, 0, _, _, _ => exact ⟨e (.n 1191), outCell_sound _ σ KT 320 1191 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1191) = qv inp (.HB 10 0) from g320,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 0 0 (by decide) (by decide)]; rfl⟩
  | 10, 0, 1, _, _, _ => exact ⟨e (.n 1190), outCell_sound _ σ KT 321 1190 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1190) = qv inp (.HB 10 0) from g321,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 0 1 (by decide) (by decide)]; rfl⟩
  | 10, 0, 2, _, _, _ => exact ⟨e (.n 1189), outCell_sound _ σ KT 322 1189 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1189) = qv inp (.HB 10 0) from g322,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 0 2 (by decide) (by decide)]; rfl⟩
  | 10, 0, 3, _, _, _ => exact ⟨e (.n 1188), outCell_sound _ σ KT 323 1188 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1188) = qv inp (.HB 10 0) from g323,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 0 3 (by decide) (by decide)]; rfl⟩
  | 10, 1, 0, _, _, _ => exact ⟨e (.n 1187), outCell_sound _ σ KT 324 1187 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1187) = qv inp (.HB 10 1) from g324,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 1 0 (by decide) (by decide)]; rfl⟩
  | 10, 1, 1, _, _, _ => exact ⟨e (.n 1186), outCell_sound _ σ KT 325 1186 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1186) = qv inp (.HB 10 1) from g325,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 1 1 (by decide) (by decide)]; rfl⟩
  | 10, 1, 2, _, _, _ => exact ⟨e (.n 1185), outCell_sound _ σ KT 326 1185 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1185) = qv inp (.HB 10 1) from g326,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 1 2 (by decide) (by decide)]; rfl⟩
  | 10, 1, 3, _, _, _ => exact ⟨e (.n 1184), outCell_sound _ σ KT 327 1184 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1184) = qv inp (.HB 10 1) from g327,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 1 3 (by decide) (by decide)]; rfl⟩
  | 10, 2, 0, _, _, _ => exact ⟨e (.n 1183), outCell_sound _ σ KT 328 1183 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1183) = qv inp (.HB 10 2) from g328,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 2 0 (by decide) (by decide)]; rfl⟩
  | 10, 2, 1, _, _, _ => exact ⟨e (.n 1182), outCell_sound _ σ KT 329 1182 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1182) = qv inp (.HB 10 2) from g329,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 2 1 (by decide) (by decide)]; rfl⟩
  | 10, 2, 2, _, _, _ => exact ⟨e (.n 1181), outCell_sound _ σ KT 330 1181 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1181) = qv inp (.HB 10 2) from g330,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 2 2 (by decide) (by decide)]; rfl⟩
  | 10, 2, 3, _, _, _ => exact ⟨e (.n 1180), outCell_sound _ σ KT 331 1180 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1180) = qv inp (.HB 10 2) from g331,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 2 3 (by decide) (by decide)]; rfl⟩
  | 10, 3, 0, _, _, _ => exact ⟨e (.n 1179), outCell_sound _ σ KT 332 1179 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1179) = qv inp (.HB 10 3) from g332,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 3 0 (by decide) (by decide)]; rfl⟩
  | 10, 3, 1, _, _, _ => exact ⟨e (.n 1178), outCell_sound _ σ KT 333 1178 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1178) = qv inp (.HB 10 3) from g333,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 3 1 (by decide) (by decide)]; rfl⟩
  | 10, 3, 2, _, _, _ => exact ⟨e (.n 1177), outCell_sound _ σ KT 334 1177 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1177) = qv inp (.HB 10 3) from g334,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 3 2 (by decide) (by decide)]; rfl⟩
  | 10, 3, 3, _, _, _ => exact ⟨e (.n 1176), outCell_sound _ σ KT 335 1176 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1176) = qv inp (.HB 10 3) from g335,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 3 3 (by decide) (by decide)]; rfl⟩
  | 10, 4, 0, _, _, _ => exact ⟨e (.n 1175), outCell_sound _ σ KT 336 1175 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1175) = qv inp (.HB 10 4) from g336,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 4 0 (by decide) (by decide)]; rfl⟩
  | 10, 4, 1, _, _, _ => exact ⟨e (.n 1174), outCell_sound _ σ KT 337 1174 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1174) = qv inp (.HB 10 4) from g337,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 4 1 (by decide) (by decide)]; rfl⟩
  | 10, 4, 2, _, _, _ => exact ⟨e (.n 1173), outCell_sound _ σ KT 338 1173 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1173) = qv inp (.HB 10 4) from g338,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 4 2 (by decide) (by decide)]; rfl⟩
  | 10, 4, 3, _, _, _ => exact ⟨e (.n 1172), outCell_sound _ σ KT 339 1172 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1172) = qv inp (.HB 10 4) from g339,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 4 3 (by decide) (by decide)]; rfl⟩
  | 10, 5, 0, _, _, _ => exact ⟨e (.n 1171), outCell_sound _ σ KT 340 1171 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1171) = qv inp (.HB 10 5) from g340,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 5 0 (by decide) (by decide)]; rfl⟩
  | 10, 5, 1, _, _, _ => exact ⟨e (.n 1170), outCell_sound _ σ KT 341 1170 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1170) = qv inp (.HB 10 5) from g341,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 5 1 (by decide) (by decide)]; rfl⟩
  | 10, 5, 2, _, _, _ => exact ⟨e (.n 1169), outCell_sound _ σ KT 342 1169 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1169) = qv inp (.HB 10 5) from g342,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 5 2 (by decide) (by decide)]; rfl⟩
  | 10, 5, 3, _, _, _ => exact ⟨e (.n 1168), outCell_sound _ σ KT 343 1168 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1168) = qv inp (.HB 10 5) from g343,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 5 3 (by decide) (by decide)]; rfl⟩
  | 10, 6, 0, _, _, _ => exact ⟨e (.n 1167), outCell_sound _ σ KT 344 1167 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1167) = qv inp (.HB 10 6) from g344,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 6 0 (by decide) (by decide)]; rfl⟩
  | 10, 6, 1, _, _, _ => exact ⟨e (.n 1166), outCell_sound _ σ KT 345 1166 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1166) = qv inp (.HB 10 6) from g345,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 6 1 (by decide) (by decide)]; rfl⟩
  | 10, 6, 2, _, _, _ => exact ⟨e (.n 1165), outCell_sound _ σ KT 346 1165 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1165) = qv inp (.HB 10 6) from g346,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 6 2 (by decide) (by decide)]; rfl⟩
  | 10, 6, 3, _, _, _ => exact ⟨e (.n 1164), outCell_sound _ σ KT 347 1164 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1164) = qv inp (.HB 10 6) from g347,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 6 3 (by decide) (by decide)]; rfl⟩
  | 10, 7, 0, _, _, _ => exact ⟨e (.n 1163), outCell_sound _ σ KT 348 1163 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1163) = qv inp (.HB 10 7) from g348,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 7 0 (by decide) (by decide)]; rfl⟩
  | 10, 7, 1, _, _, _ => exact ⟨e (.n 1162), outCell_sound _ σ KT 349 1162 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1162) = qv inp (.HB 10 7) from g349,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 7 1 (by decide) (by decide)]; rfl⟩
  | 10, 7, 2, _, _, _ => exact ⟨e (.n 1161), outCell_sound _ σ KT 350 1161 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1161) = qv inp (.HB 10 7) from g350,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 7 2 (by decide) (by decide)]; rfl⟩
  | 10, 7, 3, _, _, _ => exact ⟨e (.n 1160), outCell_sound _ σ KT 351 1160 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1160) = qv inp (.HB 10 7) from g351,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 7 3 (by decide) (by decide)]; rfl⟩
  | 11, 0, 0, _, _, _ => exact ⟨e (.n 1159), outCell_sound _ σ KT 352 1159 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1159) = qv inp (.HB 11 0) from g352,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 0 0 (by decide) (by decide)]; rfl⟩
  | 11, 0, 1, _, _, _ => exact ⟨e (.n 1158), outCell_sound _ σ KT 353 1158 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1158) = qv inp (.HB 11 0) from g353,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 0 1 (by decide) (by decide)]; rfl⟩
  | 11, 0, 2, _, _, _ => exact ⟨e (.n 1157), outCell_sound _ σ KT 354 1157 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1157) = qv inp (.HB 11 0) from g354,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 0 2 (by decide) (by decide)]; rfl⟩
  | 11, 0, 3, _, _, _ => exact ⟨e (.n 1156), outCell_sound _ σ KT 355 1156 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1156) = qv inp (.HB 11 0) from g355,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 0 3 (by decide) (by decide)]; rfl⟩
  | 11, 1, 0, _, _, _ => exact ⟨e (.n 1155), outCell_sound _ σ KT 356 1155 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1155) = qv inp (.HB 11 1) from g356,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 1 0 (by decide) (by decide)]; rfl⟩
  | 11, 1, 1, _, _, _ => exact ⟨e (.n 1154), outCell_sound _ σ KT 357 1154 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1154) = qv inp (.HB 11 1) from g357,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 1 1 (by decide) (by decide)]; rfl⟩
  | 11, 1, 2, _, _, _ => exact ⟨e (.n 1153), outCell_sound _ σ KT 358 1153 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1153) = qv inp (.HB 11 1) from g358,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 1 2 (by decide) (by decide)]; rfl⟩
  | 11, 1, 3, _, _, _ => exact ⟨e (.n 1152), outCell_sound _ σ KT 359 1152 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1152) = qv inp (.HB 11 1) from g359,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 1 3 (by decide) (by decide)]; rfl⟩
  | 11, 2, 0, _, _, _ => exact ⟨e (.n 1151), outCell_sound _ σ KT 360 1151 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1151) = qv inp (.HB 11 2) from g360,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 2 0 (by decide) (by decide)]; rfl⟩
  | 11, 2, 1, _, _, _ => exact ⟨e (.n 1150), outCell_sound _ σ KT 361 1150 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1150) = qv inp (.HB 11 2) from g361,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 2 1 (by decide) (by decide)]; rfl⟩
  | 11, 2, 2, _, _, _ => exact ⟨e (.n 1149), outCell_sound _ σ KT 362 1149 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1149) = qv inp (.HB 11 2) from g362,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 2 2 (by decide) (by decide)]; rfl⟩
  | 11, 2, 3, _, _, _ => exact ⟨e (.n 1148), outCell_sound _ σ KT 363 1148 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1148) = qv inp (.HB 11 2) from g363,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 2 3 (by decide) (by decide)]; rfl⟩
  | 11, 3, 0, _, _, _ => exact ⟨e (.n 1147), outCell_sound _ σ KT 364 1147 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1147) = qv inp (.HB 11 3) from g364,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 3 0 (by decide) (by decide)]; rfl⟩
  | 11, 3, 1, _, _, _ => exact ⟨e (.n 1146), outCell_sound _ σ KT 365 1146 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1146) = qv inp (.HB 11 3) from g365,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 3 1 (by decide) (by decide)]; rfl⟩
  | 11, 3, 2, _, _, _ => exact ⟨e (.n 1145), outCell_sound _ σ KT 366 1145 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1145) = qv inp (.HB 11 3) from g366,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 3 2 (by decide) (by decide)]; rfl⟩
  | 11, 3, 3, _, _, _ => exact ⟨e (.n 1144), outCell_sound _ σ KT 367 1144 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1144) = qv inp (.HB 11 3) from g367,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 3 3 (by decide) (by decide)]; rfl⟩
  | 11, 4, 0, _, _, _ => exact ⟨e (.n 1143), outCell_sound _ σ KT 368 1143 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1143) = qv inp (.HB 11 4) from g368,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 4 0 (by decide) (by decide)]; rfl⟩
  | 11, 4, 1, _, _, _ => exact ⟨e (.n 1142), outCell_sound _ σ KT 369 1142 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1142) = qv inp (.HB 11 4) from g369,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 4 1 (by decide) (by decide)]; rfl⟩
  | 11, 4, 2, _, _, _ => exact ⟨e (.n 1141), outCell_sound _ σ KT 370 1141 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1141) = qv inp (.HB 11 4) from g370,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 4 2 (by decide) (by decide)]; rfl⟩
  | 11, 4, 3, _, _, _ => exact ⟨e (.n 1140), outCell_sound _ σ KT 371 1140 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1140) = qv inp (.HB 11 4) from g371,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 4 3 (by decide) (by decide)]; rfl⟩
  | 11, 5, 0, _, _, _ => exact ⟨e (.n 1139), outCell_sound _ σ KT 372 1139 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1139) = qv inp (.HB 11 5) from g372,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 5 0 (by decide) (by decide)]; rfl⟩
  | 11, 5, 1, _, _, _ => exact ⟨e (.n 1138), outCell_sound _ σ KT 373 1138 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1138) = qv inp (.HB 11 5) from g373,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 5 1 (by decide) (by decide)]; rfl⟩
  | 11, 5, 2, _, _, _ => exact ⟨e (.n 1137), outCell_sound _ σ KT 374 1137 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1137) = qv inp (.HB 11 5) from g374,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 5 2 (by decide) (by decide)]; rfl⟩
  | 11, 5, 3, _, _, _ => exact ⟨e (.n 1136), outCell_sound _ σ KT 375 1136 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1136) = qv inp (.HB 11 5) from g375,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 5 3 (by decide) (by decide)]; rfl⟩
  | 11, 6, 0, _, _, _ => exact ⟨e (.n 1135), outCell_sound _ σ KT 376 1135 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1135) = qv inp (.HB 11 6) from g376,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 6 0 (by decide) (by decide)]; rfl⟩
  | 11, 6, 1, _, _, _ => exact ⟨e (.n 1134), outCell_sound _ σ KT 377 1134 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1134) = qv inp (.HB 11 6) from g377,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 6 1 (by decide) (by decide)]; rfl⟩
  | 11, 6, 2, _, _, _ => exact ⟨e (.n 1133), outCell_sound _ σ KT 378 1133 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1133) = qv inp (.HB 11 6) from g378,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 6 2 (by decide) (by decide)]; rfl⟩
  | 11, 6, 3, _, _, _ => exact ⟨e (.n 1132), outCell_sound _ σ KT 379 1132 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1132) = qv inp (.HB 11 6) from g379,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 6 3 (by decide) (by decide)]; rfl⟩
  | 11, 7, 0, _, _, _ => exact ⟨e (.n 1131), outCell_sound _ σ KT 380 1131 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1131) = qv inp (.HB 11 7) from g380,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 7 0 (by decide) (by decide)]; rfl⟩
  | 11, 7, 1, _, _, _ => exact ⟨e (.n 1130), outCell_sound _ σ KT 381 1130 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1130) = qv inp (.HB 11 7) from g381,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 7 1 (by decide) (by decide)]; rfl⟩
  | 11, 7, 2, _, _, _ => exact ⟨e (.n 1129), outCell_sound _ σ KT 382 1129 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1129) = qv inp (.HB 11 7) from g382,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 7 2 (by decide) (by decide)]; rfl⟩
  | 11, 7, 3, _, _, _ => exact ⟨e (.n 1128), outCell_sound _ σ KT 383 1128 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1128) = qv inp (.HB 11 7) from g383,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 7 3 (by decide) (by decide)]; rfl⟩
  | 12, 0, 0, _, _, _ => exact ⟨e (.n 1127), outCell_sound _ σ KT 384 1127 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1127) = qv inp (.HB 12 0) from g384,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 0 0 (by decide) (by decide)]; rfl⟩
  | 12, 0, 1, _, _, _ => exact ⟨e (.n 1126), outCell_sound _ σ KT 385 1126 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1126) = qv inp (.HB 12 0) from g385,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 0 1 (by decide) (by decide)]; rfl⟩
  | 12, 0, 2, _, _, _ => exact ⟨e (.n 1125), outCell_sound _ σ KT 386 1125 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1125) = qv inp (.HB 12 0) from g386,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 0 2 (by decide) (by decide)]; rfl⟩
  | 12, 0, 3, _, _, _ => exact ⟨e (.n 1124), outCell_sound _ σ KT 387 1124 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1124) = qv inp (.HB 12 0) from g387,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 0 3 (by decide) (by decide)]; rfl⟩
  | 12, 1, 0, _, _, _ => exact ⟨e (.n 1123), outCell_sound _ σ KT 388 1123 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1123) = qv inp (.HB 12 1) from g388,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 1 0 (by decide) (by decide)]; rfl⟩
  | 12, 1, 1, _, _, _ => exact ⟨e (.n 1122), outCell_sound _ σ KT 389 1122 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1122) = qv inp (.HB 12 1) from g389,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 1 1 (by decide) (by decide)]; rfl⟩
  | 12, 1, 2, _, _, _ => exact ⟨e (.n 1121), outCell_sound _ σ KT 390 1121 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1121) = qv inp (.HB 12 1) from g390,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 1 2 (by decide) (by decide)]; rfl⟩
  | 12, 1, 3, _, _, _ => exact ⟨e (.n 1120), outCell_sound _ σ KT 391 1120 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1120) = qv inp (.HB 12 1) from g391,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 1 3 (by decide) (by decide)]; rfl⟩
  | 12, 2, 0, _, _, _ => exact ⟨e (.n 1119), outCell_sound _ σ KT 392 1119 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1119) = qv inp (.HB 12 2) from g392,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 2 0 (by decide) (by decide)]; rfl⟩
  | 12, 2, 1, _, _, _ => exact ⟨e (.n 1118), outCell_sound _ σ KT 393 1118 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1118) = qv inp (.HB 12 2) from g393,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 2 1 (by decide) (by decide)]; rfl⟩
  | 12, 2, 2, _, _, _ => exact ⟨e (.n 1117), outCell_sound _ σ KT 394 1117 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1117) = qv inp (.HB 12 2) from g394,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 2 2 (by decide) (by decide)]; rfl⟩
  | 12, 2, 3, _, _, _ => exact ⟨e (.n 1116), outCell_sound _ σ KT 395 1116 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1116) = qv inp (.HB 12 2) from g395,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 2 3 (by decide) (by decide)]; rfl⟩
  | 12, 3, 0, _, _, _ => exact ⟨e (.n 1115), outCell_sound _ σ KT 396 1115 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1115) = qv inp (.HB 12 3) from g396,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 3 0 (by decide) (by decide)]; rfl⟩
  | 12, 3, 1, _, _, _ => exact ⟨e (.n 1114), outCell_sound _ σ KT 397 1114 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1114) = qv inp (.HB 12 3) from g397,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 3 1 (by decide) (by decide)]; rfl⟩
  | 12, 3, 2, _, _, _ => exact ⟨e (.n 1113), outCell_sound _ σ KT 398 1113 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1113) = qv inp (.HB 12 3) from g398,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 3 2 (by decide) (by decide)]; rfl⟩
  | 12, 3, 3, _, _, _ => exact ⟨e (.n 1112), outCell_sound _ σ KT 399 1112 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1112) = qv inp (.HB 12 3) from g399,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 3 3 (by decide) (by decide)]; rfl⟩
  | 12, 4, 0, _, _, _ => exact ⟨e (.n 1111), outCell_sound _ σ KT 400 1111 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1111) = qv inp (.HB 12 4) from g400,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 4 0 (by decide) (by decide)]; rfl⟩
  | 12, 4, 1, _, _, _ => exact ⟨e (.n 1110), outCell_sound _ σ KT 401 1110 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1110) = qv inp (.HB 12 4) from g401,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 4 1 (by decide) (by decide)]; rfl⟩
  | 12, 4, 2, _, _, _ => exact ⟨e (.n 1109), outCell_sound _ σ KT 402 1109 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1109) = qv inp (.HB 12 4) from g402,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 4 2 (by decide) (by decide)]; rfl⟩
  | 12, 4, 3, _, _, _ => exact ⟨e (.n 1108), outCell_sound _ σ KT 403 1108 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1108) = qv inp (.HB 12 4) from g403,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 4 3 (by decide) (by decide)]; rfl⟩
  | 12, 5, 0, _, _, _ => exact ⟨e (.n 1107), outCell_sound _ σ KT 404 1107 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1107) = qv inp (.HB 12 5) from g404,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 5 0 (by decide) (by decide)]; rfl⟩
  | 12, 5, 1, _, _, _ => exact ⟨e (.n 1106), outCell_sound _ σ KT 405 1106 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1106) = qv inp (.HB 12 5) from g405,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 5 1 (by decide) (by decide)]; rfl⟩
  | 12, 5, 2, _, _, _ => exact ⟨e (.n 1105), outCell_sound _ σ KT 406 1105 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1105) = qv inp (.HB 12 5) from g406,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 5 2 (by decide) (by decide)]; rfl⟩
  | 12, 5, 3, _, _, _ => exact ⟨e (.n 1104), outCell_sound _ σ KT 407 1104 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1104) = qv inp (.HB 12 5) from g407,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 5 3 (by decide) (by decide)]; rfl⟩
  | 12, 6, 0, _, _, _ => exact ⟨e (.n 1103), outCell_sound _ σ KT 408 1103 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1103) = qv inp (.HB 12 6) from g408,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 6 0 (by decide) (by decide)]; rfl⟩
  | 12, 6, 1, _, _, _ => exact ⟨e (.n 1102), outCell_sound _ σ KT 409 1102 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1102) = qv inp (.HB 12 6) from g409,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 6 1 (by decide) (by decide)]; rfl⟩
  | 12, 6, 2, _, _, _ => exact ⟨e (.n 1101), outCell_sound _ σ KT 410 1101 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1101) = qv inp (.HB 12 6) from g410,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 6 2 (by decide) (by decide)]; rfl⟩
  | 12, 6, 3, _, _, _ => exact ⟨e (.n 1100), outCell_sound _ σ KT 411 1100 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1100) = qv inp (.HB 12 6) from g411,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 6 3 (by decide) (by decide)]; rfl⟩
  | 12, 7, 0, _, _, _ => exact ⟨e (.n 1099), outCell_sound _ σ KT 412 1099 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1099) = qv inp (.HB 12 7) from g412,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 7 0 (by decide) (by decide)]; rfl⟩
  | 12, 7, 1, _, _, _ => exact ⟨e (.n 1098), outCell_sound _ σ KT 413 1098 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1098) = qv inp (.HB 12 7) from g413,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 7 1 (by decide) (by decide)]; rfl⟩
  | 12, 7, 2, _, _, _ => exact ⟨e (.n 1097), outCell_sound _ σ KT 414 1097 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1097) = qv inp (.HB 12 7) from g414,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 7 2 (by decide) (by decide)]; rfl⟩
  | 12, 7, 3, _, _, _ => exact ⟨e (.n 1096), outCell_sound _ σ KT 415 1096 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1096) = qv inp (.HB 12 7) from g415,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 7 3 (by decide) (by decide)]; rfl⟩
  | 13, 0, 0, _, _, _ => exact ⟨e (.n 1095), outCell_sound _ σ KT 416 1095 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1095) = qv inp (.HB 13 0) from g416,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 0 0 (by decide) (by decide)]; rfl⟩
  | 13, 0, 1, _, _, _ => exact ⟨e (.n 1094), outCell_sound _ σ KT 417 1094 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1094) = qv inp (.HB 13 0) from g417,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 0 1 (by decide) (by decide)]; rfl⟩
  | 13, 0, 2, _, _, _ => exact ⟨e (.n 1093), outCell_sound _ σ KT 418 1093 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1093) = qv inp (.HB 13 0) from g418,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 0 2 (by decide) (by decide)]; rfl⟩
  | 13, 0, 3, _, _, _ => exact ⟨e (.n 1092), outCell_sound _ σ KT 419 1092 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1092) = qv inp (.HB 13 0) from g419,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 0 3 (by decide) (by decide)]; rfl⟩
  | 13, 1, 0, _, _, _ => exact ⟨e (.n 1091), outCell_sound _ σ KT 420 1091 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1091) = qv inp (.HB 13 1) from g420,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 1 0 (by decide) (by decide)]; rfl⟩
  | 13, 1, 1, _, _, _ => exact ⟨e (.n 1090), outCell_sound _ σ KT 421 1090 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1090) = qv inp (.HB 13 1) from g421,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 1 1 (by decide) (by decide)]; rfl⟩
  | 13, 1, 2, _, _, _ => exact ⟨e (.n 1089), outCell_sound _ σ KT 422 1089 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1089) = qv inp (.HB 13 1) from g422,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 1 2 (by decide) (by decide)]; rfl⟩
  | 13, 1, 3, _, _, _ => exact ⟨e (.n 1088), outCell_sound _ σ KT 423 1088 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1088) = qv inp (.HB 13 1) from g423,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 1 3 (by decide) (by decide)]; rfl⟩
  | 13, 2, 0, _, _, _ => exact ⟨e (.n 1087), outCell_sound _ σ KT 424 1087 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1087) = qv inp (.HB 13 2) from g424,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 2 0 (by decide) (by decide)]; rfl⟩
  | 13, 2, 1, _, _, _ => exact ⟨e (.n 1086), outCell_sound _ σ KT 425 1086 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1086) = qv inp (.HB 13 2) from g425,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 2 1 (by decide) (by decide)]; rfl⟩
  | 13, 2, 2, _, _, _ => exact ⟨e (.n 1085), outCell_sound _ σ KT 426 1085 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1085) = qv inp (.HB 13 2) from g426,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 2 2 (by decide) (by decide)]; rfl⟩
  | 13, 2, 3, _, _, _ => exact ⟨e (.n 1084), outCell_sound _ σ KT 427 1084 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1084) = qv inp (.HB 13 2) from g427,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 2 3 (by decide) (by decide)]; rfl⟩
  | 13, 3, 0, _, _, _ => exact ⟨e (.n 1083), outCell_sound _ σ KT 428 1083 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1083) = qv inp (.HB 13 3) from g428,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 3 0 (by decide) (by decide)]; rfl⟩
  | 13, 3, 1, _, _, _ => exact ⟨e (.n 1082), outCell_sound _ σ KT 429 1082 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1082) = qv inp (.HB 13 3) from g429,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 3 1 (by decide) (by decide)]; rfl⟩
  | 13, 3, 2, _, _, _ => exact ⟨e (.n 1081), outCell_sound _ σ KT 430 1081 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1081) = qv inp (.HB 13 3) from g430,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 3 2 (by decide) (by decide)]; rfl⟩
  | 13, 3, 3, _, _, _ => exact ⟨e (.n 1080), outCell_sound _ σ KT 431 1080 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1080) = qv inp (.HB 13 3) from g431,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 3 3 (by decide) (by decide)]; rfl⟩
  | 13, 4, 0, _, _, _ => exact ⟨e (.n 1079), outCell_sound _ σ KT 432 1079 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1079) = qv inp (.HB 13 4) from g432,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 4 0 (by decide) (by decide)]; rfl⟩
  | 13, 4, 1, _, _, _ => exact ⟨e (.n 1078), outCell_sound _ σ KT 433 1078 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1078) = qv inp (.HB 13 4) from g433,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 4 1 (by decide) (by decide)]; rfl⟩
  | 13, 4, 2, _, _, _ => exact ⟨e (.n 1077), outCell_sound _ σ KT 434 1077 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1077) = qv inp (.HB 13 4) from g434,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 4 2 (by decide) (by decide)]; rfl⟩
  | 13, 4, 3, _, _, _ => exact ⟨e (.n 1076), outCell_sound _ σ KT 435 1076 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1076) = qv inp (.HB 13 4) from g435,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 4 3 (by decide) (by decide)]; rfl⟩
  | 13, 5, 0, _, _, _ => exact ⟨e (.n 1075), outCell_sound _ σ KT 436 1075 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1075) = qv inp (.HB 13 5) from g436,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 5 0 (by decide) (by decide)]; rfl⟩
  | 13, 5, 1, _, _, _ => exact ⟨e (.n 1074), outCell_sound _ σ KT 437 1074 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1074) = qv inp (.HB 13 5) from g437,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 5 1 (by decide) (by decide)]; rfl⟩
  | 13, 5, 2, _, _, _ => exact ⟨e (.n 1073), outCell_sound _ σ KT 438 1073 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1073) = qv inp (.HB 13 5) from g438,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 5 2 (by decide) (by decide)]; rfl⟩
  | 13, 5, 3, _, _, _ => exact ⟨e (.n 1072), outCell_sound _ σ KT 439 1072 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1072) = qv inp (.HB 13 5) from g439,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 5 3 (by decide) (by decide)]; rfl⟩
  | 13, 6, 0, _, _, _ => exact ⟨e (.n 1071), outCell_sound _ σ KT 440 1071 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1071) = qv inp (.HB 13 6) from g440,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 6 0 (by decide) (by decide)]; rfl⟩
  | 13, 6, 1, _, _, _ => exact ⟨e (.n 1070), outCell_sound _ σ KT 441 1070 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1070) = qv inp (.HB 13 6) from g441,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 6 1 (by decide) (by decide)]; rfl⟩
  | 13, 6, 2, _, _, _ => exact ⟨e (.n 1069), outCell_sound _ σ KT 442 1069 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1069) = qv inp (.HB 13 6) from g442,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 6 2 (by decide) (by decide)]; rfl⟩
  | 13, 6, 3, _, _, _ => exact ⟨e (.n 1068), outCell_sound _ σ KT 443 1068 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1068) = qv inp (.HB 13 6) from g443,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 6 3 (by decide) (by decide)]; rfl⟩
  | 13, 7, 0, _, _, _ => exact ⟨e (.n 1067), outCell_sound _ σ KT 444 1067 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1067) = qv inp (.HB 13 7) from g444,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 7 0 (by decide) (by decide)]; rfl⟩
  | 13, 7, 1, _, _, _ => exact ⟨e (.n 1066), outCell_sound _ σ KT 445 1066 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1066) = qv inp (.HB 13 7) from g445,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 7 1 (by decide) (by decide)]; rfl⟩
  | 13, 7, 2, _, _, _ => exact ⟨e (.n 1065), outCell_sound _ σ KT 446 1065 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1065) = qv inp (.HB 13 7) from g446,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 7 2 (by decide) (by decide)]; rfl⟩
  | 13, 7, 3, _, _, _ => exact ⟨e (.n 1064), outCell_sound _ σ KT 447 1064 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1064) = qv inp (.HB 13 7) from g447,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 7 3 (by decide) (by decide)]; rfl⟩
  | 14, 0, 0, _, _, _ => exact ⟨e (.n 1063), outCell_sound _ σ KT 448 1063 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1063) = qv inp (.HB 14 0) from g448,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 0 0 (by decide) (by decide)]; rfl⟩
  | 14, 0, 1, _, _, _ => exact ⟨e (.n 1062), outCell_sound _ σ KT 449 1062 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1062) = qv inp (.HB 14 0) from g449,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 0 1 (by decide) (by decide)]; rfl⟩
  | 14, 0, 2, _, _, _ => exact ⟨e (.n 1061), outCell_sound _ σ KT 450 1061 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1061) = qv inp (.HB 14 0) from g450,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 0 2 (by decide) (by decide)]; rfl⟩
  | 14, 0, 3, _, _, _ => exact ⟨e (.n 1060), outCell_sound _ σ KT 451 1060 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1060) = qv inp (.HB 14 0) from g451,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 0 3 (by decide) (by decide)]; rfl⟩
  | 14, 1, 0, _, _, _ => exact ⟨e (.n 1059), outCell_sound _ σ KT 452 1059 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1059) = qv inp (.HB 14 1) from g452,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 1 0 (by decide) (by decide)]; rfl⟩
  | 14, 1, 1, _, _, _ => exact ⟨e (.n 1058), outCell_sound _ σ KT 453 1058 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1058) = qv inp (.HB 14 1) from g453,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 1 1 (by decide) (by decide)]; rfl⟩
  | 14, 1, 2, _, _, _ => exact ⟨e (.n 1057), outCell_sound _ σ KT 454 1057 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1057) = qv inp (.HB 14 1) from g454,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 1 2 (by decide) (by decide)]; rfl⟩
  | 14, 1, 3, _, _, _ => exact ⟨e (.n 1056), outCell_sound _ σ KT 455 1056 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1056) = qv inp (.HB 14 1) from g455,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 1 3 (by decide) (by decide)]; rfl⟩
  | 14, 2, 0, _, _, _ => exact ⟨e (.n 1055), outCell_sound _ σ KT 456 1055 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1055) = qv inp (.HB 14 2) from g456,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 2 0 (by decide) (by decide)]; rfl⟩
  | 14, 2, 1, _, _, _ => exact ⟨e (.n 1054), outCell_sound _ σ KT 457 1054 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1054) = qv inp (.HB 14 2) from g457,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 2 1 (by decide) (by decide)]; rfl⟩
  | 14, 2, 2, _, _, _ => exact ⟨e (.n 1053), outCell_sound _ σ KT 458 1053 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1053) = qv inp (.HB 14 2) from g458,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 2 2 (by decide) (by decide)]; rfl⟩
  | 14, 2, 3, _, _, _ => exact ⟨e (.n 1052), outCell_sound _ σ KT 459 1052 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1052) = qv inp (.HB 14 2) from g459,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 2 3 (by decide) (by decide)]; rfl⟩
  | 14, 3, 0, _, _, _ => exact ⟨e (.n 1051), outCell_sound _ σ KT 460 1051 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1051) = qv inp (.HB 14 3) from g460,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 3 0 (by decide) (by decide)]; rfl⟩
  | 14, 3, 1, _, _, _ => exact ⟨e (.n 1050), outCell_sound _ σ KT 461 1050 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1050) = qv inp (.HB 14 3) from g461,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 3 1 (by decide) (by decide)]; rfl⟩
  | 14, 3, 2, _, _, _ => exact ⟨e (.n 1049), outCell_sound _ σ KT 462 1049 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1049) = qv inp (.HB 14 3) from g462,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 3 2 (by decide) (by decide)]; rfl⟩
  | 14, 3, 3, _, _, _ => exact ⟨e (.n 1048), outCell_sound _ σ KT 463 1048 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1048) = qv inp (.HB 14 3) from g463,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 3 3 (by decide) (by decide)]; rfl⟩
  | 14, 4, 0, _, _, _ => exact ⟨e (.n 1047), outCell_sound _ σ KT 464 1047 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1047) = qv inp (.HB 14 4) from g464,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 4 0 (by decide) (by decide)]; rfl⟩
  | 14, 4, 1, _, _, _ => exact ⟨e (.n 1046), outCell_sound _ σ KT 465 1046 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1046) = qv inp (.HB 14 4) from g465,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 4 1 (by decide) (by decide)]; rfl⟩
  | 14, 4, 2, _, _, _ => exact ⟨e (.n 1045), outCell_sound _ σ KT 466 1045 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1045) = qv inp (.HB 14 4) from g466,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 4 2 (by decide) (by decide)]; rfl⟩
  | 14, 4, 3, _, _, _ => exact ⟨e (.n 1044), outCell_sound _ σ KT 467 1044 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1044) = qv inp (.HB 14 4) from g467,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 4 3 (by decide) (by decide)]; rfl⟩
  | 14, 5, 0, _, _, _ => exact ⟨e (.n 1043), outCell_sound _ σ KT 468 1043 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1043) = qv inp (.HB 14 5) from g468,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 5 0 (by decide) (by decide)]; rfl⟩
  | 14, 5, 1, _, _, _ => exact ⟨e (.n 1042), outCell_sound _ σ KT 469 1042 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1042) = qv inp (.HB 14 5) from g469,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 5 1 (by decide) (by decide)]; rfl⟩
  | 14, 5, 2, _, _, _ => exact ⟨e (.n 1041), outCell_sound _ σ KT 470 1041 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1041) = qv inp (.HB 14 5) from g470,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 5 2 (by decide) (by decide)]; rfl⟩
  | 14, 5, 3, _, _, _ => exact ⟨e (.n 1040), outCell_sound _ σ KT 471 1040 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1040) = qv inp (.HB 14 5) from g471,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 5 3 (by decide) (by decide)]; rfl⟩
  | 14, 6, 0, _, _, _ => exact ⟨e (.n 1039), outCell_sound _ σ KT 472 1039 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1039) = qv inp (.HB 14 6) from g472,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 6 0 (by decide) (by decide)]; rfl⟩
  | 14, 6, 1, _, _, _ => exact ⟨e (.n 1038), outCell_sound _ σ KT 473 1038 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1038) = qv inp (.HB 14 6) from g473,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 6 1 (by decide) (by decide)]; rfl⟩
  | 14, 6, 2, _, _, _ => exact ⟨e (.n 1037), outCell_sound _ σ KT 474 1037 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1037) = qv inp (.HB 14 6) from g474,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 6 2 (by decide) (by decide)]; rfl⟩
  | 14, 6, 3, _, _, _ => exact ⟨e (.n 1036), outCell_sound _ σ KT 475 1036 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1036) = qv inp (.HB 14 6) from g475,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 6 3 (by decide) (by decide)]; rfl⟩
  | 14, 7, 0, _, _, _ => exact ⟨e (.n 1035), outCell_sound _ σ KT 476 1035 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1035) = qv inp (.HB 14 7) from g476,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 7 0 (by decide) (by decide)]; rfl⟩
  | 14, 7, 1, _, _, _ => exact ⟨e (.n 1034), outCell_sound _ σ KT 477 1034 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1034) = qv inp (.HB 14 7) from g477,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 7 1 (by decide) (by decide)]; rfl⟩
  | 14, 7, 2, _, _, _ => exact ⟨e (.n 1033), outCell_sound _ σ KT 478 1033 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1033) = qv inp (.HB 14 7) from g478,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 7 2 (by decide) (by decide)]; rfl⟩
  | 14, 7, 3, _, _, _ => exact ⟨e (.n 1032), outCell_sound _ σ KT 479 1032 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1032) = qv inp (.HB 14 7) from g479,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 7 3 (by decide) (by decide)]; rfl⟩
  | 15, 0, 0, _, _, _ => exact ⟨e (.n 1031), outCell_sound _ σ KT 480 1031 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1031) = qv inp (.HB 15 0) from g480,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 0 0 (by decide) (by decide)]; rfl⟩
  | 15, 0, 1, _, _, _ => exact ⟨e (.n 1030), outCell_sound _ σ KT 481 1030 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1030) = qv inp (.HB 15 0) from g481,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 0 1 (by decide) (by decide)]; rfl⟩
  | 15, 0, 2, _, _, _ => exact ⟨e (.n 1029), outCell_sound _ σ KT 482 1029 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1029) = qv inp (.HB 15 0) from g482,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 0 2 (by decide) (by decide)]; rfl⟩
  | 15, 0, 3, _, _, _ => exact ⟨e (.n 1028), outCell_sound _ σ KT 483 1028 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1028) = qv inp (.HB 15 0) from g483,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 0 3 (by decide) (by decide)]; rfl⟩
  | 15, 1, 0, _, _, _ => exact ⟨e (.n 1027), outCell_sound _ σ KT 484 1027 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1027) = qv inp (.HB 15 1) from g484,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 1 0 (by decide) (by decide)]; rfl⟩
  | 15, 1, 1, _, _, _ => exact ⟨e (.n 1026), outCell_sound _ σ KT 485 1026 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1026) = qv inp (.HB 15 1) from g485,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 1 1 (by decide) (by decide)]; rfl⟩
  | 15, 1, 2, _, _, _ => exact ⟨e (.n 1025), outCell_sound _ σ KT 486 1025 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1025) = qv inp (.HB 15 1) from g486,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 1 2 (by decide) (by decide)]; rfl⟩
  | 15, 1, 3, _, _, _ => exact ⟨e (.n 1024), outCell_sound _ σ KT 487 1024 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1024) = qv inp (.HB 15 1) from g487,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 1 3 (by decide) (by decide)]; rfl⟩
  | 15, 2, 0, _, _, _ => exact ⟨e (.n 1023), outCell_sound _ σ KT 488 1023 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1023) = qv inp (.HB 15 2) from g488,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 2 0 (by decide) (by decide)]; rfl⟩
  | 15, 2, 1, _, _, _ => exact ⟨e (.n 1022), outCell_sound _ σ KT 489 1022 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1022) = qv inp (.HB 15 2) from g489,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 2 1 (by decide) (by decide)]; rfl⟩
  | 15, 2, 2, _, _, _ => exact ⟨e (.n 1021), outCell_sound _ σ KT 490 1021 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1021) = qv inp (.HB 15 2) from g490,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 2 2 (by decide) (by decide)]; rfl⟩
  | 15, 2, 3, _, _, _ => exact ⟨e (.n 1020), outCell_sound _ σ KT 491 1020 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1020) = qv inp (.HB 15 2) from g491,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 2 3 (by decide) (by decide)]; rfl⟩
  | 15, 3, 0, _, _, _ => exact ⟨e (.n 1019), outCell_sound _ σ KT 492 1019 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1019) = qv inp (.HB 15 3) from g492,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 3 0 (by decide) (by decide)]; rfl⟩
  | 15, 3, 1, _, _, _ => exact ⟨e (.n 1018), outCell_sound _ σ KT 493 1018 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1018) = qv inp (.HB 15 3) from g493,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 3 1 (by decide) (by decide)]; rfl⟩
  | 15, 3, 2, _, _, _ => exact ⟨e (.n 1017), outCell_sound _ σ KT 494 1017 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1017) = qv inp (.HB 15 3) from g494,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 3 2 (by decide) (by decide)]; rfl⟩
  | 15, 3, 3, _, _, _ => exact ⟨e (.n 1016), outCell_sound _ σ KT 495 1016 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1016) = qv inp (.HB 15 3) from g495,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 3 3 (by decide) (by decide)]; rfl⟩
  | 15, 4, 0, _, _, _ => exact ⟨e (.n 1015), outCell_sound _ σ KT 496 1015 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1015) = qv inp (.HB 15 4) from g496,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 4 0 (by decide) (by decide)]; rfl⟩
  | 15, 4, 1, _, _, _ => exact ⟨e (.n 1014), outCell_sound _ σ KT 497 1014 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1014) = qv inp (.HB 15 4) from g497,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 4 1 (by decide) (by decide)]; rfl⟩
  | 15, 4, 2, _, _, _ => exact ⟨e (.n 1013), outCell_sound _ σ KT 498 1013 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1013) = qv inp (.HB 15 4) from g498,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 4 2 (by decide) (by decide)]; rfl⟩
  | 15, 4, 3, _, _, _ => exact ⟨e (.n 1012), outCell_sound _ σ KT 499 1012 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1012) = qv inp (.HB 15 4) from g499,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 4 3 (by decide) (by decide)]; rfl⟩
  | 15, 5, 0, _, _, _ => exact ⟨e (.n 1011), outCell_sound _ σ KT 500 1011 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1011) = qv inp (.HB 15 5) from g500,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 5 0 (by decide) (by decide)]; rfl⟩
  | 15, 5, 1, _, _, _ => exact ⟨e (.n 1010), outCell_sound _ σ KT 501 1010 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1010) = qv inp (.HB 15 5) from g501,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 5 1 (by decide) (by decide)]; rfl⟩
  | 15, 5, 2, _, _, _ => exact ⟨e (.n 1009), outCell_sound _ σ KT 502 1009 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1009) = qv inp (.HB 15 5) from g502,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 5 2 (by decide) (by decide)]; rfl⟩
  | 15, 5, 3, _, _, _ => exact ⟨e (.n 1008), outCell_sound _ σ KT 503 1008 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1008) = qv inp (.HB 15 5) from g503,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 5 3 (by decide) (by decide)]; rfl⟩
  | 15, 6, 0, _, _, _ => exact ⟨e (.n 1007), outCell_sound _ σ KT 504 1007 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1007) = qv inp (.HB 15 6) from g504,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 6 0 (by decide) (by decide)]; rfl⟩
  | 15, 6, 1, _, _, _ => exact ⟨e (.n 1006), outCell_sound _ σ KT 505 1006 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1006) = qv inp (.HB 15 6) from g505,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 6 1 (by decide) (by decide)]; rfl⟩
  | 15, 6, 2, _, _, _ => exact ⟨e (.n 1005), outCell_sound _ σ KT 506 1005 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1005) = qv inp (.HB 15 6) from g506,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 6 2 (by decide) (by decide)]; rfl⟩
  | 15, 6, 3, _, _, _ => exact ⟨e (.n 1004), outCell_sound _ σ KT 507 1004 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1004) = qv inp (.HB 15 6) from g507,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 6 3 (by decide) (by decide)]; rfl⟩
  | 15, 7, 0, _, _, _ => exact ⟨e (.n 1003), outCell_sound _ σ KT 508 1003 0 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1003) = qv inp (.HB 15 7) from g508,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 7 0 (by decide) (by decide)]; rfl⟩
  | 15, 7, 1, _, _, _ => exact ⟨e (.n 1002), outCell_sound _ σ KT 509 1002 1 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1002) = qv inp (.HB 15 7) from g509,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 7 1 (by decide) (by decide)]; rfl⟩
  | 15, 7, 2, _, _, _ => exact ⟨e (.n 1001), outCell_sound _ σ KT 510 1001 2 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1001) = qv inp (.HB 15 7) from g510,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 7 2 (by decide) (by decide)]; rfl⟩
  | 15, 7, 3, _, _, _ => exact ⟨e (.n 1000), outCell_sound _ σ KT 511 1000 3 (KT_cell _ _ _ (by decide)),
      by rw [show e (.n 1000) = qv inp (.HB 15 7) from g511,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 7 3 (by decide) (by decide)]; rfl⟩
  | _ + 16, _, _, hn, _, _ => omega
  | _, _ + 8, _, _, hi, _ => omega
  | _, _, _ + 4, _, _, hb => omega


/-- The 512 `(o, id, b)` output cells of `KTE`, checked once. -/
def KTE_tab : List (Nat × Nat × Nat) := [(0, 1511, 0), (1, 1510, 1), (2, 1509, 2), (3, 1508, 3), (4, 1507, 0), (5, 1506, 1), (6, 1505, 2), (7, 1504, 3), (8, 1503, 0), (9, 1502, 1), (10, 1501, 2), (11, 1500, 3), (12, 1499, 0), (13, 1498, 1), (14, 1497, 2), (15, 1496, 3), (16, 1495, 0), (17, 1494, 1), (18, 1493, 2), (19, 1492, 3), (20, 1491, 0), (21, 1490, 1), (22, 1489, 2), (23, 1488, 3), (24, 1487, 0), (25, 1486, 1), (26, 1485, 2), (27, 1484, 3), (28, 1483, 0), (29, 1482, 1), (30, 1481, 2), (31, 1480, 3), (32, 1479, 0), (33, 1478, 1), (34, 1477, 2), (35, 1476, 3), (36, 1475, 0), (37, 1474, 1), (38, 1473, 2), (39, 1472, 3), (40, 1471, 0), (41, 1470, 1), (42, 1469, 2), (43, 1468, 3), (44, 1467, 0), (45, 1466, 1), (46, 1465, 2), (47, 1464, 3), (48, 1463, 0), (49, 1462, 1), (50, 1461, 2), (51, 1460, 3), (52, 1459, 0), (53, 1458, 1), (54, 1457, 2), (55, 1456, 3), (56, 1455, 0), (57, 1454, 1), (58, 1453, 2), (59, 1452, 3), (60, 1451, 0), (61, 1450, 1), (62, 1449, 2), (63, 1448, 3), (64, 1447, 0), (65, 1446, 1), (66, 1445, 2), (67, 1444, 3), (68, 1443, 0), (69, 1442, 1), (70, 1441, 2), (71, 1440, 3), (72, 1439, 0), (73, 1438, 1), (74, 1437, 2), (75, 1436, 3), (76, 1435, 0), (77, 1434, 1), (78, 1433, 2), (79, 1432, 3), (80, 1431, 0), (81, 1430, 1), (82, 1429, 2), (83, 1428, 3), (84, 1427, 0), (85, 1426, 1), (86, 1425, 2), (87, 1424, 3), (88, 1423, 0), (89, 1422, 1), (90, 1421, 2), (91, 1420, 3), (92, 1419, 0), (93, 1418, 1), (94, 1417, 2), (95, 1416, 3), (96, 1415, 0), (97, 1414, 1), (98, 1413, 2), (99, 1412, 3), (100, 1411, 0), (101, 1410, 1), (102, 1409, 2), (103, 1408, 3), (104, 1407, 0), (105, 1406, 1), (106, 1405, 2), (107, 1404, 3), (108, 1403, 0), (109, 1402, 1), (110, 1401, 2), (111, 1400, 3), (112, 1399, 0), (113, 1398, 1), (114, 1397, 2), (115, 1396, 3), (116, 1395, 0), (117, 1394, 1), (118, 1393, 2), (119, 1392, 3), (120, 1391, 0), (121, 1390, 1), (122, 1389, 2), (123, 1388, 3), (124, 1387, 0), (125, 1386, 1), (126, 1385, 2), (127, 1384, 3), (128, 1383, 0), (129, 1382, 1), (130, 1381, 2), (131, 1380, 3), (132, 1379, 0), (133, 1378, 1), (134, 1377, 2), (135, 1376, 3), (136, 1375, 0), (137, 1374, 1), (138, 1373, 2), (139, 1372, 3), (140, 1371, 0), (141, 1370, 1), (142, 1369, 2), (143, 1368, 3), (144, 1367, 0), (145, 1366, 1), (146, 1365, 2), (147, 1364, 3), (148, 1363, 0), (149, 1362, 1), (150, 1361, 2), (151, 1360, 3), (152, 1359, 0), (153, 1358, 1), (154, 1357, 2), (155, 1356, 3), (156, 1355, 0), (157, 1354, 1), (158, 1353, 2), (159, 1352, 3), (160, 1351, 0), (161, 1350, 1), (162, 1349, 2), (163, 1348, 3), (164, 1347, 0), (165, 1346, 1), (166, 1345, 2), (167, 1344, 3), (168, 1343, 0), (169, 1342, 1), (170, 1341, 2), (171, 1340, 3), (172, 1339, 0), (173, 1338, 1), (174, 1337, 2), (175, 1336, 3), (176, 1335, 0), (177, 1334, 1), (178, 1333, 2), (179, 1332, 3), (180, 1331, 0), (181, 1330, 1), (182, 1329, 2), (183, 1328, 3), (184, 1327, 0), (185, 1326, 1), (186, 1325, 2), (187, 1324, 3), (188, 1323, 0), (189, 1322, 1), (190, 1321, 2), (191, 1320, 3), (192, 1319, 0), (193, 1318, 1), (194, 1317, 2), (195, 1316, 3), (196, 1315, 0), (197, 1314, 1), (198, 1313, 2), (199, 1312, 3), (200, 1311, 0), (201, 1310, 1), (202, 1309, 2), (203, 1308, 3), (204, 1307, 0), (205, 1306, 1), (206, 1305, 2), (207, 1304, 3), (208, 1303, 0), (209, 1302, 1), (210, 1301, 2), (211, 1300, 3), (212, 1299, 0), (213, 1298, 1), (214, 1297, 2), (215, 1296, 3), (216, 1295, 0), (217, 1294, 1), (218, 1293, 2), (219, 1292, 3), (220, 1291, 0), (221, 1290, 1), (222, 1289, 2), (223, 1288, 3), (224, 1287, 0), (225, 1286, 1), (226, 1285, 2), (227, 1284, 3), (228, 1283, 0), (229, 1282, 1), (230, 1281, 2), (231, 1280, 3), (232, 1279, 0), (233, 1278, 1), (234, 1277, 2), (235, 1276, 3), (236, 1275, 0), (237, 1274, 1), (238, 1273, 2), (239, 1272, 3), (240, 1271, 0), (241, 1270, 1), (242, 1269, 2), (243, 1268, 3), (244, 1267, 0), (245, 1266, 1), (246, 1265, 2), (247, 1264, 3), (248, 1263, 0), (249, 1262, 1), (250, 1261, 2), (251, 1260, 3), (252, 1259, 0), (253, 1258, 1), (254, 1257, 2), (255, 1256, 3), (256, 1255, 0), (257, 1254, 1), (258, 1253, 2), (259, 1252, 3), (260, 1251, 0), (261, 1250, 1), (262, 1249, 2), (263, 1248, 3), (264, 1247, 0), (265, 1246, 1), (266, 1245, 2), (267, 1244, 3), (268, 1243, 0), (269, 1242, 1), (270, 1241, 2), (271, 1240, 3), (272, 1239, 0), (273, 1238, 1), (274, 1237, 2), (275, 1236, 3), (276, 1235, 0), (277, 1234, 1), (278, 1233, 2), (279, 1232, 3), (280, 1231, 0), (281, 1230, 1), (282, 1229, 2), (283, 1228, 3), (284, 1227, 0), (285, 1226, 1), (286, 1225, 2), (287, 1224, 3), (288, 1223, 0), (289, 1222, 1), (290, 1221, 2), (291, 1220, 3), (292, 1219, 0), (293, 1218, 1), (294, 1217, 2), (295, 1216, 3), (296, 1215, 0), (297, 1214, 1), (298, 1213, 2), (299, 1212, 3), (300, 1211, 0), (301, 1210, 1), (302, 1209, 2), (303, 1208, 3), (304, 1207, 0), (305, 1206, 1), (306, 1205, 2), (307, 1204, 3), (308, 1203, 0), (309, 1202, 1), (310, 1201, 2), (311, 1200, 3), (312, 1199, 0), (313, 1198, 1), (314, 1197, 2), (315, 1196, 3), (316, 1195, 0), (317, 1194, 1), (318, 1193, 2), (319, 1192, 3), (320, 1191, 0), (321, 1190, 1), (322, 1189, 2), (323, 1188, 3), (324, 1187, 0), (325, 1186, 1), (326, 1185, 2), (327, 1184, 3), (328, 1183, 0), (329, 1182, 1), (330, 1181, 2), (331, 1180, 3), (332, 1179, 0), (333, 1178, 1), (334, 1177, 2), (335, 1176, 3), (336, 1175, 0), (337, 1174, 1), (338, 1173, 2), (339, 1172, 3), (340, 1171, 0), (341, 1170, 1), (342, 1169, 2), (343, 1168, 3), (344, 1167, 0), (345, 1166, 1), (346, 1165, 2), (347, 1164, 3), (348, 1163, 0), (349, 1162, 1), (350, 1161, 2), (351, 1160, 3), (352, 1159, 0), (353, 1158, 1), (354, 1157, 2), (355, 1156, 3), (356, 1155, 0), (357, 1154, 1), (358, 1153, 2), (359, 1152, 3), (360, 1151, 0), (361, 1150, 1), (362, 1149, 2), (363, 1148, 3), (364, 1147, 0), (365, 1146, 1), (366, 1145, 2), (367, 1144, 3), (368, 1143, 0), (369, 1142, 1), (370, 1141, 2), (371, 1140, 3), (372, 1139, 0), (373, 1138, 1), (374, 1137, 2), (375, 1136, 3), (376, 1135, 0), (377, 1134, 1), (378, 1133, 2), (379, 1132, 3), (380, 1131, 0), (381, 1130, 1), (382, 1129, 2), (383, 1128, 3), (384, 1127, 0), (385, 1126, 1), (386, 1125, 2), (387, 1124, 3), (388, 1123, 0), (389, 1122, 1), (390, 1121, 2), (391, 1120, 3), (392, 1119, 0), (393, 1118, 1), (394, 1117, 2), (395, 1116, 3), (396, 1115, 0), (397, 1114, 1), (398, 1113, 2), (399, 1112, 3), (400, 1111, 0), (401, 1110, 1), (402, 1109, 2), (403, 1108, 3), (404, 1107, 0), (405, 1106, 1), (406, 1105, 2), (407, 1104, 3), (408, 1103, 0), (409, 1102, 1), (410, 1101, 2), (411, 1100, 3), (412, 1099, 0), (413, 1098, 1), (414, 1097, 2), (415, 1096, 3), (416, 1095, 0), (417, 1094, 1), (418, 1093, 2), (419, 1092, 3), (420, 1091, 0), (421, 1090, 1), (422, 1089, 2), (423, 1088, 3), (424, 1087, 0), (425, 1086, 1), (426, 1085, 2), (427, 1084, 3), (428, 1083, 0), (429, 1082, 1), (430, 1081, 2), (431, 1080, 3), (432, 1079, 0), (433, 1078, 1), (434, 1077, 2), (435, 1076, 3), (436, 1075, 0), (437, 1074, 1), (438, 1073, 2), (439, 1072, 3), (440, 1071, 0), (441, 1070, 1), (442, 1069, 2), (443, 1068, 3), (444, 1067, 0), (445, 1066, 1), (446, 1065, 2), (447, 1064, 3), (448, 1063, 0), (449, 1062, 1), (450, 1061, 2), (451, 1060, 3), (452, 1059, 0), (453, 1058, 1), (454, 1057, 2), (455, 1056, 3), (456, 1055, 0), (457, 1054, 1), (458, 1053, 2), (459, 1052, 3), (460, 1051, 0), (461, 1050, 1), (462, 1049, 2), (463, 1048, 3), (464, 1047, 0), (465, 1046, 1), (466, 1045, 2), (467, 1044, 3), (468, 1043, 0), (469, 1042, 1), (470, 1041, 2), (471, 1040, 3), (472, 1039, 0), (473, 1038, 1), (474, 1037, 2), (475, 1036, 3), (476, 1035, 0), (477, 1034, 1), (478, 1033, 2), (479, 1032, 3), (480, 1031, 0), (481, 1030, 1), (482, 1029, 2), (483, 1028, 3), (484, 1027, 0), (485, 1026, 1), (486, 1025, 2), (487, 1024, 3), (488, 1023, 0), (489, 1022, 1), (490, 1021, 2), (491, 1020, 3), (492, 1019, 0), (493, 1018, 1), (494, 1017, 2), (495, 1016, 3), (496, 1015, 0), (497, 1014, 1), (498, 1013, 2), (499, 1012, 3), (500, 1011, 0), (501, 1010, 1), (502, 1009, 2), (503, 1008, 3), (504, 1007, 0), (505, 1006, 1), (506, 1005, 2), (507, 1004, 3), (508, 1003, 0), (509, 1002, 1), (510, 1001, 2), (511, 1000, 3)]

theorem KTE_cells : KTE_tab.all (fun t => outCell KTE t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem KTE_cell (o id b : Nat) (h : (o, id, b) ∈ KTE_tab) : outCell KTE o id b = true :=
  List.all_eq_true.mp KTE_cells (o, id, b) h

/-- The write log of a turn ending in `KTE` holds the 16 digests, from the invariant at `L217`. -/
theorem outOk_KTE (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L217) :
    OutOk inp (σ 1) 16 (mapState e σ KTE).mem := by
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
  intro n i b hn hi hb
  match n, i, b, hn, hi, hb with
  | 0, 0, 0, _, _, _ => exact ⟨e (.n 1511), outCell_sound _ σ KTE 0 1511 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1511) = qv inp (.HB 0 0) from g0,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 0 0 (by decide) (by decide)]; rfl⟩
  | 0, 0, 1, _, _, _ => exact ⟨e (.n 1510), outCell_sound _ σ KTE 1 1510 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1510) = qv inp (.HB 0 0) from g1,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 0 1 (by decide) (by decide)]; rfl⟩
  | 0, 0, 2, _, _, _ => exact ⟨e (.n 1509), outCell_sound _ σ KTE 2 1509 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1509) = qv inp (.HB 0 0) from g2,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 0 2 (by decide) (by decide)]; rfl⟩
  | 0, 0, 3, _, _, _ => exact ⟨e (.n 1508), outCell_sound _ σ KTE 3 1508 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1508) = qv inp (.HB 0 0) from g3,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 0 3 (by decide) (by decide)]; rfl⟩
  | 0, 1, 0, _, _, _ => exact ⟨e (.n 1507), outCell_sound _ σ KTE 4 1507 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1507) = qv inp (.HB 0 1) from g4,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 1 0 (by decide) (by decide)]; rfl⟩
  | 0, 1, 1, _, _, _ => exact ⟨e (.n 1506), outCell_sound _ σ KTE 5 1506 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1506) = qv inp (.HB 0 1) from g5,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 1 1 (by decide) (by decide)]; rfl⟩
  | 0, 1, 2, _, _, _ => exact ⟨e (.n 1505), outCell_sound _ σ KTE 6 1505 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1505) = qv inp (.HB 0 1) from g6,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 1 2 (by decide) (by decide)]; rfl⟩
  | 0, 1, 3, _, _, _ => exact ⟨e (.n 1504), outCell_sound _ σ KTE 7 1504 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1504) = qv inp (.HB 0 1) from g7,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 1 3 (by decide) (by decide)]; rfl⟩
  | 0, 2, 0, _, _, _ => exact ⟨e (.n 1503), outCell_sound _ σ KTE 8 1503 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1503) = qv inp (.HB 0 2) from g8,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 2 0 (by decide) (by decide)]; rfl⟩
  | 0, 2, 1, _, _, _ => exact ⟨e (.n 1502), outCell_sound _ σ KTE 9 1502 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1502) = qv inp (.HB 0 2) from g9,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 2 1 (by decide) (by decide)]; rfl⟩
  | 0, 2, 2, _, _, _ => exact ⟨e (.n 1501), outCell_sound _ σ KTE 10 1501 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1501) = qv inp (.HB 0 2) from g10,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 2 2 (by decide) (by decide)]; rfl⟩
  | 0, 2, 3, _, _, _ => exact ⟨e (.n 1500), outCell_sound _ σ KTE 11 1500 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1500) = qv inp (.HB 0 2) from g11,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 2 3 (by decide) (by decide)]; rfl⟩
  | 0, 3, 0, _, _, _ => exact ⟨e (.n 1499), outCell_sound _ σ KTE 12 1499 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1499) = qv inp (.HB 0 3) from g12,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 3 0 (by decide) (by decide)]; rfl⟩
  | 0, 3, 1, _, _, _ => exact ⟨e (.n 1498), outCell_sound _ σ KTE 13 1498 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1498) = qv inp (.HB 0 3) from g13,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 3 1 (by decide) (by decide)]; rfl⟩
  | 0, 3, 2, _, _, _ => exact ⟨e (.n 1497), outCell_sound _ σ KTE 14 1497 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1497) = qv inp (.HB 0 3) from g14,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 3 2 (by decide) (by decide)]; rfl⟩
  | 0, 3, 3, _, _, _ => exact ⟨e (.n 1496), outCell_sound _ σ KTE 15 1496 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1496) = qv inp (.HB 0 3) from g15,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 3 3 (by decide) (by decide)]; rfl⟩
  | 0, 4, 0, _, _, _ => exact ⟨e (.n 1495), outCell_sound _ σ KTE 16 1495 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1495) = qv inp (.HB 0 4) from g16,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 4 0 (by decide) (by decide)]; rfl⟩
  | 0, 4, 1, _, _, _ => exact ⟨e (.n 1494), outCell_sound _ σ KTE 17 1494 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1494) = qv inp (.HB 0 4) from g17,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 4 1 (by decide) (by decide)]; rfl⟩
  | 0, 4, 2, _, _, _ => exact ⟨e (.n 1493), outCell_sound _ σ KTE 18 1493 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1493) = qv inp (.HB 0 4) from g18,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 4 2 (by decide) (by decide)]; rfl⟩
  | 0, 4, 3, _, _, _ => exact ⟨e (.n 1492), outCell_sound _ σ KTE 19 1492 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1492) = qv inp (.HB 0 4) from g19,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 4 3 (by decide) (by decide)]; rfl⟩
  | 0, 5, 0, _, _, _ => exact ⟨e (.n 1491), outCell_sound _ σ KTE 20 1491 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1491) = qv inp (.HB 0 5) from g20,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 5 0 (by decide) (by decide)]; rfl⟩
  | 0, 5, 1, _, _, _ => exact ⟨e (.n 1490), outCell_sound _ σ KTE 21 1490 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1490) = qv inp (.HB 0 5) from g21,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 5 1 (by decide) (by decide)]; rfl⟩
  | 0, 5, 2, _, _, _ => exact ⟨e (.n 1489), outCell_sound _ σ KTE 22 1489 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1489) = qv inp (.HB 0 5) from g22,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 5 2 (by decide) (by decide)]; rfl⟩
  | 0, 5, 3, _, _, _ => exact ⟨e (.n 1488), outCell_sound _ σ KTE 23 1488 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1488) = qv inp (.HB 0 5) from g23,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 5 3 (by decide) (by decide)]; rfl⟩
  | 0, 6, 0, _, _, _ => exact ⟨e (.n 1487), outCell_sound _ σ KTE 24 1487 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1487) = qv inp (.HB 0 6) from g24,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 6 0 (by decide) (by decide)]; rfl⟩
  | 0, 6, 1, _, _, _ => exact ⟨e (.n 1486), outCell_sound _ σ KTE 25 1486 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1486) = qv inp (.HB 0 6) from g25,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 6 1 (by decide) (by decide)]; rfl⟩
  | 0, 6, 2, _, _, _ => exact ⟨e (.n 1485), outCell_sound _ σ KTE 26 1485 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1485) = qv inp (.HB 0 6) from g26,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 6 2 (by decide) (by decide)]; rfl⟩
  | 0, 6, 3, _, _, _ => exact ⟨e (.n 1484), outCell_sound _ σ KTE 27 1484 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1484) = qv inp (.HB 0 6) from g27,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 6 3 (by decide) (by decide)]; rfl⟩
  | 0, 7, 0, _, _, _ => exact ⟨e (.n 1483), outCell_sound _ σ KTE 28 1483 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1483) = qv inp (.HB 0 7) from g28,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 7 0 (by decide) (by decide)]; rfl⟩
  | 0, 7, 1, _, _, _ => exact ⟨e (.n 1482), outCell_sound _ σ KTE 29 1482 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1482) = qv inp (.HB 0 7) from g29,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 7 1 (by decide) (by decide)]; rfl⟩
  | 0, 7, 2, _, _, _ => exact ⟨e (.n 1481), outCell_sound _ σ KTE 30 1481 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1481) = qv inp (.HB 0 7) from g30,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 7 2 (by decide) (by decide)]; rfl⟩
  | 0, 7, 3, _, _, _ => exact ⟨e (.n 1480), outCell_sound _ σ KTE 31 1480 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1480) = qv inp (.HB 0 7) from g31,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 7 3 (by decide) (by decide)]; rfl⟩
  | 1, 0, 0, _, _, _ => exact ⟨e (.n 1479), outCell_sound _ σ KTE 32 1479 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1479) = qv inp (.HB 1 0) from g32,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 0 0 (by decide) (by decide)]; rfl⟩
  | 1, 0, 1, _, _, _ => exact ⟨e (.n 1478), outCell_sound _ σ KTE 33 1478 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1478) = qv inp (.HB 1 0) from g33,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 0 1 (by decide) (by decide)]; rfl⟩
  | 1, 0, 2, _, _, _ => exact ⟨e (.n 1477), outCell_sound _ σ KTE 34 1477 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1477) = qv inp (.HB 1 0) from g34,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 0 2 (by decide) (by decide)]; rfl⟩
  | 1, 0, 3, _, _, _ => exact ⟨e (.n 1476), outCell_sound _ σ KTE 35 1476 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1476) = qv inp (.HB 1 0) from g35,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 0 3 (by decide) (by decide)]; rfl⟩
  | 1, 1, 0, _, _, _ => exact ⟨e (.n 1475), outCell_sound _ σ KTE 36 1475 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1475) = qv inp (.HB 1 1) from g36,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 1 0 (by decide) (by decide)]; rfl⟩
  | 1, 1, 1, _, _, _ => exact ⟨e (.n 1474), outCell_sound _ σ KTE 37 1474 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1474) = qv inp (.HB 1 1) from g37,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 1 1 (by decide) (by decide)]; rfl⟩
  | 1, 1, 2, _, _, _ => exact ⟨e (.n 1473), outCell_sound _ σ KTE 38 1473 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1473) = qv inp (.HB 1 1) from g38,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 1 2 (by decide) (by decide)]; rfl⟩
  | 1, 1, 3, _, _, _ => exact ⟨e (.n 1472), outCell_sound _ σ KTE 39 1472 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1472) = qv inp (.HB 1 1) from g39,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 1 3 (by decide) (by decide)]; rfl⟩
  | 1, 2, 0, _, _, _ => exact ⟨e (.n 1471), outCell_sound _ σ KTE 40 1471 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1471) = qv inp (.HB 1 2) from g40,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 2 0 (by decide) (by decide)]; rfl⟩
  | 1, 2, 1, _, _, _ => exact ⟨e (.n 1470), outCell_sound _ σ KTE 41 1470 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1470) = qv inp (.HB 1 2) from g41,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 2 1 (by decide) (by decide)]; rfl⟩
  | 1, 2, 2, _, _, _ => exact ⟨e (.n 1469), outCell_sound _ σ KTE 42 1469 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1469) = qv inp (.HB 1 2) from g42,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 2 2 (by decide) (by decide)]; rfl⟩
  | 1, 2, 3, _, _, _ => exact ⟨e (.n 1468), outCell_sound _ σ KTE 43 1468 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1468) = qv inp (.HB 1 2) from g43,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 2 3 (by decide) (by decide)]; rfl⟩
  | 1, 3, 0, _, _, _ => exact ⟨e (.n 1467), outCell_sound _ σ KTE 44 1467 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1467) = qv inp (.HB 1 3) from g44,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 3 0 (by decide) (by decide)]; rfl⟩
  | 1, 3, 1, _, _, _ => exact ⟨e (.n 1466), outCell_sound _ σ KTE 45 1466 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1466) = qv inp (.HB 1 3) from g45,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 3 1 (by decide) (by decide)]; rfl⟩
  | 1, 3, 2, _, _, _ => exact ⟨e (.n 1465), outCell_sound _ σ KTE 46 1465 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1465) = qv inp (.HB 1 3) from g46,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 3 2 (by decide) (by decide)]; rfl⟩
  | 1, 3, 3, _, _, _ => exact ⟨e (.n 1464), outCell_sound _ σ KTE 47 1464 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1464) = qv inp (.HB 1 3) from g47,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 3 3 (by decide) (by decide)]; rfl⟩
  | 1, 4, 0, _, _, _ => exact ⟨e (.n 1463), outCell_sound _ σ KTE 48 1463 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1463) = qv inp (.HB 1 4) from g48,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 4 0 (by decide) (by decide)]; rfl⟩
  | 1, 4, 1, _, _, _ => exact ⟨e (.n 1462), outCell_sound _ σ KTE 49 1462 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1462) = qv inp (.HB 1 4) from g49,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 4 1 (by decide) (by decide)]; rfl⟩
  | 1, 4, 2, _, _, _ => exact ⟨e (.n 1461), outCell_sound _ σ KTE 50 1461 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1461) = qv inp (.HB 1 4) from g50,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 4 2 (by decide) (by decide)]; rfl⟩
  | 1, 4, 3, _, _, _ => exact ⟨e (.n 1460), outCell_sound _ σ KTE 51 1460 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1460) = qv inp (.HB 1 4) from g51,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 4 3 (by decide) (by decide)]; rfl⟩
  | 1, 5, 0, _, _, _ => exact ⟨e (.n 1459), outCell_sound _ σ KTE 52 1459 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1459) = qv inp (.HB 1 5) from g52,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 5 0 (by decide) (by decide)]; rfl⟩
  | 1, 5, 1, _, _, _ => exact ⟨e (.n 1458), outCell_sound _ σ KTE 53 1458 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1458) = qv inp (.HB 1 5) from g53,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 5 1 (by decide) (by decide)]; rfl⟩
  | 1, 5, 2, _, _, _ => exact ⟨e (.n 1457), outCell_sound _ σ KTE 54 1457 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1457) = qv inp (.HB 1 5) from g54,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 5 2 (by decide) (by decide)]; rfl⟩
  | 1, 5, 3, _, _, _ => exact ⟨e (.n 1456), outCell_sound _ σ KTE 55 1456 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1456) = qv inp (.HB 1 5) from g55,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 5 3 (by decide) (by decide)]; rfl⟩
  | 1, 6, 0, _, _, _ => exact ⟨e (.n 1455), outCell_sound _ σ KTE 56 1455 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1455) = qv inp (.HB 1 6) from g56,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 6 0 (by decide) (by decide)]; rfl⟩
  | 1, 6, 1, _, _, _ => exact ⟨e (.n 1454), outCell_sound _ σ KTE 57 1454 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1454) = qv inp (.HB 1 6) from g57,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 6 1 (by decide) (by decide)]; rfl⟩
  | 1, 6, 2, _, _, _ => exact ⟨e (.n 1453), outCell_sound _ σ KTE 58 1453 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1453) = qv inp (.HB 1 6) from g58,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 6 2 (by decide) (by decide)]; rfl⟩
  | 1, 6, 3, _, _, _ => exact ⟨e (.n 1452), outCell_sound _ σ KTE 59 1452 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1452) = qv inp (.HB 1 6) from g59,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 6 3 (by decide) (by decide)]; rfl⟩
  | 1, 7, 0, _, _, _ => exact ⟨e (.n 1451), outCell_sound _ σ KTE 60 1451 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1451) = qv inp (.HB 1 7) from g60,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 7 0 (by decide) (by decide)]; rfl⟩
  | 1, 7, 1, _, _, _ => exact ⟨e (.n 1450), outCell_sound _ σ KTE 61 1450 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1450) = qv inp (.HB 1 7) from g61,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 7 1 (by decide) (by decide)]; rfl⟩
  | 1, 7, 2, _, _, _ => exact ⟨e (.n 1449), outCell_sound _ σ KTE 62 1449 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1449) = qv inp (.HB 1 7) from g62,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 7 2 (by decide) (by decide)]; rfl⟩
  | 1, 7, 3, _, _, _ => exact ⟨e (.n 1448), outCell_sound _ σ KTE 63 1448 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1448) = qv inp (.HB 1 7) from g63,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 7 3 (by decide) (by decide)]; rfl⟩
  | 2, 0, 0, _, _, _ => exact ⟨e (.n 1447), outCell_sound _ σ KTE 64 1447 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1447) = qv inp (.HB 2 0) from g64,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 0 0 (by decide) (by decide)]; rfl⟩
  | 2, 0, 1, _, _, _ => exact ⟨e (.n 1446), outCell_sound _ σ KTE 65 1446 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1446) = qv inp (.HB 2 0) from g65,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 0 1 (by decide) (by decide)]; rfl⟩
  | 2, 0, 2, _, _, _ => exact ⟨e (.n 1445), outCell_sound _ σ KTE 66 1445 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1445) = qv inp (.HB 2 0) from g66,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 0 2 (by decide) (by decide)]; rfl⟩
  | 2, 0, 3, _, _, _ => exact ⟨e (.n 1444), outCell_sound _ σ KTE 67 1444 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1444) = qv inp (.HB 2 0) from g67,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 0 3 (by decide) (by decide)]; rfl⟩
  | 2, 1, 0, _, _, _ => exact ⟨e (.n 1443), outCell_sound _ σ KTE 68 1443 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1443) = qv inp (.HB 2 1) from g68,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 1 0 (by decide) (by decide)]; rfl⟩
  | 2, 1, 1, _, _, _ => exact ⟨e (.n 1442), outCell_sound _ σ KTE 69 1442 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1442) = qv inp (.HB 2 1) from g69,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 1 1 (by decide) (by decide)]; rfl⟩
  | 2, 1, 2, _, _, _ => exact ⟨e (.n 1441), outCell_sound _ σ KTE 70 1441 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1441) = qv inp (.HB 2 1) from g70,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 1 2 (by decide) (by decide)]; rfl⟩
  | 2, 1, 3, _, _, _ => exact ⟨e (.n 1440), outCell_sound _ σ KTE 71 1440 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1440) = qv inp (.HB 2 1) from g71,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 1 3 (by decide) (by decide)]; rfl⟩
  | 2, 2, 0, _, _, _ => exact ⟨e (.n 1439), outCell_sound _ σ KTE 72 1439 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1439) = qv inp (.HB 2 2) from g72,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 2 0 (by decide) (by decide)]; rfl⟩
  | 2, 2, 1, _, _, _ => exact ⟨e (.n 1438), outCell_sound _ σ KTE 73 1438 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1438) = qv inp (.HB 2 2) from g73,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 2 1 (by decide) (by decide)]; rfl⟩
  | 2, 2, 2, _, _, _ => exact ⟨e (.n 1437), outCell_sound _ σ KTE 74 1437 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1437) = qv inp (.HB 2 2) from g74,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 2 2 (by decide) (by decide)]; rfl⟩
  | 2, 2, 3, _, _, _ => exact ⟨e (.n 1436), outCell_sound _ σ KTE 75 1436 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1436) = qv inp (.HB 2 2) from g75,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 2 3 (by decide) (by decide)]; rfl⟩
  | 2, 3, 0, _, _, _ => exact ⟨e (.n 1435), outCell_sound _ σ KTE 76 1435 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1435) = qv inp (.HB 2 3) from g76,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 3 0 (by decide) (by decide)]; rfl⟩
  | 2, 3, 1, _, _, _ => exact ⟨e (.n 1434), outCell_sound _ σ KTE 77 1434 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1434) = qv inp (.HB 2 3) from g77,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 3 1 (by decide) (by decide)]; rfl⟩
  | 2, 3, 2, _, _, _ => exact ⟨e (.n 1433), outCell_sound _ σ KTE 78 1433 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1433) = qv inp (.HB 2 3) from g78,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 3 2 (by decide) (by decide)]; rfl⟩
  | 2, 3, 3, _, _, _ => exact ⟨e (.n 1432), outCell_sound _ σ KTE 79 1432 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1432) = qv inp (.HB 2 3) from g79,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 3 3 (by decide) (by decide)]; rfl⟩
  | 2, 4, 0, _, _, _ => exact ⟨e (.n 1431), outCell_sound _ σ KTE 80 1431 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1431) = qv inp (.HB 2 4) from g80,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 4 0 (by decide) (by decide)]; rfl⟩
  | 2, 4, 1, _, _, _ => exact ⟨e (.n 1430), outCell_sound _ σ KTE 81 1430 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1430) = qv inp (.HB 2 4) from g81,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 4 1 (by decide) (by decide)]; rfl⟩
  | 2, 4, 2, _, _, _ => exact ⟨e (.n 1429), outCell_sound _ σ KTE 82 1429 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1429) = qv inp (.HB 2 4) from g82,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 4 2 (by decide) (by decide)]; rfl⟩
  | 2, 4, 3, _, _, _ => exact ⟨e (.n 1428), outCell_sound _ σ KTE 83 1428 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1428) = qv inp (.HB 2 4) from g83,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 4 3 (by decide) (by decide)]; rfl⟩
  | 2, 5, 0, _, _, _ => exact ⟨e (.n 1427), outCell_sound _ σ KTE 84 1427 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1427) = qv inp (.HB 2 5) from g84,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 5 0 (by decide) (by decide)]; rfl⟩
  | 2, 5, 1, _, _, _ => exact ⟨e (.n 1426), outCell_sound _ σ KTE 85 1426 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1426) = qv inp (.HB 2 5) from g85,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 5 1 (by decide) (by decide)]; rfl⟩
  | 2, 5, 2, _, _, _ => exact ⟨e (.n 1425), outCell_sound _ σ KTE 86 1425 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1425) = qv inp (.HB 2 5) from g86,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 5 2 (by decide) (by decide)]; rfl⟩
  | 2, 5, 3, _, _, _ => exact ⟨e (.n 1424), outCell_sound _ σ KTE 87 1424 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1424) = qv inp (.HB 2 5) from g87,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 5 3 (by decide) (by decide)]; rfl⟩
  | 2, 6, 0, _, _, _ => exact ⟨e (.n 1423), outCell_sound _ σ KTE 88 1423 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1423) = qv inp (.HB 2 6) from g88,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 6 0 (by decide) (by decide)]; rfl⟩
  | 2, 6, 1, _, _, _ => exact ⟨e (.n 1422), outCell_sound _ σ KTE 89 1422 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1422) = qv inp (.HB 2 6) from g89,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 6 1 (by decide) (by decide)]; rfl⟩
  | 2, 6, 2, _, _, _ => exact ⟨e (.n 1421), outCell_sound _ σ KTE 90 1421 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1421) = qv inp (.HB 2 6) from g90,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 6 2 (by decide) (by decide)]; rfl⟩
  | 2, 6, 3, _, _, _ => exact ⟨e (.n 1420), outCell_sound _ σ KTE 91 1420 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1420) = qv inp (.HB 2 6) from g91,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 6 3 (by decide) (by decide)]; rfl⟩
  | 2, 7, 0, _, _, _ => exact ⟨e (.n 1419), outCell_sound _ σ KTE 92 1419 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1419) = qv inp (.HB 2 7) from g92,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 7 0 (by decide) (by decide)]; rfl⟩
  | 2, 7, 1, _, _, _ => exact ⟨e (.n 1418), outCell_sound _ σ KTE 93 1418 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1418) = qv inp (.HB 2 7) from g93,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 7 1 (by decide) (by decide)]; rfl⟩
  | 2, 7, 2, _, _, _ => exact ⟨e (.n 1417), outCell_sound _ σ KTE 94 1417 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1417) = qv inp (.HB 2 7) from g94,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 7 2 (by decide) (by decide)]; rfl⟩
  | 2, 7, 3, _, _, _ => exact ⟨e (.n 1416), outCell_sound _ σ KTE 95 1416 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1416) = qv inp (.HB 2 7) from g95,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 7 3 (by decide) (by decide)]; rfl⟩
  | 3, 0, 0, _, _, _ => exact ⟨e (.n 1415), outCell_sound _ σ KTE 96 1415 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1415) = qv inp (.HB 3 0) from g96,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 0 0 (by decide) (by decide)]; rfl⟩
  | 3, 0, 1, _, _, _ => exact ⟨e (.n 1414), outCell_sound _ σ KTE 97 1414 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1414) = qv inp (.HB 3 0) from g97,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 0 1 (by decide) (by decide)]; rfl⟩
  | 3, 0, 2, _, _, _ => exact ⟨e (.n 1413), outCell_sound _ σ KTE 98 1413 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1413) = qv inp (.HB 3 0) from g98,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 0 2 (by decide) (by decide)]; rfl⟩
  | 3, 0, 3, _, _, _ => exact ⟨e (.n 1412), outCell_sound _ σ KTE 99 1412 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1412) = qv inp (.HB 3 0) from g99,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 0 3 (by decide) (by decide)]; rfl⟩
  | 3, 1, 0, _, _, _ => exact ⟨e (.n 1411), outCell_sound _ σ KTE 100 1411 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1411) = qv inp (.HB 3 1) from g100,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 1 0 (by decide) (by decide)]; rfl⟩
  | 3, 1, 1, _, _, _ => exact ⟨e (.n 1410), outCell_sound _ σ KTE 101 1410 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1410) = qv inp (.HB 3 1) from g101,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 1 1 (by decide) (by decide)]; rfl⟩
  | 3, 1, 2, _, _, _ => exact ⟨e (.n 1409), outCell_sound _ σ KTE 102 1409 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1409) = qv inp (.HB 3 1) from g102,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 1 2 (by decide) (by decide)]; rfl⟩
  | 3, 1, 3, _, _, _ => exact ⟨e (.n 1408), outCell_sound _ σ KTE 103 1408 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1408) = qv inp (.HB 3 1) from g103,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 1 3 (by decide) (by decide)]; rfl⟩
  | 3, 2, 0, _, _, _ => exact ⟨e (.n 1407), outCell_sound _ σ KTE 104 1407 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1407) = qv inp (.HB 3 2) from g104,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 2 0 (by decide) (by decide)]; rfl⟩
  | 3, 2, 1, _, _, _ => exact ⟨e (.n 1406), outCell_sound _ σ KTE 105 1406 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1406) = qv inp (.HB 3 2) from g105,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 2 1 (by decide) (by decide)]; rfl⟩
  | 3, 2, 2, _, _, _ => exact ⟨e (.n 1405), outCell_sound _ σ KTE 106 1405 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1405) = qv inp (.HB 3 2) from g106,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 2 2 (by decide) (by decide)]; rfl⟩
  | 3, 2, 3, _, _, _ => exact ⟨e (.n 1404), outCell_sound _ σ KTE 107 1404 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1404) = qv inp (.HB 3 2) from g107,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 2 3 (by decide) (by decide)]; rfl⟩
  | 3, 3, 0, _, _, _ => exact ⟨e (.n 1403), outCell_sound _ σ KTE 108 1403 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1403) = qv inp (.HB 3 3) from g108,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 3 0 (by decide) (by decide)]; rfl⟩
  | 3, 3, 1, _, _, _ => exact ⟨e (.n 1402), outCell_sound _ σ KTE 109 1402 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1402) = qv inp (.HB 3 3) from g109,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 3 1 (by decide) (by decide)]; rfl⟩
  | 3, 3, 2, _, _, _ => exact ⟨e (.n 1401), outCell_sound _ σ KTE 110 1401 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1401) = qv inp (.HB 3 3) from g110,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 3 2 (by decide) (by decide)]; rfl⟩
  | 3, 3, 3, _, _, _ => exact ⟨e (.n 1400), outCell_sound _ σ KTE 111 1400 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1400) = qv inp (.HB 3 3) from g111,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 3 3 (by decide) (by decide)]; rfl⟩
  | 3, 4, 0, _, _, _ => exact ⟨e (.n 1399), outCell_sound _ σ KTE 112 1399 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1399) = qv inp (.HB 3 4) from g112,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 4 0 (by decide) (by decide)]; rfl⟩
  | 3, 4, 1, _, _, _ => exact ⟨e (.n 1398), outCell_sound _ σ KTE 113 1398 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1398) = qv inp (.HB 3 4) from g113,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 4 1 (by decide) (by decide)]; rfl⟩
  | 3, 4, 2, _, _, _ => exact ⟨e (.n 1397), outCell_sound _ σ KTE 114 1397 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1397) = qv inp (.HB 3 4) from g114,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 4 2 (by decide) (by decide)]; rfl⟩
  | 3, 4, 3, _, _, _ => exact ⟨e (.n 1396), outCell_sound _ σ KTE 115 1396 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1396) = qv inp (.HB 3 4) from g115,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 4 3 (by decide) (by decide)]; rfl⟩
  | 3, 5, 0, _, _, _ => exact ⟨e (.n 1395), outCell_sound _ σ KTE 116 1395 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1395) = qv inp (.HB 3 5) from g116,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 5 0 (by decide) (by decide)]; rfl⟩
  | 3, 5, 1, _, _, _ => exact ⟨e (.n 1394), outCell_sound _ σ KTE 117 1394 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1394) = qv inp (.HB 3 5) from g117,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 5 1 (by decide) (by decide)]; rfl⟩
  | 3, 5, 2, _, _, _ => exact ⟨e (.n 1393), outCell_sound _ σ KTE 118 1393 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1393) = qv inp (.HB 3 5) from g118,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 5 2 (by decide) (by decide)]; rfl⟩
  | 3, 5, 3, _, _, _ => exact ⟨e (.n 1392), outCell_sound _ σ KTE 119 1392 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1392) = qv inp (.HB 3 5) from g119,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 5 3 (by decide) (by decide)]; rfl⟩
  | 3, 6, 0, _, _, _ => exact ⟨e (.n 1391), outCell_sound _ σ KTE 120 1391 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1391) = qv inp (.HB 3 6) from g120,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 6 0 (by decide) (by decide)]; rfl⟩
  | 3, 6, 1, _, _, _ => exact ⟨e (.n 1390), outCell_sound _ σ KTE 121 1390 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1390) = qv inp (.HB 3 6) from g121,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 6 1 (by decide) (by decide)]; rfl⟩
  | 3, 6, 2, _, _, _ => exact ⟨e (.n 1389), outCell_sound _ σ KTE 122 1389 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1389) = qv inp (.HB 3 6) from g122,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 6 2 (by decide) (by decide)]; rfl⟩
  | 3, 6, 3, _, _, _ => exact ⟨e (.n 1388), outCell_sound _ σ KTE 123 1388 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1388) = qv inp (.HB 3 6) from g123,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 6 3 (by decide) (by decide)]; rfl⟩
  | 3, 7, 0, _, _, _ => exact ⟨e (.n 1387), outCell_sound _ σ KTE 124 1387 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1387) = qv inp (.HB 3 7) from g124,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 7 0 (by decide) (by decide)]; rfl⟩
  | 3, 7, 1, _, _, _ => exact ⟨e (.n 1386), outCell_sound _ σ KTE 125 1386 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1386) = qv inp (.HB 3 7) from g125,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 7 1 (by decide) (by decide)]; rfl⟩
  | 3, 7, 2, _, _, _ => exact ⟨e (.n 1385), outCell_sound _ σ KTE 126 1385 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1385) = qv inp (.HB 3 7) from g126,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 7 2 (by decide) (by decide)]; rfl⟩
  | 3, 7, 3, _, _, _ => exact ⟨e (.n 1384), outCell_sound _ σ KTE 127 1384 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1384) = qv inp (.HB 3 7) from g127,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 7 3 (by decide) (by decide)]; rfl⟩
  | 4, 0, 0, _, _, _ => exact ⟨e (.n 1383), outCell_sound _ σ KTE 128 1383 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1383) = qv inp (.HB 4 0) from g128,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 0 0 (by decide) (by decide)]; rfl⟩
  | 4, 0, 1, _, _, _ => exact ⟨e (.n 1382), outCell_sound _ σ KTE 129 1382 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1382) = qv inp (.HB 4 0) from g129,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 0 1 (by decide) (by decide)]; rfl⟩
  | 4, 0, 2, _, _, _ => exact ⟨e (.n 1381), outCell_sound _ σ KTE 130 1381 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1381) = qv inp (.HB 4 0) from g130,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 0 2 (by decide) (by decide)]; rfl⟩
  | 4, 0, 3, _, _, _ => exact ⟨e (.n 1380), outCell_sound _ σ KTE 131 1380 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1380) = qv inp (.HB 4 0) from g131,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 0 3 (by decide) (by decide)]; rfl⟩
  | 4, 1, 0, _, _, _ => exact ⟨e (.n 1379), outCell_sound _ σ KTE 132 1379 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1379) = qv inp (.HB 4 1) from g132,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 1 0 (by decide) (by decide)]; rfl⟩
  | 4, 1, 1, _, _, _ => exact ⟨e (.n 1378), outCell_sound _ σ KTE 133 1378 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1378) = qv inp (.HB 4 1) from g133,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 1 1 (by decide) (by decide)]; rfl⟩
  | 4, 1, 2, _, _, _ => exact ⟨e (.n 1377), outCell_sound _ σ KTE 134 1377 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1377) = qv inp (.HB 4 1) from g134,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 1 2 (by decide) (by decide)]; rfl⟩
  | 4, 1, 3, _, _, _ => exact ⟨e (.n 1376), outCell_sound _ σ KTE 135 1376 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1376) = qv inp (.HB 4 1) from g135,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 1 3 (by decide) (by decide)]; rfl⟩
  | 4, 2, 0, _, _, _ => exact ⟨e (.n 1375), outCell_sound _ σ KTE 136 1375 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1375) = qv inp (.HB 4 2) from g136,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 2 0 (by decide) (by decide)]; rfl⟩
  | 4, 2, 1, _, _, _ => exact ⟨e (.n 1374), outCell_sound _ σ KTE 137 1374 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1374) = qv inp (.HB 4 2) from g137,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 2 1 (by decide) (by decide)]; rfl⟩
  | 4, 2, 2, _, _, _ => exact ⟨e (.n 1373), outCell_sound _ σ KTE 138 1373 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1373) = qv inp (.HB 4 2) from g138,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 2 2 (by decide) (by decide)]; rfl⟩
  | 4, 2, 3, _, _, _ => exact ⟨e (.n 1372), outCell_sound _ σ KTE 139 1372 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1372) = qv inp (.HB 4 2) from g139,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 2 3 (by decide) (by decide)]; rfl⟩
  | 4, 3, 0, _, _, _ => exact ⟨e (.n 1371), outCell_sound _ σ KTE 140 1371 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1371) = qv inp (.HB 4 3) from g140,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 3 0 (by decide) (by decide)]; rfl⟩
  | 4, 3, 1, _, _, _ => exact ⟨e (.n 1370), outCell_sound _ σ KTE 141 1370 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1370) = qv inp (.HB 4 3) from g141,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 3 1 (by decide) (by decide)]; rfl⟩
  | 4, 3, 2, _, _, _ => exact ⟨e (.n 1369), outCell_sound _ σ KTE 142 1369 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1369) = qv inp (.HB 4 3) from g142,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 3 2 (by decide) (by decide)]; rfl⟩
  | 4, 3, 3, _, _, _ => exact ⟨e (.n 1368), outCell_sound _ σ KTE 143 1368 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1368) = qv inp (.HB 4 3) from g143,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 3 3 (by decide) (by decide)]; rfl⟩
  | 4, 4, 0, _, _, _ => exact ⟨e (.n 1367), outCell_sound _ σ KTE 144 1367 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1367) = qv inp (.HB 4 4) from g144,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 4 0 (by decide) (by decide)]; rfl⟩
  | 4, 4, 1, _, _, _ => exact ⟨e (.n 1366), outCell_sound _ σ KTE 145 1366 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1366) = qv inp (.HB 4 4) from g145,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 4 1 (by decide) (by decide)]; rfl⟩
  | 4, 4, 2, _, _, _ => exact ⟨e (.n 1365), outCell_sound _ σ KTE 146 1365 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1365) = qv inp (.HB 4 4) from g146,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 4 2 (by decide) (by decide)]; rfl⟩
  | 4, 4, 3, _, _, _ => exact ⟨e (.n 1364), outCell_sound _ σ KTE 147 1364 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1364) = qv inp (.HB 4 4) from g147,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 4 3 (by decide) (by decide)]; rfl⟩
  | 4, 5, 0, _, _, _ => exact ⟨e (.n 1363), outCell_sound _ σ KTE 148 1363 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1363) = qv inp (.HB 4 5) from g148,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 5 0 (by decide) (by decide)]; rfl⟩
  | 4, 5, 1, _, _, _ => exact ⟨e (.n 1362), outCell_sound _ σ KTE 149 1362 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1362) = qv inp (.HB 4 5) from g149,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 5 1 (by decide) (by decide)]; rfl⟩
  | 4, 5, 2, _, _, _ => exact ⟨e (.n 1361), outCell_sound _ σ KTE 150 1361 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1361) = qv inp (.HB 4 5) from g150,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 5 2 (by decide) (by decide)]; rfl⟩
  | 4, 5, 3, _, _, _ => exact ⟨e (.n 1360), outCell_sound _ σ KTE 151 1360 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1360) = qv inp (.HB 4 5) from g151,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 5 3 (by decide) (by decide)]; rfl⟩
  | 4, 6, 0, _, _, _ => exact ⟨e (.n 1359), outCell_sound _ σ KTE 152 1359 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1359) = qv inp (.HB 4 6) from g152,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 6 0 (by decide) (by decide)]; rfl⟩
  | 4, 6, 1, _, _, _ => exact ⟨e (.n 1358), outCell_sound _ σ KTE 153 1358 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1358) = qv inp (.HB 4 6) from g153,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 6 1 (by decide) (by decide)]; rfl⟩
  | 4, 6, 2, _, _, _ => exact ⟨e (.n 1357), outCell_sound _ σ KTE 154 1357 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1357) = qv inp (.HB 4 6) from g154,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 6 2 (by decide) (by decide)]; rfl⟩
  | 4, 6, 3, _, _, _ => exact ⟨e (.n 1356), outCell_sound _ σ KTE 155 1356 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1356) = qv inp (.HB 4 6) from g155,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 6 3 (by decide) (by decide)]; rfl⟩
  | 4, 7, 0, _, _, _ => exact ⟨e (.n 1355), outCell_sound _ σ KTE 156 1355 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1355) = qv inp (.HB 4 7) from g156,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 4 7 0 (by decide) (by decide)]; rfl⟩
  | 4, 7, 1, _, _, _ => exact ⟨e (.n 1354), outCell_sound _ σ KTE 157 1354 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1354) = qv inp (.HB 4 7) from g157,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 4 7 1 (by decide) (by decide)]; rfl⟩
  | 4, 7, 2, _, _, _ => exact ⟨e (.n 1353), outCell_sound _ σ KTE 158 1353 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1353) = qv inp (.HB 4 7) from g158,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 4 7 2 (by decide) (by decide)]; rfl⟩
  | 4, 7, 3, _, _, _ => exact ⟨e (.n 1352), outCell_sound _ σ KTE 159 1352 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1352) = qv inp (.HB 4 7) from g159,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 4 7 3 (by decide) (by decide)]; rfl⟩
  | 5, 0, 0, _, _, _ => exact ⟨e (.n 1351), outCell_sound _ σ KTE 160 1351 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1351) = qv inp (.HB 5 0) from g160,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 0 0 (by decide) (by decide)]; rfl⟩
  | 5, 0, 1, _, _, _ => exact ⟨e (.n 1350), outCell_sound _ σ KTE 161 1350 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1350) = qv inp (.HB 5 0) from g161,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 0 1 (by decide) (by decide)]; rfl⟩
  | 5, 0, 2, _, _, _ => exact ⟨e (.n 1349), outCell_sound _ σ KTE 162 1349 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1349) = qv inp (.HB 5 0) from g162,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 0 2 (by decide) (by decide)]; rfl⟩
  | 5, 0, 3, _, _, _ => exact ⟨e (.n 1348), outCell_sound _ σ KTE 163 1348 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1348) = qv inp (.HB 5 0) from g163,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 0 3 (by decide) (by decide)]; rfl⟩
  | 5, 1, 0, _, _, _ => exact ⟨e (.n 1347), outCell_sound _ σ KTE 164 1347 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1347) = qv inp (.HB 5 1) from g164,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 1 0 (by decide) (by decide)]; rfl⟩
  | 5, 1, 1, _, _, _ => exact ⟨e (.n 1346), outCell_sound _ σ KTE 165 1346 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1346) = qv inp (.HB 5 1) from g165,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 1 1 (by decide) (by decide)]; rfl⟩
  | 5, 1, 2, _, _, _ => exact ⟨e (.n 1345), outCell_sound _ σ KTE 166 1345 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1345) = qv inp (.HB 5 1) from g166,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 1 2 (by decide) (by decide)]; rfl⟩
  | 5, 1, 3, _, _, _ => exact ⟨e (.n 1344), outCell_sound _ σ KTE 167 1344 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1344) = qv inp (.HB 5 1) from g167,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 1 3 (by decide) (by decide)]; rfl⟩
  | 5, 2, 0, _, _, _ => exact ⟨e (.n 1343), outCell_sound _ σ KTE 168 1343 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1343) = qv inp (.HB 5 2) from g168,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 2 0 (by decide) (by decide)]; rfl⟩
  | 5, 2, 1, _, _, _ => exact ⟨e (.n 1342), outCell_sound _ σ KTE 169 1342 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1342) = qv inp (.HB 5 2) from g169,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 2 1 (by decide) (by decide)]; rfl⟩
  | 5, 2, 2, _, _, _ => exact ⟨e (.n 1341), outCell_sound _ σ KTE 170 1341 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1341) = qv inp (.HB 5 2) from g170,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 2 2 (by decide) (by decide)]; rfl⟩
  | 5, 2, 3, _, _, _ => exact ⟨e (.n 1340), outCell_sound _ σ KTE 171 1340 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1340) = qv inp (.HB 5 2) from g171,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 2 3 (by decide) (by decide)]; rfl⟩
  | 5, 3, 0, _, _, _ => exact ⟨e (.n 1339), outCell_sound _ σ KTE 172 1339 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1339) = qv inp (.HB 5 3) from g172,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 3 0 (by decide) (by decide)]; rfl⟩
  | 5, 3, 1, _, _, _ => exact ⟨e (.n 1338), outCell_sound _ σ KTE 173 1338 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1338) = qv inp (.HB 5 3) from g173,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 3 1 (by decide) (by decide)]; rfl⟩
  | 5, 3, 2, _, _, _ => exact ⟨e (.n 1337), outCell_sound _ σ KTE 174 1337 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1337) = qv inp (.HB 5 3) from g174,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 3 2 (by decide) (by decide)]; rfl⟩
  | 5, 3, 3, _, _, _ => exact ⟨e (.n 1336), outCell_sound _ σ KTE 175 1336 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1336) = qv inp (.HB 5 3) from g175,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 3 3 (by decide) (by decide)]; rfl⟩
  | 5, 4, 0, _, _, _ => exact ⟨e (.n 1335), outCell_sound _ σ KTE 176 1335 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1335) = qv inp (.HB 5 4) from g176,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 4 0 (by decide) (by decide)]; rfl⟩
  | 5, 4, 1, _, _, _ => exact ⟨e (.n 1334), outCell_sound _ σ KTE 177 1334 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1334) = qv inp (.HB 5 4) from g177,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 4 1 (by decide) (by decide)]; rfl⟩
  | 5, 4, 2, _, _, _ => exact ⟨e (.n 1333), outCell_sound _ σ KTE 178 1333 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1333) = qv inp (.HB 5 4) from g178,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 4 2 (by decide) (by decide)]; rfl⟩
  | 5, 4, 3, _, _, _ => exact ⟨e (.n 1332), outCell_sound _ σ KTE 179 1332 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1332) = qv inp (.HB 5 4) from g179,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 4 3 (by decide) (by decide)]; rfl⟩
  | 5, 5, 0, _, _, _ => exact ⟨e (.n 1331), outCell_sound _ σ KTE 180 1331 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1331) = qv inp (.HB 5 5) from g180,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 5 0 (by decide) (by decide)]; rfl⟩
  | 5, 5, 1, _, _, _ => exact ⟨e (.n 1330), outCell_sound _ σ KTE 181 1330 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1330) = qv inp (.HB 5 5) from g181,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 5 1 (by decide) (by decide)]; rfl⟩
  | 5, 5, 2, _, _, _ => exact ⟨e (.n 1329), outCell_sound _ σ KTE 182 1329 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1329) = qv inp (.HB 5 5) from g182,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 5 2 (by decide) (by decide)]; rfl⟩
  | 5, 5, 3, _, _, _ => exact ⟨e (.n 1328), outCell_sound _ σ KTE 183 1328 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1328) = qv inp (.HB 5 5) from g183,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 5 3 (by decide) (by decide)]; rfl⟩
  | 5, 6, 0, _, _, _ => exact ⟨e (.n 1327), outCell_sound _ σ KTE 184 1327 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1327) = qv inp (.HB 5 6) from g184,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 6 0 (by decide) (by decide)]; rfl⟩
  | 5, 6, 1, _, _, _ => exact ⟨e (.n 1326), outCell_sound _ σ KTE 185 1326 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1326) = qv inp (.HB 5 6) from g185,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 6 1 (by decide) (by decide)]; rfl⟩
  | 5, 6, 2, _, _, _ => exact ⟨e (.n 1325), outCell_sound _ σ KTE 186 1325 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1325) = qv inp (.HB 5 6) from g186,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 6 2 (by decide) (by decide)]; rfl⟩
  | 5, 6, 3, _, _, _ => exact ⟨e (.n 1324), outCell_sound _ σ KTE 187 1324 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1324) = qv inp (.HB 5 6) from g187,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 6 3 (by decide) (by decide)]; rfl⟩
  | 5, 7, 0, _, _, _ => exact ⟨e (.n 1323), outCell_sound _ σ KTE 188 1323 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1323) = qv inp (.HB 5 7) from g188,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 5 7 0 (by decide) (by decide)]; rfl⟩
  | 5, 7, 1, _, _, _ => exact ⟨e (.n 1322), outCell_sound _ σ KTE 189 1322 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1322) = qv inp (.HB 5 7) from g189,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 5 7 1 (by decide) (by decide)]; rfl⟩
  | 5, 7, 2, _, _, _ => exact ⟨e (.n 1321), outCell_sound _ σ KTE 190 1321 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1321) = qv inp (.HB 5 7) from g190,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 5 7 2 (by decide) (by decide)]; rfl⟩
  | 5, 7, 3, _, _, _ => exact ⟨e (.n 1320), outCell_sound _ σ KTE 191 1320 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1320) = qv inp (.HB 5 7) from g191,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 5 7 3 (by decide) (by decide)]; rfl⟩
  | 6, 0, 0, _, _, _ => exact ⟨e (.n 1319), outCell_sound _ σ KTE 192 1319 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1319) = qv inp (.HB 6 0) from g192,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 0 0 (by decide) (by decide)]; rfl⟩
  | 6, 0, 1, _, _, _ => exact ⟨e (.n 1318), outCell_sound _ σ KTE 193 1318 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1318) = qv inp (.HB 6 0) from g193,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 0 1 (by decide) (by decide)]; rfl⟩
  | 6, 0, 2, _, _, _ => exact ⟨e (.n 1317), outCell_sound _ σ KTE 194 1317 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1317) = qv inp (.HB 6 0) from g194,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 0 2 (by decide) (by decide)]; rfl⟩
  | 6, 0, 3, _, _, _ => exact ⟨e (.n 1316), outCell_sound _ σ KTE 195 1316 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1316) = qv inp (.HB 6 0) from g195,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 0 3 (by decide) (by decide)]; rfl⟩
  | 6, 1, 0, _, _, _ => exact ⟨e (.n 1315), outCell_sound _ σ KTE 196 1315 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1315) = qv inp (.HB 6 1) from g196,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 1 0 (by decide) (by decide)]; rfl⟩
  | 6, 1, 1, _, _, _ => exact ⟨e (.n 1314), outCell_sound _ σ KTE 197 1314 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1314) = qv inp (.HB 6 1) from g197,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 1 1 (by decide) (by decide)]; rfl⟩
  | 6, 1, 2, _, _, _ => exact ⟨e (.n 1313), outCell_sound _ σ KTE 198 1313 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1313) = qv inp (.HB 6 1) from g198,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 1 2 (by decide) (by decide)]; rfl⟩
  | 6, 1, 3, _, _, _ => exact ⟨e (.n 1312), outCell_sound _ σ KTE 199 1312 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1312) = qv inp (.HB 6 1) from g199,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 1 3 (by decide) (by decide)]; rfl⟩
  | 6, 2, 0, _, _, _ => exact ⟨e (.n 1311), outCell_sound _ σ KTE 200 1311 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1311) = qv inp (.HB 6 2) from g200,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 2 0 (by decide) (by decide)]; rfl⟩
  | 6, 2, 1, _, _, _ => exact ⟨e (.n 1310), outCell_sound _ σ KTE 201 1310 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1310) = qv inp (.HB 6 2) from g201,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 2 1 (by decide) (by decide)]; rfl⟩
  | 6, 2, 2, _, _, _ => exact ⟨e (.n 1309), outCell_sound _ σ KTE 202 1309 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1309) = qv inp (.HB 6 2) from g202,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 2 2 (by decide) (by decide)]; rfl⟩
  | 6, 2, 3, _, _, _ => exact ⟨e (.n 1308), outCell_sound _ σ KTE 203 1308 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1308) = qv inp (.HB 6 2) from g203,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 2 3 (by decide) (by decide)]; rfl⟩
  | 6, 3, 0, _, _, _ => exact ⟨e (.n 1307), outCell_sound _ σ KTE 204 1307 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1307) = qv inp (.HB 6 3) from g204,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 3 0 (by decide) (by decide)]; rfl⟩
  | 6, 3, 1, _, _, _ => exact ⟨e (.n 1306), outCell_sound _ σ KTE 205 1306 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1306) = qv inp (.HB 6 3) from g205,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 3 1 (by decide) (by decide)]; rfl⟩
  | 6, 3, 2, _, _, _ => exact ⟨e (.n 1305), outCell_sound _ σ KTE 206 1305 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1305) = qv inp (.HB 6 3) from g206,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 3 2 (by decide) (by decide)]; rfl⟩
  | 6, 3, 3, _, _, _ => exact ⟨e (.n 1304), outCell_sound _ σ KTE 207 1304 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1304) = qv inp (.HB 6 3) from g207,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 3 3 (by decide) (by decide)]; rfl⟩
  | 6, 4, 0, _, _, _ => exact ⟨e (.n 1303), outCell_sound _ σ KTE 208 1303 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1303) = qv inp (.HB 6 4) from g208,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 4 0 (by decide) (by decide)]; rfl⟩
  | 6, 4, 1, _, _, _ => exact ⟨e (.n 1302), outCell_sound _ σ KTE 209 1302 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1302) = qv inp (.HB 6 4) from g209,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 4 1 (by decide) (by decide)]; rfl⟩
  | 6, 4, 2, _, _, _ => exact ⟨e (.n 1301), outCell_sound _ σ KTE 210 1301 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1301) = qv inp (.HB 6 4) from g210,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 4 2 (by decide) (by decide)]; rfl⟩
  | 6, 4, 3, _, _, _ => exact ⟨e (.n 1300), outCell_sound _ σ KTE 211 1300 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1300) = qv inp (.HB 6 4) from g211,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 4 3 (by decide) (by decide)]; rfl⟩
  | 6, 5, 0, _, _, _ => exact ⟨e (.n 1299), outCell_sound _ σ KTE 212 1299 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1299) = qv inp (.HB 6 5) from g212,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 5 0 (by decide) (by decide)]; rfl⟩
  | 6, 5, 1, _, _, _ => exact ⟨e (.n 1298), outCell_sound _ σ KTE 213 1298 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1298) = qv inp (.HB 6 5) from g213,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 5 1 (by decide) (by decide)]; rfl⟩
  | 6, 5, 2, _, _, _ => exact ⟨e (.n 1297), outCell_sound _ σ KTE 214 1297 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1297) = qv inp (.HB 6 5) from g214,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 5 2 (by decide) (by decide)]; rfl⟩
  | 6, 5, 3, _, _, _ => exact ⟨e (.n 1296), outCell_sound _ σ KTE 215 1296 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1296) = qv inp (.HB 6 5) from g215,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 5 3 (by decide) (by decide)]; rfl⟩
  | 6, 6, 0, _, _, _ => exact ⟨e (.n 1295), outCell_sound _ σ KTE 216 1295 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1295) = qv inp (.HB 6 6) from g216,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 6 0 (by decide) (by decide)]; rfl⟩
  | 6, 6, 1, _, _, _ => exact ⟨e (.n 1294), outCell_sound _ σ KTE 217 1294 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1294) = qv inp (.HB 6 6) from g217,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 6 1 (by decide) (by decide)]; rfl⟩
  | 6, 6, 2, _, _, _ => exact ⟨e (.n 1293), outCell_sound _ σ KTE 218 1293 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1293) = qv inp (.HB 6 6) from g218,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 6 2 (by decide) (by decide)]; rfl⟩
  | 6, 6, 3, _, _, _ => exact ⟨e (.n 1292), outCell_sound _ σ KTE 219 1292 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1292) = qv inp (.HB 6 6) from g219,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 6 3 (by decide) (by decide)]; rfl⟩
  | 6, 7, 0, _, _, _ => exact ⟨e (.n 1291), outCell_sound _ σ KTE 220 1291 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1291) = qv inp (.HB 6 7) from g220,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 6 7 0 (by decide) (by decide)]; rfl⟩
  | 6, 7, 1, _, _, _ => exact ⟨e (.n 1290), outCell_sound _ σ KTE 221 1290 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1290) = qv inp (.HB 6 7) from g221,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 6 7 1 (by decide) (by decide)]; rfl⟩
  | 6, 7, 2, _, _, _ => exact ⟨e (.n 1289), outCell_sound _ σ KTE 222 1289 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1289) = qv inp (.HB 6 7) from g222,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 6 7 2 (by decide) (by decide)]; rfl⟩
  | 6, 7, 3, _, _, _ => exact ⟨e (.n 1288), outCell_sound _ σ KTE 223 1288 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1288) = qv inp (.HB 6 7) from g223,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 6 7 3 (by decide) (by decide)]; rfl⟩
  | 7, 0, 0, _, _, _ => exact ⟨e (.n 1287), outCell_sound _ σ KTE 224 1287 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1287) = qv inp (.HB 7 0) from g224,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 0 0 (by decide) (by decide)]; rfl⟩
  | 7, 0, 1, _, _, _ => exact ⟨e (.n 1286), outCell_sound _ σ KTE 225 1286 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1286) = qv inp (.HB 7 0) from g225,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 0 1 (by decide) (by decide)]; rfl⟩
  | 7, 0, 2, _, _, _ => exact ⟨e (.n 1285), outCell_sound _ σ KTE 226 1285 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1285) = qv inp (.HB 7 0) from g226,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 0 2 (by decide) (by decide)]; rfl⟩
  | 7, 0, 3, _, _, _ => exact ⟨e (.n 1284), outCell_sound _ σ KTE 227 1284 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1284) = qv inp (.HB 7 0) from g227,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 0 3 (by decide) (by decide)]; rfl⟩
  | 7, 1, 0, _, _, _ => exact ⟨e (.n 1283), outCell_sound _ σ KTE 228 1283 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1283) = qv inp (.HB 7 1) from g228,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 1 0 (by decide) (by decide)]; rfl⟩
  | 7, 1, 1, _, _, _ => exact ⟨e (.n 1282), outCell_sound _ σ KTE 229 1282 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1282) = qv inp (.HB 7 1) from g229,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 1 1 (by decide) (by decide)]; rfl⟩
  | 7, 1, 2, _, _, _ => exact ⟨e (.n 1281), outCell_sound _ σ KTE 230 1281 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1281) = qv inp (.HB 7 1) from g230,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 1 2 (by decide) (by decide)]; rfl⟩
  | 7, 1, 3, _, _, _ => exact ⟨e (.n 1280), outCell_sound _ σ KTE 231 1280 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1280) = qv inp (.HB 7 1) from g231,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 1 3 (by decide) (by decide)]; rfl⟩
  | 7, 2, 0, _, _, _ => exact ⟨e (.n 1279), outCell_sound _ σ KTE 232 1279 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1279) = qv inp (.HB 7 2) from g232,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 2 0 (by decide) (by decide)]; rfl⟩
  | 7, 2, 1, _, _, _ => exact ⟨e (.n 1278), outCell_sound _ σ KTE 233 1278 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1278) = qv inp (.HB 7 2) from g233,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 2 1 (by decide) (by decide)]; rfl⟩
  | 7, 2, 2, _, _, _ => exact ⟨e (.n 1277), outCell_sound _ σ KTE 234 1277 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1277) = qv inp (.HB 7 2) from g234,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 2 2 (by decide) (by decide)]; rfl⟩
  | 7, 2, 3, _, _, _ => exact ⟨e (.n 1276), outCell_sound _ σ KTE 235 1276 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1276) = qv inp (.HB 7 2) from g235,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 2 3 (by decide) (by decide)]; rfl⟩
  | 7, 3, 0, _, _, _ => exact ⟨e (.n 1275), outCell_sound _ σ KTE 236 1275 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1275) = qv inp (.HB 7 3) from g236,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 3 0 (by decide) (by decide)]; rfl⟩
  | 7, 3, 1, _, _, _ => exact ⟨e (.n 1274), outCell_sound _ σ KTE 237 1274 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1274) = qv inp (.HB 7 3) from g237,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 3 1 (by decide) (by decide)]; rfl⟩
  | 7, 3, 2, _, _, _ => exact ⟨e (.n 1273), outCell_sound _ σ KTE 238 1273 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1273) = qv inp (.HB 7 3) from g238,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 3 2 (by decide) (by decide)]; rfl⟩
  | 7, 3, 3, _, _, _ => exact ⟨e (.n 1272), outCell_sound _ σ KTE 239 1272 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1272) = qv inp (.HB 7 3) from g239,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 3 3 (by decide) (by decide)]; rfl⟩
  | 7, 4, 0, _, _, _ => exact ⟨e (.n 1271), outCell_sound _ σ KTE 240 1271 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1271) = qv inp (.HB 7 4) from g240,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 4 0 (by decide) (by decide)]; rfl⟩
  | 7, 4, 1, _, _, _ => exact ⟨e (.n 1270), outCell_sound _ σ KTE 241 1270 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1270) = qv inp (.HB 7 4) from g241,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 4 1 (by decide) (by decide)]; rfl⟩
  | 7, 4, 2, _, _, _ => exact ⟨e (.n 1269), outCell_sound _ σ KTE 242 1269 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1269) = qv inp (.HB 7 4) from g242,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 4 2 (by decide) (by decide)]; rfl⟩
  | 7, 4, 3, _, _, _ => exact ⟨e (.n 1268), outCell_sound _ σ KTE 243 1268 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1268) = qv inp (.HB 7 4) from g243,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 4 3 (by decide) (by decide)]; rfl⟩
  | 7, 5, 0, _, _, _ => exact ⟨e (.n 1267), outCell_sound _ σ KTE 244 1267 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1267) = qv inp (.HB 7 5) from g244,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 5 0 (by decide) (by decide)]; rfl⟩
  | 7, 5, 1, _, _, _ => exact ⟨e (.n 1266), outCell_sound _ σ KTE 245 1266 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1266) = qv inp (.HB 7 5) from g245,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 5 1 (by decide) (by decide)]; rfl⟩
  | 7, 5, 2, _, _, _ => exact ⟨e (.n 1265), outCell_sound _ σ KTE 246 1265 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1265) = qv inp (.HB 7 5) from g246,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 5 2 (by decide) (by decide)]; rfl⟩
  | 7, 5, 3, _, _, _ => exact ⟨e (.n 1264), outCell_sound _ σ KTE 247 1264 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1264) = qv inp (.HB 7 5) from g247,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 5 3 (by decide) (by decide)]; rfl⟩
  | 7, 6, 0, _, _, _ => exact ⟨e (.n 1263), outCell_sound _ σ KTE 248 1263 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1263) = qv inp (.HB 7 6) from g248,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 6 0 (by decide) (by decide)]; rfl⟩
  | 7, 6, 1, _, _, _ => exact ⟨e (.n 1262), outCell_sound _ σ KTE 249 1262 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1262) = qv inp (.HB 7 6) from g249,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 6 1 (by decide) (by decide)]; rfl⟩
  | 7, 6, 2, _, _, _ => exact ⟨e (.n 1261), outCell_sound _ σ KTE 250 1261 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1261) = qv inp (.HB 7 6) from g250,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 6 2 (by decide) (by decide)]; rfl⟩
  | 7, 6, 3, _, _, _ => exact ⟨e (.n 1260), outCell_sound _ σ KTE 251 1260 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1260) = qv inp (.HB 7 6) from g251,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 6 3 (by decide) (by decide)]; rfl⟩
  | 7, 7, 0, _, _, _ => exact ⟨e (.n 1259), outCell_sound _ σ KTE 252 1259 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1259) = qv inp (.HB 7 7) from g252,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 7 7 0 (by decide) (by decide)]; rfl⟩
  | 7, 7, 1, _, _, _ => exact ⟨e (.n 1258), outCell_sound _ σ KTE 253 1258 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1258) = qv inp (.HB 7 7) from g253,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 7 7 1 (by decide) (by decide)]; rfl⟩
  | 7, 7, 2, _, _, _ => exact ⟨e (.n 1257), outCell_sound _ σ KTE 254 1257 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1257) = qv inp (.HB 7 7) from g254,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 7 7 2 (by decide) (by decide)]; rfl⟩
  | 7, 7, 3, _, _, _ => exact ⟨e (.n 1256), outCell_sound _ σ KTE 255 1256 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1256) = qv inp (.HB 7 7) from g255,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 7 7 3 (by decide) (by decide)]; rfl⟩
  | 8, 0, 0, _, _, _ => exact ⟨e (.n 1255), outCell_sound _ σ KTE 256 1255 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1255) = qv inp (.HB 8 0) from g256,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 0 0 (by decide) (by decide)]; rfl⟩
  | 8, 0, 1, _, _, _ => exact ⟨e (.n 1254), outCell_sound _ σ KTE 257 1254 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1254) = qv inp (.HB 8 0) from g257,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 0 1 (by decide) (by decide)]; rfl⟩
  | 8, 0, 2, _, _, _ => exact ⟨e (.n 1253), outCell_sound _ σ KTE 258 1253 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1253) = qv inp (.HB 8 0) from g258,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 0 2 (by decide) (by decide)]; rfl⟩
  | 8, 0, 3, _, _, _ => exact ⟨e (.n 1252), outCell_sound _ σ KTE 259 1252 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1252) = qv inp (.HB 8 0) from g259,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 0 3 (by decide) (by decide)]; rfl⟩
  | 8, 1, 0, _, _, _ => exact ⟨e (.n 1251), outCell_sound _ σ KTE 260 1251 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1251) = qv inp (.HB 8 1) from g260,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 1 0 (by decide) (by decide)]; rfl⟩
  | 8, 1, 1, _, _, _ => exact ⟨e (.n 1250), outCell_sound _ σ KTE 261 1250 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1250) = qv inp (.HB 8 1) from g261,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 1 1 (by decide) (by decide)]; rfl⟩
  | 8, 1, 2, _, _, _ => exact ⟨e (.n 1249), outCell_sound _ σ KTE 262 1249 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1249) = qv inp (.HB 8 1) from g262,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 1 2 (by decide) (by decide)]; rfl⟩
  | 8, 1, 3, _, _, _ => exact ⟨e (.n 1248), outCell_sound _ σ KTE 263 1248 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1248) = qv inp (.HB 8 1) from g263,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 1 3 (by decide) (by decide)]; rfl⟩
  | 8, 2, 0, _, _, _ => exact ⟨e (.n 1247), outCell_sound _ σ KTE 264 1247 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1247) = qv inp (.HB 8 2) from g264,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 2 0 (by decide) (by decide)]; rfl⟩
  | 8, 2, 1, _, _, _ => exact ⟨e (.n 1246), outCell_sound _ σ KTE 265 1246 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1246) = qv inp (.HB 8 2) from g265,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 2 1 (by decide) (by decide)]; rfl⟩
  | 8, 2, 2, _, _, _ => exact ⟨e (.n 1245), outCell_sound _ σ KTE 266 1245 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1245) = qv inp (.HB 8 2) from g266,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 2 2 (by decide) (by decide)]; rfl⟩
  | 8, 2, 3, _, _, _ => exact ⟨e (.n 1244), outCell_sound _ σ KTE 267 1244 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1244) = qv inp (.HB 8 2) from g267,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 2 3 (by decide) (by decide)]; rfl⟩
  | 8, 3, 0, _, _, _ => exact ⟨e (.n 1243), outCell_sound _ σ KTE 268 1243 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1243) = qv inp (.HB 8 3) from g268,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 3 0 (by decide) (by decide)]; rfl⟩
  | 8, 3, 1, _, _, _ => exact ⟨e (.n 1242), outCell_sound _ σ KTE 269 1242 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1242) = qv inp (.HB 8 3) from g269,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 3 1 (by decide) (by decide)]; rfl⟩
  | 8, 3, 2, _, _, _ => exact ⟨e (.n 1241), outCell_sound _ σ KTE 270 1241 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1241) = qv inp (.HB 8 3) from g270,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 3 2 (by decide) (by decide)]; rfl⟩
  | 8, 3, 3, _, _, _ => exact ⟨e (.n 1240), outCell_sound _ σ KTE 271 1240 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1240) = qv inp (.HB 8 3) from g271,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 3 3 (by decide) (by decide)]; rfl⟩
  | 8, 4, 0, _, _, _ => exact ⟨e (.n 1239), outCell_sound _ σ KTE 272 1239 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1239) = qv inp (.HB 8 4) from g272,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 4 0 (by decide) (by decide)]; rfl⟩
  | 8, 4, 1, _, _, _ => exact ⟨e (.n 1238), outCell_sound _ σ KTE 273 1238 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1238) = qv inp (.HB 8 4) from g273,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 4 1 (by decide) (by decide)]; rfl⟩
  | 8, 4, 2, _, _, _ => exact ⟨e (.n 1237), outCell_sound _ σ KTE 274 1237 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1237) = qv inp (.HB 8 4) from g274,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 4 2 (by decide) (by decide)]; rfl⟩
  | 8, 4, 3, _, _, _ => exact ⟨e (.n 1236), outCell_sound _ σ KTE 275 1236 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1236) = qv inp (.HB 8 4) from g275,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 4 3 (by decide) (by decide)]; rfl⟩
  | 8, 5, 0, _, _, _ => exact ⟨e (.n 1235), outCell_sound _ σ KTE 276 1235 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1235) = qv inp (.HB 8 5) from g276,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 5 0 (by decide) (by decide)]; rfl⟩
  | 8, 5, 1, _, _, _ => exact ⟨e (.n 1234), outCell_sound _ σ KTE 277 1234 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1234) = qv inp (.HB 8 5) from g277,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 5 1 (by decide) (by decide)]; rfl⟩
  | 8, 5, 2, _, _, _ => exact ⟨e (.n 1233), outCell_sound _ σ KTE 278 1233 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1233) = qv inp (.HB 8 5) from g278,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 5 2 (by decide) (by decide)]; rfl⟩
  | 8, 5, 3, _, _, _ => exact ⟨e (.n 1232), outCell_sound _ σ KTE 279 1232 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1232) = qv inp (.HB 8 5) from g279,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 5 3 (by decide) (by decide)]; rfl⟩
  | 8, 6, 0, _, _, _ => exact ⟨e (.n 1231), outCell_sound _ σ KTE 280 1231 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1231) = qv inp (.HB 8 6) from g280,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 6 0 (by decide) (by decide)]; rfl⟩
  | 8, 6, 1, _, _, _ => exact ⟨e (.n 1230), outCell_sound _ σ KTE 281 1230 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1230) = qv inp (.HB 8 6) from g281,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 6 1 (by decide) (by decide)]; rfl⟩
  | 8, 6, 2, _, _, _ => exact ⟨e (.n 1229), outCell_sound _ σ KTE 282 1229 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1229) = qv inp (.HB 8 6) from g282,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 6 2 (by decide) (by decide)]; rfl⟩
  | 8, 6, 3, _, _, _ => exact ⟨e (.n 1228), outCell_sound _ σ KTE 283 1228 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1228) = qv inp (.HB 8 6) from g283,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 6 3 (by decide) (by decide)]; rfl⟩
  | 8, 7, 0, _, _, _ => exact ⟨e (.n 1227), outCell_sound _ σ KTE 284 1227 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1227) = qv inp (.HB 8 7) from g284,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 8 7 0 (by decide) (by decide)]; rfl⟩
  | 8, 7, 1, _, _, _ => exact ⟨e (.n 1226), outCell_sound _ σ KTE 285 1226 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1226) = qv inp (.HB 8 7) from g285,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 8 7 1 (by decide) (by decide)]; rfl⟩
  | 8, 7, 2, _, _, _ => exact ⟨e (.n 1225), outCell_sound _ σ KTE 286 1225 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1225) = qv inp (.HB 8 7) from g286,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 8 7 2 (by decide) (by decide)]; rfl⟩
  | 8, 7, 3, _, _, _ => exact ⟨e (.n 1224), outCell_sound _ σ KTE 287 1224 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1224) = qv inp (.HB 8 7) from g287,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 8 7 3 (by decide) (by decide)]; rfl⟩
  | 9, 0, 0, _, _, _ => exact ⟨e (.n 1223), outCell_sound _ σ KTE 288 1223 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1223) = qv inp (.HB 9 0) from g288,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 0 0 (by decide) (by decide)]; rfl⟩
  | 9, 0, 1, _, _, _ => exact ⟨e (.n 1222), outCell_sound _ σ KTE 289 1222 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1222) = qv inp (.HB 9 0) from g289,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 0 1 (by decide) (by decide)]; rfl⟩
  | 9, 0, 2, _, _, _ => exact ⟨e (.n 1221), outCell_sound _ σ KTE 290 1221 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1221) = qv inp (.HB 9 0) from g290,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 0 2 (by decide) (by decide)]; rfl⟩
  | 9, 0, 3, _, _, _ => exact ⟨e (.n 1220), outCell_sound _ σ KTE 291 1220 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1220) = qv inp (.HB 9 0) from g291,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 0 3 (by decide) (by decide)]; rfl⟩
  | 9, 1, 0, _, _, _ => exact ⟨e (.n 1219), outCell_sound _ σ KTE 292 1219 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1219) = qv inp (.HB 9 1) from g292,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 1 0 (by decide) (by decide)]; rfl⟩
  | 9, 1, 1, _, _, _ => exact ⟨e (.n 1218), outCell_sound _ σ KTE 293 1218 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1218) = qv inp (.HB 9 1) from g293,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 1 1 (by decide) (by decide)]; rfl⟩
  | 9, 1, 2, _, _, _ => exact ⟨e (.n 1217), outCell_sound _ σ KTE 294 1217 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1217) = qv inp (.HB 9 1) from g294,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 1 2 (by decide) (by decide)]; rfl⟩
  | 9, 1, 3, _, _, _ => exact ⟨e (.n 1216), outCell_sound _ σ KTE 295 1216 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1216) = qv inp (.HB 9 1) from g295,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 1 3 (by decide) (by decide)]; rfl⟩
  | 9, 2, 0, _, _, _ => exact ⟨e (.n 1215), outCell_sound _ σ KTE 296 1215 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1215) = qv inp (.HB 9 2) from g296,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 2 0 (by decide) (by decide)]; rfl⟩
  | 9, 2, 1, _, _, _ => exact ⟨e (.n 1214), outCell_sound _ σ KTE 297 1214 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1214) = qv inp (.HB 9 2) from g297,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 2 1 (by decide) (by decide)]; rfl⟩
  | 9, 2, 2, _, _, _ => exact ⟨e (.n 1213), outCell_sound _ σ KTE 298 1213 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1213) = qv inp (.HB 9 2) from g298,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 2 2 (by decide) (by decide)]; rfl⟩
  | 9, 2, 3, _, _, _ => exact ⟨e (.n 1212), outCell_sound _ σ KTE 299 1212 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1212) = qv inp (.HB 9 2) from g299,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 2 3 (by decide) (by decide)]; rfl⟩
  | 9, 3, 0, _, _, _ => exact ⟨e (.n 1211), outCell_sound _ σ KTE 300 1211 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1211) = qv inp (.HB 9 3) from g300,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 3 0 (by decide) (by decide)]; rfl⟩
  | 9, 3, 1, _, _, _ => exact ⟨e (.n 1210), outCell_sound _ σ KTE 301 1210 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1210) = qv inp (.HB 9 3) from g301,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 3 1 (by decide) (by decide)]; rfl⟩
  | 9, 3, 2, _, _, _ => exact ⟨e (.n 1209), outCell_sound _ σ KTE 302 1209 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1209) = qv inp (.HB 9 3) from g302,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 3 2 (by decide) (by decide)]; rfl⟩
  | 9, 3, 3, _, _, _ => exact ⟨e (.n 1208), outCell_sound _ σ KTE 303 1208 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1208) = qv inp (.HB 9 3) from g303,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 3 3 (by decide) (by decide)]; rfl⟩
  | 9, 4, 0, _, _, _ => exact ⟨e (.n 1207), outCell_sound _ σ KTE 304 1207 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1207) = qv inp (.HB 9 4) from g304,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 4 0 (by decide) (by decide)]; rfl⟩
  | 9, 4, 1, _, _, _ => exact ⟨e (.n 1206), outCell_sound _ σ KTE 305 1206 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1206) = qv inp (.HB 9 4) from g305,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 4 1 (by decide) (by decide)]; rfl⟩
  | 9, 4, 2, _, _, _ => exact ⟨e (.n 1205), outCell_sound _ σ KTE 306 1205 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1205) = qv inp (.HB 9 4) from g306,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 4 2 (by decide) (by decide)]; rfl⟩
  | 9, 4, 3, _, _, _ => exact ⟨e (.n 1204), outCell_sound _ σ KTE 307 1204 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1204) = qv inp (.HB 9 4) from g307,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 4 3 (by decide) (by decide)]; rfl⟩
  | 9, 5, 0, _, _, _ => exact ⟨e (.n 1203), outCell_sound _ σ KTE 308 1203 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1203) = qv inp (.HB 9 5) from g308,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 5 0 (by decide) (by decide)]; rfl⟩
  | 9, 5, 1, _, _, _ => exact ⟨e (.n 1202), outCell_sound _ σ KTE 309 1202 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1202) = qv inp (.HB 9 5) from g309,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 5 1 (by decide) (by decide)]; rfl⟩
  | 9, 5, 2, _, _, _ => exact ⟨e (.n 1201), outCell_sound _ σ KTE 310 1201 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1201) = qv inp (.HB 9 5) from g310,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 5 2 (by decide) (by decide)]; rfl⟩
  | 9, 5, 3, _, _, _ => exact ⟨e (.n 1200), outCell_sound _ σ KTE 311 1200 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1200) = qv inp (.HB 9 5) from g311,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 5 3 (by decide) (by decide)]; rfl⟩
  | 9, 6, 0, _, _, _ => exact ⟨e (.n 1199), outCell_sound _ σ KTE 312 1199 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1199) = qv inp (.HB 9 6) from g312,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 6 0 (by decide) (by decide)]; rfl⟩
  | 9, 6, 1, _, _, _ => exact ⟨e (.n 1198), outCell_sound _ σ KTE 313 1198 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1198) = qv inp (.HB 9 6) from g313,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 6 1 (by decide) (by decide)]; rfl⟩
  | 9, 6, 2, _, _, _ => exact ⟨e (.n 1197), outCell_sound _ σ KTE 314 1197 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1197) = qv inp (.HB 9 6) from g314,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 6 2 (by decide) (by decide)]; rfl⟩
  | 9, 6, 3, _, _, _ => exact ⟨e (.n 1196), outCell_sound _ σ KTE 315 1196 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1196) = qv inp (.HB 9 6) from g315,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 6 3 (by decide) (by decide)]; rfl⟩
  | 9, 7, 0, _, _, _ => exact ⟨e (.n 1195), outCell_sound _ σ KTE 316 1195 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1195) = qv inp (.HB 9 7) from g316,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 9 7 0 (by decide) (by decide)]; rfl⟩
  | 9, 7, 1, _, _, _ => exact ⟨e (.n 1194), outCell_sound _ σ KTE 317 1194 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1194) = qv inp (.HB 9 7) from g317,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 9 7 1 (by decide) (by decide)]; rfl⟩
  | 9, 7, 2, _, _, _ => exact ⟨e (.n 1193), outCell_sound _ σ KTE 318 1193 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1193) = qv inp (.HB 9 7) from g318,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 9 7 2 (by decide) (by decide)]; rfl⟩
  | 9, 7, 3, _, _, _ => exact ⟨e (.n 1192), outCell_sound _ σ KTE 319 1192 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1192) = qv inp (.HB 9 7) from g319,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 9 7 3 (by decide) (by decide)]; rfl⟩
  | 10, 0, 0, _, _, _ => exact ⟨e (.n 1191), outCell_sound _ σ KTE 320 1191 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1191) = qv inp (.HB 10 0) from g320,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 0 0 (by decide) (by decide)]; rfl⟩
  | 10, 0, 1, _, _, _ => exact ⟨e (.n 1190), outCell_sound _ σ KTE 321 1190 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1190) = qv inp (.HB 10 0) from g321,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 0 1 (by decide) (by decide)]; rfl⟩
  | 10, 0, 2, _, _, _ => exact ⟨e (.n 1189), outCell_sound _ σ KTE 322 1189 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1189) = qv inp (.HB 10 0) from g322,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 0 2 (by decide) (by decide)]; rfl⟩
  | 10, 0, 3, _, _, _ => exact ⟨e (.n 1188), outCell_sound _ σ KTE 323 1188 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1188) = qv inp (.HB 10 0) from g323,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 0 3 (by decide) (by decide)]; rfl⟩
  | 10, 1, 0, _, _, _ => exact ⟨e (.n 1187), outCell_sound _ σ KTE 324 1187 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1187) = qv inp (.HB 10 1) from g324,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 1 0 (by decide) (by decide)]; rfl⟩
  | 10, 1, 1, _, _, _ => exact ⟨e (.n 1186), outCell_sound _ σ KTE 325 1186 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1186) = qv inp (.HB 10 1) from g325,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 1 1 (by decide) (by decide)]; rfl⟩
  | 10, 1, 2, _, _, _ => exact ⟨e (.n 1185), outCell_sound _ σ KTE 326 1185 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1185) = qv inp (.HB 10 1) from g326,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 1 2 (by decide) (by decide)]; rfl⟩
  | 10, 1, 3, _, _, _ => exact ⟨e (.n 1184), outCell_sound _ σ KTE 327 1184 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1184) = qv inp (.HB 10 1) from g327,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 1 3 (by decide) (by decide)]; rfl⟩
  | 10, 2, 0, _, _, _ => exact ⟨e (.n 1183), outCell_sound _ σ KTE 328 1183 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1183) = qv inp (.HB 10 2) from g328,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 2 0 (by decide) (by decide)]; rfl⟩
  | 10, 2, 1, _, _, _ => exact ⟨e (.n 1182), outCell_sound _ σ KTE 329 1182 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1182) = qv inp (.HB 10 2) from g329,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 2 1 (by decide) (by decide)]; rfl⟩
  | 10, 2, 2, _, _, _ => exact ⟨e (.n 1181), outCell_sound _ σ KTE 330 1181 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1181) = qv inp (.HB 10 2) from g330,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 2 2 (by decide) (by decide)]; rfl⟩
  | 10, 2, 3, _, _, _ => exact ⟨e (.n 1180), outCell_sound _ σ KTE 331 1180 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1180) = qv inp (.HB 10 2) from g331,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 2 3 (by decide) (by decide)]; rfl⟩
  | 10, 3, 0, _, _, _ => exact ⟨e (.n 1179), outCell_sound _ σ KTE 332 1179 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1179) = qv inp (.HB 10 3) from g332,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 3 0 (by decide) (by decide)]; rfl⟩
  | 10, 3, 1, _, _, _ => exact ⟨e (.n 1178), outCell_sound _ σ KTE 333 1178 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1178) = qv inp (.HB 10 3) from g333,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 3 1 (by decide) (by decide)]; rfl⟩
  | 10, 3, 2, _, _, _ => exact ⟨e (.n 1177), outCell_sound _ σ KTE 334 1177 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1177) = qv inp (.HB 10 3) from g334,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 3 2 (by decide) (by decide)]; rfl⟩
  | 10, 3, 3, _, _, _ => exact ⟨e (.n 1176), outCell_sound _ σ KTE 335 1176 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1176) = qv inp (.HB 10 3) from g335,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 3 3 (by decide) (by decide)]; rfl⟩
  | 10, 4, 0, _, _, _ => exact ⟨e (.n 1175), outCell_sound _ σ KTE 336 1175 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1175) = qv inp (.HB 10 4) from g336,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 4 0 (by decide) (by decide)]; rfl⟩
  | 10, 4, 1, _, _, _ => exact ⟨e (.n 1174), outCell_sound _ σ KTE 337 1174 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1174) = qv inp (.HB 10 4) from g337,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 4 1 (by decide) (by decide)]; rfl⟩
  | 10, 4, 2, _, _, _ => exact ⟨e (.n 1173), outCell_sound _ σ KTE 338 1173 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1173) = qv inp (.HB 10 4) from g338,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 4 2 (by decide) (by decide)]; rfl⟩
  | 10, 4, 3, _, _, _ => exact ⟨e (.n 1172), outCell_sound _ σ KTE 339 1172 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1172) = qv inp (.HB 10 4) from g339,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 4 3 (by decide) (by decide)]; rfl⟩
  | 10, 5, 0, _, _, _ => exact ⟨e (.n 1171), outCell_sound _ σ KTE 340 1171 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1171) = qv inp (.HB 10 5) from g340,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 5 0 (by decide) (by decide)]; rfl⟩
  | 10, 5, 1, _, _, _ => exact ⟨e (.n 1170), outCell_sound _ σ KTE 341 1170 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1170) = qv inp (.HB 10 5) from g341,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 5 1 (by decide) (by decide)]; rfl⟩
  | 10, 5, 2, _, _, _ => exact ⟨e (.n 1169), outCell_sound _ σ KTE 342 1169 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1169) = qv inp (.HB 10 5) from g342,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 5 2 (by decide) (by decide)]; rfl⟩
  | 10, 5, 3, _, _, _ => exact ⟨e (.n 1168), outCell_sound _ σ KTE 343 1168 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1168) = qv inp (.HB 10 5) from g343,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 5 3 (by decide) (by decide)]; rfl⟩
  | 10, 6, 0, _, _, _ => exact ⟨e (.n 1167), outCell_sound _ σ KTE 344 1167 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1167) = qv inp (.HB 10 6) from g344,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 6 0 (by decide) (by decide)]; rfl⟩
  | 10, 6, 1, _, _, _ => exact ⟨e (.n 1166), outCell_sound _ σ KTE 345 1166 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1166) = qv inp (.HB 10 6) from g345,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 6 1 (by decide) (by decide)]; rfl⟩
  | 10, 6, 2, _, _, _ => exact ⟨e (.n 1165), outCell_sound _ σ KTE 346 1165 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1165) = qv inp (.HB 10 6) from g346,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 6 2 (by decide) (by decide)]; rfl⟩
  | 10, 6, 3, _, _, _ => exact ⟨e (.n 1164), outCell_sound _ σ KTE 347 1164 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1164) = qv inp (.HB 10 6) from g347,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 6 3 (by decide) (by decide)]; rfl⟩
  | 10, 7, 0, _, _, _ => exact ⟨e (.n 1163), outCell_sound _ σ KTE 348 1163 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1163) = qv inp (.HB 10 7) from g348,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 10 7 0 (by decide) (by decide)]; rfl⟩
  | 10, 7, 1, _, _, _ => exact ⟨e (.n 1162), outCell_sound _ σ KTE 349 1162 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1162) = qv inp (.HB 10 7) from g349,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 10 7 1 (by decide) (by decide)]; rfl⟩
  | 10, 7, 2, _, _, _ => exact ⟨e (.n 1161), outCell_sound _ σ KTE 350 1161 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1161) = qv inp (.HB 10 7) from g350,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 10 7 2 (by decide) (by decide)]; rfl⟩
  | 10, 7, 3, _, _, _ => exact ⟨e (.n 1160), outCell_sound _ σ KTE 351 1160 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1160) = qv inp (.HB 10 7) from g351,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 10 7 3 (by decide) (by decide)]; rfl⟩
  | 11, 0, 0, _, _, _ => exact ⟨e (.n 1159), outCell_sound _ σ KTE 352 1159 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1159) = qv inp (.HB 11 0) from g352,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 0 0 (by decide) (by decide)]; rfl⟩
  | 11, 0, 1, _, _, _ => exact ⟨e (.n 1158), outCell_sound _ σ KTE 353 1158 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1158) = qv inp (.HB 11 0) from g353,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 0 1 (by decide) (by decide)]; rfl⟩
  | 11, 0, 2, _, _, _ => exact ⟨e (.n 1157), outCell_sound _ σ KTE 354 1157 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1157) = qv inp (.HB 11 0) from g354,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 0 2 (by decide) (by decide)]; rfl⟩
  | 11, 0, 3, _, _, _ => exact ⟨e (.n 1156), outCell_sound _ σ KTE 355 1156 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1156) = qv inp (.HB 11 0) from g355,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 0 3 (by decide) (by decide)]; rfl⟩
  | 11, 1, 0, _, _, _ => exact ⟨e (.n 1155), outCell_sound _ σ KTE 356 1155 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1155) = qv inp (.HB 11 1) from g356,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 1 0 (by decide) (by decide)]; rfl⟩
  | 11, 1, 1, _, _, _ => exact ⟨e (.n 1154), outCell_sound _ σ KTE 357 1154 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1154) = qv inp (.HB 11 1) from g357,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 1 1 (by decide) (by decide)]; rfl⟩
  | 11, 1, 2, _, _, _ => exact ⟨e (.n 1153), outCell_sound _ σ KTE 358 1153 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1153) = qv inp (.HB 11 1) from g358,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 1 2 (by decide) (by decide)]; rfl⟩
  | 11, 1, 3, _, _, _ => exact ⟨e (.n 1152), outCell_sound _ σ KTE 359 1152 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1152) = qv inp (.HB 11 1) from g359,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 1 3 (by decide) (by decide)]; rfl⟩
  | 11, 2, 0, _, _, _ => exact ⟨e (.n 1151), outCell_sound _ σ KTE 360 1151 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1151) = qv inp (.HB 11 2) from g360,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 2 0 (by decide) (by decide)]; rfl⟩
  | 11, 2, 1, _, _, _ => exact ⟨e (.n 1150), outCell_sound _ σ KTE 361 1150 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1150) = qv inp (.HB 11 2) from g361,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 2 1 (by decide) (by decide)]; rfl⟩
  | 11, 2, 2, _, _, _ => exact ⟨e (.n 1149), outCell_sound _ σ KTE 362 1149 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1149) = qv inp (.HB 11 2) from g362,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 2 2 (by decide) (by decide)]; rfl⟩
  | 11, 2, 3, _, _, _ => exact ⟨e (.n 1148), outCell_sound _ σ KTE 363 1148 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1148) = qv inp (.HB 11 2) from g363,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 2 3 (by decide) (by decide)]; rfl⟩
  | 11, 3, 0, _, _, _ => exact ⟨e (.n 1147), outCell_sound _ σ KTE 364 1147 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1147) = qv inp (.HB 11 3) from g364,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 3 0 (by decide) (by decide)]; rfl⟩
  | 11, 3, 1, _, _, _ => exact ⟨e (.n 1146), outCell_sound _ σ KTE 365 1146 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1146) = qv inp (.HB 11 3) from g365,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 3 1 (by decide) (by decide)]; rfl⟩
  | 11, 3, 2, _, _, _ => exact ⟨e (.n 1145), outCell_sound _ σ KTE 366 1145 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1145) = qv inp (.HB 11 3) from g366,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 3 2 (by decide) (by decide)]; rfl⟩
  | 11, 3, 3, _, _, _ => exact ⟨e (.n 1144), outCell_sound _ σ KTE 367 1144 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1144) = qv inp (.HB 11 3) from g367,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 3 3 (by decide) (by decide)]; rfl⟩
  | 11, 4, 0, _, _, _ => exact ⟨e (.n 1143), outCell_sound _ σ KTE 368 1143 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1143) = qv inp (.HB 11 4) from g368,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 4 0 (by decide) (by decide)]; rfl⟩
  | 11, 4, 1, _, _, _ => exact ⟨e (.n 1142), outCell_sound _ σ KTE 369 1142 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1142) = qv inp (.HB 11 4) from g369,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 4 1 (by decide) (by decide)]; rfl⟩
  | 11, 4, 2, _, _, _ => exact ⟨e (.n 1141), outCell_sound _ σ KTE 370 1141 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1141) = qv inp (.HB 11 4) from g370,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 4 2 (by decide) (by decide)]; rfl⟩
  | 11, 4, 3, _, _, _ => exact ⟨e (.n 1140), outCell_sound _ σ KTE 371 1140 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1140) = qv inp (.HB 11 4) from g371,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 4 3 (by decide) (by decide)]; rfl⟩
  | 11, 5, 0, _, _, _ => exact ⟨e (.n 1139), outCell_sound _ σ KTE 372 1139 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1139) = qv inp (.HB 11 5) from g372,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 5 0 (by decide) (by decide)]; rfl⟩
  | 11, 5, 1, _, _, _ => exact ⟨e (.n 1138), outCell_sound _ σ KTE 373 1138 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1138) = qv inp (.HB 11 5) from g373,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 5 1 (by decide) (by decide)]; rfl⟩
  | 11, 5, 2, _, _, _ => exact ⟨e (.n 1137), outCell_sound _ σ KTE 374 1137 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1137) = qv inp (.HB 11 5) from g374,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 5 2 (by decide) (by decide)]; rfl⟩
  | 11, 5, 3, _, _, _ => exact ⟨e (.n 1136), outCell_sound _ σ KTE 375 1136 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1136) = qv inp (.HB 11 5) from g375,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 5 3 (by decide) (by decide)]; rfl⟩
  | 11, 6, 0, _, _, _ => exact ⟨e (.n 1135), outCell_sound _ σ KTE 376 1135 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1135) = qv inp (.HB 11 6) from g376,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 6 0 (by decide) (by decide)]; rfl⟩
  | 11, 6, 1, _, _, _ => exact ⟨e (.n 1134), outCell_sound _ σ KTE 377 1134 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1134) = qv inp (.HB 11 6) from g377,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 6 1 (by decide) (by decide)]; rfl⟩
  | 11, 6, 2, _, _, _ => exact ⟨e (.n 1133), outCell_sound _ σ KTE 378 1133 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1133) = qv inp (.HB 11 6) from g378,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 6 2 (by decide) (by decide)]; rfl⟩
  | 11, 6, 3, _, _, _ => exact ⟨e (.n 1132), outCell_sound _ σ KTE 379 1132 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1132) = qv inp (.HB 11 6) from g379,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 6 3 (by decide) (by decide)]; rfl⟩
  | 11, 7, 0, _, _, _ => exact ⟨e (.n 1131), outCell_sound _ σ KTE 380 1131 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1131) = qv inp (.HB 11 7) from g380,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 11 7 0 (by decide) (by decide)]; rfl⟩
  | 11, 7, 1, _, _, _ => exact ⟨e (.n 1130), outCell_sound _ σ KTE 381 1130 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1130) = qv inp (.HB 11 7) from g381,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 11 7 1 (by decide) (by decide)]; rfl⟩
  | 11, 7, 2, _, _, _ => exact ⟨e (.n 1129), outCell_sound _ σ KTE 382 1129 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1129) = qv inp (.HB 11 7) from g382,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 11 7 2 (by decide) (by decide)]; rfl⟩
  | 11, 7, 3, _, _, _ => exact ⟨e (.n 1128), outCell_sound _ σ KTE 383 1128 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1128) = qv inp (.HB 11 7) from g383,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 11 7 3 (by decide) (by decide)]; rfl⟩
  | 12, 0, 0, _, _, _ => exact ⟨e (.n 1127), outCell_sound _ σ KTE 384 1127 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1127) = qv inp (.HB 12 0) from g384,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 0 0 (by decide) (by decide)]; rfl⟩
  | 12, 0, 1, _, _, _ => exact ⟨e (.n 1126), outCell_sound _ σ KTE 385 1126 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1126) = qv inp (.HB 12 0) from g385,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 0 1 (by decide) (by decide)]; rfl⟩
  | 12, 0, 2, _, _, _ => exact ⟨e (.n 1125), outCell_sound _ σ KTE 386 1125 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1125) = qv inp (.HB 12 0) from g386,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 0 2 (by decide) (by decide)]; rfl⟩
  | 12, 0, 3, _, _, _ => exact ⟨e (.n 1124), outCell_sound _ σ KTE 387 1124 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1124) = qv inp (.HB 12 0) from g387,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 0 3 (by decide) (by decide)]; rfl⟩
  | 12, 1, 0, _, _, _ => exact ⟨e (.n 1123), outCell_sound _ σ KTE 388 1123 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1123) = qv inp (.HB 12 1) from g388,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 1 0 (by decide) (by decide)]; rfl⟩
  | 12, 1, 1, _, _, _ => exact ⟨e (.n 1122), outCell_sound _ σ KTE 389 1122 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1122) = qv inp (.HB 12 1) from g389,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 1 1 (by decide) (by decide)]; rfl⟩
  | 12, 1, 2, _, _, _ => exact ⟨e (.n 1121), outCell_sound _ σ KTE 390 1121 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1121) = qv inp (.HB 12 1) from g390,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 1 2 (by decide) (by decide)]; rfl⟩
  | 12, 1, 3, _, _, _ => exact ⟨e (.n 1120), outCell_sound _ σ KTE 391 1120 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1120) = qv inp (.HB 12 1) from g391,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 1 3 (by decide) (by decide)]; rfl⟩
  | 12, 2, 0, _, _, _ => exact ⟨e (.n 1119), outCell_sound _ σ KTE 392 1119 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1119) = qv inp (.HB 12 2) from g392,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 2 0 (by decide) (by decide)]; rfl⟩
  | 12, 2, 1, _, _, _ => exact ⟨e (.n 1118), outCell_sound _ σ KTE 393 1118 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1118) = qv inp (.HB 12 2) from g393,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 2 1 (by decide) (by decide)]; rfl⟩
  | 12, 2, 2, _, _, _ => exact ⟨e (.n 1117), outCell_sound _ σ KTE 394 1117 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1117) = qv inp (.HB 12 2) from g394,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 2 2 (by decide) (by decide)]; rfl⟩
  | 12, 2, 3, _, _, _ => exact ⟨e (.n 1116), outCell_sound _ σ KTE 395 1116 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1116) = qv inp (.HB 12 2) from g395,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 2 3 (by decide) (by decide)]; rfl⟩
  | 12, 3, 0, _, _, _ => exact ⟨e (.n 1115), outCell_sound _ σ KTE 396 1115 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1115) = qv inp (.HB 12 3) from g396,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 3 0 (by decide) (by decide)]; rfl⟩
  | 12, 3, 1, _, _, _ => exact ⟨e (.n 1114), outCell_sound _ σ KTE 397 1114 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1114) = qv inp (.HB 12 3) from g397,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 3 1 (by decide) (by decide)]; rfl⟩
  | 12, 3, 2, _, _, _ => exact ⟨e (.n 1113), outCell_sound _ σ KTE 398 1113 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1113) = qv inp (.HB 12 3) from g398,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 3 2 (by decide) (by decide)]; rfl⟩
  | 12, 3, 3, _, _, _ => exact ⟨e (.n 1112), outCell_sound _ σ KTE 399 1112 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1112) = qv inp (.HB 12 3) from g399,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 3 3 (by decide) (by decide)]; rfl⟩
  | 12, 4, 0, _, _, _ => exact ⟨e (.n 1111), outCell_sound _ σ KTE 400 1111 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1111) = qv inp (.HB 12 4) from g400,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 4 0 (by decide) (by decide)]; rfl⟩
  | 12, 4, 1, _, _, _ => exact ⟨e (.n 1110), outCell_sound _ σ KTE 401 1110 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1110) = qv inp (.HB 12 4) from g401,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 4 1 (by decide) (by decide)]; rfl⟩
  | 12, 4, 2, _, _, _ => exact ⟨e (.n 1109), outCell_sound _ σ KTE 402 1109 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1109) = qv inp (.HB 12 4) from g402,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 4 2 (by decide) (by decide)]; rfl⟩
  | 12, 4, 3, _, _, _ => exact ⟨e (.n 1108), outCell_sound _ σ KTE 403 1108 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1108) = qv inp (.HB 12 4) from g403,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 4 3 (by decide) (by decide)]; rfl⟩
  | 12, 5, 0, _, _, _ => exact ⟨e (.n 1107), outCell_sound _ σ KTE 404 1107 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1107) = qv inp (.HB 12 5) from g404,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 5 0 (by decide) (by decide)]; rfl⟩
  | 12, 5, 1, _, _, _ => exact ⟨e (.n 1106), outCell_sound _ σ KTE 405 1106 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1106) = qv inp (.HB 12 5) from g405,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 5 1 (by decide) (by decide)]; rfl⟩
  | 12, 5, 2, _, _, _ => exact ⟨e (.n 1105), outCell_sound _ σ KTE 406 1105 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1105) = qv inp (.HB 12 5) from g406,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 5 2 (by decide) (by decide)]; rfl⟩
  | 12, 5, 3, _, _, _ => exact ⟨e (.n 1104), outCell_sound _ σ KTE 407 1104 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1104) = qv inp (.HB 12 5) from g407,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 5 3 (by decide) (by decide)]; rfl⟩
  | 12, 6, 0, _, _, _ => exact ⟨e (.n 1103), outCell_sound _ σ KTE 408 1103 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1103) = qv inp (.HB 12 6) from g408,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 6 0 (by decide) (by decide)]; rfl⟩
  | 12, 6, 1, _, _, _ => exact ⟨e (.n 1102), outCell_sound _ σ KTE 409 1102 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1102) = qv inp (.HB 12 6) from g409,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 6 1 (by decide) (by decide)]; rfl⟩
  | 12, 6, 2, _, _, _ => exact ⟨e (.n 1101), outCell_sound _ σ KTE 410 1101 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1101) = qv inp (.HB 12 6) from g410,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 6 2 (by decide) (by decide)]; rfl⟩
  | 12, 6, 3, _, _, _ => exact ⟨e (.n 1100), outCell_sound _ σ KTE 411 1100 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1100) = qv inp (.HB 12 6) from g411,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 6 3 (by decide) (by decide)]; rfl⟩
  | 12, 7, 0, _, _, _ => exact ⟨e (.n 1099), outCell_sound _ σ KTE 412 1099 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1099) = qv inp (.HB 12 7) from g412,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 12 7 0 (by decide) (by decide)]; rfl⟩
  | 12, 7, 1, _, _, _ => exact ⟨e (.n 1098), outCell_sound _ σ KTE 413 1098 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1098) = qv inp (.HB 12 7) from g413,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 12 7 1 (by decide) (by decide)]; rfl⟩
  | 12, 7, 2, _, _, _ => exact ⟨e (.n 1097), outCell_sound _ σ KTE 414 1097 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1097) = qv inp (.HB 12 7) from g414,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 12 7 2 (by decide) (by decide)]; rfl⟩
  | 12, 7, 3, _, _, _ => exact ⟨e (.n 1096), outCell_sound _ σ KTE 415 1096 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1096) = qv inp (.HB 12 7) from g415,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 12 7 3 (by decide) (by decide)]; rfl⟩
  | 13, 0, 0, _, _, _ => exact ⟨e (.n 1095), outCell_sound _ σ KTE 416 1095 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1095) = qv inp (.HB 13 0) from g416,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 0 0 (by decide) (by decide)]; rfl⟩
  | 13, 0, 1, _, _, _ => exact ⟨e (.n 1094), outCell_sound _ σ KTE 417 1094 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1094) = qv inp (.HB 13 0) from g417,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 0 1 (by decide) (by decide)]; rfl⟩
  | 13, 0, 2, _, _, _ => exact ⟨e (.n 1093), outCell_sound _ σ KTE 418 1093 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1093) = qv inp (.HB 13 0) from g418,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 0 2 (by decide) (by decide)]; rfl⟩
  | 13, 0, 3, _, _, _ => exact ⟨e (.n 1092), outCell_sound _ σ KTE 419 1092 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1092) = qv inp (.HB 13 0) from g419,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 0 3 (by decide) (by decide)]; rfl⟩
  | 13, 1, 0, _, _, _ => exact ⟨e (.n 1091), outCell_sound _ σ KTE 420 1091 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1091) = qv inp (.HB 13 1) from g420,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 1 0 (by decide) (by decide)]; rfl⟩
  | 13, 1, 1, _, _, _ => exact ⟨e (.n 1090), outCell_sound _ σ KTE 421 1090 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1090) = qv inp (.HB 13 1) from g421,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 1 1 (by decide) (by decide)]; rfl⟩
  | 13, 1, 2, _, _, _ => exact ⟨e (.n 1089), outCell_sound _ σ KTE 422 1089 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1089) = qv inp (.HB 13 1) from g422,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 1 2 (by decide) (by decide)]; rfl⟩
  | 13, 1, 3, _, _, _ => exact ⟨e (.n 1088), outCell_sound _ σ KTE 423 1088 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1088) = qv inp (.HB 13 1) from g423,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 1 3 (by decide) (by decide)]; rfl⟩
  | 13, 2, 0, _, _, _ => exact ⟨e (.n 1087), outCell_sound _ σ KTE 424 1087 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1087) = qv inp (.HB 13 2) from g424,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 2 0 (by decide) (by decide)]; rfl⟩
  | 13, 2, 1, _, _, _ => exact ⟨e (.n 1086), outCell_sound _ σ KTE 425 1086 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1086) = qv inp (.HB 13 2) from g425,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 2 1 (by decide) (by decide)]; rfl⟩
  | 13, 2, 2, _, _, _ => exact ⟨e (.n 1085), outCell_sound _ σ KTE 426 1085 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1085) = qv inp (.HB 13 2) from g426,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 2 2 (by decide) (by decide)]; rfl⟩
  | 13, 2, 3, _, _, _ => exact ⟨e (.n 1084), outCell_sound _ σ KTE 427 1084 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1084) = qv inp (.HB 13 2) from g427,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 2 3 (by decide) (by decide)]; rfl⟩
  | 13, 3, 0, _, _, _ => exact ⟨e (.n 1083), outCell_sound _ σ KTE 428 1083 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1083) = qv inp (.HB 13 3) from g428,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 3 0 (by decide) (by decide)]; rfl⟩
  | 13, 3, 1, _, _, _ => exact ⟨e (.n 1082), outCell_sound _ σ KTE 429 1082 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1082) = qv inp (.HB 13 3) from g429,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 3 1 (by decide) (by decide)]; rfl⟩
  | 13, 3, 2, _, _, _ => exact ⟨e (.n 1081), outCell_sound _ σ KTE 430 1081 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1081) = qv inp (.HB 13 3) from g430,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 3 2 (by decide) (by decide)]; rfl⟩
  | 13, 3, 3, _, _, _ => exact ⟨e (.n 1080), outCell_sound _ σ KTE 431 1080 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1080) = qv inp (.HB 13 3) from g431,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 3 3 (by decide) (by decide)]; rfl⟩
  | 13, 4, 0, _, _, _ => exact ⟨e (.n 1079), outCell_sound _ σ KTE 432 1079 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1079) = qv inp (.HB 13 4) from g432,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 4 0 (by decide) (by decide)]; rfl⟩
  | 13, 4, 1, _, _, _ => exact ⟨e (.n 1078), outCell_sound _ σ KTE 433 1078 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1078) = qv inp (.HB 13 4) from g433,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 4 1 (by decide) (by decide)]; rfl⟩
  | 13, 4, 2, _, _, _ => exact ⟨e (.n 1077), outCell_sound _ σ KTE 434 1077 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1077) = qv inp (.HB 13 4) from g434,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 4 2 (by decide) (by decide)]; rfl⟩
  | 13, 4, 3, _, _, _ => exact ⟨e (.n 1076), outCell_sound _ σ KTE 435 1076 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1076) = qv inp (.HB 13 4) from g435,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 4 3 (by decide) (by decide)]; rfl⟩
  | 13, 5, 0, _, _, _ => exact ⟨e (.n 1075), outCell_sound _ σ KTE 436 1075 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1075) = qv inp (.HB 13 5) from g436,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 5 0 (by decide) (by decide)]; rfl⟩
  | 13, 5, 1, _, _, _ => exact ⟨e (.n 1074), outCell_sound _ σ KTE 437 1074 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1074) = qv inp (.HB 13 5) from g437,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 5 1 (by decide) (by decide)]; rfl⟩
  | 13, 5, 2, _, _, _ => exact ⟨e (.n 1073), outCell_sound _ σ KTE 438 1073 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1073) = qv inp (.HB 13 5) from g438,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 5 2 (by decide) (by decide)]; rfl⟩
  | 13, 5, 3, _, _, _ => exact ⟨e (.n 1072), outCell_sound _ σ KTE 439 1072 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1072) = qv inp (.HB 13 5) from g439,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 5 3 (by decide) (by decide)]; rfl⟩
  | 13, 6, 0, _, _, _ => exact ⟨e (.n 1071), outCell_sound _ σ KTE 440 1071 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1071) = qv inp (.HB 13 6) from g440,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 6 0 (by decide) (by decide)]; rfl⟩
  | 13, 6, 1, _, _, _ => exact ⟨e (.n 1070), outCell_sound _ σ KTE 441 1070 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1070) = qv inp (.HB 13 6) from g441,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 6 1 (by decide) (by decide)]; rfl⟩
  | 13, 6, 2, _, _, _ => exact ⟨e (.n 1069), outCell_sound _ σ KTE 442 1069 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1069) = qv inp (.HB 13 6) from g442,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 6 2 (by decide) (by decide)]; rfl⟩
  | 13, 6, 3, _, _, _ => exact ⟨e (.n 1068), outCell_sound _ σ KTE 443 1068 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1068) = qv inp (.HB 13 6) from g443,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 6 3 (by decide) (by decide)]; rfl⟩
  | 13, 7, 0, _, _, _ => exact ⟨e (.n 1067), outCell_sound _ σ KTE 444 1067 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1067) = qv inp (.HB 13 7) from g444,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 13 7 0 (by decide) (by decide)]; rfl⟩
  | 13, 7, 1, _, _, _ => exact ⟨e (.n 1066), outCell_sound _ σ KTE 445 1066 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1066) = qv inp (.HB 13 7) from g445,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 13 7 1 (by decide) (by decide)]; rfl⟩
  | 13, 7, 2, _, _, _ => exact ⟨e (.n 1065), outCell_sound _ σ KTE 446 1065 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1065) = qv inp (.HB 13 7) from g446,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 13 7 2 (by decide) (by decide)]; rfl⟩
  | 13, 7, 3, _, _, _ => exact ⟨e (.n 1064), outCell_sound _ σ KTE 447 1064 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1064) = qv inp (.HB 13 7) from g447,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 13 7 3 (by decide) (by decide)]; rfl⟩
  | 14, 0, 0, _, _, _ => exact ⟨e (.n 1063), outCell_sound _ σ KTE 448 1063 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1063) = qv inp (.HB 14 0) from g448,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 0 0 (by decide) (by decide)]; rfl⟩
  | 14, 0, 1, _, _, _ => exact ⟨e (.n 1062), outCell_sound _ σ KTE 449 1062 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1062) = qv inp (.HB 14 0) from g449,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 0 1 (by decide) (by decide)]; rfl⟩
  | 14, 0, 2, _, _, _ => exact ⟨e (.n 1061), outCell_sound _ σ KTE 450 1061 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1061) = qv inp (.HB 14 0) from g450,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 0 2 (by decide) (by decide)]; rfl⟩
  | 14, 0, 3, _, _, _ => exact ⟨e (.n 1060), outCell_sound _ σ KTE 451 1060 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1060) = qv inp (.HB 14 0) from g451,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 0 3 (by decide) (by decide)]; rfl⟩
  | 14, 1, 0, _, _, _ => exact ⟨e (.n 1059), outCell_sound _ σ KTE 452 1059 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1059) = qv inp (.HB 14 1) from g452,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 1 0 (by decide) (by decide)]; rfl⟩
  | 14, 1, 1, _, _, _ => exact ⟨e (.n 1058), outCell_sound _ σ KTE 453 1058 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1058) = qv inp (.HB 14 1) from g453,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 1 1 (by decide) (by decide)]; rfl⟩
  | 14, 1, 2, _, _, _ => exact ⟨e (.n 1057), outCell_sound _ σ KTE 454 1057 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1057) = qv inp (.HB 14 1) from g454,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 1 2 (by decide) (by decide)]; rfl⟩
  | 14, 1, 3, _, _, _ => exact ⟨e (.n 1056), outCell_sound _ σ KTE 455 1056 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1056) = qv inp (.HB 14 1) from g455,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 1 3 (by decide) (by decide)]; rfl⟩
  | 14, 2, 0, _, _, _ => exact ⟨e (.n 1055), outCell_sound _ σ KTE 456 1055 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1055) = qv inp (.HB 14 2) from g456,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 2 0 (by decide) (by decide)]; rfl⟩
  | 14, 2, 1, _, _, _ => exact ⟨e (.n 1054), outCell_sound _ σ KTE 457 1054 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1054) = qv inp (.HB 14 2) from g457,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 2 1 (by decide) (by decide)]; rfl⟩
  | 14, 2, 2, _, _, _ => exact ⟨e (.n 1053), outCell_sound _ σ KTE 458 1053 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1053) = qv inp (.HB 14 2) from g458,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 2 2 (by decide) (by decide)]; rfl⟩
  | 14, 2, 3, _, _, _ => exact ⟨e (.n 1052), outCell_sound _ σ KTE 459 1052 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1052) = qv inp (.HB 14 2) from g459,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 2 3 (by decide) (by decide)]; rfl⟩
  | 14, 3, 0, _, _, _ => exact ⟨e (.n 1051), outCell_sound _ σ KTE 460 1051 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1051) = qv inp (.HB 14 3) from g460,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 3 0 (by decide) (by decide)]; rfl⟩
  | 14, 3, 1, _, _, _ => exact ⟨e (.n 1050), outCell_sound _ σ KTE 461 1050 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1050) = qv inp (.HB 14 3) from g461,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 3 1 (by decide) (by decide)]; rfl⟩
  | 14, 3, 2, _, _, _ => exact ⟨e (.n 1049), outCell_sound _ σ KTE 462 1049 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1049) = qv inp (.HB 14 3) from g462,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 3 2 (by decide) (by decide)]; rfl⟩
  | 14, 3, 3, _, _, _ => exact ⟨e (.n 1048), outCell_sound _ σ KTE 463 1048 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1048) = qv inp (.HB 14 3) from g463,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 3 3 (by decide) (by decide)]; rfl⟩
  | 14, 4, 0, _, _, _ => exact ⟨e (.n 1047), outCell_sound _ σ KTE 464 1047 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1047) = qv inp (.HB 14 4) from g464,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 4 0 (by decide) (by decide)]; rfl⟩
  | 14, 4, 1, _, _, _ => exact ⟨e (.n 1046), outCell_sound _ σ KTE 465 1046 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1046) = qv inp (.HB 14 4) from g465,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 4 1 (by decide) (by decide)]; rfl⟩
  | 14, 4, 2, _, _, _ => exact ⟨e (.n 1045), outCell_sound _ σ KTE 466 1045 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1045) = qv inp (.HB 14 4) from g466,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 4 2 (by decide) (by decide)]; rfl⟩
  | 14, 4, 3, _, _, _ => exact ⟨e (.n 1044), outCell_sound _ σ KTE 467 1044 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1044) = qv inp (.HB 14 4) from g467,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 4 3 (by decide) (by decide)]; rfl⟩
  | 14, 5, 0, _, _, _ => exact ⟨e (.n 1043), outCell_sound _ σ KTE 468 1043 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1043) = qv inp (.HB 14 5) from g468,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 5 0 (by decide) (by decide)]; rfl⟩
  | 14, 5, 1, _, _, _ => exact ⟨e (.n 1042), outCell_sound _ σ KTE 469 1042 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1042) = qv inp (.HB 14 5) from g469,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 5 1 (by decide) (by decide)]; rfl⟩
  | 14, 5, 2, _, _, _ => exact ⟨e (.n 1041), outCell_sound _ σ KTE 470 1041 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1041) = qv inp (.HB 14 5) from g470,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 5 2 (by decide) (by decide)]; rfl⟩
  | 14, 5, 3, _, _, _ => exact ⟨e (.n 1040), outCell_sound _ σ KTE 471 1040 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1040) = qv inp (.HB 14 5) from g471,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 5 3 (by decide) (by decide)]; rfl⟩
  | 14, 6, 0, _, _, _ => exact ⟨e (.n 1039), outCell_sound _ σ KTE 472 1039 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1039) = qv inp (.HB 14 6) from g472,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 6 0 (by decide) (by decide)]; rfl⟩
  | 14, 6, 1, _, _, _ => exact ⟨e (.n 1038), outCell_sound _ σ KTE 473 1038 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1038) = qv inp (.HB 14 6) from g473,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 6 1 (by decide) (by decide)]; rfl⟩
  | 14, 6, 2, _, _, _ => exact ⟨e (.n 1037), outCell_sound _ σ KTE 474 1037 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1037) = qv inp (.HB 14 6) from g474,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 6 2 (by decide) (by decide)]; rfl⟩
  | 14, 6, 3, _, _, _ => exact ⟨e (.n 1036), outCell_sound _ σ KTE 475 1036 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1036) = qv inp (.HB 14 6) from g475,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 6 3 (by decide) (by decide)]; rfl⟩
  | 14, 7, 0, _, _, _ => exact ⟨e (.n 1035), outCell_sound _ σ KTE 476 1035 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1035) = qv inp (.HB 14 7) from g476,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 14 7 0 (by decide) (by decide)]; rfl⟩
  | 14, 7, 1, _, _, _ => exact ⟨e (.n 1034), outCell_sound _ σ KTE 477 1034 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1034) = qv inp (.HB 14 7) from g477,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 14 7 1 (by decide) (by decide)]; rfl⟩
  | 14, 7, 2, _, _, _ => exact ⟨e (.n 1033), outCell_sound _ σ KTE 478 1033 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1033) = qv inp (.HB 14 7) from g478,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 14 7 2 (by decide) (by decide)]; rfl⟩
  | 14, 7, 3, _, _, _ => exact ⟨e (.n 1032), outCell_sound _ σ KTE 479 1032 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1032) = qv inp (.HB 14 7) from g479,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 14 7 3 (by decide) (by decide)]; rfl⟩
  | 15, 0, 0, _, _, _ => exact ⟨e (.n 1031), outCell_sound _ σ KTE 480 1031 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1031) = qv inp (.HB 15 0) from g480,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 0 0 (by decide) (by decide)]; rfl⟩
  | 15, 0, 1, _, _, _ => exact ⟨e (.n 1030), outCell_sound _ σ KTE 481 1030 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1030) = qv inp (.HB 15 0) from g481,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 0 1 (by decide) (by decide)]; rfl⟩
  | 15, 0, 2, _, _, _ => exact ⟨e (.n 1029), outCell_sound _ σ KTE 482 1029 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1029) = qv inp (.HB 15 0) from g482,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 0 2 (by decide) (by decide)]; rfl⟩
  | 15, 0, 3, _, _, _ => exact ⟨e (.n 1028), outCell_sound _ σ KTE 483 1028 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1028) = qv inp (.HB 15 0) from g483,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 0 3 (by decide) (by decide)]; rfl⟩
  | 15, 1, 0, _, _, _ => exact ⟨e (.n 1027), outCell_sound _ σ KTE 484 1027 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1027) = qv inp (.HB 15 1) from g484,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 1 0 (by decide) (by decide)]; rfl⟩
  | 15, 1, 1, _, _, _ => exact ⟨e (.n 1026), outCell_sound _ σ KTE 485 1026 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1026) = qv inp (.HB 15 1) from g485,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 1 1 (by decide) (by decide)]; rfl⟩
  | 15, 1, 2, _, _, _ => exact ⟨e (.n 1025), outCell_sound _ σ KTE 486 1025 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1025) = qv inp (.HB 15 1) from g486,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 1 2 (by decide) (by decide)]; rfl⟩
  | 15, 1, 3, _, _, _ => exact ⟨e (.n 1024), outCell_sound _ σ KTE 487 1024 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1024) = qv inp (.HB 15 1) from g487,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 1 3 (by decide) (by decide)]; rfl⟩
  | 15, 2, 0, _, _, _ => exact ⟨e (.n 1023), outCell_sound _ σ KTE 488 1023 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1023) = qv inp (.HB 15 2) from g488,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 2 0 (by decide) (by decide)]; rfl⟩
  | 15, 2, 1, _, _, _ => exact ⟨e (.n 1022), outCell_sound _ σ KTE 489 1022 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1022) = qv inp (.HB 15 2) from g489,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 2 1 (by decide) (by decide)]; rfl⟩
  | 15, 2, 2, _, _, _ => exact ⟨e (.n 1021), outCell_sound _ σ KTE 490 1021 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1021) = qv inp (.HB 15 2) from g490,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 2 2 (by decide) (by decide)]; rfl⟩
  | 15, 2, 3, _, _, _ => exact ⟨e (.n 1020), outCell_sound _ σ KTE 491 1020 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1020) = qv inp (.HB 15 2) from g491,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 2 3 (by decide) (by decide)]; rfl⟩
  | 15, 3, 0, _, _, _ => exact ⟨e (.n 1019), outCell_sound _ σ KTE 492 1019 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1019) = qv inp (.HB 15 3) from g492,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 3 0 (by decide) (by decide)]; rfl⟩
  | 15, 3, 1, _, _, _ => exact ⟨e (.n 1018), outCell_sound _ σ KTE 493 1018 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1018) = qv inp (.HB 15 3) from g493,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 3 1 (by decide) (by decide)]; rfl⟩
  | 15, 3, 2, _, _, _ => exact ⟨e (.n 1017), outCell_sound _ σ KTE 494 1017 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1017) = qv inp (.HB 15 3) from g494,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 3 2 (by decide) (by decide)]; rfl⟩
  | 15, 3, 3, _, _, _ => exact ⟨e (.n 1016), outCell_sound _ σ KTE 495 1016 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1016) = qv inp (.HB 15 3) from g495,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 3 3 (by decide) (by decide)]; rfl⟩
  | 15, 4, 0, _, _, _ => exact ⟨e (.n 1015), outCell_sound _ σ KTE 496 1015 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1015) = qv inp (.HB 15 4) from g496,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 4 0 (by decide) (by decide)]; rfl⟩
  | 15, 4, 1, _, _, _ => exact ⟨e (.n 1014), outCell_sound _ σ KTE 497 1014 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1014) = qv inp (.HB 15 4) from g497,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 4 1 (by decide) (by decide)]; rfl⟩
  | 15, 4, 2, _, _, _ => exact ⟨e (.n 1013), outCell_sound _ σ KTE 498 1013 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1013) = qv inp (.HB 15 4) from g498,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 4 2 (by decide) (by decide)]; rfl⟩
  | 15, 4, 3, _, _, _ => exact ⟨e (.n 1012), outCell_sound _ σ KTE 499 1012 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1012) = qv inp (.HB 15 4) from g499,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 4 3 (by decide) (by decide)]; rfl⟩
  | 15, 5, 0, _, _, _ => exact ⟨e (.n 1011), outCell_sound _ σ KTE 500 1011 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1011) = qv inp (.HB 15 5) from g500,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 5 0 (by decide) (by decide)]; rfl⟩
  | 15, 5, 1, _, _, _ => exact ⟨e (.n 1010), outCell_sound _ σ KTE 501 1010 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1010) = qv inp (.HB 15 5) from g501,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 5 1 (by decide) (by decide)]; rfl⟩
  | 15, 5, 2, _, _, _ => exact ⟨e (.n 1009), outCell_sound _ σ KTE 502 1009 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1009) = qv inp (.HB 15 5) from g502,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 5 2 (by decide) (by decide)]; rfl⟩
  | 15, 5, 3, _, _, _ => exact ⟨e (.n 1008), outCell_sound _ σ KTE 503 1008 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1008) = qv inp (.HB 15 5) from g503,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 5 3 (by decide) (by decide)]; rfl⟩
  | 15, 6, 0, _, _, _ => exact ⟨e (.n 1007), outCell_sound _ σ KTE 504 1007 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1007) = qv inp (.HB 15 6) from g504,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 6 0 (by decide) (by decide)]; rfl⟩
  | 15, 6, 1, _, _, _ => exact ⟨e (.n 1006), outCell_sound _ σ KTE 505 1006 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1006) = qv inp (.HB 15 6) from g505,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 6 1 (by decide) (by decide)]; rfl⟩
  | 15, 6, 2, _, _, _ => exact ⟨e (.n 1005), outCell_sound _ σ KTE 506 1005 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1005) = qv inp (.HB 15 6) from g506,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 6 2 (by decide) (by decide)]; rfl⟩
  | 15, 6, 3, _, _, _ => exact ⟨e (.n 1004), outCell_sound _ σ KTE 507 1004 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1004) = qv inp (.HB 15 6) from g507,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 6 3 (by decide) (by decide)]; rfl⟩
  | 15, 7, 0, _, _, _ => exact ⟨e (.n 1003), outCell_sound _ σ KTE 508 1003 0 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1003) = qv inp (.HB 15 7) from g508,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 15 7 0 (by decide) (by decide)]; rfl⟩
  | 15, 7, 1, _, _, _ => exact ⟨e (.n 1002), outCell_sound _ σ KTE 509 1002 1 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1002) = qv inp (.HB 15 7) from g509,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 15 7 1 (by decide) (by decide)]; rfl⟩
  | 15, 7, 2, _, _, _ => exact ⟨e (.n 1001), outCell_sound _ σ KTE 510 1001 2 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1001) = qv inp (.HB 15 7) from g510,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 15 7 2 (by decide) (by decide)]; rfl⟩
  | 15, 7, 3, _, _, _ => exact ⟨e (.n 1000), outCell_sound _ σ KTE 511 1000 3 (KTE_cell _ _ _ (by decide)),
      by rw [show e (.n 1000) = qv inp (.HB 15 7) from g511,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 15 7 3 (by decide) (by decide)]; rfl⟩
  | _ + 16, _, _, hn, _, _ => omega
  | _, _ + 8, _, _, hi, _ => omega
  | _, _, _ + 4, _, _, hb => omega

end Hashtree.Proofs.Avx512X16WOut
