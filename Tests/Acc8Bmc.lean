import Loom
import Machines.Acc8.Core

/-!
# First certificate-checked BMC result on Acc8 (task 1.2 deliverable)

We bit-blast (`Loom/Dp/Cnf.lean`) the one-cycle transition relation of the
compiled Acc8 core into a `CNF Nat`, unroll it for bounded model checking
(`Loom/Dp/Bmc.lean`), and check an UNSAT certificate — produced offline by
`cadical --no-binary --lrat` and translated to `Check.Step` form by
`scripts/lrat_to_step.py` (both untrusted) — with the in-house
kernel-reducible RUP/LRAT checker (`Loom/Dp/Cert/Check.lean`, `by decide`).

**Property.** `stickyP s := ¬s.halted ∨ haltedNext(s)` where `haltedNext`
is the compiler-produced next-value expression for the `halted` register.
"Once `halted` is set it stays set": a genuine structural safety property of
Acc8, and a tautology of the register's `mux(halted, halted, …)` tree — so
it survives the encoding's arithmetic/`memRead` over-approximation (the
inner opcode comparators are free variables and never matter).

`acc8_bmc_holds` is the payoff: a **real, kernel-checked** theorem that the
property holds at every state Acc8 reaches within the bound, obtained from
`Bmc.bmc_sound` + `Check.check_sound` — no `sorry`, no `native_decide`, no
new axioms. The certificate has 260 RUP steps over a 1328-clause, 328-var
formula; the kernel `decide` re-check runs in ≈ 32 s.
-/

namespace Tests.Acc8Bmc

open Loom.Dp.Bmc Loom.Dp.Cnf Loom.Emit.MicroVerilog Loom.Dp.Cert Std.Sat

set_option maxRecDepth 8000

/-- The compiled Acc8 core (the program image is irrelevant: `memRead` is
over-approximated, so the certificate holds for every ROM contents). -/
def acc8 : Module := Loom.Hw.Compile.compile (Machines.Acc8.Core.design (fun _ => 0#16))

/-- The compiler's next-value expression for the `halted` register. -/
def haltedNext : Expr 1 :=
  match acc8.regs.find? (fun r => r.name == "halted") with
  | some r => if h : r.width = 1 then h ▸ r.next else .lit 0#1
  | none => .lit 0#1

/-- "`halted` is sticky": `halted → haltedNext`. -/
def stickyP : Expr 1 := .or (.not (.reg 1 "halted")) haltedNext

def acc8Cert : List Check.Step := [
  .add [(77, true), (79, true), (95, false)] [0, 17],
  .add [(77, true), (79, false), (95, false)] [1, 20],
  .add [(77, false), (79, true), (95, false)] [2, 23],
  .add [(77, false), (79, false), (95, true)] [3, 26],
  .add [(77, true), (81, true), (97, false)] [5, 29],
  .add [(77, true), (81, false), (97, false)] [6, 32],
  .add [(77, false), (81, true), (97, false)] [7, 35],
  .add [(77, false), (81, false), (97, true)] [8, 38],
  .add [(77, true), (83, true), (99, false)] [10, 41],
  .add [(77, true), (83, false), (99, false)] [11, 44],
  .add [(77, false), (83, true), (99, false)] [12, 47],
  .add [(77, false), (83, false), (99, true)] [13, 50],
  .add [(77, true), (85, true), (101, false)] [15, 53],
  .add [(77, true), (85, false), (101, false)] [16, 56],
  .add [(77, false), (85, true), (101, false)] [17, 59],
  .add [(77, false), (85, false), (101, true)] [18, 62],
  .add [(77, true), (87, true), (103, false)] [20, 65],
  .add [(77, true), (87, false), (103, false)] [21, 68],
  .add [(77, false), (87, true), (103, false)] [22, 71],
  .add [(77, false), (87, false), (103, true)] [23, 74],
  .add [(77, true), (89, true), (105, false)] [25, 77],
  .add [(77, true), (89, false), (105, false)] [26, 80],
  .add [(77, false), (89, true), (105, false)] [27, 83],
  .add [(77, false), (89, false), (105, true)] [28, 86],
  .add [(77, true), (91, true), (107, false)] [30, 89],
  .add [(77, true), (91, false), (107, false)] [31, 92],
  .add [(77, false), (91, true), (107, false)] [32, 95],
  .add [(77, false), (91, false), (107, true)] [33, 98],
  .add [(77, true), (93, true), (109, false)] [35, 101],
  .add [(77, true), (93, false), (109, false)] [36, 104],
  .add [(77, false), (93, true), (109, false)] [37, 107],
  .add [(77, false), (93, false), (109, true)] [38, 110],
  .add [(75, true), (95, true), (111, false)] [32, 113],
  .add [(75, true), (95, false), (111, true)] [33, 115],
  .add [(75, false), (95, true), (111, false)] [34, 119],
  .add [(75, false), (95, false), (111, false)] [35, 121],
  .add [(75, true), (97, true), (113, false)] [37, 125],
  .add [(75, true), (97, false), (113, true)] [38, 127],
  .add [(75, false), (97, true), (113, false)] [39, 131],
  .add [(75, false), (97, false), (113, false)] [40, 133],
  .add [(75, true), (99, true), (115, false)] [42, 137],
  .add [(75, true), (99, false), (115, true)] [43, 139],
  .add [(75, false), (99, true), (115, false)] [44, 143],
  .add [(75, false), (99, false), (115, false)] [45, 145],
  .add [(75, true), (101, true), (117, false)] [47, 149],
  .add [(75, true), (101, false), (117, true)] [48, 151],
  .add [(75, false), (101, true), (117, false)] [49, 155],
  .add [(75, false), (101, false), (117, false)] [50, 157],
  .add [(75, true), (103, true), (119, false)] [52, 161],
  .add [(75, true), (103, false), (119, true)] [53, 163],
  .add [(75, false), (103, true), (119, false)] [54, 167],
  .add [(75, false), (103, false), (119, false)] [55, 169],
  .add [(75, true), (105, true), (121, false)] [57, 173],
  .add [(75, true), (105, false), (121, true)] [58, 175],
  .add [(75, false), (105, true), (121, false)] [59, 179],
  .add [(75, false), (105, false), (121, false)] [60, 181],
  .add [(75, true), (107, true), (123, false)] [62, 185],
  .add [(75, true), (107, false), (123, true)] [63, 187],
  .add [(75, false), (107, true), (123, false)] [64, 191],
  .add [(75, false), (107, false), (123, false)] [65, 193],
  .add [(75, true), (109, true), (125, false)] [67, 197],
  .add [(75, true), (109, false), (125, true)] [68, 199],
  .add [(75, false), (109, true), (125, false)] [69, 203],
  .add [(75, false), (109, false), (125, false)] [70, 205],
  .add [(73, true), (111, true), (127, false)] [64, 209],
  .add [(73, true), (111, false), (127, true)] [65, 211],
  .add [(73, false), (111, true), (127, false)] [66, 215],
  .add [(73, false), (111, false), (127, false)] [67, 217],
  .add [(73, true), (113, true), (129, false)] [69, 221],
  .add [(73, true), (113, false), (129, true)] [70, 223],
  .add [(73, false), (113, true), (129, false)] [71, 227],
  .add [(73, false), (113, false), (129, false)] [72, 229],
  .add [(73, true), (115, true), (131, false)] [74, 233],
  .add [(73, true), (115, false), (131, true)] [75, 235],
  .add [(73, false), (115, true), (131, false)] [76, 239],
  .add [(73, false), (115, false), (131, false)] [77, 241],
  .add [(73, true), (117, true), (133, false)] [79, 245],
  .add [(73, true), (117, false), (133, true)] [80, 247],
  .add [(73, false), (117, true), (133, false)] [81, 251],
  .add [(73, false), (117, false), (133, false)] [82, 253],
  .add [(73, true), (119, true), (135, false)] [84, 257],
  .add [(73, true), (119, false), (135, true)] [85, 259],
  .add [(73, false), (119, true), (135, false)] [86, 263],
  .add [(73, false), (119, false), (135, false)] [87, 265],
  .add [(73, true), (121, true), (137, false)] [89, 269],
  .add [(73, true), (121, false), (137, true)] [90, 271],
  .add [(73, false), (121, true), (137, false)] [91, 275],
  .add [(73, false), (121, false), (137, false)] [92, 277],
  .add [(73, true), (123, true), (139, false)] [94, 281],
  .add [(73, true), (123, false), (139, true)] [95, 283],
  .add [(73, false), (123, true), (139, false)] [96, 287],
  .add [(73, false), (123, false), (139, false)] [97, 289],
  .add [(73, true), (125, true), (141, false)] [99, 293],
  .add [(73, true), (125, false), (141, true)] [100, 295],
  .add [(73, false), (125, true), (141, false)] [101, 299],
  .add [(73, false), (125, false), (141, false)] [102, 301],
  .add [(1, true), (175, true), (191, false)] [96, 497],
  .add [(1, true), (175, false), (191, true)] [97, 499],
  .add [(1, false), (175, true), (191, false)] [98, 503],
  .add [(1, false), (175, false), (191, false)] [99, 505],
  .add [(1, true), (177, true), (193, false)] [101, 509],
  .add [(1, true), (177, false), (193, true)] [102, 511],
  .add [(1, false), (177, true), (193, false)] [103, 515],
  .add [(1, false), (177, false), (193, false)] [104, 517],
  .add [(1, true), (179, true), (195, false)] [106, 521],
  .add [(1, true), (179, false), (195, true)] [107, 523],
  .add [(1, false), (179, true), (195, false)] [108, 527],
  .add [(1, false), (179, false), (195, false)] [109, 529],
  .add [(1, true), (181, true), (197, false)] [111, 533],
  .add [(1, true), (181, false), (197, true)] [112, 535],
  .add [(1, false), (181, true), (197, false)] [113, 539],
  .add [(1, false), (181, false), (197, false)] [114, 541],
  .add [(1, true), (183, true), (199, false)] [116, 545],
  .add [(1, true), (183, false), (199, true)] [117, 547],
  .add [(1, false), (183, true), (199, false)] [118, 551],
  .add [(1, false), (183, false), (199, false)] [119, 553],
  .add [(1, true), (185, true), (201, false)] [121, 557],
  .add [(1, true), (185, false), (201, true)] [122, 559],
  .add [(1, false), (185, true), (201, false)] [123, 563],
  .add [(1, false), (185, false), (201, false)] [124, 565],
  .add [(1, true), (187, true), (203, false)] [126, 569],
  .add [(1, true), (187, false), (203, true)] [127, 571],
  .add [(1, false), (187, true), (203, false)] [128, 575],
  .add [(1, false), (187, false), (203, false)] [129, 577],
  .add [(1, true), (189, true), (205, false)] [131, 581],
  .add [(1, true), (189, false), (205, true)] [132, 583],
  .add [(1, false), (189, true), (205, false)] [133, 587],
  .add [(1, false), (189, false), (205, false)] [134, 589],
  .add [(191, true), (207, false)] [144, 128, 593],
  .add [(191, false), (207, true)] [145, 129, 595],
  .add [(193, true), (209, false)] [146, 131, 603],
  .add [(193, false), (209, true)] [147, 132, 605],
  .add [(195, true), (211, false)] [148, 134, 613],
  .add [(195, false), (211, true)] [149, 135, 615],
  .add [(197, true), (213, false)] [150, 137, 623],
  .add [(197, false), (213, true)] [151, 138, 625],
  .add [(199, true), (215, false)] [152, 140, 633],
  .add [(199, false), (215, true)] [153, 141, 635],
  .add [(201, true), (217, false)] [154, 143, 643],
  .add [(201, false), (217, true)] [155, 144, 645],
  .add [(203, true), (219, false)] [156, 146, 653],
  .add [(203, false), (219, true)] [157, 147, 655],
  .add [(205, true), (221, false)] [158, 149, 663],
  .add [(205, false), (221, true)] [159, 150, 665],
  .add [(381, true), (383, true), (399, false)] [152, 753],
  .add [(381, true), (383, false), (399, false)] [153, 756],
  .add [(381, false), (383, true), (399, false)] [154, 759],
  .add [(381, false), (383, false), (399, true)] [155, 762],
  .add [(381, true), (385, true), (401, false)] [157, 765],
  .add [(381, true), (385, false), (401, false)] [158, 768],
  .add [(381, false), (385, true), (401, false)] [159, 771],
  .add [(381, false), (385, false), (401, true)] [160, 774],
  .add [(381, true), (387, true), (403, false)] [162, 777],
  .add [(381, true), (387, false), (403, false)] [163, 780],
  .add [(381, false), (387, true), (403, false)] [164, 783],
  .add [(381, false), (387, false), (403, true)] [165, 786],
  .add [(381, true), (389, true), (405, false)] [167, 789],
  .add [(381, true), (389, false), (405, false)] [168, 792],
  .add [(381, false), (389, true), (405, false)] [169, 795],
  .add [(381, false), (389, false), (405, true)] [170, 798],
  .add [(381, true), (391, true), (407, false)] [172, 801],
  .add [(381, true), (391, false), (407, false)] [173, 804],
  .add [(381, false), (391, true), (407, false)] [174, 807],
  .add [(381, false), (391, false), (407, true)] [175, 810],
  .add [(381, true), (393, true), (409, false)] [177, 813],
  .add [(381, true), (393, false), (409, false)] [178, 816],
  .add [(381, false), (393, true), (409, false)] [179, 819],
  .add [(381, false), (393, false), (409, true)] [180, 822],
  .add [(381, true), (395, true), (411, false)] [182, 825],
  .add [(381, true), (395, false), (411, false)] [183, 828],
  .add [(381, false), (395, true), (411, false)] [184, 831],
  .add [(381, false), (395, false), (411, true)] [185, 834],
  .add [(381, true), (397, true), (413, false)] [187, 837],
  .add [(381, true), (397, false), (413, false)] [188, 840],
  .add [(381, false), (397, true), (413, false)] [189, 843],
  .add [(381, false), (397, false), (413, true)] [190, 846],
  .add [(495, true), (511, false)] [192, 184, 1233],
  .add [(495, false), (511, true)] [193, 185, 1235],
  .add [(497, true), (513, false)] [194, 187, 1243],
  .add [(497, false), (513, true)] [195, 188, 1245],
  .add [(499, true), (515, false)] [196, 190, 1253],
  .add [(499, false), (515, true)] [197, 191, 1255],
  .add [(501, true), (517, false)] [198, 193, 1263],
  .add [(501, false), (517, true)] [199, 194, 1265],
  .add [(503, true), (519, false)] [200, 196, 1273],
  .add [(503, false), (519, true)] [201, 197, 1275],
  .add [(505, true), (521, false)] [202, 199, 1283],
  .add [(505, false), (521, true)] [203, 200, 1285],
  .add [(507, true), (523, false)] [204, 202, 1293],
  .add [(507, false), (523, true)] [205, 203, 1295],
  .add [(509, true), (525, false)] [206, 205, 1303],
  .add [(509, false), (525, true)] [207, 206, 1305],
  .add [(539, true), (541, true)] [208, 1329],
  .add [(539, false), (541, false)] [209, 1332],
  .add [(537, true), (541, true), (543, false)] [210, 1335],
  .add [(537, true), (541, false), (543, true)] [211, 1337],
  .add [(537, false), (541, true), (543, false)] [212, 1341],
  .add [(537, false), (541, false), (543, false)] [213, 1343],
  .add [(535, true), (543, true), (545, false)] [214, 1347],
  .add [(535, true), (543, false), (545, true)] [215, 1349],
  .add [(535, false), (543, true), (545, false)] [216, 1353],
  .add [(535, false), (543, false), (545, false)] [217, 1355],
  .add [(533, true), (545, true), (547, false)] [218, 1359],
  .add [(533, true), (545, false), (547, true)] [219, 1361],
  .add [(533, false), (545, true), (547, false)] [220, 1365],
  .add [(533, false), (545, false), (547, false)] [221, 1367],
  .add [(531, true), (547, true), (549, false)] [222, 1371],
  .add [(531, true), (547, false), (549, true)] [223, 1373],
  .add [(531, false), (547, true), (549, false)] [224, 1377],
  .add [(531, false), (547, false), (549, false)] [225, 1379],
  .add [(529, true), (549, true), (551, false)] [226, 1383],
  .add [(529, true), (549, false), (551, true)] [227, 1385],
  .add [(529, false), (549, true), (551, false)] [228, 1389],
  .add [(529, false), (549, false), (551, false)] [229, 1391],
  .add [(527, true), (551, true), (553, false)] [230, 1395],
  .add [(527, true), (551, false), (553, true)] [231, 1397],
  .add [(527, false), (551, true), (553, false)] [232, 1401],
  .add [(527, false), (551, false), (553, false)] [233, 1403],
  .add [(553, true), (555, false)] [234, 1407],
  .add [(553, false), (555, true)] [235, 1409],
  .add [(569, true), (571, true)] [236, 1419],
  .add [(569, false), (571, false)] [237, 1422],
  .add [(567, true), (571, true), (573, false)] [238, 1425],
  .add [(567, true), (571, false), (573, true)] [239, 1427],
  .add [(567, false), (571, true), (573, false)] [240, 1431],
  .add [(567, false), (571, false), (573, false)] [241, 1433],
  .add [(565, true), (573, true), (575, false)] [242, 1437],
  .add [(565, true), (573, false), (575, true)] [243, 1439],
  .add [(565, false), (573, true), (575, false)] [244, 1443],
  .add [(565, false), (573, false), (575, false)] [245, 1445],
  .add [(563, true), (575, true), (577, false)] [246, 1449],
  .add [(563, true), (575, false), (577, true)] [247, 1451],
  .add [(563, false), (575, true), (577, false)] [248, 1455],
  .add [(563, false), (575, false), (577, false)] [249, 1457],
  .add [(561, true), (577, true), (579, false)] [250, 1461],
  .add [(561, true), (577, false), (579, true)] [251, 1463],
  .add [(561, false), (577, true), (579, false)] [252, 1467],
  .add [(561, false), (577, false), (579, false)] [253, 1469],
  .add [(559, true), (579, true), (581, false)] [254, 1473],
  .add [(559, true), (579, false), (581, true)] [255, 1475],
  .add [(559, false), (579, true), (581, false)] [256, 1479],
  .add [(559, false), (579, false), (581, false)] [257, 1481],
  .add [(557, true), (581, true), (583, false)] [258, 1485],
  .add [(557, true), (581, false), (583, true)] [259, 1487],
  .add [(557, false), (581, true), (583, false)] [260, 1491],
  .add [(557, false), (581, false), (583, false)] [261, 1493],
  .add [(583, true), (585, false)] [262, 1497],
  .add [(583, false), (585, true)] [263, 1499],
  .add [(585, true), (587, true)] [264, 1509],
  .add [(585, false), (587, true)] [265, 1511],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true), (615, true), (617, false)] [1565],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true), (615, false), (617, true)] [1567],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, false), (615, true), (617, true)] [1573],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, false), (615, false), (617, true)] [1575],
  .add [(587, true)] [5, 4],
  .add [(619, false)] [0, 1582],
  .add [(617, false)] [0, 1580, 1582],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true)] [0, 1, 1582],
  .add [(615, true)] [1, 0, 5],
  .add [] [0, 2, 1, 5]
]


/-- The register names of the compiled core are distinct (the BMC
soundness discipline). -/
theorem acc8_nodup : (acc8.regs.map (·.name)).Nodup := by decide

/-- The kernel re-checks the certificate: `bmcCnf acc8 stickyP 1` is UNSAT. -/
theorem acc8_cert_ok : Check.check (bmcCnf acc8 stickyP 1) acc8Cert = true := by decide

/-- **First certificate-checked BMC result on Acc8.** The sticky-`halted`
property holds at every state reachable within one cycle from reset — a real
theorem, kernel-backed via `Bmc.bmc_sound`. -/
theorem acc8_bmc_holds :
    ∀ j, j ≤ 1 → stickyP.eval (acc8.run j acc8.reset) = 1#1 :=
  bmc_sound acc8 stickyP 1 acc8_nodup acc8Cert acc8_cert_ok

end Tests.Acc8Bmc
