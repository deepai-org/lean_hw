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
new axioms. The certificate has 244 RUP steps over a 1416-clause, 343-var
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
  .add [(77, true), (79, false)] [0, 17],
  .add [(77, false), (79, false)] [1, 22],
  .add [(77, true), (81, false)] [3, 27],
  .add [(77, false), (81, false)] [4, 32],
  .add [(77, true), (83, false)] [6, 37],
  .add [(77, false), (83, false)] [7, 42],
  .add [(77, true), (85, false)] [9, 47],
  .add [(77, false), (85, false)] [10, 52],
  .add [(77, true), (87, false)] [12, 57],
  .add [(77, false), (87, false)] [13, 62],
  .add [(77, true), (89, false)] [15, 67],
  .add [(77, false), (89, false)] [16, 72],
  .add [(77, true), (91, false)] [18, 77],
  .add [(77, false), (91, false)] [19, 82],
  .add [(77, true), (93, false)] [21, 87],
  .add [(77, false), (93, false)] [22, 92],
  .add [(95, true), (97, true), (113, false)] [16, 97],
  .add [(95, true), (97, false), (113, false)] [17, 100],
  .add [(95, false), (97, true), (113, false)] [18, 103],
  .add [(95, false), (97, false), (113, true)] [19, 106],
  .add [(95, true), (99, true), (115, false)] [21, 109],
  .add [(95, true), (99, false), (115, false)] [22, 112],
  .add [(95, false), (99, true), (115, false)] [23, 115],
  .add [(95, false), (99, false), (115, true)] [24, 118],
  .add [(95, true), (101, true), (117, false)] [26, 121],
  .add [(95, true), (101, false), (117, false)] [27, 124],
  .add [(95, false), (101, true), (117, false)] [28, 127],
  .add [(95, false), (101, false), (117, true)] [29, 130],
  .add [(95, true), (103, true), (119, false)] [31, 133],
  .add [(95, true), (103, false), (119, false)] [32, 136],
  .add [(95, false), (103, true), (119, false)] [33, 139],
  .add [(95, false), (103, false), (119, true)] [34, 142],
  .add [(95, true), (105, true), (121, false)] [36, 145],
  .add [(95, true), (105, false), (121, false)] [37, 148],
  .add [(95, false), (105, true), (121, false)] [38, 151],
  .add [(95, false), (105, false), (121, true)] [39, 154],
  .add [(95, true), (107, true), (123, false)] [41, 157],
  .add [(95, true), (107, false), (123, false)] [42, 160],
  .add [(95, false), (107, true), (123, false)] [43, 163],
  .add [(95, false), (107, false), (123, true)] [44, 166],
  .add [(95, true), (109, true), (125, false)] [46, 169],
  .add [(95, true), (109, false), (125, false)] [47, 172],
  .add [(95, false), (109, true), (125, false)] [48, 175],
  .add [(95, false), (109, false), (125, true)] [49, 178],
  .add [(95, true), (111, true), (127, false)] [51, 181],
  .add [(95, true), (111, false), (127, false)] [52, 184],
  .add [(95, false), (111, true), (127, false)] [53, 187],
  .add [(95, false), (111, false), (127, true)] [54, 190],
  .add [(73, true), (129, true), (145, false)] [48, 257],
  .add [(73, true), (129, false), (145, true)] [49, 259],
  .add [(73, false), (129, true), (145, false)] [50, 263],
  .add [(73, false), (129, false), (145, false)] [51, 265],
  .add [(73, true), (131, true), (147, false)] [53, 269],
  .add [(73, true), (131, false), (147, true)] [54, 271],
  .add [(73, false), (131, true), (147, false)] [55, 275],
  .add [(73, false), (131, false), (147, false)] [56, 277],
  .add [(73, true), (133, true), (149, false)] [58, 281],
  .add [(73, true), (133, false), (149, true)] [59, 283],
  .add [(73, false), (133, true), (149, false)] [60, 287],
  .add [(73, false), (133, false), (149, false)] [61, 289],
  .add [(73, true), (135, true), (151, false)] [63, 293],
  .add [(73, true), (135, false), (151, true)] [64, 295],
  .add [(73, false), (135, true), (151, false)] [65, 299],
  .add [(73, false), (135, false), (151, false)] [66, 301],
  .add [(73, true), (137, true), (153, false)] [68, 305],
  .add [(73, true), (137, false), (153, true)] [69, 307],
  .add [(73, false), (137, true), (153, false)] [70, 311],
  .add [(73, false), (137, false), (153, false)] [71, 313],
  .add [(73, true), (139, true), (155, false)] [73, 317],
  .add [(73, true), (139, false), (155, true)] [74, 319],
  .add [(73, false), (139, true), (155, false)] [75, 323],
  .add [(73, false), (139, false), (155, false)] [76, 325],
  .add [(73, true), (141, true), (157, false)] [78, 329],
  .add [(73, true), (141, false), (157, true)] [79, 331],
  .add [(73, false), (141, true), (157, false)] [80, 335],
  .add [(73, false), (141, false), (157, false)] [81, 337],
  .add [(73, true), (143, true), (159, false)] [83, 341],
  .add [(73, true), (143, false), (159, true)] [84, 343],
  .add [(73, false), (143, true), (159, false)] [85, 347],
  .add [(73, false), (143, false), (159, false)] [86, 349],
  .add [(1, true), (193, true), (209, false)] [80, 545],
  .add [(1, true), (193, false), (209, true)] [81, 547],
  .add [(1, false), (193, true), (209, false)] [82, 551],
  .add [(1, false), (193, false), (209, false)] [83, 553],
  .add [(1, true), (195, true), (211, false)] [85, 557],
  .add [(1, true), (195, false), (211, true)] [86, 559],
  .add [(1, false), (195, true), (211, false)] [87, 563],
  .add [(1, false), (195, false), (211, false)] [88, 565],
  .add [(1, true), (197, true), (213, false)] [90, 569],
  .add [(1, true), (197, false), (213, true)] [91, 571],
  .add [(1, false), (197, true), (213, false)] [92, 575],
  .add [(1, false), (197, false), (213, false)] [93, 577],
  .add [(1, true), (199, true), (215, false)] [95, 581],
  .add [(1, true), (199, false), (215, true)] [96, 583],
  .add [(1, false), (199, true), (215, false)] [97, 587],
  .add [(1, false), (199, false), (215, false)] [98, 589],
  .add [(1, true), (201, true), (217, false)] [100, 593],
  .add [(1, true), (201, false), (217, true)] [101, 595],
  .add [(1, false), (201, true), (217, false)] [102, 599],
  .add [(1, false), (201, false), (217, false)] [103, 601],
  .add [(1, true), (203, true), (219, false)] [105, 605],
  .add [(1, true), (203, false), (219, true)] [106, 607],
  .add [(1, false), (203, true), (219, false)] [107, 611],
  .add [(1, false), (203, false), (219, false)] [108, 613],
  .add [(1, true), (205, true), (221, false)] [110, 617],
  .add [(1, true), (205, false), (221, true)] [111, 619],
  .add [(1, false), (205, true), (221, false)] [112, 623],
  .add [(1, false), (205, false), (221, false)] [113, 625],
  .add [(1, true), (207, true), (223, false)] [115, 629],
  .add [(1, true), (207, false), (223, true)] [116, 631],
  .add [(1, false), (207, true), (223, false)] [117, 635],
  .add [(1, false), (207, false), (223, false)] [118, 637],
  .add [(209, true), (225, false)] [128, 112, 641],
  .add [(209, false), (225, true)] [129, 113, 643],
  .add [(211, true), (227, false)] [130, 115, 651],
  .add [(211, false), (227, true)] [131, 116, 653],
  .add [(213, true), (229, false)] [132, 118, 661],
  .add [(213, false), (229, true)] [133, 119, 663],
  .add [(215, true), (231, false)] [134, 121, 671],
  .add [(215, false), (231, true)] [135, 122, 673],
  .add [(217, true), (233, false)] [136, 124, 681],
  .add [(217, false), (233, true)] [137, 125, 683],
  .add [(219, true), (235, false)] [138, 127, 691],
  .add [(219, false), (235, true)] [139, 128, 693],
  .add [(221, true), (237, false)] [140, 130, 701],
  .add [(221, false), (237, true)] [141, 131, 703],
  .add [(223, true), (239, false)] [142, 133, 711],
  .add [(223, false), (239, true)] [143, 134, 713],
  .add [(399, true), (401, true), (417, false)] [136, 801],
  .add [(399, true), (401, false), (417, false)] [137, 804],
  .add [(399, false), (401, true), (417, false)] [138, 807],
  .add [(399, false), (401, false), (417, true)] [139, 810],
  .add [(399, true), (403, true), (419, false)] [141, 813],
  .add [(399, true), (403, false), (419, false)] [142, 816],
  .add [(399, false), (403, true), (419, false)] [143, 819],
  .add [(399, false), (403, false), (419, true)] [144, 822],
  .add [(399, true), (405, true), (421, false)] [146, 825],
  .add [(399, true), (405, false), (421, false)] [147, 828],
  .add [(399, false), (405, true), (421, false)] [148, 831],
  .add [(399, false), (405, false), (421, true)] [149, 834],
  .add [(399, true), (407, true), (423, false)] [151, 837],
  .add [(399, true), (407, false), (423, false)] [152, 840],
  .add [(399, false), (407, true), (423, false)] [153, 843],
  .add [(399, false), (407, false), (423, true)] [154, 846],
  .add [(399, true), (409, true), (425, false)] [156, 849],
  .add [(399, true), (409, false), (425, false)] [157, 852],
  .add [(399, false), (409, true), (425, false)] [158, 855],
  .add [(399, false), (409, false), (425, true)] [159, 858],
  .add [(399, true), (411, true), (427, false)] [161, 861],
  .add [(399, true), (411, false), (427, false)] [162, 864],
  .add [(399, false), (411, true), (427, false)] [163, 867],
  .add [(399, false), (411, false), (427, true)] [164, 870],
  .add [(399, true), (413, true), (429, false)] [166, 873],
  .add [(399, true), (413, false), (429, false)] [167, 876],
  .add [(399, false), (413, true), (429, false)] [168, 879],
  .add [(399, false), (413, false), (429, true)] [169, 882],
  .add [(399, true), (415, true), (431, false)] [171, 885],
  .add [(399, true), (415, false), (431, false)] [172, 888],
  .add [(399, false), (415, true), (431, false)] [173, 891],
  .add [(399, false), (415, false), (431, true)] [174, 894],
  .add [(513, true), (529, false)] [176, 168, 1281],
  .add [(513, false), (529, true)] [177, 169, 1283],
  .add [(515, true), (531, false)] [178, 171, 1291],
  .add [(515, false), (531, true)] [179, 172, 1293],
  .add [(517, true), (533, false)] [180, 174, 1301],
  .add [(517, false), (533, true)] [181, 175, 1303],
  .add [(519, true), (535, false)] [182, 177, 1311],
  .add [(519, false), (535, true)] [183, 178, 1313],
  .add [(521, true), (537, false)] [184, 180, 1321],
  .add [(521, false), (537, true)] [185, 181, 1323],
  .add [(523, true), (539, false)] [186, 183, 1331],
  .add [(523, false), (539, true)] [187, 184, 1333],
  .add [(525, true), (541, false)] [188, 186, 1341],
  .add [(525, false), (541, true)] [189, 187, 1343],
  .add [(527, true), (543, false)] [190, 189, 1351],
  .add [(527, false), (543, true)] [191, 190, 1353],
  .add [(557, true), (559, false)] [192, 1377],
  .add [(557, false), (559, false)] [193, 1382],
  .add [(561, true), (563, true)] [194, 1387],
  .add [(561, false), (563, false)] [195, 1390],
  .add [(553, true), (565, true), (567, false)] [196, 1401],
  .add [(553, true), (565, false), (567, true)] [197, 1403],
  .add [(553, false), (565, true), (567, false)] [198, 1407],
  .add [(553, false), (565, false), (567, false)] [199, 1409],
  .add [(551, true), (567, true), (569, false)] [200, 1413],
  .add [(551, true), (567, false), (569, true)] [201, 1415],
  .add [(551, false), (567, true), (569, false)] [202, 1419],
  .add [(551, false), (567, false), (569, false)] [203, 1421],
  .add [(549, true), (569, true), (571, false)] [204, 1425],
  .add [(549, true), (569, false), (571, true)] [205, 1427],
  .add [(549, false), (569, true), (571, false)] [206, 1431],
  .add [(549, false), (569, false), (571, false)] [207, 1433],
  .add [(547, true), (571, true), (573, false)] [208, 1437],
  .add [(547, true), (571, false), (573, true)] [209, 1439],
  .add [(547, false), (571, true), (573, false)] [210, 1443],
  .add [(547, false), (571, false), (573, false)] [211, 1445],
  .add [(545, true), (573, true), (575, false)] [212, 1449],
  .add [(545, true), (573, false), (575, true)] [213, 1451],
  .add [(545, false), (573, true), (575, false)] [214, 1455],
  .add [(545, false), (573, false), (575, false)] [215, 1457],
  .add [(575, true), (577, false)] [216, 1461],
  .add [(575, false), (577, true)] [217, 1463],
  .add [(591, true), (593, false)] [218, 1473],
  .add [(591, false), (593, false)] [219, 1478],
  .add [(595, true), (597, true)] [220, 1483],
  .add [(595, false), (597, false)] [221, 1486],
  .add [(587, true), (599, true), (601, false)] [222, 1497],
  .add [(587, true), (599, false), (601, true)] [223, 1499],
  .add [(587, false), (599, true), (601, false)] [224, 1503],
  .add [(587, false), (599, false), (601, false)] [225, 1505],
  .add [(585, true), (601, true), (603, false)] [226, 1509],
  .add [(585, true), (601, false), (603, true)] [227, 1511],
  .add [(585, false), (601, true), (603, false)] [228, 1515],
  .add [(585, false), (601, false), (603, false)] [229, 1517],
  .add [(583, true), (603, true), (605, false)] [230, 1521],
  .add [(583, true), (603, false), (605, true)] [231, 1523],
  .add [(583, false), (603, true), (605, false)] [232, 1527],
  .add [(583, false), (603, false), (605, false)] [233, 1529],
  .add [(581, true), (605, true), (607, false)] [234, 1533],
  .add [(581, true), (605, false), (607, true)] [235, 1535],
  .add [(581, false), (605, true), (607, false)] [236, 1539],
  .add [(581, false), (605, false), (607, false)] [237, 1541],
  .add [(579, true), (607, true), (609, false)] [238, 1545],
  .add [(579, true), (607, false), (609, true)] [239, 1547],
  .add [(579, false), (607, true), (609, false)] [240, 1551],
  .add [(579, false), (607, false), (609, false)] [241, 1553],
  .add [(609, true), (611, false)] [242, 1557],
  .add [(609, false), (611, true)] [243, 1559],
  .add [(611, true), (613, true)] [244, 1569],
  .add [(611, false), (613, true)] [245, 1571],
  .add [(627, true), (723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true), (629, false)] [1573],
  .add [(627, true), (723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, false), (629, true)] [1577],
  .add [(627, false), (723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true), (629, false)] [1579],
  .add [(627, false), (723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, false), (629, true)] [1583],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true), (645, true), (647, false)] [1637],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true), (645, false), (647, true)] [1639],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, false), (645, true), (647, true)] [1645],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, false), (645, false), (647, true)] [1647],
  .add [(613, true)] [9, 8],
  .add [(649, false)] [0, 1654],
  .add [(647, false)] [0, 1652, 1654],
  .add [(723931182995265726379800275976996196319286522855750164913758664745085809747434712410109516276804447591723841709638363672139545490481567371676959010377761268612834571711418598699135154436891508198490459534975966594277568719306816826192572521796940643835037184769596752341865902737483315717341996690914896138181049841521421196960883062022679042024873904367280824570567532212199681509048126547197639124733581727308626013864013615472435237986270698710286062575630807773883824988932387614476604933362266851740619110530, true)] [0, 1, 1654],
  .add [(645, true)] [1, 0, 5],
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
