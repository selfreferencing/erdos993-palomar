module

public import Erdos993Lean.Analytic.V213.FiberRootLineData

/-!
Accepted F10 typed profiles and all 24 printed endpoint controls.
Data only: canonical erased trees and Int/Nat nodes must be separately
checked before semantic use.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

inductive FiberRationalProfileIdentity where
  | a | b | d | g | h

structure FiberRationalProfileRow where
  m : lowMeanFraction
  s : lowMeanFraction
  ra : lowMeanFraction
  b : lowMeanFraction
  beta : lowMeanFraction

def fiberRationalProfileById : FiberRationalProfileIdentity → FiberRationalProfileRow
  | .a => ⟨(23, 1), (7, 2), (0, 1), (0, 1), (0, 1)⟩
  | .b => ⟨(19, 1), (13, 4), (0, 1), (0, 1), (0, 1)⟩
  | .d => ⟨(26, 1), (15, 4), (0, 1), (0, 1), (0, 1)⟩
  | .g => ⟨(50, 1), (9, 2), (0, 1), (0, 1), (0, 1)⟩
  | .h => ⟨(40, 1), (4, 1), (23, 100), (3, 20), (3, 10)⟩

inductive FiberProfileControlIdentity where
  | a_third | a_p042 | a_half | a_p06 | b_third | b_p042 | b_half | b_p06 | d_third | d_p042 | d_half | d_p052 | g_third | g_p042 | g_p044 | h_third | h_p038 | e_third | e_p038 | e_p042 | e_p044 | e_half | e_p052 | e_p06

inductive FiberProfileControlRole where
  | c0 | c1 | c2 | firstTest | secondTest

structure FiberProfileControlRow where
  printed : String
  profile : Option FiberRationalProfileIdentity
  endpoint : FiberProfileEndpointIdentity
  increasing : Bool
  t : lowMeanFraction
  a : lowMeanFraction
  R : lowMeanFraction
  z : lowMeanFraction
  e1 : lowMeanFraction
  e2 : lowMeanFraction
  c0 : lowMeanFraction
  c1 : lowMeanFraction
  c2 : lowMeanFraction

def fiberProfileControlPrinted : FiberProfileControlIdentity → String
  | .a_third => "F10:A:endpoint=1"
  | .a_p042 => "F10:A:endpoint=3"
  | .a_half => "F10:A:endpoint=5"
  | .a_p06 => "F10:A:endpoint=7"
  | .b_third => "F10:B:endpoint=1"
  | .b_p042 => "F10:B:endpoint=3"
  | .b_half => "F10:B:endpoint=5"
  | .b_p06 => "F10:B:endpoint=7"
  | .d_third => "F10:D:endpoint=1"
  | .d_p042 => "F10:D:endpoint=3"
  | .d_half => "F10:D:endpoint=5"
  | .d_p052 => "F10:D:endpoint=6"
  | .g_third => "F10:G:endpoint=1"
  | .g_p042 => "F10:G:endpoint=3"
  | .g_p044 => "F10:G:endpoint=4"
  | .h_third => "F10:H:endpoint=1"
  | .h_p038 => "F10:H:endpoint=2"
  | .e_third => "F10:Etilde:endpoint=1"
  | .e_p038 => "F10:Etilde:endpoint=2"
  | .e_p042 => "F10:Etilde:endpoint=3"
  | .e_p044 => "F10:Etilde:endpoint=4"
  | .e_half => "F10:Etilde:endpoint=5"
  | .e_p052 => "F10:Etilde:endpoint=6"
  | .e_p06 => "F10:Etilde:endpoint=7"

def fiberProfileControlById : FiberProfileControlIdentity → FiberProfileControlRow
  | .a_third => ⟨"F10:A:endpoint=1", some .a, .third, true, (1, 3), (8527, 10000), (1, 4), (33, 10), (1, 1), (1, 1000), (641832187351, 348556910625), (19122658727, 4482191700), (21851807197, 3841878600)⟩
  | .a_p042 => ⟨"F10:A:endpoint=3", some .a, .p042, true, (21, 50), (7583, 10000), (1, 4), (5, 4), (1, 1), (1, 1000), (429508464230323, 632750659750000), (45829005533, 20429692500), (2102762651, 105066990000)⟩
  | .a_half => ⟨"F10:A:endpoint=5", some .a, .half, false, (1, 2), (1651, 2500), (1, 4), (8, 25), (1, 1), (1, 1000), (14848281287, 70525015000), (280757503, 215285175), (-13487377, 3417225)⟩
  | .a_p06 => ⟨"F10:A:endpoint=7", some .a, .p06, false, (3, 5), (2643, 5000), (1, 4), (0, 1), (1, 1), (1, 1000), (-501667359442, 13709792490625), (435426321, 664084750), (-4744805017, 569215500)⟩
  | .b_third => ⟨"F10:B:endpoint=1", some .b, .third, true, (1, 3), (8527, 10000), (1, 8), (47, 20), (1, 10), (1, 1000), (22696606316159, 13245162603750), (65947724203, 15062603400), (322633603, 57933090)⟩
  | .b_p042 => ⟨"F10:B:endpoint=3", some .b, .p042, true, (21, 50), (7583, 10000), (1, 8), (89, 100), (1, 10), (1, 1000), (307130879554119, 522707066750000), (157497673971, 68654885000), (7012905581, 19804293750)⟩
  | .b_half => ⟨"F10:B:endpoint=5", some .b, .half, true, (1, 2), (1651, 2500), (1, 8), (13, 50), (1, 10), (1, 1000), (324994763, 2330391800), (74015981, 55651950), (-77452697, 24196500)⟩
  | .b_p06 => ⟨"F10:B:endpoint=7", some .b, .p06, false, (3, 5), (2643, 5000), (1, 8), (0, 1), (1, 10), (1, 1000), (-1015622354611, 11325480753125), (4463701911, 6695058500), (-4537753823, 643755625)⟩
  | .d_third => ⟨"F10:D:endpoint=1", some .d, .third, true, (1, 3), (8527, 10000), (1, 6), (237, 100), (1, 10), (1, 10000), (23680530396959, 14499967482000), (86306448323, 23438376000), (533810206, 122074875)⟩
  | .d_p042 => ⟨"F10:D:endpoint=3", some .d, .p042, true, (21, 50), (7583, 10000), (1, 6), (7, 8), (1, 10), (1, 10000), (51675268818747, 89410419312500), (620617887977, 320494200000), (-1658085483, 1571050000)⟩
  | .d_half => ⟨"F10:D:endpoint=5", some .d, .half, false, (1, 2), (1651, 2500), (1, 6), (221, 1000), (1, 10), (1, 10000), (4663973761, 29896473750), (6499987, 5773200), (-31434893, 6254300)⟩
  | .d_p052 => ⟨"F10:D:endpoint=6", some .d, .p052, false, (13, 25), (6337, 10000), (1, 6), (127, 1000), (1, 10), (1, 10000), (50811525903157, 596400197250000), (475184513977, 485713800000), (-60437977889, 10119037500)⟩
  | .g_third => ⟨"F10:G:endpoint=1", some .g, .third, true, (1, 3), (8527, 10000), (1, 4), (7, 3), (1, 1), (1, 1000), (215277557165233, 139422764250000), (33955443443, 12527865000), (252395993, 149141250)⟩
  | .g_p042 => ⟨"F10:G:endpoint=3", some .g, .p042, false, (21, 50), (7583, 10000), (1, 4), (17, 25), (1, 1), (1, 1000), (7894745113447, 13755449125000), (9947826797, 6852195000), (-23746237001, 4568130000)⟩
  | .g_p044 => ⟨"F10:G:endpoint=4", some .g, .p044, false, (11, 25), (1833, 2500), (1, 4), (49, 100), (1, 1), (1, 1000), (24911302631, 58090697500), (22025939, 17508750), (-19523186, 2918125)⟩
  | .h_third => ⟨"F10:H:endpoint=1", some .h, .third, true, (1, 3), (8527, 10000), (7, 25), (21, 10), (1, 10), (1, 1000), (10142023186053989, 8446484554200000), (3417357263, 1263834000), (2188111593709, 1360201342500)⟩
  | .h_p038 => ⟨"F10:H:endpoint=2", some .h, .p038, true, (19, 50), (4009, 5000), (7, 25), (26, 25), (1, 10), (1, 1000), (517420823755221, 824264745500000), (1333982723, 708565000), (-481226513653, 254197693750)⟩
  | .e_third => ⟨"F10:Etilde:endpoint=1", none, .third, true, (1, 3), (8527, 10000), (7, 25), (2, 1), (1, 10), (1, 1000), (28519729, 22095000), (7052843713, 3897558000), (363754793, 167038200)⟩
  | .e_p038 => ⟨"F10:Etilde:endpoint=2", none, .p038, true, (19, 50), (4009, 5000), (7, 25), (26, 25), (1, 10), (1, 1000), (22772641, 30968750), (29620845283, 21851550000), (-1015057501, 936495000)⟩
  | .e_p042 => ⟨"F10:Etilde:endpoint=3", none, .p042, false, (21, 50), (7583, 10000), (7, 25), (3, 5), (1, 10), (1, 1000), (292826019, 604250000), (5577683233, 5075700000), (-754702783, 217530000)⟩
  | .e_p044 => ⟨"F10:Etilde:endpoint=4", none, .p044, false, (11, 25), (1833, 2500), (7, 25), (21, 50), (1, 10), (1, 1000), (7544079, 20843750), (398333507, 408537500), (-16421779, 3501750)⟩
  | .e_half => ⟨"F10:Etilde:endpoint=5", none, .half, false, (1, 2), (1651, 2500), (7, 25), (9, 50), (1, 10), (1, 1000), (675977, 4245000), (264402697, 374409000), (-130168483, 16046100)⟩
  | .e_p052 => ⟨"F10:Etilde:endpoint=6", none, .p052, false, (13, 25), (6337, 10000), (7, 25), (3, 25), (1, 10), (1, 1000), (47323597, 457875000), (50638694509, 80769150000), (-32093136283, 3461535000)⟩
  | .e_p06 => ⟨"F10:Etilde:endpoint=7", none, .p06, false, (3, 5), (2643, 5000), (7, 25), (0, 1), (1, 10), (1, 1000), (-256653, 29462500), (225862851, 577465000), (-114507523, 8249500)⟩

def fiberProfileControlIdentityAt : ℕ → FiberProfileControlIdentity
  | 0 => .a_third
  | 1 => .a_p042
  | 2 => .a_half
  | 3 => .a_p06
  | 4 => .b_third
  | 5 => .b_p042
  | 6 => .b_half
  | 7 => .b_p06
  | 8 => .d_third
  | 9 => .d_p042
  | 10 => .d_half
  | 11 => .d_p052
  | 12 => .g_third
  | 13 => .g_p042
  | 14 => .g_p044
  | 15 => .h_third
  | 16 => .h_p038
  | 17 => .e_third
  | 18 => .e_p038
  | 19 => .e_p042
  | 20 => .e_p044
  | 21 => .e_half
  | 22 => .e_p052
  | _ => .e_p06

def fiberProfileControlRoleAt : ℕ → FiberProfileControlRole
  | 0 => .c0
  | 1 => .c1
  | 2 => .c2
  | 3 => .firstTest
  | _ => .secondTest

end Erdos993Lean.Analytic.V213
