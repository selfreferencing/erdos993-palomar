module

public import Erdos993Lean.Analytic.Atlas.Params
public import Erdos993Lean.Analytic.N48.Data.Params

/-!
# The n ≥ 45 pieces and strip atlas: parameters

The 46 pieces at `n ≥ 45` (0-based `p`): the sub-bands of the final configuration
(Profile30's 30 bands, 11 of them split).  Per piece: its edges
`pieceLo`, `pieceHi`, its parent band `pieceParent`; per band its first piece `pieceFirst` and its number of pieces
`pieceNsub`; the containing n ≥ 48 piece `pieceUp`; the O3 ladder row at `t = 0` used on the piece (`newEll`, `newA`:
the rate and potential coefficient, `0` = none; `rowOf`: its index in the O3 ladder rows, `26` = none); the five rates
`rates45` (the parent's, with `newEll` at `t = 0` on the rows); the caps `theta45`, `D45` (the configuration's
O2/O1 refits, else the parent band's); the O5 rank `kmin` and the floor `mmin = k/(2 q(pieceHi))` at
`n ≥ 45` (proved separately).  The strip of piece `p` is
`[q(pieceLo), q(pieceHi)] × [mmin45_p, N48.Data.mmin48_(pieceUp p)]` (up to the floor at `n ≥ 48` of the containing
piece) with the piece's caps and rates.  This file imports only Lean's core.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.N45.Data

open Erdos993Lean.Analytic.Atlas

-- v4.35 module compatibility: retain the existing private helper and its exposed body.
set_option backward.privateInPublic true

private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- The lower edges of the 46 pieces. -/
def pieceLo : List Rat :=
  [R (1) 3, R (9) 25, R (2) 5, R (9) 20, R (1) 2, R (11) 20, R (3) 5, R (13) 20, R (7) 10, R (3) 4, R (4) 5, R (21) 25, R (22) 25, R (23) 25, R (24) 25, R (1) 1, R (103) 100, R (26) 25, R (21) 20, R (107) 100, R (27) 25, R (11) 10, R (28) 25, R (57) 50, R (29) 25, R (59) 50, R (6) 5, R (49) 40, R (5) 4, R (13) 10, R (27) 20, R (7) 5, R (57) 40, R (29) 20, R (3) 2, R (8) 5, R (33) 20, R (17) 10, R (7) 4, R (9) 5, R (37) 20, R (19) 10, R (39) 20, R (2) 1, R (41) 20, R (9) 4]

/-- The upper edges of the 46 pieces. -/
def pieceHi : List Rat :=
  [R (9) 25, R (2) 5, R (9) 20, R (1) 2, R (11) 20, R (3) 5, R (13) 20, R (7) 10, R (3) 4, R (4) 5, R (21) 25, R (22) 25, R (23) 25, R (24) 25, R (1) 1, R (103) 100, R (26) 25, R (21) 20, R (107) 100, R (27) 25, R (11) 10, R (28) 25, R (57) 50, R (29) 25, R (59) 50, R (6) 5, R (49) 40, R (5) 4, R (13) 10, R (27) 20, R (7) 5, R (57) 40, R (29) 20, R (3) 2, R (8) 5, R (33) 20, R (17) 10, R (7) 4, R (9) 5, R (37) 20, R (19) 10, R (39) 20, R (2) 1, R (41) 20, R (9) 4, R (7) 3]

/-- The parent band (0-based) of each piece. -/
def pieceParent : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 22, 22, 23, 23, 23, 24, 25, 25, 25, 26, 26, 26, 27, 27, 27, 28, 29]

/-- The first piece of each band. -/
def pieceFirst : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 20, 22, 24, 26, 28, 29, 31, 34, 35, 38, 41, 44, 45]

/-- The number of pieces of each band. -/
def pieceNsub : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 1, 3, 3, 3, 1, 1]

/-- The n ≥ 48 piece containing each piece. -/
def pieceUp : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 22, 23, 24, 24, 24, 25, 26, 27, 28, 29, 29, 29, 30, 30, 30, 31, 32]

/-- The O3 ladder rate at `t = 0` of each piece (`0`: none). -/
def newEll : List Rat :=
  [R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (881) 2000, R (449) 1000, R (901) 2000, R (449) 1000, R (907) 2000, R (113) 250, R (907) 2000, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (23) 50, R (37) 80, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (939) 2000, R (47) 100, R (941) 2000, R (941) 2000, R (47) 100, R (47) 100, R (47) 100, R (0) 1, R (0) 1, R (0) 1, R (0) 1]

/-- The potential coefficient `a` of the ladder row of each piece (`0`: none). -/
def newA : List Rat :=
  [R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (23) 500, R (23) 500, R (7) 125, R (7) 125, R (29) 500, R (59) 1000, R (11) 200, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (7) 100, R (81) 1000, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (47) 500, R (97) 1000, R (1) 10, R (101) 1000, R (93) 1000, R (19) 200, R (27) 250, R (0) 1, R (0) 1, R (0) 1, R (0) 1]

/-- The index of the ladder row of each piece in `Ladder.O3.rowLo` … (`26`: none). -/
def rowOf : List Nat :=
  [26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 4, 5, 6, 7, 8, 9, 10, 26, 26, 26, 26, 26, 26, 26, 0, 11, 26, 26, 26, 26, 1, 2, 3, 12, 13, 14, 15, 26, 26, 26, 26]

/-- The five O3 rates of each piece: the parent's, with the ladder rate at `t = 0` on the rows. -/
def rates45 : List (List Rat) :=
  [[R (619) 2500, R (2353) 10000, R (551) 2500, R (489) 2500, R (169) 1000],
    [R (1309) 5000, R (613) 2500, R (2327) 10000, R (509) 2500, R (439) 2500],
    [R (2793) 10000, R (2617) 10000, R (2451) 10000, R (271) 1250, R (467) 2500],
    [R (751) 2500, R (563) 2000, R (1333) 5000, R (291) 1250, R (1001) 5000],
    [R (643) 2000, R (3013) 10000, R (2821) 10000, R (1231) 5000, R (1067) 5000],
    [R (339) 1000, R (1589) 5000, R (119) 400, R (1297) 5000, R (139) 625],
    [R (3531) 10000, R (3343) 10000, R (3129) 10000, R (1363) 5000, R (146) 625],
    [R (459) 1250, R (139) 400, R (3253) 10000, R (177) 625, R (97) 400],
    [R (953) 2500, R (1787) 5000, R (669) 2000, R (182) 625, R (623) 2500],
    [R (1959) 5000, R (3673) 10000, R (3437) 10000, R (187) 625, R (2559) 10000],
    [R (4059) 10000, R (761) 2000, R (3561) 10000, R (192) 625, R (1313) 5000],
    [R (4129) 10000, R (3871) 10000, R (3623) 10000, R (5) 16, R (267) 1000],
    [R (4199) 10000, R (3937) 10000, R (921) 2500, R (1589) 5000, R (679) 2500],
    [R (4269) 10000, R (4003) 10000, R (743) 2000, R (202) 625, R (1369) 5000],
    [R (269) 625, R (1009) 2500, R (236) 625, R (1629) 5000, R (1391) 5000],
    [R (881) 2000, R (4069) 10000, R (3807) 10000, R (657) 2000, R (701) 2500],
    [R (449) 1000, R (4069) 10000, R (3807) 10000, R (657) 2000, R (701) 2500],
    [R (901) 2000, R (827) 2000, R (1919) 5000, R (207) 625, R (1413) 5000],
    [R (449) 1000, R (827) 2000, R (1919) 5000, R (207) 625, R (1413) 5000],
    [R (907) 2000, R (827) 2000, R (1919) 5000, R (207) 625, R (1413) 5000],
    [R (113) 250, R (521) 1250, R (3869) 10000, R (1669) 5000, R (178) 625],
    [R (907) 2000, R (521) 1250, R (3869) 10000, R (1669) 5000, R (178) 625],
    [R (4481) 10000, R (4201) 10000, R (39) 100, R (841) 2500, R (178) 625],
    [R (4481) 10000, R (4201) 10000, R (39) 100, R (841) 2500, R (178) 625],
    [R (1129) 2500, R (2117) 5000, R (3931) 10000, R (3391) 10000, R (2871) 10000],
    [R (1129) 2500, R (2117) 5000, R (3931) 10000, R (3391) 10000, R (2871) 10000],
    [R (1129) 2500, R (2117) 5000, R (3931) 10000, R (841) 2500, R (2871) 10000],
    [R (1129) 2500, R (2117) 5000, R (3931) 10000, R (841) 2500, R (2871) 10000],
    [R (4551) 10000, R (2117) 5000, R (1981) 5000, R (3391) 10000, R (2871) 10000],
    [R (23) 50, R (827) 2000, R (1919) 5000, R (207) 625, R (701) 2500],
    [R (37) 80, R (827) 2000, R (1919) 5000, R (207) 625, R (701) 2500],
    [R (4481) 10000, R (521) 1250, R (3869) 10000, R (207) 625, R (701) 2500],
    [R (4481) 10000, R (521) 1250, R (3869) 10000, R (207) 625, R (701) 2500],
    [R (4481) 10000, R (521) 1250, R (3869) 10000, R (207) 625, R (701) 2500],
    [R (1129) 2500, R (4201) 10000, R (39) 100, R (1669) 5000, R (701) 2500],
    [R (939) 2000, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (47) 100, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (941) 2000, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (941) 2000, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (47) 100, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (47) 100, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (47) 100, R (2051) 5000, R (3807) 10000, R (641) 2000, R (2693) 10000],
    [R (2223) 5000, R (2051) 5000, R (3807) 10000, R (641) 2000, R (2693) 10000],
    [R (2223) 5000, R (2051) 5000, R (3807) 10000, R (641) 2000, R (2693) 10000],
    [R (269) 625, R (397) 1000, R (921) 2500, R (1549) 5000, R (651) 2500],
    [R (1129) 2500, R (521) 1250, R (3869) 10000, R (657) 2000, R (1369) 5000]]

/-- The O2 cap `θ` of each piece at `n ≥ 45`. -/
def theta45 : List Rat :=
  [R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (7) 10, R (7) 10, R (7) 10, R (7) 10, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (3) 5, R (7) 10, R (7) 10, R (7) 10, R (7) 10, R (7) 10, R (7) 10, R (1) 1, R (19) 20, R (19) 20, R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (1) 1, R (1) 1]

/-- The O1 cap `D` of each piece at `n ≥ 45`. -/
def D45 : List Rat :=
  [R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (7) 5, R (7) 5, R (7) 5, R (7) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (13) 10, R (13) 10, R (7) 5, R (7) 5, R (7) 5, R (7) 5, R (7) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5]

/-- The O5 rank of each piece at `n ≥ 45`. -/
def kmin45 : List Nat :=
  [13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16]

/-- The floor of `m` of each piece at `n ≥ 45`: `k_p/(2 q(pieceHi_p))`. -/
def mmin45 : List Rat :=
  [R (221) 9, R (91) 4, R (377) 18, R (39) 2, R (403) 22, R (52) 3, R (33) 2, R (221) 14, R (91) 6, R (117) 8, R (299) 21, R (611) 44, R (312) 23, R (637) 48, R (13) 1, R (2639) 206, R (51) 4, R (533) 42, R (2691) 214, R (338) 27, R (273) 22, R (689) 56, R (749) 57, R (378) 29, R (763) 59, R (77) 6, R (89) 7, R (63) 5, R (161) 13, R (329) 27, R (12) 1, R (679) 57, R (343) 29, R (35) 3, R (195) 16, R (265) 22, R (405) 34, R (165) 14, R (35) 3, R (855) 74, R (435) 38, R (295) 26, R (45) 4, R (915) 82, R (65) 6, R (80) 7]

/-- The parameters of the strip of piece `p`: the parent band with the piece's caps, edges, rates and floor. -/
def piece45Band (p : Nat) : Band :=
  { bandAt (pieceParent.getD p 0) with
    D := D45.getD p 0
    theta := theta45.getD p 0
    ell := rates45.getD p []
    lamLo := pieceLo.getD p 0
    lamHi := pieceHi.getD p 0
    mmin := mmin45.getD p 0 }

/-- The top of the strip of piece `p`: the floor at `n ≥ 48` of the containing piece. -/
def piece45Cap (p : Nat) : Rat := N48.Data.mmin48.getD (pieceUp.getD p 0) 0

end Erdos993Lean.Analytic.N45.Data
