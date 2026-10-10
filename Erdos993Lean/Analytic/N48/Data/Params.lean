module

public import Erdos993Lean.Analytic.Atlas.Params
public import Erdos993Lean.Analytic.N52.Data.Params

/-!
# The n ≥ 48 pieces and strip atlas: parameters

The 33 pieces at `n ≥ 48` (0-based `p`): Profile30's 30 bands with band 23 (0-based 22) split at `27/20` and band
26 (0-based 25) split at `33/20` and `17/10`.  Per piece: its edges
`pieceLo`, `pieceHi`, its parent band `pieceParent`, the new O3 row at the Laplace parameter `t = 0`
(`newEll`, `newA`: pieces 22, 26, 27, 28, rows 1–4 of the O3 ladder; `0` = none), the
five rates `rates48` (the parent's, with `newEll` at `t = 0` on the four new rows), the O5 rank `kmin48` and the
floor `mmin48 = k/(2 q(pieceHi))` at `n ≥ 48` (proved separately).  The strip of
piece `p` is `[q(pieceLo), q(pieceHi)] × [mmin48_p, N52.Data.stripFloor_{parent}]` (up to the floor at `n ≥ 52`,
the bottom of the n ≥ 52 strip) with the parent's `D`, `θ` (`Atlas.bandAt`) and the piece's rates.
This file imports only Lean's core.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.N48.Data

open Erdos993Lean.Analytic.Atlas

-- v4.35 module compatibility: retain the existing private helper and its exposed body.
set_option backward.privateInPublic true

private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- The lower edges of the 33 pieces. -/
def pieceLo : List Rat :=
  [R (1) 3, R (9) 25, R (2) 5, R (9) 20, R (1) 2, R (11) 20, R (3) 5, R (13) 20, R (7) 10, R (3) 4, R (4) 5, R (21) 25, R (22) 25, R (23) 25, R (24) 25, R (1) 1, R (26) 25, R (27) 25, R (28) 25, R (29) 25, R (6) 5, R (5) 4, R (13) 10, R (27) 20, R (7) 5, R (3) 2, R (8) 5, R (33) 20, R (17) 10, R (7) 4, R (19) 10, R (41) 20, R (9) 4]

/-- The upper edges of the 33 pieces. -/
def pieceHi : List Rat :=
  [R (9) 25, R (2) 5, R (9) 20, R (1) 2, R (11) 20, R (3) 5, R (13) 20, R (7) 10, R (3) 4, R (4) 5, R (21) 25, R (22) 25, R (23) 25, R (24) 25, R (1) 1, R (26) 25, R (27) 25, R (28) 25, R (29) 25, R (6) 5, R (5) 4, R (13) 10, R (27) 20, R (7) 5, R (3) 2, R (8) 5, R (33) 20, R (17) 10, R (7) 4, R (19) 10, R (41) 20, R (9) 4, R (7) 3]

/-- The parent band (0-based) of each piece. -/
def pieceParent : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 22, 23, 24, 25, 25, 25, 26, 27, 28, 29]

/-- The new O3 rate at `t = 0` of each piece (`0`: none; pieces 22, 26, 27, 28). -/
def newEll : List Rat :=
  [R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (23) 50, R (0) 1, R (0) 1, R (0) 1, R (939) 2000, R (47) 100, R (941) 2000, R (0) 1, R (0) 1, R (0) 1, R (0) 1]

/-- The potential coefficient `a` of each new O3 row (`0`: none). -/
def newA : List Rat :=
  [R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (0) 1, R (7) 100, R (0) 1, R (0) 1, R (0) 1, R (47) 500, R (97) 1000, R (1) 10, R (0) 1, R (0) 1, R (0) 1, R (0) 1]

/-- The five O3 rates of each piece: the parent's, with the new rate at `t = 0` on the new rows. -/
def rates48 : List (List Rat) :=
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
    [R (7) 16, R (4069) 10000, R (3807) 10000, R (657) 2000, R (701) 2500],
    [R (441) 1000, R (827) 2000, R (1919) 5000, R (207) 625, R (1413) 5000],
    [R (2223) 5000, R (521) 1250, R (3869) 10000, R (1669) 5000, R (178) 625],
    [R (4481) 10000, R (4201) 10000, R (39) 100, R (841) 2500, R (178) 625],
    [R (1129) 2500, R (2117) 5000, R (3931) 10000, R (3391) 10000, R (2871) 10000],
    [R (1129) 2500, R (2117) 5000, R (3931) 10000, R (841) 2500, R (2871) 10000],
    [R (4551) 10000, R (2117) 5000, R (1981) 5000, R (3391) 10000, R (2871) 10000],
    [R (23) 50, R (827) 2000, R (1919) 5000, R (207) 625, R (701) 2500],
    [R (2223) 5000, R (827) 2000, R (1919) 5000, R (207) 625, R (701) 2500],
    [R (4481) 10000, R (521) 1250, R (3869) 10000, R (207) 625, R (701) 2500],
    [R (1129) 2500, R (4201) 10000, R (39) 100, R (1669) 5000, R (701) 2500],
    [R (939) 2000, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (47) 100, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (941) 2000, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (2223) 5000, R (2051) 5000, R (3807) 10000, R (202) 625, R (679) 2500],
    [R (2223) 5000, R (2051) 5000, R (3807) 10000, R (641) 2000, R (2693) 10000],
    [R (269) 625, R (397) 1000, R (921) 2500, R (1549) 5000, R (651) 2500],
    [R (1129) 2500, R (521) 1250, R (3869) 10000, R (657) 2000, R (1369) 5000]]

/-- The O5 rank of each piece at `n ≥ 48`. -/
def kmin48 : List Nat :=
  [13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 17]

/-- The floor of `m` of each piece at `n ≥ 48`: `k_p/(2 q(pieceHi_p))`. -/
def mmin48 : List Rat :=
  [R (221) 9, R (91) 4, R (377) 18, R (39) 2, R (403) 22, R (52) 3, R (33) 2, R (221) 14, R (91) 6, R (117) 8, R (299) 21, R (611) 44, R (312) 23, R (343) 24, R (14) 1, R (357) 26, R (364) 27, R (53) 4, R (378) 29, R (55) 4, R (27) 2, R (345) 26, R (235) 18, R (90) 7, R (25) 2, R (195) 16, R (424) 33, R (216) 17, R (88) 7, R (232) 19, R (488) 41, R (104) 9, R (85) 7]

/-- The parameters of the strip of piece `p`: the parent band with the piece's edges, rates and floor. -/
def piece48Band (p : Nat) : Band :=
  { bandAt (pieceParent.getD p 0) with
    ell := rates48.getD p []
    lamLo := pieceLo.getD p 0
    lamHi := pieceHi.getD p 0
    mmin := mmin48.getD p 0 }

/-- The top of the strip of piece `p`: the floor of its parent band at `n ≥ 52` (the bottom of the n ≥ 52 strip). -/
def piece48Cap (p : Nat) : Rat := N52.Data.stripFloor.getD (pieceParent.getD p 0) 0

end Erdos993Lean.Analytic.N48.Data
