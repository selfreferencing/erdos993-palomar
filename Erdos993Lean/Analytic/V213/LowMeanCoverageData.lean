module

public import Erdos993Lean.Analytic.V213.LowMeanCoverageShape

/-! Reviewed Table 1 groups and T1/T4 cap/routing data; endpoints come from N44. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanGroups : List LowMeanGroupInput := [
  { iotaLo := 0, iotaHi := 5, certLo := 0, certHi := 0, l := (1, 4), h := (3, 8), D := (6, 5), theta := (1, 1), muLo := (32, 3), muHi := (50, 1), dWitness := 0, thetaWitness := 0, meanWitness := 3 },
  { iotaLo := 6, iotaHi := 9, certLo := 1, certHi := 2, l := (3, 8), h := (39, 89), D := (6, 5), theta := (7, 10), muLo := (356, 39), muHi := (23, 1), dWitness := 6, thetaWitness := 6, meanWitness := 6 },
  { iotaLo := 10, iotaHi := 13, certLo := 3, certHi := 4, l := (39, 89), h := (87, 187), D := (6, 5), theta := (13, 20), muLo := (748, 87), muHi := (20, 1), dWitness := 10, thetaWitness := 10, meanWitness := 10 },
  { iotaLo := 14, iotaHi := 17, certLo := 5, certHi := 6, l := (87, 187), h := (23, 48), D := (6, 5), theta := (3, 5), muLo := (192, 23), muHi := (19, 1), dWitness := 14, thetaWitness := 14, meanWitness := 14 },
  { iotaLo := 18, iotaHi := 24, certLo := 7, certHi := 9, l := (23, 48), h := (103, 203), D := (6, 5), theta := (3, 5), muLo := (812, 103), muHi := (19, 1), dWitness := 18, thetaWitness := 18, meanWitness := 18 },
  { iotaLo := 25, iotaHi := 27, certLo := 10, certHi := 12, l := (103, 203), h := (107, 207), D := (6, 5), theta := (3, 5), muLo := (828, 107), muHi := (19, 1), dWitness := 25, thetaWitness := 25, meanWitness := 25 },
  { iotaLo := 28, iotaHi := 29, certLo := 13, certHi := 15, l := (107, 207), h := (11, 21), D := (6, 5), theta := (3, 5), muLo := (84, 11), muHi := (19, 1), dWitness := 28, thetaWitness := 28, meanWitness := 28 },
  { iotaLo := 30, iotaHi := 37, certLo := 16, certHi := 19, l := (11, 21), h := (13, 23), D := (6, 5), theta := (3, 5), muLo := (92, 13), muHi := (26, 1), dWitness := 30, thetaWitness := 30, meanWitness := 37 },
  { iotaLo := 38, iotaHi := 43, certLo := 20, certHi := 22, l := (13, 23), h := (8, 13), D := (8, 5), theta := (7, 10), muLo := (13, 2), muHi := (50, 1), dWitness := 43, thetaWitness := 38, meanWitness := 40 },
  { iotaLo := 44, iotaHi := 49, certLo := 23, certHi := 25, l := (8, 13), h := (19, 29), D := (9, 5), theta := (1, 1), muLo := (116, 19), muHi := (50, 1), dWitness := 47, thetaWitness := 47, meanWitness := 46 },
  { iotaLo := 50, iotaHi := 54, certLo := 26, certHi := 27, l := (19, 29), h := (7, 10), D := (21, 10), theta := (1, 1), muLo := (40, 7), muHi := (50, 1), dWitness := 52, thetaWitness := 50, meanWitness := 50 }
]

def lowMeanInputRows : List LowMeanInputRow := [
  { group := 0, D := (6, 5), theta := (1, 1), mu0 := (45, 1) },
  { group := 0, D := (6, 5), theta := (1, 1), mu0 := (45, 1) },
  { group := 0, D := (6, 5), theta := (1, 1), mu0 := (45, 1) },
  { group := 0, D := (6, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 0, D := (6, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 0, D := (6, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 1, D := (6, 5), theta := (7, 10), mu0 := (23, 1) },
  { group := 1, D := (6, 5), theta := (7, 10), mu0 := (23, 1) },
  { group := 1, D := (6, 5), theta := (7, 10), mu0 := (23, 1) },
  { group := 1, D := (6, 5), theta := (7, 10), mu0 := (23, 1) },
  { group := 2, D := (6, 5), theta := (13, 20), mu0 := (20, 1) },
  { group := 2, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 2, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 2, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 3, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 3, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 3, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 3, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 4, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 5, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 5, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 5, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 6, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 6, D := (6, 5), theta := (3, 5), mu0 := (19, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (20, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (20, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (21, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (21, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (21, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (22, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (22, 1) },
  { group := 7, D := (6, 5), theta := (3, 5), mu0 := (26, 1) },
  { group := 8, D := (7, 5), theta := (7, 10), mu0 := (32, 1) },
  { group := 8, D := (7, 5), theta := (7, 10), mu0 := (36, 1) },
  { group := 8, D := (7, 5), theta := (7, 10), mu0 := (50, 1) },
  { group := 8, D := (7, 5), theta := (7, 10), mu0 := (50, 1) },
  { group := 8, D := (7, 5), theta := (7, 10), mu0 := (50, 1) },
  { group := 8, D := (8, 5), theta := (7, 10), mu0 := (50, 1) },
  { group := 9, D := (8, 5), theta := (9, 10), mu0 := (40, 1) },
  { group := 9, D := (8, 5), theta := (19, 20), mu0 := (45, 1) },
  { group := 9, D := (8, 5), theta := (19, 20), mu0 := (50, 1) },
  { group := 9, D := (9, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 9, D := (9, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 9, D := (9, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 10, D := (9, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 10, D := (9, 5), theta := (1, 1), mu0 := (50, 1) },
  { group := 10, D := (21, 10), theta := (1, 1), mu0 := (50, 1) },
  { group := 10, D := (21, 10), theta := (1, 1), mu0 := (50, 1) },
  { group := 10, D := (21, 10), theta := (1, 1), mu0 := (50, 1) }
]

def lowMeanCertificateGroups : List ℕ :=
  [0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 10]

def lowMeanGroupAt (k : ℕ) : LowMeanGroupInput := lowMeanGroups.getD k {}
def lowMeanInputRowAt (i : ℕ) : LowMeanInputRow := lowMeanInputRows.getD i {}
def lowMeanCertificateGroupAt (i : ℕ) : ℕ := lowMeanCertificateGroups.getD i 0

end Erdos993Lean.Analytic.V213
