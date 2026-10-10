module

public import F4Heavy.Analysis.ParentBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def tailScale (r : Row) : ℝ := if r = .D then 16 / 5 else 4
def tailEta (r : Row) : ℝ := match r with | .D => 1 / 5 | .H => 1 / 10 | _ => 0
def tailLogLo (r : Row) : ℝ := match r with
  | .D => 188099060 / 100000000
  | .E1 => 225129179 / 100000000
  | .E2 => 231253542 / 100000000
  | .H => 249869997 / 100000000
def tailLogHi (r : Row) : ℝ := tailLogLo r + 1 / 100000000
def tailMid (r : Row) : ℝ := ((rowData r).lo + (rowData r).hi) / 2
def tailRadius (r : Row) : ℝ := ((rowData r).hi - (rowData r).lo) / (2 * (1 + tailMid r))
def tailEpsilon (r : Row) : ℝ := tailRadius r / (3 * (1 - tailRadius r) ^ 3)
def tailCoordinate (r : Row) (lam : ℝ) : ℝ := (lam - tailMid r) / (1 + tailMid r)
def tailTauLo (r : Row) (lam : ℝ) : ℝ :=
  tailLogLo r + tailCoordinate r lam - (1 / 2 + tailEpsilon r) * (tailCoordinate r lam) ^ 2
def tailTauHi (r : Row) (lam : ℝ) : ℝ :=
  tailLogHi r + tailCoordinate r lam - (1 / 2 - tailEpsilon r) * (tailCoordinate r lam) ^ 2
def tailTau (r : Row) (lam : ℝ) : ℝ := Real.log (tailScale r * (1 + lam))
def tailS (r : Row) (lam : ℝ) : ℝ :=
  (rowData r).price / (1 + lam) * ((1 + q lam) / (2 * q lam))
def tailK (r : Row) (lam : ℝ) : ℝ := 3 * tailS r lam / 4
def tailPStar (r : Row) (lam : ℝ) : ℝ := lam / (tailScale r * (1 + lam) + lam)
def tailV (x : ℝ) : ℝ := 1 - x / 2 - x ^ 2 / 12
def tailP1 (r : Row) (lam x : ℝ) : ℝ := 1 - x + gamma r lam * tailV x
def tailAStar (r : Row) (lam : ℝ) : ℝ := 1 + gamma r lam / 2 + gamma r lam * tailPStar r lam / 6
def tailEStar (r : Row) (lam : ℝ) : ℝ := (gamma r lam - delta r lam) * tailScale r * (1 + lam) / lam
def tailLStar (r : Row) (lam : ℝ) : ℝ := tailEStar r lam - 2 * tailPStar r lam * tailAStar r lam
def tailD0 (r : Row) (lam : ℝ) : ℝ := gamma r lam - delta r lam - gamma r lam * tailPStar r lam * tailTauHi r lam
def tailM0 (r : Row) (lam : ℝ) : ℝ := alpha r lam - gamma r lam - tailS r lam * tailPStar r lam / 4
def tailC0 (r : Row) (lam : ℝ) : ℝ := alpha r lam + beta r lam - 2 * gamma r lam * (1 - tailPStar r lam)
def tailA (r : Row) (lam : ℝ) : ℝ :=
  (tailK r lam * tailPStar r lam - tailP1 r lam (tailPStar r lam)) / tailTauLo r lam
def tailC (r : Row) (lam : ℝ) : ℝ := 2 * tailP1 r lam (tailPStar r lam) - alpha r lam - beta r lam
def tailReserveK (r : Row) (lam : ℝ) : ℝ := delta r lam / tailPStar r lam
def tailD (r : Row) (lam : ℝ) : ℝ := (gamma r lam - delta r lam) / tailPStar r lam -
  tailTauHi r lam * tailP1 r lam (tailPStar r lam) - (tailEta r) ^ 2 / (2 * tailLStar r lam)
def tailChildC (lam : ℝ) : ℝ := 10 * lam / (29 + 10 * lam)
def tailChildB (lam : ℝ) : ℝ := 2 * lam / (6 + lam)
def tailChildH0 (lam : ℝ) : ℝ := 6 * (1 - q lam) * (2 - q lam) / ((q lam) ^ 2 - 12 * q lam + 12)
def tailChildHb (lam : ℝ) : ℝ := 33 / 32 - tailChildC lam / 4
def tailT (r : Row) (lam h J : ℝ) : ℝ :=
  responseNumerator (tailA r lam) (beta r lam) (tailC r lam) (tailD r lam) (tailReserveK r lam) J h

def tailGuard (r : Row) (lam : ℝ) : Nat → ℝ
  | 1 => 1 / 6 - tailPStar r lam
  | 2 => tailTauLo r lam - 3 / 2
  | 3 => alpha r lam + beta r lam - 2 * gamma r lam
  | 4 => tailD0 r lam
  | 5 => 4 * tailD0 r lam * tailM0 r lam - tailPStar r lam * tailTauHi r lam * (tailC0 r lam) ^ 2
  | 6 => tailP1 r lam (tailPStar r lam) - tailK r lam * tailPStar r lam
  | 7 => tailP1 r lam (tailPStar r lam) - tailK r lam * tailPStar r lam -
      tailPStar r lam * tailTauHi r lam * (tailAStar r lam + tailK r lam)
  | 8 => tailLStar r lam
  | 9 => tailEStar r lam - tailP1 r lam (tailPStar r lam) -
      tailTauHi r lam * tailPStar r lam * (1 - tailPStar r lam) * tailAStar r lam + tailEta r
  | 10 => 2 + 2 * gamma r lam - alpha r lam - beta r lam -
      2 * (2 + gamma r lam) * tailPStar r lam - gamma r lam * (tailPStar r lam) ^ 2 / 2
  | 11 => 2 * delta r lam - tailPStar r lam * tailC r lam * tailChildB lam
  | 12 => tailC r lam
  | 13 => tailReserveK r lam + tailD r lam * tailChildC lam
  | 14 => tailT r lam (tailChildH0 lam) (tailChildC lam)
  | 15 => tailT r lam (tailChildHb lam) (tailChildC lam)
  | 16 => tailT r lam 1 (1 / 8)
  | _ => 0

end
end F4Heavy.Analysis
