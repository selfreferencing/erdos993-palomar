module

public import F4Heavy.Contract
public import Mathlib.Data.Nat.Choose.Basic

/-! Literal light construction from the F4 note and
its four-row light source note.
All terminating decimal table entries below are exact rational expressions.
These definitions retain the full parent, source, response and chart objects.
They assert no positivity and introduce no extra input to `LightCore`. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section
open scoped BigOperators

inductive Support where
  | first | second
  deriving DecidableEq, Repr

inductive Regime where
  | A | B
  deriving DecidableEq, Repr

inductive SourcePhase where
  | first | second
  deriving DecidableEq, Repr

def slope (r : Row) : Support → ℝ
  | .first => match r with
    | .D => 11 / 5
    | .E1 | .E2 => 7 / 3
    | .H => 12 / 5
  | .second => 3 / 10

def endpointInterceptLo (r : Row) : Support → ℝ
  | .first => match r with
    | .D => -16634713915 / 10000000000
    | .E1 => -158333778 / 100000000
    | .E2 => -154103887 / 100000000
    | .H => -15097571481 / 10000000000
  | .second => match r with
    | .D => -602586430 / 10000000000
    | .E1 => 3500567 / 100000000
    | .E2 => 5922933 / 100000000
    | .H => 1033318346 / 10000000000

def endpointInterceptHi (r : Row) : Support → ℝ
  | .first => match r with
    | .D => -14914076875 / 10000000000
    | .E1 => -154103887 / 100000000
    | .E2 => -150225069 / 100000000
    | .H => -13939876548 / 10000000000
  | .second => match r with
    | .D => 349730222 / 10000000000
    | .E1 => 5922933 / 100000000
    | .E2 => 8200105 / 100000000
    | .H => 1762035691 / 10000000000

def contactLo (r : Row) : Support → ℝ
  | .first => match r with
    | .D => 4404409 / 10000000
    | .E1 => 13 / 23
    | .E2 => 29 / 49
    | .H => 996057 / 1562500
  | .second => match r with
    | .D => 19405741 / 100000000
    | .E1 => 52 / 207
    | .E2 => 116 / 441
    | .H => 14253549 / 50000000

def contactHi (r : Row) : Support → ℝ
  | .first => match r with
    | .D => 52787217 / 100000000
    | .E1 => 29 / 49
    | .E2 => 8 / 13
    | .H => 1032489 / 1562500
  | .second => match r with
    | .D => 25029329 / 100000000
    | .E1 => 116 / 441
    | .E2 => 32 / 117
    | .H => 31777527 / 100000000

def curvature : Row → ℝ
  | .D => 1
  | .E1 | .E2 => 3 / 2
  | .H => 1 / 4

def interceptError (r : Row) (lam : ℝ) : ℝ :=
  let a := (rowData r).lo
  let b := (rowData r).hi
  let qa := q a
  let qb := q b
  match r with
  | .D => qb * (1 - qb / 2) * (729 / 800) * (q lam - qa) * (qb - q lam)
  | .H => 0
  | .E1 | .E2 => qb * (1 - qb / 2) * (b - a)^2 / (8 * a^2)

def intercept (r : Row) (s : Support) (lam : ℝ) : ℝ :=
  let a := (rowData r).lo
  let b := (rowData r).hi
  match r with
  | .D | .H =>
    let omega := (q lam - q a) / (q b - q a)
    (1 - omega) * endpointInterceptLo r s + omega * endpointInterceptHi r s +
      interceptError r lam
  | .E1 | .E2 =>
    (b - lam) / (b - a) * endpointInterceptLo r s +
      (lam - a) / (b - a) * endpointInterceptHi r s + interceptError r lam

def supportLine (r : Row) (s : Support) (lam h : ℝ) : ℝ :=
  slope r s * h + intercept r s lam

def sigma : Row → ℝ
  | .D | .E1 | .E2 => 7 / 12
  | .H => 3 / 5

def hMinus (r : Row) (H : ℝ) : ℝ := 1 - sigma r * H

def hPlus (lam : ℝ) : ℝ :=
  1 - q lam / 4 - (q lam)^2 / 48 - (q lam)^3 / 192 - 19 * (q lam)^4 / 11520

def hCross (r : Row) (lam : ℝ) : ℝ :=
  (intercept r .second lam - intercept r .first lam) /
    (slope r .first - slope r .second)

def HCross (r : Row) (lam : ℝ) : ℝ := (1 - hCross r lam) / sigma r

def RegimeDomain (r : Row) (reg : Regime) (lam H : ℝ) : Prop :=
  match reg with
  | .A => q lam / 2 ≤ H ∧ H ≤ HCross r lam
  | .B => HCross r lam ≤ H ∧ H ≤ q lam

def supportEnvelope (r : Row) (reg : Regime) (lam h : ℝ) : ℝ :=
  match reg with
  | .A => supportLine r .second lam h
  | .B => min (supportLine r .first lam h) (supportLine r .second lam h)

/-- Rational form of the frozen parent's `p` in the retained coordinate H. -/
def pH (lam H : ℝ) : ℝ := lam * (1 - H) / (1 + lam * (1 - H))
def vacancyLo (lam H : ℝ) : ℝ := 1 / (1 + lam * (1 - pH lam H))
def vacancySwitch (lam H : ℝ) : ℝ := q lam / ((1 + q lam) * pH lam H)
def sourceSlopeA (lam : ℝ) : ℝ := (1 + q lam) / (2 * q lam)
def sourceSlopeB (lam : ℝ) : ℝ := sourceSlopeA lam / q lam
def sourceIntercept (lam : ℝ) : ℝ := (q lam - 1) / (2 * q lam)
def sourceH (lam H rho : ℝ) : ℝ :=
  (1 + f lam (pH lam H * rho) -
    f lam (max (1 - rho) ((1 - pH lam H * rho) * H))) / 2

def sourceAtLo (lam H : ℝ) : ℝ := sourceSlopeA lam * pH lam H * vacancyLo lam H

def sourceAtSwitchLower (lam H : ℝ) : ℝ :=
  (3 * q lam - H) / (4 * q lam) - (q lam - H)^2 / (2 * q lam * (2 - q lam))

def sourceAtHi (lam H : ℝ) : ℝ := sourceSlopeB lam * pH lam H + sourceIntercept lam

def chordSlope (phase : SourcePhase) (lam H : ℝ) : ℝ :=
  match phase with
  | .first => (sourceAtSwitchLower lam H - sourceAtLo lam H) /
      (vacancySwitch lam H - vacancyLo lam H)
  | .second =>
    (1 - H) * (1 + q lam) *
      (2 * H^2 * q lam - 3 * H * (q lam)^2 + 2 * H * q lam - 2 * H + q lam + 2) /
      (4 * q lam * (2 - q lam) * (1 - q lam * H))

def chordIntercept (phase : SourcePhase) (lam H : ℝ) : ℝ :=
  match phase with
  | .first => sourceAtLo lam H - chordSlope phase lam H * vacancyLo lam H
  | .second => sourceAtHi lam H - chordSlope phase lam H

def sourceChord (phase : SourcePhase) (lam H rho : ℝ) : ℝ :=
  chordSlope phase lam H * rho + chordIntercept phase lam H

def PhaseDomain (phase : SourcePhase) (lam H rho : ℝ) : Prop :=
  match phase with
  | .first => vacancyLo lam H ≤ rho ∧ rho ≤ vacancySwitch lam H
  | .second => vacancySwitch lam H ≤ rho ∧ rho ≤ 1

def phaseLo (phase : SourcePhase) (lam H : ℝ) : ℝ :=
  match phase with | .first => vacancyLo lam H | .second => vacancySwitch lam H

def phaseHi (phase : SourcePhase) (lam H : ℝ) : ℝ :=
  match phase with | .first => vacancySwitch lam H | .second => 1

def parentHBound (p : ℝ) : ℝ := 1 - p / 2 - p^2 / 12

def parentPPlus (r : Row) (lam H rho : ℝ) : ℝ :=
  rho * (1 - pH lam H) + gamma r lam * parentHBound (pH lam H)

def parentNHat (r : Row) (phase : SourcePhase) (lam H rho : ℝ) : ℝ :=
  (rowData r).price / (1 + lam) * rho * sourceChord phase lam H rho +
    alpha r lam * (1 - rho) - parentPPlus r lam H rho

def zMinus (H : ℝ) : ℝ := 3 * H * (2 - H) / (H^2 - 6 * H + 6)
def zPlus (H : ℝ) : ℝ := H * (H^2 - 12 * H + 12) / (6 * (1 - H) * (2 - H))

def responseC (r : Row) (lam H rho : ℝ) : ℝ :=
  pH lam H * (2 * parentPPlus r lam H rho - alpha r lam - beta r lam)

def responseD (r : Row) (lam H rho z : ℝ) : ℝ :=
  gamma r lam - delta r lam - pH lam H * z * parentPPlus r lam H rho

def scaledPayment (r : Row) (phase : SourcePhase) (lam H rho z h y L : ℝ) : ℝ :=
  parentNHat r phase lam H rho + z * beta r lam * rho * h +
    z * (2 * parentPPlus r lam H rho - alpha r lam - beta r lam) * y +
    (z * (gamma r lam - delta r lam) / pH lam H - z^2 * parentPPlus r lam H rho) * y^2 +
    z * delta r lam / (pH lam H * L) * (h - y)^2

/-- Cleared response numerator, with the entire parent/source/response retained. -/
def W (r : Row) (phase : SourcePhase) (lam H rho z h L : ℝ) : ℝ :=
  4 * (delta r lam + responseD r lam H rho z * L) *
      (pH lam H * parentNHat r phase lam H rho + z * pH lam H * beta r lam * rho * h) +
    4 * delta r lam * z * (responseC r lam H rho * h + responseD r lam H rho z * h^2) -
    z * L * (responseC r lam H rho)^2

def responseIntervalLo : Row → ℝ
  | .D => 4 / 5 | .E1 | .E2 => 3 / 4 | .H => 7 / 10

def responseIntervalHi : Row → ℝ
  | .D => 9 / 10 | .E1 | .E2 => 6 / 7 | .H => 5 / 6

def RGuard (r : Row) (lam H v e : ℝ) : ℝ :=
  2 * (gamma r lam - delta r lam) * v + pH lam H *
    (2 * parentPPlus r lam H e * (1 - zPlus H * v) - alpha r lam - beta r lam)

def SGuard (r : Row) (lam H v : ℝ) : ℝ :=
  10 * delta r lam + pH lam H * (alpha r lam + beta r lam) +
    (gamma r lam - delta r lam) * (v + 10 * intercept r .second lam) -
    pH lam H * parentPPlus r lam H 1 * (2 + zPlus H * (v + 10 * intercept r .second lam))

def childV0 (r : Row) (reg : Regime) (phase : SourcePhase) (lam H rho z : ℝ) : ℝ :=
  let s := match reg with | .A => Support.second | .B => Support.first
  W r phase lam H rho z (hMinus r H) (supportLine r s lam (hMinus r H))

def childV1 (r : Row) (phase : SourcePhase) (lam H rho z : ℝ) : ℝ :=
  W r phase lam H rho z (hCross r lam) (supportLine r .first lam (hCross r lam))

def childM0 (r : Row) (phase : SourcePhase) (lam H rho z : ℝ) : ℝ :=
  2 * W r phase lam H rho z ((hMinus r H + hCross r lam) / 2)
      ((supportLine r .first lam (hMinus r H) + supportLine r .first lam (hCross r lam)) / 2) -
    (childV0 r .B phase lam H rho z + childV1 r phase lam H rho z) / 2

/-- Power coefficients of a cubic in vacancy remain an explicit function w. -/
def vacancyChartCoefficient (w : ℕ → ℝ) (r0 r1 : ℝ) (j : ℕ) : ℝ :=
  (r1 - r0)^j * ∑ k ∈ Finset.Icc j 3, (Nat.choose k j : ℝ) * w k * r0^(k-j)

/-- The native degree-n Bernstein control of the explicitly retained cubic. -/
def vacancyControl (w : ℕ → ℝ) (r0 r1 : ℝ) (n s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (min s 3 + 1),
    (Nat.choose s j : ℝ) / (Nat.choose n j : ℝ) * vacancyChartCoefficient w r0 r1 j

def vacancyControlDegree (reg : Regime) (phase : SourcePhase) : ℕ :=
  match reg, phase with | .A, .first => 4 | _, _ => 3

/-- The parent chart retained by every rational numerator record. -/
def parentChart (r : Row) (reg : Regime) (lam t : ℝ) : ℝ :=
  match reg with
  | .A => q lam / 2 + (HCross r lam - q lam / 2) * t
  | .B => HCross r lam + (q lam - HCross r lam) * t

inductive LogEndpoint where
  | lower | upper
  deriving DecidableEq, Repr

def logEndpoint (endpoint : LogEndpoint) (H : ℝ) : ℝ :=
  match endpoint with | .lower => zMinus H | .upper => zPlus H

inductive ChildControl where
  | V0 | V1 | M0
  deriving DecidableEq, Repr

def childControlValue (r : Row) (reg : Regime) (phase : SourcePhase)
    (control : ChildControl) (lam H rho z : ℝ) : ℝ :=
  match control with
  | .V0 => childV0 r reg phase lam H rho z
  | .V1 => childV1 r phase lam H rho z
  | .M0 => childM0 r phase lam H rho z

/-- E records divide the R-guard by p; D/H retain the literal R-guard. -/
def retainedRGuard (r : Row) (lam H v e : ℝ) : ℝ :=
  match r with
  | .D | .H => RGuard r lam H v e
  | .E1 | .E2 => RGuard r lam H v e / pH lam H

end
end F4Unified.LightConstruction
