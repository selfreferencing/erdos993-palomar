module

public import Mathlib

/-! Tong Zhang's `F4_contract.lean` (unified F4, 7 October 2026), unchanged except for this module header, the
line `@[expose] public section` below, which Lean's module system requires, and one comment brought up to date. -/

@[expose] public section

/-!
F4 unified interface specification, 2026-10-07.

This file contains DEFINITIONS and target propositions, not proofs of the four
regional theorems. No axiom or `sorry` is used. The targets are proved in
`F4Heavy/Targets.lean` and `F4Heavy/TargetsRegional.lean`.

F4_final.tex defines LightFinite, whose finite sign rules imply LightCore here.
The split keeps finite certificate details private. LocalEvidence is an explicit
proof-dependency record, not an assertion that any field has been inhabited.
-/

namespace F4Unified
noncomputable section
open scoped BigOperators

inductive Row where
  | D | E1 | E2 | H
  deriving DecidableEq, Repr

structure RowData where
  lo : ℝ
  hi : ℝ
  price : ℝ
  center : ℝ
  alpha0 : ℝ
  alpha1 : ℝ
  beta0 : ℝ
  beta1 : ℝ
  gamma0 : ℝ
  gamma1 : ℝ
  delta0 : ℝ
  delta1 : ℝ
  xMin : ℝ

def rowData : Row → RowData
  | .D => ⟨4/5, 13/10, 8/5, 269/256,
      46809, 3327, 35136, 3086, 14520, 13694, 1835, 1340, 5/16⟩
  | .E1 => ⟨13/10, 29/20, 17/10, 11/8,
      44917, 29958, 28533, 57271, 17821, 20483, 3064, -4423, 1/4⟩
  | .E2 => ⟨29/20, 8/5, 17/10, 195/128,
      45775, 22238, 30825, 10297, 19913, 13978, 3161, 4340, 1/4⟩
  | .H => ⟨7/4, 7/3, 2, 523/256,
      51799, 8158, 20496, 41265, 29750, 4333, 9083, -11181, 1/4⟩

def field (m0 m1 ctr lam : ℝ) : ℝ := (m0 + m1 * (lam - ctr)) / 65536
def alpha (r : Row) (lam : ℝ) : ℝ :=
  field (rowData r).alpha0 (rowData r).alpha1 (rowData r).center lam
def beta (r : Row) (lam : ℝ) : ℝ :=
  field (rowData r).beta0 (rowData r).beta1 (rowData r).center lam
def gamma (r : Row) (lam : ℝ) : ℝ :=
  field (rowData r).gamma0 (rowData r).gamma1 (rowData r).center lam
def delta (r : Row) (lam : ℝ) : ℝ :=
  field (rowData r).delta0 (rowData r).delta1 (rowData r).center lam

def InRow (r : Row) (lam : ℝ) : Prop := (rowData r).lo ≤ lam ∧ lam ≤ (rowData r).hi
def q (lam : ℝ) : ℝ := lam / (1 + lam)
def p (lam Y : ℝ) : ℝ := lam * Real.exp (-Y) / (1 + lam * Real.exp (-Y))
def lowerVacancy (lam Y : ℝ) : ℝ := 1 / (1 + lam * (1 - p lam Y))
def FeasibleVacancy (lam Y rho : ℝ) : Prop := lowerVacancy lam Y ≤ rho ∧ rho ≤ 1
def parentH (Y : ℝ) : ℝ := 1 - Real.exp (-Y)
def childCap (lam Y : ℝ) : ℝ := min (q lam) (parentH Y)
def parentX (lam Y : ℝ) : ℝ := (1 + lam) * Real.exp (-Y)

def phi (u : ℝ) : ℝ := if u = 0 then 0 else -Real.log (1 - u)
def childH (u : ℝ) : ℝ := if u = 0 then 1 else u / phi u
def childJ (lam u : ℝ) : ℝ :=
  if u = 0 then 0 else u * childH u * Real.log (lam * (1 - u) / u)
def Admissible (lam u y : ℝ) : Prop :=
  0 < childJ lam u ∨ (childJ lam u = 0 ∧ y = childH u)
def reserve (r : Row) (lam u y : ℝ) : ℝ :=
  if 0 < childJ lam u then delta r lam * (childH u - y)^2 / childJ lam u else 0

def f (lam t : ℝ) : ℝ :=
  max ((1 + q lam) / (2 * q lam) * t)
      ((1 + q lam) / (2 * (q lam)^2) * t + (q lam - 1) / (2 * q lam))
def source (lam Y rho : ℝ) : ℝ :=
  (1 + f lam (p lam Y * rho) -
    f lam (max (1 - rho) ((1 - p lam Y * rho) * childCap lam Y))) / 2
def parentP (r : Row) (lam Y rho : ℝ) : ℝ :=
  rho * (1 - p lam Y) + gamma r lam * p lam Y / (-Real.log (1 - p lam Y))
def parentN (r : Row) (lam Y rho : ℝ) : ℝ :=
  (rowData r).price / (1 + lam) * rho * source lam Y rho +
    alpha r lam * (1 - rho) - parentP r lam Y rho
def payment (r : Row) (lam Y rho u y : ℝ) : ℝ :=
  p lam Y * parentN r lam Y rho / Y +
  p lam Y * beta r lam * rho * childH u +
  p lam Y * (2 * parentP r lam Y rho - alpha r lam - beta r lam) * y +
  (gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho) * y^2 +
  reserve r lam u y

-- The total Lean expression is only used on this specified mathematical domain.
def PairDomain (r : Row) (lam Y rho u y : ℝ) : Prop :=
  InRow r lam ∧ 0 < Y ∧ FeasibleVacancy lam Y rho ∧
    0 ≤ u ∧ u ≤ childCap lam Y ∧ Admissible lam u y
def PairPositive (r : Row) : Prop :=
  ∀ lam Y rho u y, PairDomain r lam Y rho u y → 0 < payment r lam Y rho u y
def MinAt (r : Row) (lam Y rho u m : ℝ) : Prop :=
  (∀ y, Admissible lam u y → m ≤ payment r lam Y rho u y) ∧
  (∃ y, Admissible lam u y ∧ payment r lam Y rho u y = m)

def HalfLight (r : Row) : Prop :=
  ∀ lam Y rho, InRow r lam → 0 < Y → parentH Y ≤ q lam / 2 →
    FeasibleVacancy lam Y rho →
    ∃ m, MinAt r lam Y rho (parentH Y) m ∧ 0 < m

-- All parent arguments, including source, remain fixed as u varies.
def FixedParentCap (r : Row) : Prop :=
  ∀ lam Y rho, InRow r lam → 0 < Y → parentH Y ≤ q lam →
    FeasibleVacancy lam Y rho →
    ∃ m, MinAt r lam Y rho (min (parentH Y) (q lam / 2)) m ∧
      ∀ u y, 0 ≤ u → u ≤ min (parentH Y) (q lam / 2) → Admissible lam u y →
        m + (min (parentH Y) (q lam / 2) - u) / 1000 ≤ payment r lam Y rho u y

-- Derived from the explicit LightFinite certificate specification in the text.
def LightCore (r : Row) : Prop :=
  ∀ lam Y rho u, InRow r lam → 0 < Y → parentH Y ≤ q lam →
    FeasibleVacancy lam Y rho → q lam / 2 ≤ u → u ≤ parentH Y →
    ∃ m, MinAt r lam Y rho u m ∧ 0 < m

def CompactHeavy (r : Row) : Prop :=
  ∀ lam Y rho u y, PairDomain r lam Y rho u y →
    (rowData r).xMin ≤ parentX lam Y → parentX lam Y ≤ 1 →
    0 < payment r lam Y rho u y
def TailPositive (r : Row) : Prop :=
  ∀ lam Y rho u y, PairDomain r lam Y rho u y →
    parentX lam Y ≤ (rowData r).xMin → 0 < payment r lam Y rho u y

structure LocalEvidence (r : Row) : Prop where
  boundary : HalfLight r
  cap : FixedParentCap r
  light : LightCore r
  compact : CompactHeavy r
  tail : TailPositive r

-- Four public target propositions. They are not theorem declarations.
def F4_D : Prop := PairPositive .D
def F4_E1 : Prop := PairPositive .E1
def F4_E2 : Prop := PairPositive .E2
def F4_H : Prop := PairPositive .H

-- Correct nonleaf vertex data require positive total message mass.
def VertexGoal (r : Row) : Prop :=
  ∀ (n : ℕ) (lam Y rho : ℝ) (u y : Fin n → ℝ),
    InRow r lam → 0 < Y → FeasibleVacancy lam Y rho →
    (∑ i, phi (u i)) = Y →
    (∀ i, 0 ≤ u i ∧ u i ≤ childCap lam Y ∧ Admissible lam (u i) (y i)) →
    0 < (∑ i, phi (u i) * payment r lam Y rho (u i) (y i)) +
      (p lam Y * parentP r lam Y rho + delta r lam / Y) *
      ∑ i, ∑ j, (if i < j then phi (u i) * phi (u j) * (y i - y j)^2 else 0)

-- Y=0 has its own expression, never payment with a division by zero.
def LeafPositive (r : Row) : Prop :=
  ∀ lam rho, InRow r lam → FeasibleVacancy lam 0 rho →
    0 < q lam * parentN r lam 0 rho

end
end F4Unified
