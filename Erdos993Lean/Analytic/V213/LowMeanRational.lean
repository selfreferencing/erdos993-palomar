module

public import Erdos993Lean.Analytic.V213.LowMeanMonomialSupport
public import Erdos993Lean.Analytic.V213.LowMeanMeanMargin

/-!
The rationality assertion of Lemma 6.6. Every support, extremum,
and quadratic minimum is the real cast of its explicit rational formula.
These are semantic cast lemmas, not evaluations of finite certificate
families. Large finite checks use explicit Int/Nat denominators separately.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanQMonomial (c : ℚ) (a b : ℤ) (q : ℚ) : ℚ := c * q ^ a * (1 - q) ^ b
def lowMeanQMonomialD (c : ℚ) (a b : ℤ) (q : ℚ) : ℚ :=
  lowMeanQMonomial c a b q * ((a : ℚ) / q - (b : ℚ) / (1 - q))
def lowMeanQQuad (A B C x : ℚ) : ℚ := A * x ^ 2 + B * x + C
def lowMeanQQuadMinimum (A B C L H : ℚ) : ℚ :=
  min (lowMeanQQuad A B C L) (min (lowMeanQQuad A B C H)
    (if 0 < A ∧ L ≤ -B / (2 * A) ∧ -B / (2 * A) ≤ H
     then C - B ^ 2 / (4 * A) else lowMeanQQuad A B C L))
def lowMeanQPiA (c : ℚ) (a b : ℤ) : ℚ :=
  c / |c| * ((a + b : ℤ) : ℚ) * (((a + b : ℤ) : ℚ) - 1)
def lowMeanQPiB (c : ℚ) (a b : ℤ) : ℚ :=
  -2 * (c / |c|) * (a : ℚ) * (((a + b : ℤ) : ℚ) - 1)
def lowMeanQPiC (c : ℚ) (a : ℤ) : ℚ := c / |c| * (a : ℚ) * ((a : ℚ) - 1)
def lowMeanQPiMin (c : ℚ) (a b : ℤ) (L H : ℚ) : ℚ :=
  lowMeanQQuadMinimum (lowMeanQPiA c a b) (lowMeanQPiB c a b) (lowMeanQPiC c a) L H
def lowMeanQPiMax (c : ℚ) (a b : ℤ) (L H : ℚ) : ℚ :=
  -lowMeanQQuadMinimum (-lowMeanQPiA c a b) (-lowMeanQPiB c a b) (-lowMeanQPiC c a) L H
def lowMeanQMonomialR (c : ℚ) (a b : ℤ) (L H : ℚ) : ℚ :=
  max |lowMeanQMonomial c a b L| (max |lowMeanQMonomial c a b H|
    (if 0 < a + b ∧ L ≤ (a : ℚ) / ((a + b : ℤ) : ℚ) ∧
        (a : ℚ) / ((a + b : ℤ) : ℚ) ≤ H
     then |lowMeanQMonomial c a b ((a : ℚ) / ((a + b : ℤ) : ℚ))|
     else |lowMeanQMonomial c a b L|))
def lowMeanQLambda (c : ℚ) (a b : ℤ) (L H : ℚ) : ℚ :=
  lowMeanQPiMin c a b L H * lowMeanQMonomialR c a b L H /
    min (L * (1 - L)) (H * (1 - H)) ^ 2
def lowMeanQSupport (c : ℚ) (a b : ℤ) (L H tau q : ℚ) : ℚ :=
  if lowMeanQPiMax c a b L H ≤ 0 then
    (H - q) / (H - L) * lowMeanQMonomial c a b L +
      (q - L) / (H - L) * lowMeanQMonomial c a b H
  else if 0 ≤ lowMeanQPiMin c a b L H then
    lowMeanQMonomial c a b tau + lowMeanQMonomialD c a b tau * (q - tau)
  else
    lowMeanQMonomial c a b tau + lowMeanQMonomialD c a b tau * (q - tau) +
      lowMeanQLambda c a b L H / 2 * (q - tau) ^ 2

@[simp] theorem lowMeanQMonomial_cast (c : ℚ) (a b : ℤ) (q : ℚ) :
    (lowMeanQMonomial c a b q : ℝ) = lowMeanMonomial c a b q := by
  simp [lowMeanQMonomial, lowMeanMonomial, Rat.cast_zpow]

@[simp] theorem lowMeanQMonomialD_cast (c : ℚ) (a b : ℤ) (q : ℚ) :
    (lowMeanQMonomialD c a b q : ℝ) = lowMeanMonomialD c a b q := by
  simp [lowMeanQMonomialD, lowMeanMonomialD]

@[simp] theorem lowMeanQQuad_cast (A B C x : ℚ) :
    (lowMeanQQuad A B C x : ℝ) = lowMeanQuad A B C x := by
  simp [lowMeanQQuad, lowMeanQuad]

@[simp] theorem lowMeanQQuadMinimum_cast (A B C L H : ℚ) :
    (lowMeanQQuadMinimum A B C L H : ℝ) = lowMeanQuadMinimum A B C L H := by
  have ht : (0 < A ∧ L ≤ -B / (2 * A) ∧ -B / (2 * A) ≤ H) ↔
      (0 < (A : ℝ) ∧ (L : ℝ) ≤ -(B : ℝ) / (2 * A) ∧ -(B : ℝ) / (2 * A) ≤ H) := by
    exact_mod_cast Iff.rfl
  by_cases hr : 0 < A ∧ L ≤ -B / (2 * A) ∧ -B / (2 * A) ≤ H
  · unfold lowMeanQQuadMinimum lowMeanQuadMinimum
    rw [ite_eq_left hr, ite_eq_left (ht.mp hr)]
    simp [Rat.cast_min]
  · have hs := mt ht.mpr hr
    unfold lowMeanQQuadMinimum lowMeanQuadMinimum
    rw [ite_eq_right hr, ite_eq_right hs]
    simp [Rat.cast_min]

@[simp] theorem lowMeanQPiA_cast (c : ℚ) (a b : ℤ) :
    (lowMeanQPiA c a b : ℝ) = lowMeanPiA c a b := by
  simp [lowMeanQPiA, lowMeanPiA]
@[simp] theorem lowMeanQPiB_cast (c : ℚ) (a b : ℤ) :
    (lowMeanQPiB c a b : ℝ) = lowMeanPiB c a b := by
  simp [lowMeanQPiB, lowMeanPiB]
@[simp] theorem lowMeanQPiC_cast (c : ℚ) (a : ℤ) :
    (lowMeanQPiC c a : ℝ) = lowMeanPiC c a := by
  simp [lowMeanQPiC, lowMeanPiC]
@[simp] theorem lowMeanQPiMin_cast (c : ℚ) (a b : ℤ) (L H : ℚ) :
    (lowMeanQPiMin c a b L H : ℝ) = lowMeanPiMin c a b L H := by
  simp [lowMeanQPiMin, lowMeanPiMin]
@[simp] theorem lowMeanQPiMax_cast (c : ℚ) (a b : ℤ) (L H : ℚ) :
    (lowMeanQPiMax c a b L H : ℝ) = lowMeanPiMax c a b L H := by
  simp [lowMeanQPiMax, lowMeanPiMax]
@[simp] theorem lowMeanQMonomialR_cast (c : ℚ) (a b : ℤ) (L H : ℚ) :
    (lowMeanQMonomialR c a b L H : ℝ) = lowMeanMonomialR c a b L H := by
  have ht : (0 < a + b ∧ L ≤ (a : ℚ) / ((a + b : ℤ) : ℚ) ∧
      (a : ℚ) / ((a + b : ℤ) : ℚ) ≤ H) ↔
      (0 < a + b ∧ (L : ℝ) ≤ (a : ℝ) / ((a + b : ℤ) : ℝ) ∧
      (a : ℝ) / ((a + b : ℤ) : ℝ) ≤ H) := by
    exact_mod_cast Iff.rfl
  by_cases hr : 0 < a + b ∧ L ≤ (a : ℚ) / ((a + b : ℤ) : ℚ) ∧
      (a : ℚ) / ((a + b : ℤ) : ℚ) ≤ H
  · unfold lowMeanQMonomialR lowMeanMonomialR
    rw [ite_eq_left hr, ite_eq_left (ht.mp hr)]
    simp [Rat.cast_max]
  · have hs := mt ht.mpr hr
    unfold lowMeanQMonomialR lowMeanMonomialR
    rw [ite_eq_right hr, ite_eq_right hs]
    simp [Rat.cast_max]

@[simp] theorem lowMeanQLambda_cast (c : ℚ) (a b : ℤ) (L H : ℚ) :
    (lowMeanQLambda c a b L H : ℝ) = lowMeanLambda c a b L H := by
  simp [lowMeanQLambda, lowMeanLambda, lowMeanVarianceMin, Rat.cast_min]
@[simp] theorem lowMeanQSupport_cast (c : ℚ) (a b : ℤ) (L H tau q : ℚ) :
    (lowMeanQSupport c a b L H tau q : ℝ) = lowMeanSupport c a b L H tau q := by
  have hmax : lowMeanQPiMax c a b L H ≤ 0 ↔ lowMeanPiMax (c : ℝ) a b L H ≤ 0 := by
    rw [← lowMeanQPiMax_cast]
    exact_mod_cast Iff.rfl
  have hmin : 0 ≤ lowMeanQPiMin c a b L H ↔ 0 ≤ lowMeanPiMin (c : ℝ) a b L H := by
    rw [← lowMeanQPiMin_cast]
    exact_mod_cast Iff.rfl
  by_cases hr : lowMeanQPiMax c a b L H ≤ 0
  · simp [lowMeanQSupport, lowMeanSupport, hr, hmax.mp hr]
  · have hr' := mt hmax.mpr hr
    by_cases hs : 0 ≤ lowMeanQPiMin c a b L H
    · simp [lowMeanQSupport, lowMeanSupport, hr, hr', hs, hmin.mp hs]
    · have hs' := mt hmin.mpr hs
      simp [lowMeanQSupport, lowMeanSupport, hr, hr', hs, hs']

/-- The final sentence of Lemma 6.6: all supports are rational at rational
data, including negative exponents and all curvature branches. -/
theorem lowMean_support_rational (c : ℚ) (a b : ℤ) (L H tau q : ℚ) :
    ∃ r : ℚ, (r : ℝ) = lowMeanSupport c a b L H tau q :=
  ⟨lowMeanQSupport c a b L H tau q, lowMeanQSupport_cast c a b L H tau q⟩

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanQSupport_cast
#print axioms Erdos993Lean.Analytic.V213.lowMean_support_rational
