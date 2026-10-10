module

public import Erdos993Lean.Analytic.V213.LowMeanKernelMonomials
public import Erdos993Lean.Analytic.V213.LowMeanRational

/-!
Semantic coefficients for equation r12:eq58. The explicit A,B,C below
are proved to represent the support at every real q, including irrational
points. This connects arithmetic coefficient checks to interval positivity.
No finite generated family is consumed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanSupportA (c : ℝ) (a b : ℤ) (L H : ℝ) : ℝ :=
  if lowMeanPiMax c a b L H ≤ 0 then 0
  else if 0 ≤ lowMeanPiMin c a b L H then 0
  else lowMeanLambda c a b L H / 2
noncomputable def lowMeanSupportB (c : ℝ) (a b : ℤ) (L H tau : ℝ) : ℝ :=
  if lowMeanPiMax c a b L H ≤ 0 then
    (lowMeanMonomial c a b H - lowMeanMonomial c a b L) / (H - L)
  else if 0 ≤ lowMeanPiMin c a b L H then lowMeanMonomialD c a b tau
  else lowMeanMonomialD c a b tau - lowMeanLambda c a b L H * tau
noncomputable def lowMeanSupportC (c : ℝ) (a b : ℤ) (L H tau : ℝ) : ℝ :=
  if lowMeanPiMax c a b L H ≤ 0 then
    (H * lowMeanMonomial c a b L - L * lowMeanMonomial c a b H) / (H - L)
  else if 0 ≤ lowMeanPiMin c a b L H then
    lowMeanMonomial c a b tau - lowMeanMonomialD c a b tau * tau
  else lowMeanMonomial c a b tau - lowMeanMonomialD c a b tau * tau +
    lowMeanLambda c a b L H / 2 * tau ^ 2

theorem lowMean_support_coefficients (c : ℝ) (a b : ℤ) (L H tau q : ℝ) :
    lowMeanSupport c a b L H tau q = lowMeanQuad
      (lowMeanSupportA c a b L H) (lowMeanSupportB c a b L H tau)
      (lowMeanSupportC c a b L H tau) q := by
  unfold lowMeanSupport lowMeanSupportA lowMeanSupportB lowMeanSupportC lowMeanQuad
  split_ifs <;> ring

theorem lowMean_sum_support_coefficients (terms : List (ℝ × ℤ × ℤ)) (L H tau q : ℝ) :
    (terms.map fun t => lowMeanSupport t.1 t.2.1 t.2.2 L H tau q).sum =
      lowMeanQuad
        (terms.map fun t => lowMeanSupportA t.1 t.2.1 t.2.2 L H).sum
        (terms.map fun t => lowMeanSupportB t.1 t.2.1 t.2.2 L H tau).sum
        (terms.map fun t => lowMeanSupportC t.1 t.2.1 t.2.2 L H tau).sum q := by
  induction terms with
  | nil => simp [lowMeanQuad]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [lowMean_support_coefficients, ih]
    unfold lowMeanQuad
    ring

noncomputable def lowMeanBudgetA (terms : List (ℝ × ℤ × ℤ)) (M : ℕ) (eta L H : ℝ) : ℝ :=
  eta * (M : ℝ) ^ 2 + (terms.map fun t => lowMeanSupportA t.1 t.2.1 t.2.2 L H).sum
noncomputable def lowMeanBudgetB (terms : List (ℝ × ℤ × ℤ)) (M : ℕ) (j : ℤ) (eta xi L H tau : ℝ) : ℝ :=
  -2 * eta * j * M - xi * M + (terms.map fun t => lowMeanSupportB t.1 t.2.1 t.2.2 L H tau).sum
noncomputable def lowMeanBudgetC (terms : List (ℝ × ℤ × ℤ)) (M : ℕ) (j : ℤ)
    (eta xi alpha beta gamma m0 zeta L H tau : ℝ) : ℝ :=
  eta * (j : ℝ) ^ 2 + xi * j - lowMeanPsi alpha beta gamma m0 M - zeta +
    (terms.map fun t => lowMeanSupportC t.1 t.2.1 t.2.2 L H tau).sum

/-- Equation r12:eq58 with explicit coefficients rather than existential
polynomial witnesses. -/
theorem lowMean_budget_coefficients (terms : List (ℝ × ℤ × ℤ)) (M : ℕ) (j : ℤ)
    (eta xi alpha beta gamma m0 zeta L H tau q : ℝ) :
    eta * ((j : ℝ) - M * q) ^ 2 + xi * ((j : ℝ) - M * q) -
        lowMeanPsi alpha beta gamma m0 M - zeta +
        (terms.map fun t => lowMeanSupport t.1 t.2.1 t.2.2 L H tau q).sum =
      lowMeanQuad (lowMeanBudgetA terms M eta L H) (lowMeanBudgetB terms M j eta xi L H tau)
        (lowMeanBudgetC terms M j eta xi alpha beta gamma m0 zeta L H tau) q := by
  rw [lowMean_sum_support_coefficients]
  unfold lowMeanBudgetA lowMeanBudgetB lowMeanBudgetC lowMeanQuad
  ring

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_support_coefficients
#print axioms Erdos993Lean.Analytic.V213.lowMean_budget_coefficients
