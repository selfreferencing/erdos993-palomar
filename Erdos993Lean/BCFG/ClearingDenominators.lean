module

public import Erdos993Lean.BCFG.ChartDefinitions

/-! Positive clearing factors from T6b Eq.(15).
This file contains no polynomial coefficient array or analytic clearing equality. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

def heavyA (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  1+lam+lam*v^(heavyExponent r)
def heavyE (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  (1+lam)^2+lam*v^(heavyExponent r)
def heavyB (r : AnalyticRow) (lam v : ℝ) : ℝ :=
  (1+lam)*v^(heavyExponent r)*(1+v)^2
def lightB (lam x : ℝ) : ℝ := 1+lam-lam*x
def lightC (lam x : ℝ) : ℝ := 2+2*lam-lam*x
def lightA (lam x : ℝ) : ℝ := (1+lam)^2-lam^2*x
def lightE (lam x : ℝ) : ℝ := (1+lam)*(1+2*lam)-lam^2*x

def clearingDenominator (r : AnalyticRow) (f : DeterminantFunction)
    (lam y : ℝ) : ℝ :=
  match f with
  | .H0 | .H1 => heavyB r lam y*(heavyA r lam y)^3*(heavyE r lam y)^3
  | .H3 => heavyB r lam y*(heavyA r lam y)^4
  | .H2 => heavyB r lam y*(heavyA r lam y)^4*(heavyE r lam y)^3
  | .J => lightB lam y*(lightC lam y)^3*(lightE lam y)^3*(lightA lam y)^4
  | .C0 | .C1 => (1+lam)^2*
      (lightB lam y*(lightC lam y)^3*(lightE lam y)^3*(lightA lam y)^4)

def clearingFactor (f : DeterminantFunction) (lam : ℝ) : ℝ :=
  match f with
  | .J => lam
  | _ => 1

theorem heavyA_pos {r : AnalyticRow} {lam v : ℝ} (hl : 0 < lam) (hv : 0 < v) :
    0 < heavyA r lam v := by
  unfold heavyA
  positivity

theorem heavyE_pos {r : AnalyticRow} {lam v : ℝ} (hl : 0 < lam) (hv : 0 < v) :
    0 < heavyE r lam v := by
  unfold heavyE
  positivity

theorem heavyB_pos {r : AnalyticRow} {lam v : ℝ} (hl : 0 < lam) (hv : 0 < v) :
    0 < heavyB r lam v := by
  unfold heavyB
  positivity

/-- The four printed lower factor bounds hold even on the closed leaf face. -/
theorem light_factor_lower_bounds {lam x : ℝ} (hl : 0 < lam) (hx : x ≤ 1) :
    1 ≤ lightB lam x ∧ 2+lam ≤ lightC lam x ∧
      1+2*lam ≤ lightA lam x ∧
      1+3*lam+lam^2 ≤ lightE lam x := by
  have h1 : 0 ≤ lam*(1-x) := mul_nonneg hl.le (sub_nonneg.mpr hx)
  have h2 : 0 ≤ lam^2*(1-x) := mul_nonneg (sq_nonneg lam) (sub_nonneg.mpr hx)
  unfold lightB lightC lightA lightE
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem light_factors_pos {lam x : ℝ} (hl : 0 < lam) (hx : x ≤ 1) :
    0 < lightB lam x ∧ 0 < lightC lam x ∧
      0 < lightA lam x ∧ 0 < lightE lam x := by
  obtain ⟨hB,hC,hA,hE⟩ := light_factor_lower_bounds hl hx
  refine ⟨lt_of_lt_of_le (by norm_num) hB, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith) hC
  · exact lt_of_lt_of_le (by linarith) hA
  · exact lt_of_lt_of_le (by positivity) hE

theorem clearingDenominator_pos {r : AnalyticRow} {f : DeterminantFunction}
    {lam y : ℝ} (h : FunctionDomain r f lam y) :
    0 < clearingDenominator r f lam y := by
  cases f with
  | H0 | H1 | H2 | H3 =>
      have hr : HeavyDomain r lam y := h
      have hl := activity_pos hr.1
      have hy : 0 < y := lt_of_lt_of_le (by norm_num) hr.2.1
      have hA := heavyA_pos (r := r) hl hy
      have hE := heavyE_pos (r := r) hl hy
      have hB := heavyB_pos (r := r) hl hy
      simp only [clearingDenominator]
      positivity
  | J | C0 | C1 =>
      have hr : LightDomain r lam y := h
      have hl := activity_pos hr.1
      obtain ⟨hB,hC,hA,hE⟩ := light_factors_pos hl hr.2.2
      simp only [clearingDenominator]
      positivity

theorem clearingFactor_pos {r : AnalyticRow} {f : DeterminantFunction}
    {lam y : ℝ} (h : FunctionDomain r f lam y) :
    0 < clearingFactor f lam := by
  cases f <;> simp only [clearingFactor]
  all_goals first | exact activity_pos h.1 | norm_num

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavyA
#print axioms Erdos993Lean.BCFG.Analytic.heavyA
#check Erdos993Lean.BCFG.Analytic.heavyE
#print axioms Erdos993Lean.BCFG.Analytic.heavyE
#check Erdos993Lean.BCFG.Analytic.heavyB
#print axioms Erdos993Lean.BCFG.Analytic.heavyB
#check Erdos993Lean.BCFG.Analytic.lightB
#print axioms Erdos993Lean.BCFG.Analytic.lightB
#check Erdos993Lean.BCFG.Analytic.lightC
#print axioms Erdos993Lean.BCFG.Analytic.lightC
#check Erdos993Lean.BCFG.Analytic.lightA
#print axioms Erdos993Lean.BCFG.Analytic.lightA
#check Erdos993Lean.BCFG.Analytic.lightE
#print axioms Erdos993Lean.BCFG.Analytic.lightE
#check Erdos993Lean.BCFG.Analytic.clearingDenominator
#print axioms Erdos993Lean.BCFG.Analytic.clearingDenominator
#check Erdos993Lean.BCFG.Analytic.clearingFactor
#print axioms Erdos993Lean.BCFG.Analytic.clearingFactor
#check Erdos993Lean.BCFG.Analytic.heavyA_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavyA_pos
#check Erdos993Lean.BCFG.Analytic.heavyE_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavyE_pos
#check Erdos993Lean.BCFG.Analytic.heavyB_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavyB_pos
#check Erdos993Lean.BCFG.Analytic.light_factor_lower_bounds
#print axioms Erdos993Lean.BCFG.Analytic.light_factor_lower_bounds
#check Erdos993Lean.BCFG.Analytic.light_factors_pos
#print axioms Erdos993Lean.BCFG.Analytic.light_factors_pos
#check Erdos993Lean.BCFG.Analytic.clearingDenominator_pos
#print axioms Erdos993Lean.BCFG.Analytic.clearingDenominator_pos
#check Erdos993Lean.BCFG.Analytic.clearingFactor_pos
#print axioms Erdos993Lean.BCFG.Analytic.clearingFactor_pos
