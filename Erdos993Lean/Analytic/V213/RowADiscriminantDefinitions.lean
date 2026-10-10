module

public import Erdos993Lean.Analytic.V213.RowABernstein
public import Erdos993Lean.Analytic.V213.RowAScaleRecords

/-!
Literal discriminants and Pi factors of Row A Step 4. The substitution identities
are algebraic kernel claims. No unprinted rational coefficient array is created.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

noncomputable def discriminant (kappa tau nu sigma0 q0 x : ℝ) (j : Fin 3) : ℝ :=
  4*bernsteinK kappa nu q0 x j*bernsteinM kappa tau sigma0 x j-
    (13/6-2*kappa)^2
noncomputable def discriminantMinus (x : ℝ) (j : Fin 3) : ℝ :=
  discriminant (kappaMinus x) (tauMinus x) (nuMinus x) (15/16) (1/4) x j
noncomputable def discriminantPlus (x : ℝ) (j : Fin 3) : ℝ :=
  discriminant (kappaPlus x) (tauPlus x) (nuPlus x) (55/64) (3/8) x j
noncomputable def piMinus (x : ℝ) : ℝ :=
  (1-x)*(x+2)^3*(4+28*x-5*x^2)
noncomputable def piPlus (x : ℝ) : ℝ :=
  (1-x)*(x+4)^3*(16+88*x-29*x^2)
noncomputable def fractionalX (t : ℝ) : ℝ := t/(1+t)

theorem fractionalX_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ fractionalX t ∧ fractionalX t < 1 := by
  have hu : 0 < 1+t := by linarith
  unfold fractionalX
  exact ⟨div_nonneg ht hu.le,(div_lt_iff₀ hu).2 (by linarith)⟩

theorem fractionalX_inverse {x : ℝ} (hx : x < 1) :
    fractionalX (x/(1-x)) = x := by
  have hd : 1-x ≠ 0 := by linarith
  have hu : 1+x/(1-x) = 1/(1-x) := by
    field_simp [hd]
    ring
  unfold fractionalX
  rw [hu]
  field_simp [hd]

theorem minus_factor_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < 4+28*x-5*x^2 := by
  have hxx : x^2 ≤ x := by nlinarith
  nlinarith

theorem plus_factor_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < 16+88*x-29*x^2 := by
  have hxx : x^2 ≤ x := by nlinarith
  nlinarith

theorem piMinus_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) : 0 < piMinus x := by
  unfold piMinus
  exact mul_pos (mul_pos (sub_pos.mpr hx1) (pow_pos (by linarith) _))
    (minus_factor_pos hx hx1)

theorem piPlus_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) : 0 < piPlus x := by
  unfold piPlus
  exact mul_pos (mul_pos (sub_pos.mpr hx1) (pow_pos (by linarith) _))
    (plus_factor_pos hx hx1)

theorem kappaMinus_fractional {t : ℝ} (ht : 0 ≤ t) :
    kappaMinus (fractionalX t) =
      21*(4+3*t)*(2+3*t)*(1+t)/(20*(4+36*t+27*t^2)) := by
  have hu : 0 < 1+t := by linarith
  have hA : 0 < 4+36*t+27*t^2 := by positivity
  have hx := fractionalX_bounds ht
  have hf := minus_factor_pos hx.1 hx.2
  unfold kappaMinus fractionalX at *
  field_simp [hu.ne',hA.ne',hf.ne']
  ring_nf
  have hP : 4+t*36+t^2*27≠0 := by positivity
  linear_combination (8+18*t+9*t^2)*(mul_inv_cancel₀ hP)

theorem kappaPlus_fractional {t : ℝ} (ht : 0 ≤ t) :
    kappaPlus (fractionalX t) =
      21*(8+5*t)*(4+5*t)*(1+t)/(20*(16+120*t+75*t^2)) := by
  have hu : 0 < 1+t := by linarith
  have hA : 0 < 16+120*t+75*t^2 := by positivity
  have hx := fractionalX_bounds ht
  have hf := plus_factor_pos hx.1 hx.2
  unfold kappaPlus fractionalX at *
  field_simp [hu.ne',hA.ne',hf.ne']
  ring_nf
  have hP : 16+t*120+t^2*75≠0 := by positivity
  linear_combination (32+60*t+25*t^2)*(mul_inv_cancel₀ hP)

theorem tauMinus_fractional {t : ℝ} (ht : 0 ≤ t) :
    tauMinus (fractionalX t) =
      (7*(343/400)/3)*(2/(2+3*t)+(2/(2+3*t))^3/3) := by
  have hu : 0 < 1+t := by linarith
  have hd : 0 < 2+3*t := by linarith
  unfold tauMinus fractionalX
  field_simp [hu.ne',hd.ne']
  ring

theorem tauPlus_fractional {t : ℝ} (ht : 0 ≤ t) :
    tauPlus (fractionalX t) =
      (7*(319/400)/3)*(4/(4+5*t)+(4/(4+5*t))^3/3) := by
  have hu : 0 < 1+t := by linarith
  have hd : 0 < 4+5*t := by linarith
  unfold tauPlus fractionalX
  field_simp [hu.ne',hd.ne']
  ring

theorem piMinus_fractional {t : ℝ} (ht : 0 ≤ t) :
    piMinus (fractionalX t) =
      (2+3*t)^3*(4+36*t+27*t^2)/(1+t)^6 := by
  have hu : 0 < 1+t := by linarith
  unfold piMinus fractionalX
  field_simp [hu.ne']
  ring

theorem piPlus_fractional {t : ℝ} (ht : 0 ≤ t) :
    piPlus (fractionalX t) =
      (4+5*t)^3*(16+120*t+75*t^2)/(1+t)^6 := by
  have hu : 0 < 1+t := by linarith
  unfold piPlus fractionalX
  field_simp [hu.ne']
  ring

theorem one_sub_fractional {t : ℝ} (ht : 0 ≤ t) :
    1-fractionalX t = 1/(1+t) := by
  have hu : 0 < 1+t := by linarith
  unfold fractionalX
  field_simp [hu.ne']
  ring

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piMinus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piMinus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piPlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piPlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fractionalX
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fractionalX
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fractionalX_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fractionalX_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fractionalX_inverse
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.fractionalX_inverse
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.minus_factor_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.minus_factor_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.plus_factor_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.plus_factor_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piMinus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piMinus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piPlus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piPlus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus_fractional
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus_fractional
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauMinus_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauMinus_fractional
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauPlus_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauPlus_fractional
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piMinus_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piMinus_fractional
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piPlus_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.piPlus_fractional
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.one_sub_fractional
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.one_sub_fractional
