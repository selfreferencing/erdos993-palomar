module

public import Erdos993Lean.Analytic.V213.LowMeanMonomialExtrema
public import Erdos993Lean.Analytic.V213.LowMeanQuadratic
public import Erdos993Lean.Analytic.V213.LowMeanTaylor

/-!
The signed-monomial support inequality of Lemma 6.6 of version 2.13 of the manuscript
(`r12:lem13`), equation `r12:eq57`. Extrema are computed from the finite
endpoint/vertex and endpoint/mode rules, rather than supplied as premises.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanPiA (c : ℝ) (a b : ℤ) : ℝ :=
  c / |c| * ((a + b : ℤ) : ℝ) * (((a + b : ℤ) : ℝ) - 1)
noncomputable def lowMeanPiB (c : ℝ) (a b : ℤ) : ℝ :=
  -2 * (c / |c|) * (a : ℝ) * (((a + b : ℤ) : ℝ) - 1)
noncomputable def lowMeanPiC (c : ℝ) (a : ℤ) : ℝ :=
  c / |c| * (a : ℝ) * ((a : ℝ) - 1)

theorem lowMeanPi_quad (c : ℝ) (a b : ℤ) (q : ℝ) :
    c / |c| * lowMeanPi a b q =
      lowMeanQuad (lowMeanPiA c a b) (lowMeanPiB c a b) (lowMeanPiC c a) q := by
  unfold lowMeanPi lowMeanQuad lowMeanPiA lowMeanPiB lowMeanPiC
  ring

noncomputable def lowMeanPiMin (c : ℝ) (a b : ℤ) (L H : ℝ) : ℝ :=
  lowMeanQuadMinimum (lowMeanPiA c a b) (lowMeanPiB c a b) (lowMeanPiC c a) L H
noncomputable def lowMeanPiMax (c : ℝ) (a b : ℤ) (L H : ℝ) : ℝ :=
  -lowMeanQuadMinimum (-lowMeanPiA c a b) (-lowMeanPiB c a b) (-lowMeanPiC c a) L H

theorem lowMeanPiMin_le (c : ℝ) (a b : ℤ) {L H q : ℝ}
    (hLH : L < H) (hq : q ∈ Set.Icc L H) :
    lowMeanPiMin c a b L H ≤ c / |c| * lowMeanPi a b q := by
  rw [lowMeanPi_quad]
  exact lowMeanQuadMinimum_le hLH hq

theorem lowMeanPiMax_ge (c : ℝ) (a b : ℤ) {L H q : ℝ}
    (hLH : L < H) (hq : q ∈ Set.Icc L H) :
    c / |c| * lowMeanPi a b q ≤ lowMeanPiMax c a b L H := by
  have hh := lowMeanQuadMinimum_le (A := -lowMeanPiA c a b)
    (B := -lowMeanPiB c a b) (C := -lowMeanPiC c a) hLH hq
  rw [lowMeanPi_quad]
  unfold lowMeanPiMax lowMeanQuad at *
  linarith

theorem lowMeanPiMin_attained (c : ℝ) (a b : ℤ) {L H : ℝ} (hLH : L < H) :
    ∃ q ∈ Set.Icc L H, c / |c| * lowMeanPi a b q = lowMeanPiMin c a b L H := by
  obtain ⟨q, hq, he⟩ := lowMeanQuadMinimum_attained
    (A := lowMeanPiA c a b) (B := lowMeanPiB c a b) (C := lowMeanPiC c a) hLH
  exact ⟨q, hq, by rw [lowMeanPi_quad]; exact he⟩

theorem lowMeanPiMax_attained (c : ℝ) (a b : ℤ) {L H : ℝ} (hLH : L < H) :
    ∃ q ∈ Set.Icc L H, c / |c| * lowMeanPi a b q = lowMeanPiMax c a b L H := by
  obtain ⟨q, hq, he⟩ := lowMeanQuadMinimum_attained
    (A := -lowMeanPiA c a b) (B := -lowMeanPiB c a b) (C := -lowMeanPiC c a) hLH
  refine ⟨q, hq, ?_⟩
  rw [lowMeanPi_quad]
  unfold lowMeanPiMax lowMeanQuad at *
  linarith

noncomputable def lowMeanVarianceMin (L H : ℝ) : ℝ := min (L * (1 - L)) (H * (1 - H))
noncomputable def lowMeanLambda (c : ℝ) (a b : ℤ) (L H : ℝ) : ℝ :=
  lowMeanPiMin c a b L H * lowMeanMonomialR c a b L H / lowMeanVarianceMin L H ^ 2

/-- Exactly the three branches of equation r12:eq57. -/
noncomputable def lowMeanSupport (c : ℝ) (a b : ℤ) (L H tau q : ℝ) : ℝ :=
  if lowMeanPiMax c a b L H ≤ 0 then
    (H - q) / (H - L) * lowMeanMonomial c a b L +
      (q - L) / (H - L) * lowMeanMonomial c a b H
  else if 0 ≤ lowMeanPiMin c a b L H then
    lowMeanMonomial c a b tau + lowMeanMonomialD c a b tau * (q - tau)
  else
    lowMeanMonomial c a b tau + lowMeanMonomialD c a b tau * (q - tau) +
      lowMeanLambda c a b L H / 2 * (q - tau) ^ 2

/-- Lemma 6.6, including negative exponents, a+b=0, degenerate Pi, all three
curvature cases, and anchors at either endpoint. -/
theorem lowMean_signedMonomial_support {c L H tau q : ℝ} (hc : c ≠ 0)
    (a b : ℤ) (hm : 0 ≤ a + b) (hL : 0 < L) (hH : H < 1) (hLH : L < H)
    (htau : tau ∈ Set.Icc L H) (hq : q ∈ Set.Icc L H) :
    lowMeanSupport c a b L H tau q ≤ lowMeanMonomial c a b q := by
  have hx0 x (hx : x ∈ Set.Icc L H) : 0 < x := lt_of_lt_of_le hL hx.1
  have hx1 x (hx : x ∈ Set.Icc L H) : x < 1 := lt_of_le_of_lt hx.2 hH
  have hd x (hx : x ∈ Set.Icc L H) := lowMeanMonomial_hasDerivAt c a b (hx0 x hx) (hx1 x hx)
  have hdd x (hx : x ∈ Set.Icc L H) := lowMeanMonomialD_hasDerivAt c a b (hx0 x hx) (hx1 x hx)
  have hf : ContinuousOn (lowMeanMonomial c a b) (Set.Icc L H) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  unfold lowMeanSupport
  split_ifs with hconc hconv
  · apply lowMean_concave_chord hLH ?_ hq
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc L H) hf
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hdd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Set.Icc L H := interior_subset hx
    rw [lowMeanMonomialDD_signed hc a b (hx0 x hx') (hx1 x hx')]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
        (le_trans (lowMeanPiMax_ge c a b hLH hx') hconc))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · have hbound : ∀ x ∈ Set.Icc L H, 0 ≤ lowMeanMonomialDD c a b x := by
      intro x hx
      rw [lowMeanMonomialDD_signed hc a b (hx0 x hx) (hx1 x hx)]
      exact div_nonneg (mul_nonneg (abs_nonneg _)
        (le_trans hconv (lowMeanPiMin_le c a b hLH hx)))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    simpa using lowMean_quadratic_support hf hd hdd hbound htau hq
  · have hvmin : 0 < lowMeanVarianceMin L H := by
      apply lt_min
      · exact mul_pos hL (sub_pos.mpr (lt_trans hLH hH))
      · exact mul_pos (lt_trans hL hLH) (sub_pos.mpr hH)
    have hbound : ∀ x ∈ Set.Icc L H, lowMeanLambda c a b L H ≤ lowMeanMonomialDD c a b x := by
      intro x hx
      rw [lowMeanMonomialDD_signed hc a b (hx0 x hx) (hx1 x hx)]
      have hh := lowMean_curvature_bound (abs_nonneg (lowMeanMonomial c a b x))
        (lowMeanMonomialR_bound c a b hm hL hH hLH.le hx)
        (le_of_lt (lt_of_not_ge hconv)) (lowMeanPiMin_le c a b hLH hx)
        hvmin (lowMean_variance_min hLH hx)
      simpa only [lowMeanLambda, mul_pow] using hh
    exact lowMean_quadratic_support hf hd hdd hbound htau hq

/-- Each support is an actual polynomial of degree at most two. -/
theorem lowMeanSupport_isQuadratic (c : ℝ) (a b : ℤ) (L H tau : ℝ) :
    ∃ A B C : ℝ, ∀ q : ℝ, lowMeanSupport c a b L H tau q = lowMeanQuad A B C q := by
  by_cases hconc : lowMeanPiMax c a b L H ≤ 0
  · refine ⟨0, (lowMeanMonomial c a b H - lowMeanMonomial c a b L) / (H - L),
      (H * lowMeanMonomial c a b L - L * lowMeanMonomial c a b H) / (H - L), ?_⟩
    intro q
    rw [lowMeanSupport, ite_eq_left hconc]
    unfold lowMeanQuad
    ring
  · by_cases hconv : 0 ≤ lowMeanPiMin c a b L H
    · refine ⟨0, lowMeanMonomialD c a b tau,
        lowMeanMonomial c a b tau - lowMeanMonomialD c a b tau * tau, ?_⟩
      intro q
      rw [lowMeanSupport, ite_eq_right hconc, ite_eq_left hconv]
      unfold lowMeanQuad
      ring
    · refine ⟨lowMeanLambda c a b L H / 2,
        lowMeanMonomialD c a b tau - lowMeanLambda c a b L H * tau,
        lowMeanMonomial c a b tau - lowMeanMonomialD c a b tau * tau +
          lowMeanLambda c a b L H / 2 * tau ^ 2, ?_⟩
      intro q
      rw [lowMeanSupport, ite_eq_right hconc, ite_eq_right hconv]
      unfold lowMeanQuad
      ring

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanPiMin_attained
#print axioms Erdos993Lean.Analytic.V213.lowMeanPiMax_attained
#print axioms Erdos993Lean.Analytic.V213.lowMean_signedMonomial_support
#print axioms Erdos993Lean.Analytic.V213.lowMeanSupport_isQuadratic
