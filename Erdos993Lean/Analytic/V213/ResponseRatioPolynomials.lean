module

public import Erdos993Lean.Analytic.V213.ResponseRatioBounds

/-!
# Current Lemma 5.3: the printed cubic, quartic and U upper bounds

The statements and coefficients are the printed ones. A direct reciprocal-log
derivative comparison replaces the high-order differentiation of the integral:
for P=T4, the common-denominator remainder has only nonnegative coefficients.
The polynomial identity is proved by `ring`, not supplied as certificate data.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set FreeCountVariance.Envelopes

noncomputable def ratioT3 (u : ℝ) : ℝ := 1 - u / 2 - u ^ 2 / 12 - u ^ 3 / 24
noncomputable def ratioT4 (u : ℝ) : ℝ := ratioT3 u - 19 * u ^ 4 / 720
noncomputable def ratioU (u : ℝ) : ℝ := 1 - u / 2 - u ^ 2 / 10

theorem messageRatio_le_of_derivative_remainder {P P' : ℝ → ℝ} {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1)
    (hP : ∀ x ∈ Icc 0 u, 0 < P x)
    (hdP : ∀ x ∈ Icc 0 u, HasDerivAt P (P' x) x)
    (hR : ∀ x ∈ Icc 0 u,
      0 ≤ (P x) ^ 2 - (1 - x) * (P x - x * P' x)) :
    messageRatio u ≤ P u := by
  have hd : ∀ x ∈ Icc 0 u,
      HasDerivAt (fun z => scalarLog z - z / P z)
        (((P x) ^ 2 - (1 - x) * (P x - x * P' x)) /
          ((1 - x) * (P x) ^ 2)) x := by
    intro x hx
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hu1
    have h1 : 1 - x ≠ 0 := by linarith
    have hp : P x ≠ 0 := (hP x hx).ne'
    convert (hasDerivAt_scalarLog hx1).sub
      ((hasDerivAt_id x).div (hdP x hx) hp) using 1
    all_goals
      first
      | (funext z <;> (try dsimp) <;> ring)
      | ((try dsimp only [id]) <;> field_simp [h1, hp] <;> ring)
  have hg := zero_le_value_of_nonneg_deriv (f := fun x => scalarLog x - x / P x)
    (f' := fun x => ((P x) ^ 2 - (1 - x) * (P x - x * P' x)) /
      ((1 - x) * (P x) ^ 2)) hu0.le
    (by norm_num [scalarLog]) hd (fun x hx => by
      apply div_nonneg (hR x hx)
      exact mul_nonneg (by linarith [hx.2]) (sq_nonneg _))
  have hpu := hP u ⟨hu0.le, le_rfl⟩
  have hcross : u ≤ scalarLog u * P u :=
    (div_le_iff₀ hpu).mp (by linarith [hg])
  rw [messageRatio_eq_scalarH hu0.ne', scalarH]
  exact (div_le_iff₀ (scalarLog_pos hu0 hu1)).2 (by nlinarith [hcross])

theorem ratioT4_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (251 / 720 : ℝ) ≤ ratioT4 u := by
  have h2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0 hu1
  have h3 : u ^ 3 ≤ 1 := pow_le_one₀ hu0 hu1
  have h4 : u ^ 4 ≤ 1 := pow_le_one₀ hu0 hu1
  dsimp [ratioT4, ratioT3]
  nlinarith

theorem ratioT4_hasDerivAt (u : ℝ) :
    HasDerivAt ratioT4 (-1 / 2 - u / 6 - u ^ 2 / 8 - 19 * u ^ 3 / 180) u := by
  convert ((((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).div_const 2)).sub
    ((hasDerivAt_pow 2 u).div_const 12)).sub ((hasDerivAt_pow 3 u).div_const 24)).sub
    (((hasDerivAt_pow 4 u).const_mul 19).div_const 720) using 1 <;>
    (try (funext x)) <;> (try dsimp [ratioT4, ratioT3]) <;> ring

theorem ratioT4_derivative_remainder (u : ℝ) :
    (ratioT4 u) ^ 2 - (1 - u) *
      (ratioT4 u - u * (-1 / 2 - u / 6 - u ^ 2 / 8 - 19 * u ^ 3 / 180)) =
      u ^ 5 * (58320 + 3180 * u + 1140 * u ^ 2 + 361 * u ^ 3) / 518400 := by
  dsimp [ratioT4, ratioT3]
  ring

theorem messageRatio_le_T4 {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    messageRatio u ≤ ratioT4 u := by
  by_cases hu : u = 0
  · subst u
    norm_num [messageRatio_zero, ratioT4, ratioT3]
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  apply messageRatio_le_of_derivative_remainder (P := ratioT4)
    (P' := fun x => -1 / 2 - x / 6 - x ^ 2 / 8 - 19 * x ^ 3 / 180) hup hu1
  · intro x hx
    have h := ratioT4_lower hx.1 (le_trans hx.2 hu1.le)
    linarith
  · intro x hx
    exact ratioT4_hasDerivAt x
  · intro x hx
    rw [ratioT4_derivative_remainder]
    have hx0 : 0 ≤ x := hx.1
    positivity

theorem messageRatio_le_T3 {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    messageRatio u ≤ ratioT3 u := by
  have h := messageRatio_le_T4 hu0 hu1
  have h4 : 0 ≤ u ^ 4 := pow_nonneg hu0 4
  dsimp [ratioT4] at h
  nlinarith

theorem ratioU_sub_T4 (u : ℝ) :
    ratioU u - ratioT4 u = u ^ 2 * (-1 / 60 + u / 24 + 19 * u ^ 2 / 720) := by
  dsimp [ratioU, ratioT4, ratioT3]
  ring

theorem ratioT4_le_U {u : ℝ} (hu : (3 / 8 : ℝ) ≤ u) : ratioT4 u ≤ ratioU u := by
  have hu0 : 0 ≤ u := by linarith
  have hu2 : (9 / 64 : ℝ) ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 3 / 8)]
  have hb : 0 ≤ -1 / 60 + u / 24 + 19 * u ^ 2 / 720 := by nlinarith
  have h := mul_nonneg (sq_nonneg u) hb
  rw [← ratioU_sub_T4] at h
  linarith

theorem messageRatio_le_U {u : ℝ} (hu0 : (3 / 8 : ℝ) ≤ u) (hu1 : u < 1) :
    messageRatio u ≤ ratioU u :=
  (messageRatio_le_T4 (by linarith) hu1).trans (ratioT4_le_U hu0)

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioT3
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioT3
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioU
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioU
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_of_derivative_remainder
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_of_derivative_remainder
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_derivative_remainder
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_derivative_remainder
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_T4
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_T4
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_T3
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_T3
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioU_sub_T4
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioU_sub_T4
#check Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_le_U
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ratioT4_le_U
#check Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_U
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.messageRatio_le_U

-- Audits of the reused generic scalar facts.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarLog
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_scalarLog
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
