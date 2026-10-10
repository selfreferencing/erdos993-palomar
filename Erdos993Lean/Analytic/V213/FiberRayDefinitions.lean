module

public import Erdos993Lean.Analytic.V213.FiberRayTangent
public import Erdos993Lean.Analytic.V213.FiberRayTemplate
public import Erdos993Lean.Analytic.V213.FiberRayEndpoints
public import Erdos993Lean.Analytic.V213.FiberMinimum

/-!
Literal Eq91 deficit and Lemma6.21 H/D/E definitions, bound to the actual
attained minimum over all integer ranks and the typed printed record.
The auxiliary m>0 tangent domain is independent of the actual record N.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberDeficit (q mu : ℝ) (g : ℝ → ℝ) (M : ℕ) : ℝ :=
  max 0 (fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - fiberMinimum q mu M)

noncomputable def fiberRayDelta (ra : ℝ) : ℝ := (1 - ra ^ 2)⁻¹

noncomputable def fiberRayC (id : FiberRayIdentity) (t : ℝ) : ℝ :=
  -6 * fiberRayAroot t - 2 + (lowMeanFractionReal (fiberRayById id).d_f - 11 / 10) *
    |G1 (5 / 2 * Real.log t)| + fiberRayCF (lowMeanFractionReal (fiberRayById id).m_f) *
      G2 (5 / 2 * Real.log t)

noncomputable def fiberRayA (id : FiberRayIdentity) (t : ℝ) : ℝ :=
  4 * G (5 / 2 * Real.log t) / lowMeanFractionReal (fiberRayById id).rho_f

noncomputable def fiberRayK (id : FiberRayIdentity) (t : ℝ) : ℝ :=
  lowMeanFractionReal (fiberRayById id).k_f * G (5 / 2 * Real.log t) /
    lowMeanFractionReal (fiberRayById id).rho_f

noncomputable def fiberRayH (id : FiberRayIdentity) (t ra u N : ℝ) : ℝ :=
  fiberRayHPolynomial (fiberRayC id t) (fiberRayA id t) (fiberRayK id t) (fiberRayDelta ra) u N

noncomputable def fiberRayD (id : FiberRayIdentity) (g : ℝ → ℝ) (m t ra u : ℝ) : ℝ :=
  fiberRayF t + g t + fiberRayH id t ra u (m * t + 2) / m

noncomputable def fiberRayE (id : FiberRayIdentity) (g : ℝ → ℝ) (m t ra u : ℝ) : ℝ :=
  fiberRayF t + g t + t * fiberRayHPrime (fiberRayA id t) (fiberRayK id t) (fiberRayDelta ra) u (m * t + 2)

theorem fiber_ray_HSecond_printed (id : FiberRayIdentity) (t ra u : ℝ) {N : ℝ}
    (hN : 0 < N) :
    fiberRayHSecond (fiberRayA id t) (fiberRayDelta ra) u N =
      -fiberRayA id t * u / (4 * N ^ (3 / 2 : ℝ)) - 2 * fiberRayDelta ra * u ^ 2 := by
  have hp : N ^ (3 / 2 : ℝ) = N * Real.sqrt N := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,Real.rpow_add hN,Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hp]
  unfold fiberRayHSecond
  ring

theorem fiber_deficit_nonneg (q mu : ℝ) (g : ℝ → ℝ) (M : ℕ) : 0 ≤ fiberDeficit q mu g M :=
  le_max_left _ _

theorem fiber_deficit_reflect (q mu : ℝ) (g : ℝ → ℝ) (M : ℕ) :
    fiberDeficit (1 - q) mu g M = fiberDeficit q mu g M := by
  unfold fiberDeficit
  rw [fiber_minimum_reflect]

theorem fiber_deficit_pointwise {q mu L : ℝ} {g : ℝ → ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu) (M : ℕ)
    (h : ∀ j : ℤ, fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - L ≤ fiberF q mu M j) :
    fiberDeficit q mu g M ≤ max 0 L := by
  have hmin := fiber_minimum_lower hq0 hq1 hmu M h
  unfold fiberDeficit
  apply max_le_max (le_refl _)
  linarith only [hmin]

theorem fiber_ray_tangent_consumer (id : FiberRayIdentity) {g : ℝ → ℝ} {M m t ra u : ℝ}
    (hM : 0 < M) (hm : 0 < m) (ht : 0 < t) (hmt : m * t ≤ M)
    (hra : 0 ≤ ra) (hrah : ra ≤ 1 / 2) (hu : 0 ≤ u) :
    max 0 (fiberRayF t + g t + t / M * fiberRayH id t ra u (M + 2)) ≤
      max 0 (max (fiberRayD id g m t ra u) (fiberRayE id g m t ra u)) := by
  have hg := fiber_ray_record_guards id
  dsimp at hg
  have hrf := hg.2.2.2.2.2.1
  have hA : 0 ≤ fiberRayA id t := by
    unfold fiberRayA
    exact div_nonneg (mul_nonneg (by norm_num) (shared_G_nonneg _)) hrf.le
  have hd : 0 ≤ fiberRayDelta ra := by
    have ho := fiberRayCalc_activity_denominator_pos hra hrah
    unfold fiberRayDelta
    positivity
  exact fiber_ray_tangent_max (C := fiberRayC id t) (K := fiberRayK id t)
    hA hd hu hM hm ht hmt

end Erdos993Lean.Analytic.V213
