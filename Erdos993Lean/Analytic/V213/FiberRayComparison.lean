module

public import Erdos993Lean.Analytic.V213.FiberRayTransport
public import Erdos993Lean.Analytic.V213.FiberLowerComparison

/-!
Literal Lemma6.21 ray bound. The lower offsets and nonnegative upper
omega have zero deficit; the actual negative upper omega is transported
to H_r(N), then to the two tangent endpoints. All integer ranks and
all closed t/r endpoints are retained, without extra record assumptions.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_nonnegative_omega {M : ℕ} {q mu : ℝ}
    (hM : 8 ≤ M) (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (hω : 0 ≤ fiberUpperOmega mu (fiberSkew q) (M + 2)) :
    fiberPsi ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  have hq0' : 0 < q := by linarith only [hq0]
  have hq1 : q < 1 := by linarith only [hqh]
  have hNp : 0 < (M : ℝ) + 2 := by positivity
  have hB : 0 < ((M : ℝ) + 2) / mu := div_pos hNp hmu
  have h := fiber_upper_constrained_gain hM hq0 hqh hmu j hw
  rw [min_eq_left hω,shared_G_zero,mul_zero,sub_zero] at h
  have hb := fiber_bonus_at_least_one hq0' hq1 M
  have hF : ((M : ℝ) + 2) / mu ≤ fiberF q mu M j := by
    simpa only [one_mul] using (le_div_iff₀ hB).mp (hb.trans h)
  have ht : (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu :=
    div_le_div_of_nonneg_right (by linarith) hmu.le
  have hpsi : fiberPsi ((M : ℝ) / mu) ≤ (M : ℝ) / mu := by
    unfold fiberPsi
    nlinarith only [sq_nonneg ((M : ℝ) / mu - 1)]
  exact hpsi.trans (ht.trans hF)

theorem fiber_ray_bound (id : FiberRayIdentity) {M : ℕ} {q mu ra m : ℝ} {g : ℝ → ℝ}
    (hMf : lowMeanFractionReal (fiberRayById id).m_f ≤ (M : ℝ))
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu19 : 19 ≤ mu)
    (hra : 0 ≤ ra) (har : ra ≤ fiberSkew q)
    (hrR : fiberSkew q ≤ lowMeanFractionReal (fiberRayById id).R)
    (ht0 : 1 / 3 ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 3 / 5)
    (hg : g ((M : ℝ) / mu) ≤ 0) (hm : 0 < m) (hmt : m * ((M : ℝ) / mu) ≤ (M : ℝ)) :
    fiberDeficit q mu g M ≤
      max 0 (max (fiberRayD id g m ((M : ℝ) / mu) ra (fiberSkew q))
        (fiberRayE id g m ((M : ℝ) / mu) ra (fiberSkew q))) := by
  have hguard := fiber_ray_record_guards id
  dsimp at hguard
  have hmf : (8 : ℝ) ≤ lowMeanFractionReal (fiberRayById id).m_f := by
    linarith only [hguard.2.2.1,hguard.2.2.2.1]
  have hM8 : (8 : ℝ) ≤ M := hmf.trans hMf
  have hM : 8 ≤ M := by exact_mod_cast hM8
  have hMp : 0 < (M : ℝ) := by linarith only [hM8]
  have hmu : 0 < mu := by linarith only [hmu19]
  have ht : 0 < (M : ℝ) / mu := div_pos hMp hmu
  have hq0' : 0 < q := by linarith only [hq0]
  have hq1 : q < 1 := by linarith only [hqh]
  have hr : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith only [hq0]
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith only [hqh]
  have hrah : ra ≤ 1 / 2 := har.trans hrh
  let L := fiberRayF ((M : ℝ) / mu) + g ((M : ℝ) / mu) +
    ((M : ℝ) / mu) / (M : ℝ) *
      fiberRayH id ((M : ℝ) / mu) ra (fiberSkew q) ((M : ℝ) + 2)
  have hpoint (j : ℤ) : fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - max 0 L ≤
      fiberF q mu M j := by
    by_cases hw : fiberSquareOffset q M j ≤ fiberBonus q M
    · have h := fiber_lower_offset_comparison hmu19 hq0 hqh M j hw
      have hmargin : 0 ≤ 1 / (4 * mu) := by positivity
      linarith only [h,hmargin,hg,le_max_left (0 : ℝ) L]
    have hw' : fiberBonus q M ≤ fiberSquareOffset q M j := le_of_lt (lt_of_not_ge hw)
    by_cases hω : 0 ≤ fiberUpperOmega mu (fiberSkew q) (M + 2)
    · have h := fiber_ray_nonnegative_omega hM hq0 hqh hmu j hw' hω
      linarith only [h,hg,le_max_left (0 : ℝ) L]
    have hω' := lt_of_not_ge hω
    have h := fiber_ray_negative_transport id hMf hq0 hqh hmu hra har hrR ht0 ht1 j hw' hω'
    have hid : L * mu = g ((M : ℝ) / mu) * mu -
        (M : ℝ) * fiberTaylorS ((M : ℝ) / mu) +
          fiberRayH id ((M : ℝ) / mu) ra (fiberSkew q) ((M : ℝ) + 2) := by
      dsimp [L]
      rw [fiber_ray_f_identity ht]
      field_simp [hMp.ne',hmu.ne']
      ring
    have hdiff : fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - fiberF q mu M j ≤ L := by
      apply (mul_le_mul_iff_left₀ hmu).mp
      have h' : (fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - fiberF q mu M j) * mu ≤ L * mu := by
        linarith only [h,hid]
      exact h'
    linarith only [hdiff,le_max_right (0 : ℝ) L]
  have hdef := fiber_deficit_pointwise hq0' hq1 hmu M hpoint
  rw [max_eq_right (le_max_left (0 : ℝ) L)] at hdef
  exact hdef.trans (fiber_ray_tangent_consumer id hMp hm ht hmt hra hrah hr)

theorem fiber_ray_bound_printed (id : FiberRayIdentity) {M : ℕ} {r ra m t : ℝ} {g : ℝ → ℝ}
    (hMf : lowMeanFractionReal (fiberRayById id).m_f ≤ (M : ℝ))
    (hra : 0 ≤ ra) (har : ra ≤ r) (hrR : r ≤ lowMeanFractionReal (fiberRayById id).R)
    (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 5) (hmu : 19 ≤ (M : ℝ) / t)
    (hg : g t ≤ 0) (hm : 0 < m) (hmt : m * t ≤ (M : ℝ)) :
    fiberDeficit ((1 + r) / 2) ((M : ℝ) / t) g M ≤
      max 0 (max (fiberRayD id g m t ra r) (fiberRayE id g m t ra r)) := by
  have hguard := fiber_ray_record_guards id
  dsimp at hguard
  have hmf : (8 : ℝ) ≤ lowMeanFractionReal (fiberRayById id).m_f := by
    linarith only [hguard.2.2.1,hguard.2.2.2.1]
  have hMp : 0 < (M : ℝ) := by linarith only [hmf,hMf]
  have htp : 0 < t := by linarith only [ht0]
  have hr0 := hra.trans har
  have hrh : r ≤ 1 / 2 := by linarith only [hrR,hguard.2.1]
  have heq : (M : ℝ) / ((M : ℝ) / t) = t := by field_simp [hMp.ne']
  have hsk : fiberSkew ((1 + r) / 2) = r := by unfold fiberSkew; ring
  have h := fiber_ray_bound id (M := M) (q := (1 + r) / 2) (mu := (M : ℝ) / t)
    (ra := ra) (m := m) (g := g) hMf (by linarith only [hr0]) (by linarith only [hrh]) hmu
    hra (by rwa [hsk]) (by rwa [hsk]) (by rwa [heq]) (by rwa [heq])
    (by rwa [heq]) hm (by rwa [heq])
  simpa only [heq,hsk] using h

/-- Section6.3 absolute skew, with the actual original q retained in Def_g. -/
theorem fiber_ray_bound_all_q (id : FiberRayIdentity) {M : ℕ} {q mu ra m : ℝ} {g : ℝ → ℝ}
    (hMf : lowMeanFractionReal (fiberRayById id).m_f ≤ (M : ℝ))
    (hq0 : 1 / 4 ≤ q) (hqh : q ≤ 3 / 4) (hmu19 : 19 ≤ mu)
    (hra : 0 ≤ ra) (har : ra ≤ |fiberSkew q|)
    (hrR : |fiberSkew q| ≤ lowMeanFractionReal (fiberRayById id).R)
    (ht0 : 1 / 3 ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 3 / 5)
    (hg : g ((M : ℝ) / mu) ≤ 0) (hm : 0 < m) (hmt : m * ((M : ℝ) / mu) ≤ (M : ℝ)) :
    fiberDeficit q mu g M ≤
      max 0 (max (fiberRayD id g m ((M : ℝ) / mu) ra |fiberSkew q|)
        (fiberRayE id g m ((M : ℝ) / mu) ra |fiberSkew q|)) := by
  by_cases hq : 1 / 2 ≤ q
  · have hr : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith only [hq]
    simpa only [abs_of_nonneg hr] using fiber_ray_bound id hMf hq hqh hmu19
      hra (by simpa only [abs_of_nonneg hr] using har)
      (by simpa only [abs_of_nonneg hr] using hrR) ht0 ht1 hg hm hmt
  · have hr : fiberSkew q ≤ 0 := by unfold fiberSkew; linarith only [le_of_not_ge hq]
    have hsk : fiberSkew (1 - q) = |fiberSkew q| := by
      rw [fiber_skew_reflect,abs_of_nonpos hr]
    have h := fiber_ray_bound id (q := 1 - q) hMf (by linarith only [le_of_not_ge hq])
      (by linarith only [hq0]) hmu19 hra (by rwa [hsk]) (by rwa [hsk]) ht0 ht1 hg hm hmt
    simpa only [fiber_deficit_reflect,hsk] using h

end Erdos993Lean.Analytic.V213
