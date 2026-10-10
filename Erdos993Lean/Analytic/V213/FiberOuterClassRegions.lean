module

public import Erdos993Lean.Analytic.V213.FiberOuterClassSound
public import Erdos993Lean.Analytic.V213.FiberOuterUniversalRegion
public import Erdos993Lean.Analytic.V213.FiberOuterNamedComparison

/-!
All eight class start tests composed with the actual upper-offset
region theorem. The exact mu_D*tau+2 width, closed skew bounds, starts,
and target associations are obtained from the printed-identity checks.
All natural widths and integer ranks are covered above each closed start.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_outer_class_width (id : FiberOuterClassIdentity) {M : ℕ} {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberOuterClassById id).mu_D ≤ mu)
    (ht : lowMeanFractionReal (fiberOuterClassById id).tau ≤ (M : ℝ) / mu) :
    0 < mu ∧ lowMeanFractionReal (fiberOuterClassById id).required_N ≤ (M : ℝ) + 2 := by
  have hc := fiber_outer_class_controls id
  let r := fiberOuterClassById id
  rcases hc with ⟨hra,hrb,hb0,hb1,hbeta0,hbeta1,hmu40,ht0,hN,ha,hr,htau⟩
  have hm : 0 < mu := by linarith only [hmu40,hmu]
  have hM : lowMeanFractionReal r.tau * mu ≤ (M : ℝ) := (le_div_iff₀ hm).mp ht
  have hprod := mul_le_mul_of_nonneg_right hmu ht0.le
  exact ⟨hm,hN.trans (by nlinarith only [hM,hprod])⟩

theorem fiber_outer_class_upper_comparison (id : FiberOuterClassIdentity)
    {M : ℕ} {q mu : ℝ}
    (hmu : lowMeanFractionReal (fiberOuterClassById id).mu_D ≤ mu)
    (hra : lowMeanFractionReal (fiberOuterClassById id).skew_lower ≤ fiberSkew q)
    (hrb : fiberSkew q ≤ lowMeanFractionReal (fiberOuterClassById id).skew_upper)
    (ht : lowMeanFractionReal (fiberOuterClassById id).tau ≤ (M : ℝ) / mu)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    let r := fiberOuterClassById id
    fiberPsi ((M : ℝ) / mu) + lowMeanFractionReal r.b +
      lowMeanFractionReal r.beta_prime * ((M : ℝ) / mu - 1) ≤ fiberF q mu M j := by
  let r := fiberOuterClassById id
  have hc := fiber_outer_class_controls id
  rcases hc with ⟨hra0,hrb0,hb0,hb1,hbeta0,hbeta1,hmu40,ht0,hN,ha,hr,htau⟩
  have hwidth := fiber_outer_class_width id hmu ht
  have hroute := fiber_outer_class_route_sound id
  change fiberOuterClassRouteMeaning id at hroute
  unfold fiberOuterClassRouteMeaning at hroute
  dsimp only at hroute
  cases hs : r.start with
  | none =>
      rw [show (fiberOuterClassById id).start = none from hs] at hroute
      rcases hroute with ⟨hNr,har,hrr,htr⟩
      have hn : 26 ≤ (M : ℝ) + 2 := by rw [← hNr]; exact hwidth.2
      have hlo : (1 / 4 : ℝ) ≤ fiberSkew q := by rw [← har]; exact ha.trans hra
      have hhi : fiberSkew q ≤ (1 / 2 : ℝ) := by rw [← hrr]; exact hrb.trans hr
      have ht' : (3 / 5 : ℝ) ≤ (M : ℝ) / mu := by rw [← htr]; exact htau.trans ht
      exact fiber_outer_universal_region hn hlo hhi hwidth.1 hb0 hb1 hbeta0 hbeta1 j hw ht'
  | some k =>
      rw [show (fiberOuterClassById id).start = some k from hs] at hroute
      rcases hroute with ⟨hNr,har,hrr,htr,hb,hbeta⟩
      have hn : lowMeanFractionReal (fiberOuterStartById k).n ≤ (M : ℝ) + 2 := by rw [← hNr]; exact hwidth.2
      have hlo : lowMeanFractionReal (fiberOuterStartById k).a ≤ fiberSkew q := by rw [← har]; exact ha.trans hra
      have hhi : fiberSkew q ≤ (2 / 5 : ℝ) := by rw [← hrr]; exact hrb.trans hr
      have ht' : lowMeanFractionReal (fiberOuterStartById k).sigma ≤ (M : ℝ) / mu := by rw [← htr]; exact htau.trans ht
      exact fiber_outer_named_comparison k hn hlo hhi hwidth.1 hb0 hb hbeta hbeta1 j hw ht'

end Erdos993Lean.Analytic.V213
