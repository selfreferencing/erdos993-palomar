module

public import Erdos993Lean.Analytic.V213.FiberWindowGuards

/-!
Actual Eq103 consumer for every named F13 window. Each numerical
condition is discharged by the complete canonical checks and the actual
class domain; both signs of X and the full original-q deficit are covered.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberWindowTarget (id : FiberWindowIdentity) (t : ℝ) : ℝ :=
  let c := fiberOuterClassById (fiberWindowById id).outerClass
  lowMeanFractionReal c.b + lowMeanFractionReal c.beta_prime*(t-1)

theorem fiber_window_named_deficit (id : FiberWindowIdentity) {q mu : ℝ} {M : ℕ}
    (hql : 1/4 ≤ q) (hqh : q ≤ 3/4)
    (har : lowMeanFractionReal (fiberOuterClassById (fiberWindowById id).outerClass).skew_lower ≤ |fiberSkew q|)
    (hrb : |fiberSkew q| ≤ lowMeanFractionReal (fiberOuterClassById (fiberWindowById id).outerClass).skew_upper)
    (hmean : lowMeanFractionReal (fiberOuterClassById (fiberWindowById id).outerClass).mu_D ≤ mu)
    (htl : lowMeanFractionReal (fiberWindowById id).l ≤ (M : ℝ)/mu)
    (hth : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberWindowById id).h) :
    fiberDeficit q mu (fiberWindowTarget id) M ≤ lowMeanFractionReal (fiberWindowById id).L_W := by
  have hg := fiber_window_real_guards id
  dsimp only at hg
  rcases hg with ⟨hN0,hga,hgb,hbase,hl,hv,hh,hmuD,hb0,hbh,hbeta0,hbetah,hprice0⟩
  have hmu40 : 40 ≤ mu := hmuD.trans hmean
  have hmu : 0 < mu := by linarith only [hmu40]
  have hm := (le_div_iff₀ hmu).1 htl
  have hp := mul_le_mul_of_nonneg_right hmean hl.le
  have hN : fiberWindowN0 id ≤ (M : ℝ)+2 := by
    unfold fiberWindowN0
    nlinarith only [hm,hp]
  have h := fiber_window_deficit_bound hql hqh hga har hrb hgb hbase hN hl hv hmu40 htl hth hh
    hb0 hbh hbeta0 hbetah (fiber_window_minorant_checked id).le
  rw [fiber_window_price_value] at h
  exact h

end Erdos993Lean.Analytic.V213
