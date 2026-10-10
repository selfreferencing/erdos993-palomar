module

public import Erdos993Lean.Analytic.V213.FiberTailDeficit
public import Erdos993Lean.Analytic.V213.FiberTailDecay
public import Erdos993Lean.Analytic.V213.FiberSpikePrice

/-!
Literal Eq91. The original q stays in
its inverse Laplace weight. Both branches of the geometric maximum and
width zero are included. The mean bound is a full real half-line result.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_weight_upper {q L : ℝ} (hq1 : q < 1)
    (hL : -Real.log (1-q) ≤ L) (M : ℕ) :
    ((1-q)^M)⁻¹ ≤ Real.exp (L*(M : ℝ)) := by
  have he : ((1-q)^M)⁻¹ = Real.exp ((M : ℝ)*(-Real.log (1-q))) := by
    rw [Real.exp_nat_mul,Real.exp_neg,Real.exp_log (sub_pos.mpr hq1),inv_pow]
  rw [he]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  nlinarith only [h]

theorem fiber_tail_small_power {a : ℝ} (ha : 0 ≤ a) {M : ℕ} (hM : M ≤ 7) :
    a^M ≤ max 1 (a^7) := by
  by_cases h : a ≤ 1
  · exact (pow_le_one₀ ha h).trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hM).trans (le_max_right _ _)

theorem fiber_tail_small_price {q mu mu0 rhi b beta ell Lb : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4) (3/4)) (hmu0 : 19 ≤ mu0) (hmu : mu0 ≤ mu)
    (hM : M ≤ 7) (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta) (hL : -Real.log (1-q) ≤ Lb)
    (hdecay : 3/2 ≤ ell*mu0) :
    fiberSpikeTerm q mu ell (fun t => b+beta*(t-1)) M ≤
      (51*fiberTailC rhi/200)*mu0^(3/2 : ℝ)*Real.exp (-ell*mu0)*
        max 1 (((27/40 : ℝ)*Real.exp Lb)^7) := by
  have hmu0p : 0 < mu0 := by linarith only [hmu0]
  have hmup := hmu0p.trans_le hmu
  have hell : 0 < ell := by nlinarith only [hdecay,hmu0p]
  have hq1 : q < 1 := by linarith [hq.2]
  have hdef := fiber_tail_small_deficit hq (hmu0.trans hmu) hM hr0 hr1 hr hb hbeta
  have hw := fiber_tail_weight_upper hq1 hL M
  have he0 := Real.exp_pos (-ell*mu)
  have hweight0 : 0 ≤ ((1-q)^M)⁻¹ := by positivity
  have h1 := mul_le_mul hw (le_refl (Real.exp (-ell*mu))) he0.le (Real.exp_pos _).le
  have h2 := mul_le_mul h1 hdef (fiber_deficit_nonneg _ _ _ _) (by positivity : 0 ≤ Real.exp (Lb*(M : ℝ))*Real.exp (-ell*mu))
  have hfactor : Real.exp (Lb*(M : ℝ))*Real.exp (-ell*mu)*
      (fiberTailC rhi*mu^(3/2 : ℝ)*((51/200 : ℝ)*(27/40 : ℝ)^M)) =
      ((51/200 : ℝ)*fiberTailC rhi)*(mu^(3/2 : ℝ)*Real.exp (-ell*mu))*
        (((27/40 : ℝ)*Real.exp Lb)^M) := by
    rw [mul_comm Lb (M : ℝ),Real.exp_nat_mul,mul_pow]
    ring
  have hpow := fiber_tail_small_power (by positivity : 0 ≤ (27/40 : ℝ)*Real.exp Lb) hM
  have hd := fiber_tail_decay_bound hell hmu0p hdecay hmu
  have hC := (fiber_tail_C_pos hr0 hr1).le
  have hcoeff : 0 ≤ (51/200 : ℝ)*fiberTailC rhi := mul_nonneg (by norm_num) hC
  have hfirst := mul_le_mul_of_nonneg_left hd hcoeff
  have hfinal := mul_le_mul hfirst hpow (by positivity)
    (by positivity : 0 ≤ ((51/200 : ℝ)*fiberTailC rhi)*(mu0^(3/2 : ℝ)*Real.exp (-ell*mu0)))
  unfold fiberSpikeTerm
  rw [hfactor] at h2
  exact h2.trans (by convert hfinal using 1 <;> ring)

end Erdos993Lean.Analytic.V213
