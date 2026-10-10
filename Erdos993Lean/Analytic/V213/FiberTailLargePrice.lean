module

public import Erdos993Lean.Analytic.V213.FiberTailSmallPrice

/-!
Literal Eq92. The least starting mean
mu0 and the shifted decay start max(mu0,8/c) remain distinct. All real
means and all natural widths above seven are included. The original q
is retained in the weight, and the actual rate difference is ell-c*L.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_large_price {q mu mu0 rhi b beta ell Lb L c : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4) (3/4)) (hmu0 : 19 ≤ mu0) (hmu : mu0 ≤ mu)
    (hM : 8 ≤ M) (hcut : (M : ℝ) < c*mu) (hc : c ≤ 27/50)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta)
    (hLb : -Real.log (1-q) ≤ Lb) (hL : Lb ≤ L)
    (hd : 0 < ell-c*L) (hdecay : 3/2 ≤ (ell-c*L)*max mu0 (8/c)) :
    fiberSpikeTerm q mu ell (fun t => b+beta*(t-1)) M ≤
      (81*fiberTailC rhi/5000)*(max mu0 (8/c))^(3/2 : ℝ)*
        Real.exp (-(ell-c*L)*max mu0 (8/c)) := by
  have hmu0p : 0 < mu0 := by linarith only [hmu0]
  have hmup := hmu0p.trans_le hmu
  have hMq : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hcp : 0 < c := by
    by_contra hn
    have hn' : c ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonpos_of_nonneg hn' hmup.le
    linarith only [hcut,hMq,hm]
  have hstart : max mu0 (8/c) ≤ mu := by
    apply max_le hmu
    apply (div_le_iff₀ hcp).2
    nlinarith only [hMq,hcut]
  have hstartp := hmu0p.trans_le (le_max_left mu0 (8/c))
  have hq1 : q < 1 := by linarith [hq.2]
  have hL0 : 0 ≤ L := by
    have hn := Real.log_nonpos (by linarith [hq.2] : 0 ≤ 1-q) (by linarith [hq.1] : 1-q ≤ 1)
    linarith only [hn,hLb,hL]
  have hweight := fiber_tail_weight_upper hq1 (hLb.trans hL) M
  have hmul := mul_le_mul_of_nonneg_left hcut.le hL0
  have he := Real.exp_le_exp.mpr hmul
  have hweight' : ((1-q)^M)⁻¹ ≤ Real.exp (L*(c*mu)) := hweight.trans he
  have hdef := fiber_tail_large_deficit hq (hmu0.trans hmu) hM hc hcut hr0 hr1 hr hb hbeta
  have hw := mul_le_mul hweight' (le_refl (Real.exp (-ell*mu)))
    (Real.exp_pos _).le (Real.exp_pos _).le
  have hbound := mul_le_mul hw hdef (fiber_deficit_nonneg _ _ _ _)
    (by positivity : 0 ≤ Real.exp (L*(c*mu))*Real.exp (-ell*mu))
  have heq : Real.exp (L*(c*mu))*Real.exp (-ell*mu) = Real.exp (-(ell-c*L)*mu) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hbound
  have hdec := fiber_tail_decay_bound hd hstartp hdecay hstart
  have hC := (fiber_tail_C_pos hr0 hr1).le
  have hfinal := mul_le_mul_of_nonneg_left hdec
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81/5000) hC)
  unfold fiberSpikeTerm
  exact hbound.trans (by convert hfinal using 1 <;> ring)

end Erdos993Lean.Analytic.V213
