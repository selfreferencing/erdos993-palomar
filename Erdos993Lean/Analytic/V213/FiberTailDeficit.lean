module

public import Erdos993Lean.Analytic.V213.FiberTailNormalization

/-!
The actual small-fiber deficit consequences preceding Eq91/92.
Both printed negative target tests are retained, with all natural widths
(including zero) and every integer rank. The original q is never reflected
inside a later Laplace factor.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_pointwise_negative_kernel {q mu rhi : ℝ} (M : ℕ) (j : ℤ)
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi) :
    -(fiberTailC rhi*mu^(3/2 : ℝ)*
      max 0 (-kernel2 q (fiberWeightL q) (fiberWeightR q) M j)) ≤ fiberF q mu M j := by
  let k := kernel2 q (fiberWeightL q) (fiberWeightR q) M j
  have hkn : -(max 0 (-k)) ≤ k := by linarith only [le_max_right (0 : ℝ) (-k)]
  have hK : 0 ≤ max 0 (-k) := le_max_left _ _
  have hn := fiber_normalization_pos hq0 hq1 hmu
  have hu := fiber_tail_normalization_upper hq0 hq1 hmu hr0 hr1 hr
  have h1 := mul_le_mul_of_nonneg_left hkn hn.le
  have h2 := mul_le_mul_of_nonneg_right hu hK
  have hs : 0 ≤ fiberOffset q M j^2/(fiberVariance q*mu) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (fiber_variance_pos hq0 hq1).le hmu.le)
  unfold fiberF
  dsimp [k] at h1 h2
  nlinarith only [h1,h2,hs]

theorem fiber_tail_psi_seven_nineteen : fiberPsi (7/19)+2/5 < 0 := by
  norm_num [fiberPsi]

theorem fiber_tail_psi_twentyseven_fifty : fiberPsi (27/50)+2/5 < 0 := by
  norm_num [fiberPsi]

theorem fiber_tail_psi_monotone {t s : ℝ} (ht : t ≤ s) (hs : s ≤ 1) :
    fiberPsi t ≤ fiberPsi s := by
  have hp : 0 ≤ (s-t)*(10-(9/2 : ℝ)*(s+t)) := by
    apply mul_nonneg (sub_nonneg.mpr ht)
    linarith only [ht,hs]
  unfold fiberPsi
  nlinarith only [hp]

theorem fiber_tail_target_nonpos {b beta t s : ℝ}
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta) (ht : t ≤ s) (hs : s ≤ 1)
    (hpsi : fiberPsi s+2/5 ≤ 0) :
    fiberPsi t+(b+beta*(t-1)) ≤ 0 := by
  have hm := fiber_tail_psi_monotone ht hs
  have hline : beta*(t-1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hbeta (by linarith only [ht,hs])
  linarith only [hm,hline,hb,hpsi]

theorem fiber_tail_small_deficit {q mu rhi b beta : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4) (3/4)) (hmu : 19 ≤ mu) (hM : M ≤ 7)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta) :
    fiberDeficit q mu (fun t => b+beta*(t-1)) M ≤
      fiberTailC rhi*mu^(3/2 : ℝ)*((51/200 : ℝ)*(27/40 : ℝ)^M) := by
  have hmup : 0 < mu := by linarith only [hmu]
  have hMc : (M : ℝ) ≤ 7 := by exact_mod_cast hM
  have ht : (M : ℝ)/mu ≤ 7/19 := by
    apply (div_le_iff₀ hmup).2
    nlinarith only [hMc,hmu]
  have htarget := fiber_tail_target_nonpos hb hbeta ht (by norm_num : (7/19 : ℝ) ≤ 1)
    fiber_tail_psi_seven_nineteen.le
  have hkernel : ∀ j : ℤ, -((51/200 : ℝ)*(27/40 : ℝ)^M) ≤
      kernel2 q (fiberWeightL q) (fiberWeightR q) M j := by
    intro j
    have hk := fiber_small_width_kernel hM hq j
    have hg := fiber_small_width_geometric hM
    linarith only [hk,hg]
  exact fiber_tail_deficit_lower_kernel (fun t => b+beta*(t-1))
    (by linarith [hq.1]) (by linarith [hq.2]) hmup hr0 hr1 hr
    (by positivity) htarget hkernel

theorem fiber_tail_large_deficit {q mu rhi b beta c : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4) (3/4)) (hmu : 19 ≤ mu) (hM : 8 ≤ M)
    (hc : c ≤ 27/50) (hcut : (M : ℝ) < c*mu)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta) :
    fiberDeficit q mu (fun t => b+beta*(t-1)) M ≤
      fiberTailC rhi*mu^(3/2 : ℝ)*(81/5000 : ℝ) := by
  have hmup : 0 < mu := by linarith only [hmu]
  have ht : (M : ℝ)/mu ≤ 27/50 :=
    ((div_lt_iff₀ hmup).2 hcut).le.trans hc
  have htarget := fiber_tail_target_nonpos hb hbeta ht (by norm_num : (27/50 : ℝ) ≤ 1)
    fiber_tail_psi_twentyseven_fifty.le
  exact fiber_tail_deficit_lower_kernel (fun t => b+beta*(t-1))
    (by linarith [hq.1]) (by linarith [hq.2]) hmup hr0 hr1 hr
    (by norm_num) htarget (fiber_large_width_kernel (by omega) hq)

end Erdos993Lean.Analytic.V213
