module

public import Erdos993Lean.Analytic.V213.FiberOuterEndpointGeometry
public import Erdos993Lean.Analytic.V213.FiberNegativeBarrier

/-!
Global endpoint cutoffs, signed start targets and actual inverse-G
barrier. These analytical guards retain tau>0 and the exact tstar^2<=2c/9
condition. They are generic and consume no generated start family.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_outer_endpoint_start_square (p : ℝ) :
    fiberEndpointStart p ^ 2 = Real.exp (-4 * p / 5) := by
  unfold fiberEndpointStart
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

theorem fiber_outer_endpoint_cutoff {p b beta : ℝ} (hp : 1 / 6 < p)
    (hb : b ≤ 2 / 5) (hbeta : 0 ≤ beta) :
    fiberEndpointStart p ^ 2 < 15 / 17 ∧
      fiberEndpointStart p ^ 2 ≤ 2 * (9 / 2 + beta - b) / 9 := by
  have hE := Real.add_one_le_exp (4 * p / 5)
  have he : (17 / 15 : ℝ) < Real.exp (4 * p / 5) := by linarith only [hp,hE]
  have hpos := Real.exp_pos (4 * p / 5)
  have hinv : 1 / Real.exp (4 * p / 5) < (15 / 17 : ℝ) :=
    (div_lt_iff₀ hpos).2 (by linarith only [he])
  have hneg : Real.exp (-4 * p / 5) = 1 / Real.exp (4 * p / 5) := by
    rw [neg_mul,neg_div,Real.exp_neg,one_div]
  have hstar : fiberEndpointStart p ^ 2 < (15 / 17 : ℝ) := by
    rw [fiber_outer_endpoint_start_square,hneg]
    exact hinv
  exact ⟨hstar,hstar.le.trans (by linarith only [hb,hbeta])⟩

theorem fiber_outer_target_start_order {sigma b beta b0 beta0 : ℝ}
    (hs : 0 < sigma) (hsh : sigma ≤ 1) (hb : b ≤ b0) (hbeta : beta0 ≤ beta) :
    fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) sigma ≤
      fiberEndpointTarget (10 + beta0) (9 / 2 + beta0 - b0) sigma := by
  have hbta := mul_le_mul_of_nonpos_right hbeta (by linarith only [hsh] : sigma - 1 ≤ 0)
  have he := fiber_outer_target_identity hs b beta
  have he0 := fiber_outer_target_identity hs b0 beta0
  apply (mul_le_mul_iff_left₀ hs).mp
  linarith only [hb,hbta,he,he0]

theorem fiber_outer_signed_negative_start {eta f f0 : ℝ} (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1) (hf : f ≤ f0) (hf0 : f0 < 0) :
    max f (eta * f) ≤ eta * f0 := by
  have hneg : f ≤ 0 := hf.trans hf0.le
  have h1 : f ≤ eta * f := by nlinarith only [heta1,hneg]
  have h2 := mul_le_mul_of_nonneg_left hf heta0
  exact max_le (h1.trans h2) h2

theorem fiber_outer_endpoint_barrier_lower {p d R tau v : ℝ}
    (hR : 0 < R) (hv0 : 0 ≤ v) (hv3 : v ≤ 3)
    (hlambda : -v ≤ fiberEndpointLambda p tau) :
    1 + d - 2 * (v ^ 2 / (4 - v + v ^ 2 / 48)) / R ≤
      fiberEndpointUpper p d R tau := by
  have hm : -v ≤ min 0 (fiberEndpointLambda p tau) := le_min (by linarith only [hv0]) hlambda
  have hg := shared_G_antitoneOn_nonpos (by linarith only [hv0] : -v ≤ 0)
    (min_le_left (0 : ℝ) _) hm
  have hb := hg.trans (fiber_negative_root_barrier hv0 hv3)
  have hloss := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 / R)
  have he : 2 / R * (v ^ 2 / (4 - v + v ^ 2 / 48)) =
      2 * (v ^ 2 / (4 - v + v ^ 2 / 48)) / R := by ring
  rw [he] at hloss
  unfold fiberEndpointUpper
  linarith only [hloss]

end Erdos993Lean.Analytic.V213
