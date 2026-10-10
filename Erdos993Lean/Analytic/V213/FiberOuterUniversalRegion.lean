module

public import Erdos993Lean.Analytic.V213.FiberOuterUniversalParameters
public import Erdos993Lean.Analytic.V213.FiberUpperEndpointStart

/-!
Literal universal outer upper-offset region Lemma6.17(i). The
actual all-integer kernel, both signed endpoint targets, global positive-t
supremum and exact cutoff are retained. All printed scalar constants are
bound by the accepted F05 singleton checker; no numerical premise remains.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_outer_negative_coarse_bound {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    V22.G (-v) ≤ v ^ 2 / (4 - v) := by
  have hb := fiber_negative_root_barrier hv0 hv3
  have hd : 0 < 4 - v := by linarith only [hv3]
  exact hb.trans (div_le_div_of_nonneg_left (sq_nonneg v) hd (by nlinarith only [sq_nonneg v]))

theorem fiber_outer_universal_start {b beta : ℝ} (hb : b ≤ 2 / 5)
    (hbeta : 0 ≤ beta) :
    max (fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) (3 / 5))
      ((12 / 13) * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) (3 / 5)) ≤
      fiberEndpointUpper (2 / 5) (5 / 3) (1 / 3) (3 / 5) := by
  have ht := fiber_outer_target_start_order (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 / 5 : ℝ) ≤ 1) hb hbeta
  have ht0 : fiberEndpointTarget (10 + (0 : ℝ)) (9 / 2 + 0 - 2 / 5) (3 / 5) = (7 / 15 : ℝ) := by
    norm_num [fiberEndpointTarget]
  rw [ht0] at ht
  have hscaled : (12 / 13 : ℝ) * fiberEndpointTarget (10 + beta)
      (9 / 2 + beta - b) (3 / 5) ≤ 7 / 15 := by
    by_cases hf : 0 ≤ fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) (3 / 5)
    · have hm := mul_le_mul_of_nonneg_right (by norm_num : (12 / 13 : ℝ) ≤ 1) hf
      have hm' : (12 / 13 : ℝ) * fiberEndpointTarget (10 + beta)
          (9 / 2 + beta - b) (3 / 5) ≤ fiberEndpointTarget (10 + beta)
          (9 / 2 + beta - b) (3 / 5) := by simpa only [one_mul] using hm
      exact hm'.trans ht
    · have hm := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 12 / 13)
        (le_of_lt (lt_of_not_ge hf))
      exact hm.trans (by norm_num)
  have hl := fiber_upper_start_log_bounds.1
  have harg : -(79 / 90 : ℝ) ≤ min 0 (fiberEndpointLambda (2 / 5) (3 / 5)) := by
    apply le_min (by norm_num)
    unfold fiberEndpointLambda
    linarith only [hl]
  have hg := shared_G_antitoneOn_nonpos (by norm_num : -(79 / 90 : ℝ) ≤ 0)
    (min_le_left (0 : ℝ) _) harg
  have hbnd := hg.trans (fiber_outer_negative_coarse_bound
    (by norm_num : (0 : ℝ) ≤ 79 / 90) (by norm_num : (79 / 90 : ℝ) ≤ 3))
  have hU : (8 / 3 : ℝ) - 6 * ((79 / 90) ^ 2 / (4 - 79 / 90)) ≤
      fiberEndpointUpper (2 / 5) (5 / 3) (1 / 3) (3 / 5) := by
    unfold fiberEndpointUpper
    norm_num only
    linarith only [hbnd]
  have hgap := fiber_outer_universal_gap_scalar
  have heq := fiber_outer_universal_gap_identity
  exact (max_le ht hscaled).trans (by linarith only [hU,hgap,heq])

theorem fiber_outer_universal_cutoff {b beta : ℝ} (hb : b ≤ 2 / 5)
    (hbeta : 0 ≤ beta) :
    fiberEndpointStart (2 / 5) ^ 2 ≤ 25 / 33 ∧
      (25 / 33 : ℝ) < 41 / 45 ∧
      (41 / 45 : ℝ) ≤ 2 * (9 / 2 + beta - b) / 9 := by
  have h := Real.add_one_le_exp (8 / 25 : ℝ)
  have he : (33 / 25 : ℝ) ≤ Real.exp (8 / 25 : ℝ) := by linarith only [h]
  have hi : 1 / Real.exp (8 / 25 : ℝ) ≤ (25 / 33 : ℝ) :=
    (div_le_iff₀ (Real.exp_pos _)).2 (by linarith only [he])
  have hsq : fiberEndpointStart (2 / 5) ^ 2 = 1 / Real.exp (8 / 25 : ℝ) := by
    rw [fiber_outer_endpoint_start_square]
    norm_num only
    rw [Real.exp_neg,one_div]
  rw [hsq]
  exact ⟨hi,by norm_num,by linarith only [hb,hbeta]⟩

theorem fiber_outer_universal_region {M : ℕ} {q mu b beta : ℝ}
    (hN : 26 ≤ (M : ℝ) + 2) (hr0 : 1 / 4 ≤ fiberSkew q)
    (hrh : fiberSkew q ≤ 1 / 2) (hmu : 0 < mu)
    (hb0 : 0 ≤ b) (hbh : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (ht : 3 / 5 ≤ (M : ℝ) / mu) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) ≤ fiberF q mu M j := by
  have hq0 : 1 / 2 ≤ q := by unfold fiberSkew at hr0; linarith only [hr0]
  have hqh : q ≤ 3 / 4 := by unfold fiberSkew at hrh; linarith only [hrh]
  have hp := fiber_outer_universal_parameters hN hr0 hrh
  have hcut := fiber_outer_universal_cutoff hbh hbeta0
  have hcap := (fiber_outer_target_supremum hbh hbeta0 hbetah).2.le.trans
    (by norm_num : (3 / 2 : ℝ) ≤ 1 + 5 / 3)
  have hs := fiber_outer_universal_start hbh hbeta0
  have he := fiber_upper_endpoint_comparison (N0 := (26 : ℝ)) (p := (2 / 5 : ℝ))
    (R := (1 / 3 : ℝ)) (d := (5 / 3 : ℝ)) (A := 10 + beta)
    (c := 9 / 2 + beta - b) (tau := (3 / 5 : ℝ)) (by norm_num) hN hq0 hqh hmu
    (by norm_num) (by norm_num) (by norm_num) (by linarith only [hbeta0])
    (by linarith only [hbh,hbeta0]) (by norm_num) hp.1.le hp.2.1 hp.2.2.le
    (hcut.1.trans (hcut.2.1.le.trans hcut.2.2)) hcap
    (by convert hs using 1 <;> norm_num) j hw ht
  rw [fiber_outer_target_identity (by linarith only [ht] : 0 < (M : ℝ) / mu)] at he
  exact he

end Erdos993Lean.Analytic.V213
