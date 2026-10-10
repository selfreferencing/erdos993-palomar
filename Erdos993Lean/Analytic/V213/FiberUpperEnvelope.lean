module

public import Erdos993Lean.Analytic.V213.FiberUpperConsumer
public import Erdos993Lean.Analytic.V213.FiberEndpointPrinciple

/-!
The general actual-fiber bridge following the endpoint principle.
Parameter lower bounds rho_U>=R, Delta>=d,
Phi>=p and N>=N0>=10 imply the actual upper-offset envelope. The signed
target transfer uses eta=(N0-2)/N0 and the actual t/B=(N-2)/N.
These generic helpers retain the printed parameter/start hypotheses;
they introduce no paper theorem as an assumption and use no finite data.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_upper_envelope_parameters {M : ℕ} {N0 q mu p R d : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2)
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu)
    (_hp : 0 < p) (hR : 0 < R) (_hd : 0 ≤ d)
    (hRbound : R ≤ V22.rhoU (fiberSkew q) ((M : ℝ) + 2))
    (hdbound : d ≤ V22.Delta (fiberSkew q) ((M : ℝ) + 2))
    (hpbound : p ≤ V22.phiR (fiberSkew q) ((M : ℝ) + 2)) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    fiberEndpointUpper p d R ((M : ℝ) / mu) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hM : 8 ≤ M := by exact_mod_cast (show (8 : ℝ) ≤ M by linarith)
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hRU : 0 < V22.rhoU (fiberSkew q) ((M : ℝ) + 2) := hR.trans_le hRbound
  have ho := fiber_actual_upper_omega_gain (r := fiberSkew q) hmu hM
  have hl : fiberEndpointLambda p ((M : ℝ) / mu) ≤
      fiberUpperOmega mu (fiberSkew q) (M + 2) := by
    unfold fiberEndpointLambda
    linarith only [ho, hpbound]
  have hg := shared_G_antitoneOn_nonpos (min_le_left (0 : ℝ) _)
    (min_le_left (0 : ℝ) _) (min_le_min_left (0 : ℝ) hl)
  have hg0 := shared_G_nonneg (min 0 (fiberEndpointLambda p ((M : ℝ) / mu)))
  have hr : 2 / V22.rhoU (fiberSkew q) ((M : ℝ) + 2) ≤ 2 / R :=
    div_le_div_of_nonneg_left (by norm_num) hR hRbound
  have he := mul_le_mul (by exact hg) hr (by positivity :
    0 ≤ 2 / V22.rhoU (fiberSkew q) ((M : ℝ) + 2)) hg0
  have hf := fiber_upper_constrained_gain hM hq0 hqh hmu j hw
  rw [← fiber_upper_gamma_identity hq0' hq1 M] at hf
  unfold V22.gamma at hf
  unfold fiberEndpointUpper
  linarith only [he, hf, hdbound]

theorem fiber_upper_size_ratio_sandwich {M : ℕ} {N0 : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2) :
    (N0 - 2) / N0 ≤ (M : ℝ) / ((M : ℝ) + 2) ∧
      (M : ℝ) / ((M : ℝ) + 2) ≤ 1 := by
  have hn0 : 0 < N0 := by linarith
  have hn : 0 < (M : ℝ) + 2 := by positivity
  constructor
  · apply (div_le_div_iff₀ hn0 hn).2
    nlinarith only [hN]
  · exact (div_le_one hn).2 (by linarith)

theorem fiber_upper_signed_target {eta theta f : ℝ}
    (he : eta ≤ theta) (ht : theta ≤ 1) : theta * f ≤ max f (eta * f) := by
  by_cases hf : 0 ≤ f
  · exact (by nlinarith only [ht, hf] : theta * f ≤ f).trans (le_max_left _ _)
  · exact (mul_le_mul_of_nonpos_right he (le_of_lt (lt_of_not_ge hf))).trans (le_max_right _ _)

theorem fiber_upper_target_transfer {M : ℕ} {N0 q mu p R d f : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2)
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu)
    (hp : 0 < p) (hR : 0 < R) (hd : 0 ≤ d)
    (hRbound : R ≤ V22.rhoU (fiberSkew q) ((M : ℝ) + 2))
    (hdbound : d ≤ V22.Delta (fiberSkew q) ((M : ℝ) + 2))
    (hpbound : p ≤ V22.phiR (fiberSkew q) ((M : ℝ) + 2)) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (htarget : max f (((N0 - 2) / N0) * f) ≤
      fiberEndpointUpper p d R ((M : ℝ) / mu)) :
    (M : ℝ) / mu * f ≤ fiberF q mu M j := by
  have hs := fiber_upper_size_ratio_sandwich hN0 hN
  have hb := fiber_upper_envelope_parameters hN0 hN hq0 hqh hmu hp hR hd
    hRbound hdbound hpbound j hw
  have hc := (fiber_upper_signed_target (f := f) hs.1 hs.2).trans (htarget.trans hb)
  have hmul := (le_div_iff₀ (by positivity : 0 < ((M : ℝ) + 2) / mu)).mp hc
  have he : (M : ℝ) / ((M : ℝ) + 2) * f * (((M : ℝ) + 2) / mu) =
      (M : ℝ) / mu * f := by
    field_simp [hmu.ne', (by positivity : (M : ℝ) + 2 ≠ 0)]
  rw [he] at hmul
  exact hmul

theorem fiber_upper_endpoint_comparison {M : ℕ} {N0 q mu p R d A c tau : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2)
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu)
    (hp : 0 < p) (hR : 0 < R) (hd : 0 ≤ d) (hA : 0 < A) (hc : 0 < c)
    (htau : 0 < tau)
    (hRbound : R ≤ V22.rhoU (fiberSkew q) ((M : ℝ) + 2))
    (hdbound : d ≤ V22.Delta (fiberSkew q) ((M : ℝ) + 2))
    (hpbound : p ≤ V22.phiR (fiberSkew q) ((M : ℝ) + 2))
    (hstar : fiberEndpointStart p ^ 2 ≤ 2 * c / 9)
    (hcap : sSup ((fiberEndpointTarget A c) '' Ioi 0) ≤ 1 + d)
    (hstart : max (fiberEndpointTarget A c tau)
      (((N0 - 2) / N0) * fiberEndpointTarget A c tau) ≤ fiberEndpointUpper p d R tau)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (ht : tau ≤ (M : ℝ) / mu) :
    (M : ℝ) / mu * fiberEndpointTarget A c ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  have hn0 : 0 < N0 := by linarith
  have heta0 : 0 < (N0 - 2) / N0 := div_pos (by linarith) hn0
  have heta1 : (N0 - 2) / N0 ≤ 1 := (div_le_one hn0).2 (by linarith)
  have he := fiber_endpoint_principle hp hR hd heta0 heta1 hA hc htau hstar hcap hstart
    ((M : ℝ) / mu) ht
  exact fiber_upper_target_transfer hN0 hN hq0 hqh hmu hp hR hd hRbound hdbound hpbound j hw he

end Erdos993Lean.Analytic.V213
