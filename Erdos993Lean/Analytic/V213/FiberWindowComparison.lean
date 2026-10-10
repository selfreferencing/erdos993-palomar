module

public import Erdos993Lean.Analytic.V213.FiberWindowRootLoss
public import Erdos993Lean.Analytic.V213.FiberUpperConsumer
public import Erdos993Lean.Analytic.V213.FiberPointwiseReflection

/-!
The actual Eq102 window minorant. The analytic controls discharge
the exact omega, rate and bonus comparisons on the whole window. Both
omega signs and both sides of q=1/2 are included; original q remains in F.
Finite routing/window tests and lower-offset deficit assembly are later
C119/C120 consumers, not hypotheses pretending to prove them here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_window_analytic_controls {a b N0 l q mu : ℝ} {M : ℕ}
    (ha : 23 / 100 ≤ a) (har : a ≤ fiberSkew q) (hrb : fiberSkew q ≤ b)
    (hbh : b ≤ 1 / 2) (hN0 : 14 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2)
    (hl : 0 < l) (ht : l ≤ (M : ℝ) / mu) (hmu : 0 < mu) :
    (5 / 2) * Real.log l + fiberRationalGain a b N0 ≤ fiberUpperOmega mu (fiberSkew q) (M + 2) ∧
      fiberWindowRho b N0 ≤ V22.rhoU (fiberSkew q) ((M : ℝ) + 2) ∧
        fiberWindowDelta a N0 ≤ V22.Delta (fiberSkew q) ((M : ℝ) + 2) := by
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hr0 : 0 ≤ fiberSkew q := ha0.trans har
  have hb0 : 0 ≤ b := hr0.trans hrb
  have hab : a ≤ b := har.trans hrb
  have hNr : (14 : ℝ) ≤ (M : ℝ) + 2 := hN0.trans hN
  have hM : 8 ≤ M := by
    have hc : (8 : ℝ) ≤ M := by linarith only [hNr]
    exact_mod_cast hc
  have hgain := fiber_rational_gain_actual (by linarith only [ha] : 0 < a) har hrb hbh
    (by linarith only [hNr] : 10 ≤ (M : ℝ) + 2)
  have hmono := (fiber_rational_gain_increases ha hab hbh).monotoneOn
    (show N0 ∈ Ici 14 from hN0) (show (M : ℝ) + 2 ∈ Ici 14 from hNr) hN
  have homega := fiber_actual_upper_omega_gain (r := fiberSkew q) hmu hM
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_log hl ht) (by norm_num : (0 : ℝ) ≤ 5 / 2)
  have hrho0 := fiber_window_rho_star hb0 hbh (by linarith only [hN0] : 1 < N0)
  rcases fiber_upper_coefficient_monotonicity hb0 hbh with ⟨_,_,_,_,_,hrhom⟩
  have hrhostar := hrhom (show N0 ∈ Ici 10 by change 10 ≤ N0; linarith only [hN0])
    (show (M : ℝ) + 2 ∈ Ici 10 by change 10 ≤ (M : ℝ) + 2; linarith only [hNr]) hN
  have hrhoU := fiber_upper_rate_lower (by linarith only [hNr] : 10 ≤ (M : ℝ) + 2) hr0 hrb hbh
  have hdN := fiber_window_delta_width_mono ha0 (hab.trans hbh)
    (by linarith only [hN0] : 1 ≤ N0) hN
  have hdr := fiber_window_delta_skew_mono ha0 har (hrb.trans hbh)
    (by linarith only [hNr] : 1 ≤ (M : ℝ) + 2)
  exact ⟨by push_cast at homega; linarith only [hmono,hgain,homega,hlog],
    hrho0.trans (hrhostar.trans hrhoU),by rw [fiber_window_delta_actual]; exact hdN.trans hdr⟩

theorem fiber_window_upper_direct {a b N0 l v q mu : ℝ} {M : ℕ}
    (ha : 23 / 100 ≤ a) (har : a ≤ fiberSkew q) (hrb : fiberSkew q ≤ b)
    (hbh : b ≤ 1 / 2) (hN0 : 14 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2)
    (hl : 0 < l) (hv : 0 < v) (ht : l ≤ (M : ℝ) / mu) (hmu : 0 < mu)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    (((M : ℝ) + 2) / mu) * fiberWindowX a b N0 l v ≤ fiberF q mu M j := by
  have hq0 : 1 / 2 ≤ q := by unfold fiberSkew at har; linarith only [ha,har]
  have hqh : q ≤ 3 / 4 := by unfold fiberSkew at hrb; linarith only [hrb,hbh]
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hb0 : 0 ≤ b := ha0.trans (har.trans hrb)
  have hab : a ≤ b := har.trans hrb
  have hNr : (14 : ℝ) ≤ (M : ℝ) + 2 := hN0.trans hN
  have hM : 8 ≤ M := by
    have hc : (8 : ℝ) ≤ M := by linarith only [hNr]
    exact_mod_cast hc
  have hc := fiber_window_analytic_controls ha har hrb hbh hN0 hN hl ht hmu
  have hg := fiber_rational_gain_strict ha hab hbh hN0
  have hrho := fiber_window_rho_strict hb0 hbh hN0
  have hG := fiber_window_clipped_loss hl hv (by linarith only [hg]) hc.1
    (show 0 < fiberWindowRho b N0 by linarith only [hrho]) hc.2.1
  have hgamma := fiber_upper_gamma_identity (by linarith only [hq0] : 0 < q)
    (by linarith only [hqh] : q < 1) M
  unfold V22.gamma at hgamma
  have hX : fiberWindowX a b N0 l v ≤ fiberBonus q M -
      2 / V22.rhoU (fiberSkew q) ((M : ℝ) + 2) *
        V22.G (min 0 (fiberUpperOmega mu (fiberSkew q) (M + 2))) := by
    unfold fiberWindowX
    dsimp only
    linarith only [hG,hc.2.2,hgamma]
  have h := hX.trans (fiber_upper_constrained_gain hM hq0 hqh hmu j hw)
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hh := (le_div_iff₀ hB).1 h
  simpa only [mul_comm] using hh

/-- Full Section6.3 probability domain, retaining the actual original-q F. -/
theorem fiber_window_upper_all_q {a b N0 l v q mu : ℝ} {M : ℕ}
    (hq0 : 1 / 4 ≤ q) (hqh : q ≤ 3 / 4) (ha : 23 / 100 ≤ a)
    (har : a ≤ |fiberSkew q|) (hrb : |fiberSkew q| ≤ b) (hbh : b ≤ 1 / 2)
    (hN0 : 14 ≤ N0) (hN : N0 ≤ (M : ℝ) + 2)
    (hl : 0 < l) (hv : 0 < v) (ht : l ≤ (M : ℝ) / mu) (hmu : 0 < mu)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    (((M : ℝ) + 2) / mu) * fiberWindowX a b N0 l v ≤ fiberF q mu M j := by
  by_cases hq : 1 / 2 ≤ q
  · have hr : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith only [hq]
    exact fiber_window_upper_direct ha (by simpa only [abs_of_nonneg hr] using har)
      (by simpa only [abs_of_nonneg hr] using hrb) hbh hN0 hN hl hv ht hmu j hw
  · have hr : fiberSkew q ≤ 0 := by unfold fiberSkew; linarith only [le_of_not_ge hq]
    have hsk : fiberSkew (1 - q) = |fiberSkew q| := by
      rw [fiber_skew_reflect,abs_of_nonpos hr]
    have hwr : fiberBonus (1 - q) M ≤ fiberSquareOffset (1 - q) M ((M : ℤ) - j) := by
      rwa [fiber_bonus_reflect,fiber_square_offset_reflect]
    have h := fiber_window_upper_direct (q := 1 - q) ha (by rwa [hsk]) (by rwa [hsk])
      hbh hN0 hN hl hv ht hmu ((M : ℤ) - j) hwr
    rwa [fiber_F_reflect] at h

/-- Eq102's actual N0=mu_D*l+2, with its width containment derived. -/
theorem fiber_window_upper_printed {a b l v q mu muD : ℝ} {M : ℕ}
    (hq0 : 1 / 4 ≤ q) (hqh : q ≤ 3 / 4) (ha : 23 / 100 ≤ a)
    (har : a ≤ |fiberSkew q|) (hrb : |fiberSkew q| ≤ b) (hbh : b ≤ 1 / 2)
    (hbase : 14 ≤ muD * l + 2) (hmu : 0 < mu) (hmean : muD ≤ mu)
    (hl : 0 < l) (hv : 0 < v) (ht : l ≤ (M : ℝ) / mu)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    (((M : ℝ) + 2) / mu) * fiberWindowX a b (muD * l + 2) l v ≤ fiberF q mu M j := by
  have hm := (le_div_iff₀ hmu).1 ht
  have hprod := mul_le_mul_of_nonneg_right hmean hl.le
  have hN : muD * l + 2 ≤ (M : ℝ) + 2 := by nlinarith only [hm,hprod]
  exact fiber_window_upper_all_q hq0 hqh ha har hrb hbh hbase hN hl hv ht hmu j hw

end Erdos993Lean.Analytic.V213
