module

public import Erdos993Lean.Analytic.V213.FiberSpikePrice
public import Erdos993Lean.Analytic.V213.FiberIntervalSkew
public import Erdos993Lean.Analytic.V213.FiberAveraging

/-!
Literal Lemma6.19 and Eq88. The spike price is
an attained actual maximum over the exact strict width domain. The high
width comparison, strictly positive printed margin, probability and five
Eq10 moments are exactly the legitimate conditional inputs of this lemma.
Later finite-control modules discharge the comparison and margin. No forest
specialization or Section5 replacement premise is introduced.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberTargetLine (b betaPrime t : ℝ) : ℝ := b + betaPrime * (t - 1)

theorem fiber_target_psi_identity (b betaPrime t : ℝ) :
    fiberPsi t + fiberTargetLine b betaPrime t =
      1 + b + (1 + betaPrime) * (t - 1) - 9 / 2 * (t - 1) ^ 2 := by
  unfold fiberPsi fiberTargetLine
  ring

theorem fiber_spike_exponential_cancel (q mu ell ts : ℝ) (g : ℝ → ℝ) :
    (fiberSpikePrice q mu ell ts g * Real.exp (ell * mu)) * Real.exp (-ell * mu) =
      fiberSpikePrice q mu ell ts g := by
  rw [show -ell * mu = -(ell * mu) by ring,Real.exp_neg]
  field_simp [Real.exp_ne_zero (ell * mu)]

theorem fiber_spike_averaging {ι : Type} (X : Mixture ι) (k : ℤ)
    {q qlo qhi mu ell ts theta D b betaPrime : ℝ}
    (hlo : qlo ∈ Set.Icc (1 / 4) (3 / 4)) (hhi : qhi ∈ Set.Icc (1 / 4) (3 / 4))
    (hq : q ∈ Set.Icc qlo qhi) (hmu : 0 < mu) (hts : 0 < ts)
    (hb : b ∈ Set.Icc 0 (2 / 5)) (hbeta : 0 ≤ betaPrime)
    (hhigh : ∀ (M : ℕ) (j : ℤ), ts * mu ≤ (M : ℝ) →
      fiberPsi ((M : ℝ) / mu) + fiberTargetLine b betaPrime ((M : ℝ) / mu) ≤ fiberF q mu M j)
    (hmargin : 0 < 1 + b - theta - 9 * D / (2 * mu) -
      fiberInputSkewHigh qlo qhi ^ 2 / ((1 - fiberInputSkewHigh qlo qhi ^ 2) * mu) -
      fiberSpikePrice q mu ell ts (fiberTargetLine b betaPrime))
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q k M Y) = 0)
    (hvar : X.varM ≤ D * mu)
    (hdelta2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤ theta * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤ Real.exp (-ell * mu)) :
    ¬ X.WeakValley q k := by
  have hq' : q ∈ Set.Icc (1 / 4) (3 / 4) := ⟨hlo.1.trans hq.1,hq.2.trans hhi.2⟩
  have hq0 : 0 < q := by linarith only [hq'.1]
  have hq1 : q < 1 := by linarith only [hq'.2]
  let g := fiberTargetLine b betaPrime
  let Z := fiberSpikePrice q mu ell ts g * Real.exp (ell * mu)
  have hZ : 0 ≤ Z := mul_nonneg (fiber_spike_price_nonneg hq1 hts hmu ell g) (Real.exp_pos _).le
  apply fiber_shifted_penalty_average X k hq' hmu (by norm_num : (0 : ℝ) ≤ 9 / 2) hZ
    (alpha := 1 + b) (beta := 1 + betaPrime) (Gamma := 9 / 2) (Z := Z)
    ?_ ?_ hX hmean hdelta hvar hdelta2 htail
  · intro M j
    have h := fiber_spike_pointwise (ell := ell) (ts := ts) hq0 hq1 hmu hts (fiberTargetLine b betaPrime) hhigh M j
    rw [fiber_target_psi_identity] at h
    simpa only [Z,g,mul_assoc] using h
  · have hcost := fiber_skew_interval_cost hlo hhi hq hmu
    have hc := fiber_spike_exponential_cancel q mu ell ts g
    have hid : 1 + b - theta - (9 / 2) * D / mu -
        fiberSkew q ^ 2 / ((1 - fiberSkew q ^ 2) * mu) - Z * Real.exp (-ell * mu) =
        1 + b - theta - 9 * D / (2 * mu) -
          fiberSkew q ^ 2 / ((1 - fiberSkew q ^ 2) * mu) - fiberSpikePrice q mu ell ts g := by
      dsimp [Z]
      have hd : (9 / 2) * D / mu = 9 * D / (2 * mu) := by
        field_simp [hmu.ne'] <;> ring
      rw [hc,hd]
    rw [hid]
    change 0 < 1 + b - theta - 9 * D / (2 * mu) -
      fiberInputSkewHigh qlo qhi ^ 2 / ((1 - fiberInputSkewHigh qlo qhi ^ 2) * mu) -
      fiberSpikePrice q mu ell ts g at hmargin
    linarith only [hmargin,hcost]

end Erdos993Lean.Analytic.V213
