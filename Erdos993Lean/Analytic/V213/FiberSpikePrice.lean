module

public import Erdos993Lean.Analytic.V213.FiberRayDefinitions
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
The actual spike price. Its strict natural-width domain is
proved finite and nonempty, and its maximum is attained. The original q
is used in every inverse Laplace weight. The full rank minimum is the
already proved actual fiberMinimum, including both integer tails and M=0.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberSpikeWidths (ts mu : ℝ) : Set ℕ :=
  {M | (M : ℝ) < ts * mu}

noncomputable def fiberSpikeTerm (q mu ell : ℝ) (g : ℝ → ℝ) (M : ℕ) : ℝ :=
  ((1 - q) ^ M)⁻¹ * Real.exp (-ell * mu) * fiberDeficit q mu g M

noncomputable def fiberSpikePrice (q mu ell ts : ℝ) (g : ℝ → ℝ) : ℝ :=
  sSup (fiberSpikeTerm q mu ell g '' fiberSpikeWidths ts mu)

theorem fiber_spike_widths_finite (ts mu : ℝ) : (fiberSpikeWidths ts mu).Finite := by
  have hsub : fiberSpikeWidths ts mu ⊆ Set.Iio (Nat.ceil (ts * mu)) := by
    intro M hM
    exact Nat.lt_ceil.mpr hM
  exact (Set.finite_Iio _).subset hsub

theorem fiber_spike_widths_nonempty {ts mu : ℝ} (hts : 0 < ts) (hmu : 0 < mu) :
    (fiberSpikeWidths ts mu).Nonempty := by
  refine ⟨0,?_⟩
  simpa only [fiberSpikeWidths,Nat.cast_zero,Set.mem_setOf_eq] using mul_pos hts hmu

theorem fiber_spike_term_nonneg {q : ℝ} (hq1 : q < 1) (mu ell : ℝ)
    (g : ℝ → ℝ) (M : ℕ) : 0 ≤ fiberSpikeTerm q mu ell g M := by
  have hp : 0 < (1 - q) ^ M := pow_pos (sub_pos.mpr hq1) M
  unfold fiberSpikeTerm
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hp.le) (Real.exp_pos _).le)
    (fiber_deficit_nonneg q mu g M)

theorem fiber_spike_price_attained (q ell : ℝ) (g : ℝ → ℝ) {ts mu : ℝ}
    (hts : 0 < ts) (hmu : 0 < mu) :
    ∃ M : ℕ, (M : ℝ) < ts * mu ∧
      fiberSpikePrice q mu ell ts g = fiberSpikeTerm q mu ell g M ∧
      ∀ K : ℕ, (K : ℝ) < ts * mu → fiberSpikeTerm q mu ell g K ≤ fiberSpikeTerm q mu ell g M := by
  have hs := fiber_spike_widths_finite ts mu
  have hne := fiber_spike_widths_nonempty hts hmu
  obtain ⟨M,hM,hmax⟩ := Set.exists_max_image (fiberSpikeWidths ts mu)
    (fiberSpikeTerm q mu ell g) hs hne
  have himg := hs.image (fiberSpikeTerm q mu ell g)
  have heq : fiberSpikePrice q mu ell ts g = fiberSpikeTerm q mu ell g M := by
    unfold fiberSpikePrice
    apply le_antisymm
    · apply csSup_le (hne.image _)
      rintro x ⟨K,hK,rfl⟩
      exact hmax K hK
    · exact le_csSup himg.bddAbove ⟨M,hM,rfl⟩
  exact ⟨M,hM,heq,hmax⟩

theorem fiber_spike_price_nonneg {q ts mu : ℝ} (hq1 : q < 1)
    (hts : 0 < ts) (hmu : 0 < mu) (ell : ℝ) (g : ℝ → ℝ) :
    0 ≤ fiberSpikePrice q mu ell ts g := by
  obtain ⟨M,_,heq,_⟩ := fiber_spike_price_attained q ell g hts hmu
  rw [heq]
  exact fiber_spike_term_nonneg hq1 mu ell g M

theorem fiber_spike_term_le_price (q mu ell ts : ℝ) (g : ℝ → ℝ) (M : ℕ)
    (hM : (M : ℝ) < ts * mu) :
    fiberSpikeTerm q mu ell g M ≤ fiberSpikePrice q mu ell ts g := by
  exact le_csSup ((fiber_spike_widths_finite ts mu).image _).bddAbove ⟨M,hM,rfl⟩

theorem fiber_deficit_rank {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (g : ℝ → ℝ) (M : ℕ) (j : ℤ) :
    fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - fiberF q mu M j ≤ fiberDeficit q mu g M := by
  obtain ⟨k,_,_,heq,hmin⟩ := fiber_minimum_attained hq0 hq1 hmu M
  have h := hmin j
  have hm : fiberMinimum q mu M ≤ fiberF q mu M j := by rwa [heq]
  unfold fiberDeficit
  linarith only [hm,le_max_right (0 : ℝ) (fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) - fiberMinimum q mu M)]

theorem fiber_spike_deficit_price {q mu ell ts : ℝ} (hq1 : q < 1)
    (g : ℝ → ℝ) (M : ℕ) (hM : (M : ℝ) < ts * mu) :
    fiberDeficit q mu g M ≤ fiberSpikePrice q mu ell ts g * Real.exp (ell * mu) * (1 - q) ^ M := by
  have hp : 0 < (1 - q) ^ M := pow_pos (sub_pos.mpr hq1) M
  have h := mul_le_mul_of_nonneg_right (fiber_spike_term_le_price q mu ell ts g M hM)
    (mul_nonneg (Real.exp_pos (ell * mu)).le hp.le)
  have hid : fiberSpikeTerm q mu ell g M * (Real.exp (ell * mu) * (1 - q) ^ M) =
      fiberDeficit q mu g M := by
    unfold fiberSpikeTerm
    rw [show -ell * mu = -(ell * mu) by ring,Real.exp_neg]
    field_simp [hp.ne',Real.exp_ne_zero (ell * mu)]
  rw [hid] at h
  simpa only [mul_assoc] using h

theorem fiber_spike_pointwise {q mu ell ts : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (hts : 0 < ts) (g : ℝ → ℝ)
    (hhigh : ∀ (M : ℕ) (j : ℤ), ts * mu ≤ (M : ℝ) →
      fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) ≤ fiberF q mu M j) :
    ∀ (M : ℕ) (j : ℤ), fiberPsi ((M : ℝ) / mu) + g ((M : ℝ) / mu) -
      fiberSpikePrice q mu ell ts g * Real.exp (ell * mu) * (1 - q) ^ M ≤ fiberF q mu M j := by
  intro M j
  by_cases hM : (M : ℝ) < ts * mu
  · have h := fiber_deficit_rank hq0 hq1 hmu g M j
    have hp := fiber_spike_deficit_price (ell := ell) (ts := ts) hq1 g M hM
    linarith only [h,hp]
  have h := hhigh M j (le_of_not_gt hM)
  have hprice := fiber_spike_price_nonneg hq1 hts hmu ell g
  have hw : 0 ≤ fiberSpikePrice q mu ell ts g * Real.exp (ell * mu) * (1 - q) ^ M :=
    mul_nonneg (mul_nonneg hprice (Real.exp_pos _).le) (pow_pos (sub_pos.mpr hq1) M).le
  linarith only [h,hw]

end Erdos993Lean.Analytic.V213
