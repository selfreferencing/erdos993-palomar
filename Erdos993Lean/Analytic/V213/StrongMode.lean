module

public import Erdos993Lean.Analytic.V213.BernoulliMass

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

#print axioms mul_lt_mul_iff_of_pos_left

/-!
Lemma 2.1's added-trial/deleted-trial proof.  A strict upper cap
on the probabilities replaces their attained maximum in the internal
theorem.  The literal maximum statement is a corollary.  The empty
family is included in the cap theorem and closes by its support.
-/

namespace Erdos993Lean.Analytic.V213.Bernoulli

open Finset Polynomial

theorem bernPoly_factor {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) {i : ι} (hi : i ∈ s) :
    bernPoly s p = bernFactor (p i) * bernPoly (s.erase i) p := by
  exact (Finset.mul_prod_erase s (fun i => bernFactor (p i)) hi).symm

theorem bernFactor_mul_coeff_succ (p : ℝ) (P : ℝ[X]) (k : ℕ) :
    (bernFactor p * P).coeff (k + 1) =
      (1 - p) * P.coeff (k + 1) + p * P.coeff k := by
  have h : bernFactor p * P = C (1 - p) * P + C p * (X * P) := by
    unfold bernFactor
    ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul]

theorem derivative_bernFactor (p : ℝ) :
    Polynomial.derivative (bernFactor p) = C p := by
  simp [bernFactor]

theorem derivative_bernPoly {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) :
    Polynomial.derivative (bernPoly s p) =
      ∑ i ∈ s, C (p i) * bernPoly (s.erase i) p := by
  unfold bernPoly
  rw [Polynomial.derivative_prod_finset]
  apply Finset.sum_congr rfl
  intro i hi
  rw [derivative_bernFactor]
  ring

/-- The PGF's mean equals the sum of its trial probabilities. -/
theorem bernPoly_derivative_eval_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) :
    (Polynomial.derivative (bernPoly s p)).eval 1 = ∑ i ∈ s, p i := by
  rw [derivative_bernPoly, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, bernPoly_eval_one, mul_one]

theorem derivative_augmented {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (c : ℝ) :
    Polynomial.derivative (bernFactor c * bernPoly s p) =
      C c * bernPoly s p +
      ∑ i ∈ s, C (p i) * (bernFactor c * bernPoly (s.erase i) p) := by
  rw [Polynomial.derivative_mul, derivative_bernFactor, derivative_bernPoly,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The paper's size-biased coefficient identity for the augmented family. -/
theorem augmented_weighted_coefficient {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (c : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * (bernFactor c * bernPoly s p).coeff (k + 1) =
      c * (bernPoly s p).coeff k +
      ∑ i ∈ s, p i * (bernFactor c * bernPoly (s.erase i) p).coeff k := by
  have h := congrArg (fun P : ℝ[X] => P.coeff k) (derivative_augmented s p c)
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_add,
    Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Nat.cast_add,
    Nat.cast_one] at h
  nlinarith only [h]

/-- The displayed drift identity, with the added trial's term separated. -/
theorem augmented_drift_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (c : ℝ) (k : ℕ) :
    ((∑ i ∈ s, p i) + c - ((k : ℝ) + 1)) *
        (bernFactor c * bernPoly s p).coeff (k + 1) =
      c * (1 - c) * ((bernPoly s p).coeff (k + 1) - (bernPoly s p).coeff k) +
      ∑ i ∈ s, p i * (1 - p i) *
        ((bernFactor c * bernPoly (s.erase i) p).coeff (k + 1) -
          (bernFactor c * bernPoly (s.erase i) p).coeff k) := by
  let F := bernPoly s p
  let Y := bernFactor c * F
  let G := fun i => bernFactor c * bernPoly (s.erase i) p
  have hrec (i : ι) (hi : i ∈ s) :
      Y.coeff (k + 1) = (1 - p i) * (G i).coeff (k + 1) + p i * (G i).coeff k := by
    have hY : Y = bernFactor (p i) * G i := by
      dsimp [Y, F, G]
      rw [bernPoly_factor s p hi]
      ring
    rw [hY, bernFactor_mul_coeff_succ]
  have hadd : Y.coeff (k + 1) = (1 - c) * F.coeff (k + 1) + c * F.coeff k :=
    bernFactor_mul_coeff_succ c F k
  have hweight : ((k : ℝ) + 1) * Y.coeff (k + 1) =
      c * F.coeff k + ∑ i ∈ s, p i * (G i).coeff k :=
    augmented_weighted_coefficient s p c k
  have hsum : (∑ i ∈ s, p i * (1 - p i) *
        ((G i).coeff (k + 1) - (G i).coeff k)) =
      (∑ i ∈ s, p i) * Y.coeff (k + 1) - ∑ i ∈ s, p i * (G i).coeff k := by
    calc
      _ = ∑ i ∈ s, (p i * Y.coeff (k + 1) - p i * (G i).coeff k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrec i hi]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change ((∑ i ∈ s, p i) + c - ((k : ℝ) + 1)) * Y.coeff (k + 1) =
    c * (1 - c) * (F.coeff (k + 1) - F.coeff k) +
      ∑ i ∈ s, p i * (1 - p i) * ((G i).coeff (k + 1) - (G i).coeff k)
  rw [hsum]
  have hadded : c * (1 - c) * (F.coeff (k + 1) - F.coeff k) =
      c * Y.coeff (k + 1) - c * F.coeff k := by
    rw [hadd]
    ring
  rw [hadded]
  nlinarith only [hweight]

/-- Replacing one probability by a larger strict probability preserves a strict rise. -/
theorem replace_trial_preserves_rise {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (c : ℝ) (k : ℕ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1)
    (hc : 0 < c ∧ c < 1) (hk : k < s.card)
    (hrise : (bernPoly s p).coeff k < (bernPoly s p).coeff (k + 1))
    {i : ι} (hi : i ∈ s) (hcap : p i ≤ c) :
    (bernFactor c * bernPoly (s.erase i) p).coeff k <
      (bernFactor c * bernPoly (s.erase i) p).coeff (k + 1) := by
  have hpe : ∀ j ∈ s.erase i, 0 < p j ∧ p j < 1 :=
    fun j hj => hp j (Finset.mem_of_mem_erase hj)
  have hs := bernPoly_support s p hp
  have he := bernPoly_support (s.erase i) p hpe
  have hfk : 0 < (bernPoly s p).coeff k := by
    have h := hs.pos (k : ℤ) (by omega) (by omega)
    simpa only [coeffZ_nat] using h
  have hak : 0 < coeffZ (bernPoly (s.erase i) p) (k : ℤ) :=
    he.pos (k : ℤ) (by omega) (by rw [Finset.card_erase_of_mem hi]; omega)
  have hgk : 0 < (bernFactor c * bernPoly (s.erase i) p).coeff k := by
    rw [← coeffZ_nat, coeffZ_bernFactor_mul]
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hc.2) hak)
      (mul_nonneg hc.1.le (he.nonneg _))
  have hd := addTrial_determinant_nonneg (bernPoly_logConcave (s.erase i) p hpe)
    hcap (k : ℤ)
  simp only [← coeffZ_bernFactor_mul, ← bernPoly_factor s p hi] at hd
  have hkZ : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hkZ] at hd
  simp only [coeffZ_nat] at hd
  have hstrict := lt_of_lt_of_le (mul_lt_mul_of_pos_right hrise hgk) hd
  apply (mul_lt_mul_iff_of_pos_left hfk).mp
  nlinarith only [hstrict]

/-- The paper's stronger mode bound, with any strict upper probability cap. -/
theorem bernPoly_succ_le_of_mean_add_cap_le {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (c : ℝ) (k : ℕ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1)
    (hc : 0 < c ∧ c < 1) (hcap : ∀ i ∈ s, p i ≤ c)
    (hmean : (∑ i ∈ s, p i) + c ≤ (k : ℝ) + 1) :
    (bernPoly s p).coeff (k + 1) ≤ (bernPoly s p).coeff k := by
  classical
  by_contra hn
  have hrise : (bernPoly s p).coeff k < (bernPoly s p).coeff (k + 1) := lt_of_not_ge hn
  have hs := bernPoly_support s p hp
  have hk : k < s.card := by
    by_contra hk
    have hz := hs.zero ((k + 1 : ℕ) : ℤ) (Or.inr (by omega))
    have hnonneg := hs.nonneg (k : ℤ)
    simp only [coeffZ_nat] at hz hnonneg
    linarith
  have hgrise (i : ι) (hi : i ∈ s) :=
    replace_trial_preserves_rise s p c k hp hc hk hrise hi (hcap i hi)
  have hsum : 0 ≤ ∑ i ∈ s, p i * (1 - p i) *
      ((bernFactor c * bernPoly (s.erase i) p).coeff (k + 1) -
        (bernFactor c * bernPoly (s.erase i) p).coeff k) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (hp i hi).1.le (sub_nonneg.mpr (hp i hi).2.le))
      (sub_nonneg.mpr (hgrise i hi).le)
  have hadded : 0 < c * (1 - c) *
      ((bernPoly s p).coeff (k + 1) - (bernPoly s p).coeff k) :=
    mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (sub_pos.mpr hrise)
  have hmass : 0 ≤ (bernFactor c * bernPoly s p).coeff (k + 1) := by
    have h := (hs.twoTerm (sub_pos.mpr hc.2) hc.1).nonneg ((k + 1 : ℕ) : ℤ)
    rw [← coeffZ_bernFactor_mul, coeffZ_nat] at h
    exact h
  have hleft := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmean) hmass
  have hdrift := augmented_drift_identity s p c k
  linarith only [hdrift, hleft, hadded, hsum]

/-- Literal maximum-probability form of Lemma 2.1. -/
theorem bernPoly_succ_le_of_mean_add_max_le {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (pStar : ℝ) (k : ℕ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1)
    (hattained : ∃ i ∈ s, p i = pStar)
    (hmax : ∀ i ∈ s, p i ≤ pStar)
    (hmean : (∑ i ∈ s, p i) + pStar ≤ (k : ℝ) + 1) :
    (bernPoly s p).coeff (k + 1) ≤ (bernPoly s p).coeff k := by
  obtain ⟨i, hi, heq⟩ := hattained
  have hc : 0 < pStar ∧ pStar < 1 := by simpa only [heq] using hp i hi
  exact bernPoly_succ_le_of_mean_add_cap_le s p pStar k hp hc hmax hmean

end Erdos993Lean.Analytic.V213.Bernoulli

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_factor
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_factor

#check Erdos993Lean.Analytic.V213.Bernoulli.bernFactor_mul_coeff_succ
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernFactor_mul_coeff_succ

#check Erdos993Lean.Analytic.V213.Bernoulli.derivative_bernFactor
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.derivative_bernFactor

#check Erdos993Lean.Analytic.V213.Bernoulli.derivative_bernPoly
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.derivative_bernPoly

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_derivative_eval_one
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_derivative_eval_one

#check Erdos993Lean.Analytic.V213.Bernoulli.derivative_augmented
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.derivative_augmented

#check Erdos993Lean.Analytic.V213.Bernoulli.augmented_weighted_coefficient
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.augmented_weighted_coefficient

#check Erdos993Lean.Analytic.V213.Bernoulli.augmented_drift_identity
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.augmented_drift_identity

#check Erdos993Lean.Analytic.V213.Bernoulli.replace_trial_preserves_rise
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.replace_trial_preserves_rise

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_succ_le_of_mean_add_cap_le
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_succ_le_of_mean_add_cap_le

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_succ_le_of_mean_add_max_le
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_succ_le_of_mean_add_max_le
