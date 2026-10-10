module

public import Mathlib

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

#print axioms mul_le_mul_iff_of_pos_left

/-!
The two-term convolution argument printed in version 2.13 of the manuscript, Lemma 2.1.
Integer-indexed coefficients are zero below zero.  Strict positive support
includes the empty product, whose mass is concentrated at zero.
No mode/mean theorem is assumed in this module.
-/

namespace Erdos993Lean.Analytic.V213

open Finset Polynomial

namespace Bernoulli

def LogConcaveZ (a : ℤ → ℝ) : Prop :=
  ∀ j, a (j - 1) * a (j + 1) ≤ a j * a j

def NoInternalZerosZ (a : ℤ → ℝ) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → 0 < a i → 0 < a k → 0 < a j

structure PositiveSupport (a : ℤ → ℝ) (T : ℕ) : Prop where
  nonneg : ∀ j, 0 ≤ a j
  pos : ∀ j, 0 ≤ j → j ≤ (T : ℤ) → 0 < a j
  zero : ∀ j, j < 0 ∨ (T : ℤ) < j → a j = 0

theorem PositiveSupport.noInternalZeros {a : ℤ → ℝ} {T : ℕ}
    (h : PositiveSupport a T) : NoInternalZerosZ a := by
  intro i j k hij hjk hi hk
  have hi0 : 0 ≤ i := by
    by_contra hn
    have hz := h.zero i (Or.inl (by omega))
    linarith
  have hkT : k ≤ (T : ℤ) := by
    by_contra hn
    have hz := h.zero k (Or.inr (by omega))
    linarith
  exact h.pos j (by omega) (by omega)

/-- The cross term required by the printed two-term identity. -/
theorem adjacent_cross {a : ℤ → ℝ}
    (hnonneg : ∀ j, 0 ≤ a j) (hnz : NoInternalZerosZ a)
    (hlc : LogConcaveZ a) (j : ℤ) :
    a (j - 2) * a (j + 1) ≤ a (j - 1) * a j := by
  by_cases hleft : a (j - 2) = 0
  · simp only [hleft, zero_mul]
    exact mul_nonneg (hnonneg _) (hnonneg _)
  by_cases hright : a (j + 1) = 0
  · simp only [hright, mul_zero]
    exact mul_nonneg (hnonneg _) (hnonneg _)
  have hleftpos : 0 < a (j - 2) := lt_of_le_of_ne (hnonneg _) (Ne.symm hleft)
  have hrightpos : 0 < a (j + 1) := lt_of_le_of_ne (hnonneg _) (Ne.symm hright)
  have hjpos : 0 < a j := hnz (j - 2) j (j + 1) (by omega) (by omega)
    hleftpos hrightpos
  have hprev : a (j - 2) * a j ≤ a (j - 1) * a (j - 1) := by
    have h1 : j - 1 - 1 = j - 2 := by omega
    have h2 : j - 1 + 1 = j := by omega
    simpa only [h1, h2] using hlc (j - 1)
  apply (mul_le_mul_iff_of_pos_left hjpos).mp
  calc
    a j * (a (j - 2) * a (j + 1)) =
        (a (j - 2) * a j) * a (j + 1) := by ring
    _ ≤ (a (j - 1) * a (j - 1)) * a (j + 1) :=
      mul_le_mul_of_nonneg_right hprev (hnonneg _)
    _ = a (j - 1) * (a (j - 1) * a (j + 1)) := by ring
    _ ≤ a (j - 1) * (a j * a j) :=
      mul_le_mul_of_nonneg_left (hlc j) (hnonneg _)
    _ = a j * (a (j - 1) * a j) := by ring

def twoTerm (u v : ℝ) (a : ℤ → ℝ) (j : ℤ) : ℝ :=
  u * a j + v * a (j - 1)

theorem twoTerm_lc_identity (u v : ℝ) (a : ℤ → ℝ) (j : ℤ) :
    (twoTerm u v a j) ^ 2 - twoTerm u v a (j - 1) * twoTerm u v a (j + 1) =
      u ^ 2 * (a j ^ 2 - a (j - 1) * a (j + 1)) +
      v ^ 2 * (a (j - 1) ^ 2 - a (j - 2) * a j) +
      u * v * (a j * a (j - 1) - a (j - 2) * a (j + 1)) := by
  have h1 : j - 1 - 1 = j - 2 := by omega
  have h2 : j + 1 - 1 = j := by omega
  simp only [twoTerm, h1, h2]
  ring

theorem twoTerm_logConcave {a : ℤ → ℝ} {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hnonneg : ∀ j, 0 ≤ a j) (hnz : NoInternalZerosZ a)
    (hlc : LogConcaveZ a) : LogConcaveZ (twoTerm u v a) := by
  intro j
  have h1 : 0 ≤ a j ^ 2 - a (j - 1) * a (j + 1) := by
    nlinarith only [hlc j]
  have hp : a (j - 2) * a j ≤ a (j - 1) * a (j - 1) := by
    have h1 : j - 1 - 1 = j - 2 := by omega
    have h2 : j - 1 + 1 = j := by omega
    simpa only [h1, h2] using hlc (j - 1)
  have h2 : 0 ≤ a (j - 1) ^ 2 - a (j - 2) * a j := by nlinarith only [hp]
  have h3 : 0 ≤ a j * a (j - 1) - a (j - 2) * a (j + 1) := by
    nlinarith only [adjacent_cross hnonneg hnz hlc j]
  have h : 0 ≤ (twoTerm u v a j) ^ 2 -
      twoTerm u v a (j - 1) * twoTerm u v a (j + 1) := by
    rw [twoTerm_lc_identity]
    exact add_nonneg
      (add_nonneg (mul_nonneg (sq_nonneg u) h1) (mul_nonneg (sq_nonneg v) h2))
      (mul_nonneg (mul_nonneg hu hv) h3)
  nlinarith only [h]

theorem PositiveSupport.twoTerm {a : ℤ → ℝ} {T : ℕ} {u v : ℝ}
    (h : PositiveSupport a T) (hu : 0 < u) (hv : 0 < v) :
    PositiveSupport (twoTerm u v a) (T + 1) := by
  constructor
  · intro j
    exact add_nonneg (mul_nonneg hu.le (h.nonneg j))
      (mul_nonneg hv.le (h.nonneg (j - 1)))
  · intro j hj0 hjT
    by_cases hj : j ≤ (T : ℤ)
    · exact add_pos_of_pos_of_nonneg (mul_pos hu (h.pos j hj0 hj))
        (mul_nonneg hv.le (h.nonneg (j - 1)))
    · have hprev : 0 ≤ j - 1 ∧ j - 1 ≤ (T : ℤ) := by omega
      exact add_pos_of_nonneg_of_pos (mul_nonneg hu.le (h.nonneg j))
        (mul_pos hv (h.pos (j - 1) hprev.1 hprev.2))
  · intro j hj
    have hz : a j = 0 := h.zero j (by rcases hj with hj | hj <;> omega)
    have hp : a (j - 1) = 0 := h.zero (j - 1) (by rcases hj with hj | hj <;> omega)
    change u * a j + v * a (j - 1) = 0
    rw [hz, hp]
    ring

def deltaZero (j : ℤ) : ℝ := if j = 0 then 1 else 0

theorem deltaZero_support : PositiveSupport deltaZero 0 := by
  constructor
  · intro j
    dsimp [deltaZero]
    split <;> norm_num
  · intro j hj0 hj
    have hz : j = 0 := by omega
    simp [deltaZero, hz]
  · intro j hj
    have hz : j ≠ 0 := by rcases hj with hj | hj <;> omega
    simp [deltaZero, hz]

theorem deltaZero_logConcave : LogConcaveZ deltaZero := by
  intro j
  by_cases h : j - 1 = 0
  · have h' : j + 1 ≠ 0 := by omega
    simp only [deltaZero, if_pos h, if_neg h', mul_zero]
    split_ifs <;> norm_num
  · simp only [deltaZero, if_neg h, zero_mul]
    split_ifs <;> norm_num

noncomputable def bernFactor (p : ℝ) : ℝ[X] := C (1 - p) + C p * X

noncomputable def bernPoly {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ[X] :=
  ∏ i ∈ s, bernFactor (p i)

noncomputable def coeffZ (P : ℝ[X]) (j : ℤ) : ℝ :=
  if 0 ≤ j then P.coeff j.toNat else 0

@[simp] theorem coeffZ_nat (P : ℝ[X]) (k : ℕ) : coeffZ P (k : ℤ) = P.coeff k := by
  simp [coeffZ]

theorem coeffZ_one : coeffZ 1 = deltaZero := by
  funext j
  by_cases hj : 0 ≤ j
  · have hz : j.toNat = 0 ↔ j = 0 := by omega
    simp [coeffZ, hj, Polynomial.coeff_one, deltaZero, hz]
  · have hz : j ≠ 0 := by omega
    simp [coeffZ, hj, deltaZero, hz]

theorem coeffZ_bernFactor_mul (p : ℝ) (P : ℝ[X]) :
    coeffZ (bernFactor p * P) = twoTerm (1 - p) p (coeffZ P) := by
  have hexpand : bernFactor p * P = C (1 - p) * P + C p * (X * P) := by
    unfold bernFactor
    ring
  funext j
  by_cases hj : 0 ≤ j
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg hj⟩
    cases k with
    | zero => simp [hexpand, twoTerm, coeffZ, Polynomial.coeff_X_mul_zero]
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      simp only [twoTerm, Nat.succ_eq_add_one, hk, coeffZ_nat, hexpand,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
  · have hj' : ¬0 ≤ j - 1 := by omega
    simp only [coeffZ, twoTerm, if_neg hj, if_neg hj', mul_zero, add_zero]

theorem bernPoly_empty {ι : Type*} (p : ι → ℝ) : bernPoly ∅ p = 1 := by
  simp [bernPoly]

theorem bernPoly_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (i : ι) (hi : i ∉ s) :
    bernPoly (insert i s) p = bernFactor (p i) * bernPoly s p := by
  simp only [bernPoly, Finset.prod_insert hi]

/-- The full Bernoulli support and log-concavity assertion, including no trials. -/
theorem bernPoly_support_logConcave {ι : Type*}
    (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1) :
    PositiveSupport (coeffZ (bernPoly s p)) s.card ∧
      LogConcaveZ (coeffZ (bernPoly s p)) := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty =>
    intro hp
    simpa only [bernPoly_empty, coeffZ_one, Finset.card_empty] using
      And.intro deltaZero_support deltaZero_logConcave
  | @insert i s hi ih =>
    intro hp
    have hpi := hp i (by simp)
    have hps : ∀ j ∈ s, 0 < p j ∧ p j < 1 := fun j hj => hp j (by simp [hj])
    obtain ⟨hs, hlc⟩ := ih hps
    rw [bernPoly_insert s p i hi, coeffZ_bernFactor_mul]
    constructor
    · simpa only [Finset.card_insert_of_notMem hi] using
        hs.twoTerm (sub_pos.mpr hpi.2) hpi.1
    · exact twoTerm_logConcave (sub_nonneg.mpr hpi.2.le) hpi.1.le
        hs.nonneg hs.noInternalZeros hlc

theorem bernPoly_support {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1) :
    PositiveSupport (coeffZ (bernPoly s p)) s.card :=
  (bernPoly_support_logConcave s p hp).1

theorem bernPoly_logConcave {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1) :
    LogConcaveZ (coeffZ (bernPoly s p)) :=
  (bernPoly_support_logConcave s p hp).2

theorem bernPoly_noInternalZeros {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1) :
    NoInternalZerosZ (coeffZ (bernPoly s p)) :=
  (bernPoly_support s p hp).noInternalZeros

theorem bernPoly_eval_one {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    (bernPoly s p).eval 1 = 1 := by
  simp [bernPoly, bernFactor, Polynomial.eval_prod]

/-- The second identity printed in Lemma 2.1. -/
theorem addTrial_determinant_identity (a : ℤ → ℝ) (t₁ t₂ : ℝ) (k : ℤ) :
    twoTerm (1 - t₂) t₂ a (k + 1) * twoTerm (1 - t₁) t₁ a k -
      twoTerm (1 - t₁) t₁ a (k + 1) * twoTerm (1 - t₂) t₂ a k =
      (t₂ - t₁) * (a k ^ 2 - a (k - 1) * a (k + 1)) := by
  have hk : k + 1 - 1 = k := by omega
  simp only [twoTerm, hk]
  ring

theorem addTrial_determinant_nonneg {a : ℤ → ℝ} {t₁ t₂ : ℝ}
    (hlc : LogConcaveZ a) (ht : t₁ ≤ t₂) (k : ℤ) :
    twoTerm (1 - t₁) t₁ a (k + 1) * twoTerm (1 - t₂) t₂ a k ≤
      twoTerm (1 - t₂) t₂ a (k + 1) * twoTerm (1 - t₁) t₁ a k := by
  have hd : 0 ≤ a k ^ 2 - a (k - 1) * a (k + 1) := by nlinarith only [hlc k]
  have h := mul_nonneg (sub_nonneg.mpr ht) hd
  rw [← addTrial_determinant_identity a t₁ t₂ k] at h
  linarith only [h]

end Bernoulli
end Erdos993Lean.Analytic.V213

#check Erdos993Lean.Analytic.V213.Bernoulli.PositiveSupport.noInternalZeros
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.PositiveSupport.noInternalZeros

#check Erdos993Lean.Analytic.V213.Bernoulli.adjacent_cross
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.adjacent_cross

#check Erdos993Lean.Analytic.V213.Bernoulli.twoTerm_lc_identity
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.twoTerm_lc_identity

#check Erdos993Lean.Analytic.V213.Bernoulli.twoTerm_logConcave
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.twoTerm_logConcave

#check Erdos993Lean.Analytic.V213.Bernoulli.PositiveSupport.twoTerm
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.PositiveSupport.twoTerm

#check Erdos993Lean.Analytic.V213.Bernoulli.deltaZero_support
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.deltaZero_support

#check Erdos993Lean.Analytic.V213.Bernoulli.deltaZero_logConcave
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.deltaZero_logConcave

#check Erdos993Lean.Analytic.V213.Bernoulli.coeffZ_nat
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.coeffZ_nat

#check Erdos993Lean.Analytic.V213.Bernoulli.coeffZ_one
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.coeffZ_one

#check Erdos993Lean.Analytic.V213.Bernoulli.coeffZ_bernFactor_mul
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.coeffZ_bernFactor_mul

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_empty
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_empty

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_insert
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_insert

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_support_logConcave
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_support_logConcave

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_support
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_support

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_logConcave
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_logConcave

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_noInternalZeros
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_noInternalZeros

#check Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_eval_one
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.bernPoly_eval_one

#check Erdos993Lean.Analytic.V213.Bernoulli.addTrial_determinant_identity
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.addTrial_determinant_identity

#check Erdos993Lean.Analytic.V213.Bernoulli.addTrial_determinant_nonneg
#print axioms Erdos993Lean.Analytic.V213.Bernoulli.addTrial_determinant_nonneg
