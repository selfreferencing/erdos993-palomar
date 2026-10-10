module

public import Erdos993Lean.Analytic.V213.LowMeanMonomial

/-!
The endpoint and a/(a+b) rule for the absolute monomial maximum
in Lemma 6.6, including negative exponents and a+b=0.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMeanMonomial_nonneg {c : ℝ} (hc : 0 ≤ c) (a b : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) : 0 ≤ lowMeanMonomial c a b q := by
  exact mul_nonneg (mul_nonneg hc (zpow_pos hq0 a).le)
    (zpow_pos (sub_pos.mpr hq1) b).le

theorem lowMeanMonomial_monotone {c L H : ℝ} (hc : 0 ≤ c) (a b : ℤ)
    (hL : 0 < L) (hH : H < 1)
    (hsign : ∀ q ∈ Set.Icc L H, 0 ≤ (a : ℝ) - ((a + b : ℤ) : ℝ) * q) :
    MonotoneOn (lowMeanMonomial c a b) (Set.Icc L H) := by
  have hd q (hq : q ∈ Set.Icc L H) := lowMeanMonomial_hasDerivAt c a b
    (lt_of_lt_of_le hL hq.1) (lt_of_le_of_lt hq.2 hH)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc L H)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc L H := interior_subset hq
  have hq0 := lt_of_lt_of_le hL hq'.1
  have hq1 := lt_of_le_of_lt hq'.2 hH
  rw [lowMeanMonomialD_affine c a b hq0 hq1]
  exact div_nonneg (mul_nonneg (lowMeanMonomial_nonneg hc a b hq0 hq1) (hsign q hq'))
    (mul_nonneg hq0.le (sub_nonneg.mpr hq1.le))

theorem lowMeanMonomial_antitone {c L H : ℝ} (hc : 0 ≤ c) (a b : ℤ)
    (hL : 0 < L) (hH : H < 1)
    (hsign : ∀ q ∈ Set.Icc L H, (a : ℝ) - ((a + b : ℤ) : ℝ) * q ≤ 0) :
    AntitoneOn (lowMeanMonomial c a b) (Set.Icc L H) := by
  have hd q (hq : q ∈ Set.Icc L H) := lowMeanMonomial_hasDerivAt c a b
    (lt_of_lt_of_le hL hq.1) (lt_of_le_of_lt hq.2 hH)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc L H)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc L H := interior_subset hq
  have hq0 := lt_of_lt_of_le hL hq'.1
  have hq1 := lt_of_le_of_lt hq'.2 hH
  rw [lowMeanMonomialD_affine c a b hq0 hq1]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (lowMeanMonomial_nonneg hc a b hq0 hq1) (hsign q hq'))
    (mul_nonneg hq0.le (sub_nonneg.mpr hq1.le))

/-- Bounds at just the printed candidates imply the bound everywhere. -/
theorem lowMeanMonomial_upper {c L H bound : ℝ} (hc : 0 ≤ c) (a b : ℤ)
    (hm : 0 ≤ a + b) (hL : 0 < L) (hH : H < 1) (hLH : L ≤ H)
    (hleft : lowMeanMonomial c a b L ≤ bound) (hright : lowMeanMonomial c a b H ≤ bound)
    (hmode : 0 < a + b → L ≤ (a : ℝ) / ((a + b : ℤ) : ℝ) →
      (a : ℝ) / ((a + b : ℤ) : ℝ) ≤ H →
      lowMeanMonomial c a b ((a : ℝ) / ((a + b : ℤ) : ℝ)) ≤ bound)
    {q : ℝ} (hq : q ∈ Set.Icc L H) : lowMeanMonomial c a b q ≤ bound := by
  have hmR : (0 : ℝ) ≤ ((a + b : ℤ) : ℝ) := by exact_mod_cast hm
  have hLmem : L ∈ Set.Icc L H := ⟨le_rfl, hLH⟩
  have hHmem : H ∈ Set.Icc L H := ⟨hLH, le_rfl⟩
  by_cases hm0 : a + b = 0
  · have hz : ((a + b : ℤ) : ℝ) = 0 := by rw [hm0]; norm_num
    rcases le_total 0 (a : ℝ) with ha | ha
    · exact le_trans (lowMeanMonomial_monotone hc a b hL hH
        (fun x _ => by rw [hz]; simpa using ha) hq hHmem hq.2) hright
    · exact le_trans (lowMeanMonomial_antitone hc a b hL hH
        (fun x _ => by rw [hz]; simpa using ha) hLmem hq hq.1) hleft
  · have hmpos : 0 < a + b := lt_of_le_of_ne hm (Ne.symm hm0)
    have hmRpos : (0 : ℝ) < ((a + b : ℤ) : ℝ) := by exact_mod_cast hmpos
    let tau := (a : ℝ) / ((a + b : ℤ) : ℝ)
    have he : ((a + b : ℤ) : ℝ) * tau = (a : ℝ) := by dsimp [tau]; field_simp
    by_cases htL : tau < L
    · exact le_trans (lowMeanMonomial_antitone hc a b hL hH
        (fun x hx => by nlinarith [hx.1]) hLmem hq hq.1) hleft
    · by_cases htH : H < tau
      · exact le_trans (lowMeanMonomial_monotone hc a b hL hH
          (fun x hx => by nlinarith [hx.2]) hq hHmem hq.2) hright
      · have htL' : L ≤ tau := le_of_not_gt htL
        have htH' : tau ≤ H := le_of_not_gt htH
        have ht0 : 0 < tau := lt_of_lt_of_le hL htL'
        have ht1 : tau < 1 := lt_of_le_of_lt htH' hH
        have hmb := hmode hmpos htL' htH'
        rcases le_total q tau with hqt | htq
        · exact le_trans (lowMeanMonomial_monotone hc a b hL ht1
            (fun x hx => by nlinarith [hx.2]) ⟨hq.1, hqt⟩ ⟨htL', le_rfl⟩ hqt) hmb
        · exact le_trans (lowMeanMonomial_antitone hc a b ht0 hH
            (fun x hx => by nlinarith [hx.1]) ⟨le_rfl, htH'⟩ ⟨htq, hq.2⟩ htq) hmb

/-- The exact R in Lemma 6.6, expressed using at most three evaluations. -/
noncomputable def lowMeanMonomialR (c : ℝ) (a b : ℤ) (L H : ℝ) : ℝ :=
  max |lowMeanMonomial c a b L| (max |lowMeanMonomial c a b H|
    (if 0 < a + b ∧ L ≤ (a : ℝ) / ((a + b : ℤ) : ℝ) ∧
        (a : ℝ) / ((a + b : ℤ) : ℝ) ≤ H
     then |lowMeanMonomial c a b ((a : ℝ) / ((a + b : ℤ) : ℝ))|
     else |lowMeanMonomial c a b L|))

theorem lowMeanMonomialR_bound (c : ℝ) (a b : ℤ) (hm : 0 ≤ a + b)
    {L H q : ℝ} (hL : 0 < L) (hH : H < 1) (hLH : L ≤ H) (hq : q ∈ Set.Icc L H) :
    |lowMeanMonomial c a b q| ≤ lowMeanMonomialR c a b L H := by
  have he (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
      lowMeanMonomial |c| a b x = |lowMeanMonomial c a b x| :=
    (lowMeanMonomial_abs c a b hx0 hx1).symm
  rw [← he q (lt_of_lt_of_le hL hq.1) (lt_of_le_of_lt hq.2 hH)]
  apply lowMeanMonomial_upper (abs_nonneg c) a b hm hL hH hLH ?_ ?_ ?_ hq
  · rw [he L hL (lt_of_le_of_lt hLH hH)]
    exact le_max_left _ _
  · rw [he H (lt_of_lt_of_le hL hLH) hH]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro hmpos htL htH
    rw [he _ (lt_of_lt_of_le hL htL) (lt_of_le_of_lt htH hH)]
    unfold lowMeanMonomialR
    rw [ite_eq_left ⟨hmpos, htL, htH⟩]
    exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The finite candidate maximum is attained on the closed interval. Together
with `lowMeanMonomialR_bound`, this identifies R as the exact maximum. -/
theorem lowMeanMonomialR_attained (c : ℝ) (a b : ℤ) {L H : ℝ} (hLH : L ≤ H) :
    ∃ q ∈ Set.Icc L H, |lowMeanMonomial c a b q| = lowMeanMonomialR c a b L H := by
  let tau := (a : ℝ) / ((a + b : ℤ) : ℝ)
  have hLmem : L ∈ Set.Icc L H := ⟨le_rfl, hLH⟩
  have hHmem : H ∈ Set.Icc L H := ⟨hLH, le_rfl⟩
  unfold lowMeanMonomialR
  by_cases ht : 0 < a + b ∧ L ≤ tau ∧ tau ≤ H
  · rw [ite_eq_left ht]
    rcases le_total |lowMeanMonomial c a b H| |lowMeanMonomial c a b tau| with hHt | htH
    · rw [max_eq_right hHt]
      rcases le_total |lowMeanMonomial c a b L| |lowMeanMonomial c a b tau| with hLt | htL
      · exact ⟨tau, ht.2, (max_eq_right hLt).symm⟩
      · exact ⟨L, hLmem, (max_eq_left htL).symm⟩
    · rw [max_eq_left htH]
      rcases le_total |lowMeanMonomial c a b L| |lowMeanMonomial c a b H| with hLH' | hHL'
      · exact ⟨H, hHmem, (max_eq_right hLH').symm⟩
      · exact ⟨L, hLmem, (max_eq_left hHL').symm⟩
  · rw [ite_eq_right ht, max_left_comm, max_self]
    rcases le_total |lowMeanMonomial c a b H| |lowMeanMonomial c a b L| with hHL | hLH'
    · exact ⟨L, hLmem, (max_eq_right hHL).symm⟩
    · exact ⟨H, hHmem, (max_eq_left hLH').symm⟩

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomial_upper
#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomialR_bound
#print axioms Erdos993Lean.Analytic.V213.lowMeanMonomialR_attained
