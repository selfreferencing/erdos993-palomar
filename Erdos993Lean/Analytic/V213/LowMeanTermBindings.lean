module

public import Erdos993Lean.Analytic.V213.LowMeanCanonicalMonomials
public import Erdos993Lean.Analytic.V213.LowMeanIntegerShape

/-!
Integer coefficient and exponent coverage checks. Every exponent in
both lists is included in the comparison, and every coefficient is checked
by signed integer cross multiplication. Thus a grouped transcription is
proved equal to its source as a function on the entire probability domain.
No generated record is used here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

@[reducible] def lowMeanIntegerTerm := lowMeanFraction × ℤ × ℤ
noncomputable def lowMeanIntegerTermsReal (ts : List lowMeanIntegerTerm) : List (ℝ × ℤ × ℤ) :=
  ts.map fun t => (lowMeanFractionReal t.1, t.2)
def lowMeanIntegerTermsValid (ts : List lowMeanIntegerTerm) : Bool :=
  ts.all fun t => decide (lowMeanFractionValid t.1)
def lowMeanIntegerCoefficient (ts : List lowMeanIntegerTerm) (p : ℤ × ℤ) : lowMeanFraction :=
  match ts with
  | [] => (0, 1)
  | t :: rest => lowMeanFractionAdd (if t.2 = p then t.1 else (0, 1)) (lowMeanIntegerCoefficient rest p)
def lowMeanIntegerExponents (source terms : List lowMeanIntegerTerm) : List (ℤ × ℤ) :=
  (source ++ terms).map fun t => t.2
def lowMeanIntegerBindingCheck (source terms : List lowMeanIntegerTerm) : Bool :=
  lowMeanIntegerTermsValid source && lowMeanIntegerTermsValid terms &&
    (lowMeanIntegerExponents source terms).all fun p =>
      decide (lowMeanFractionEq (lowMeanIntegerCoefficient source p) (lowMeanIntegerCoefficient terms p))

theorem lowMean_integerTerms_valid {ts : List lowMeanIntegerTerm}
    (h : lowMeanIntegerTermsValid ts = true) : ∀ t ∈ ts, lowMeanFractionValid t.1 := by
  simpa [lowMeanIntegerTermsValid, List.all_eq_true] using h

theorem lowMean_integerCoefficient_valid (ts : List lowMeanIntegerTerm) (p : ℤ × ℤ)
    (h : ∀ t ∈ ts, lowMeanFractionValid t.1) : lowMeanFractionValid (lowMeanIntegerCoefficient ts p) := by
  induction ts with
  | nil => exact Nat.zero_lt_one
  | cons t ts ih =>
    apply Nat.mul_pos
    · by_cases htp : t.2 = p
      · simpa [htp, lowMeanFractionValid] using h t List.mem_cons_self
      · simp [htp]
    · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem lowMean_integerCoefficient_real (ts : List lowMeanIntegerTerm) (p : ℤ × ℤ)
    (h : ∀ t ∈ ts, lowMeanFractionValid t.1) :
    lowMeanFractionReal (lowMeanIntegerCoefficient ts p) =
      lowMeanTermCoefficient (lowMeanIntegerTermsReal ts) p := by
  induction ts with
  | nil => simp [lowMeanIntegerCoefficient, lowMeanIntegerTermsReal, lowMeanTermCoefficient, lowMeanFractionReal]
  | cons t ts ih =>
    have ht : lowMeanFractionValid (if t.2 = p then t.1 else (0, 1)) := by
      by_cases htp : t.2 = p
      · simpa [htp, lowMeanFractionValid] using h t List.mem_cons_self
      · simp [htp, lowMeanFractionValid]
    have hts : ∀ t ∈ ts, lowMeanFractionValid t.1 := fun t ht => h t (List.mem_cons_of_mem _ ht)
    rw [lowMeanIntegerCoefficient, lowMean_fraction_add ht (lowMean_integerCoefficient_valid ts p hts), ih hts]
    simp [lowMeanIntegerTermsReal, lowMeanTermCoefficient, lowMeanTermExponent]
    split_ifs <;> simp_all [lowMeanFractionReal]

/-- Exhaustive coefficient checks include the union of both exponent lists;
extra, missing, duplicate and cancelled terms cannot evade the identity. -/
theorem lowMean_integerBinding_identity (source terms : List lowMeanIntegerTerm)
    (h : lowMeanIntegerBindingCheck source terms = true) (q : ℝ) :
    ((lowMeanIntegerTermsReal source).map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum =
      ((lowMeanIntegerTermsReal terms).map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum := by
  simp only [lowMeanIntegerBindingCheck, Bool.and_eq_true] at h
  have hs := lowMean_integerTerms_valid h.1.1
  have ht := lowMean_integerTerms_valid h.1.2
  apply lowMean_monomial_identity_of_coefficients _ _ (lowMeanIntegerExponents source terms).toFinset
  · intro t hmem
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hmem
    simp only [List.mem_toFinset, lowMeanIntegerExponents, List.mem_map, lowMeanTermExponent]
    exact ⟨u, List.mem_append_left _ hu, rfl⟩
  · intro t hmem
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hmem
    simp only [List.mem_toFinset, lowMeanIntegerExponents, List.mem_map, lowMeanTermExponent]
    exact ⟨u, List.mem_append_right _ hu, rfl⟩
  · intro p hp
    have hcheck := (List.all_eq_true.mp h.2) p (List.mem_toFinset.mp hp)
    have heq : lowMeanFractionEq (lowMeanIntegerCoefficient source p) (lowMeanIntegerCoefficient terms p) :=
      of_decide_eq_true hcheck
    rw [← lowMean_integerCoefficient_real source p hs, ← lowMean_integerCoefficient_real terms p ht]
    exact (lowMean_fraction_eq_iff (lowMean_integerCoefficient_valid source p hs)
      (lowMean_integerCoefficient_valid terms p ht)).mp heq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_integerBinding_identity
