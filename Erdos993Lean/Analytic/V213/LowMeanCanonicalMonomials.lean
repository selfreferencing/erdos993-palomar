module

public import Erdos993Lean.Analytic.V213.LowMeanKernelMonomials

/-!
Canonical monomial identities and coefficient grouping. Grouping equal
exponents is justified algebraically, including the priced term's mergers
at boundary ranks. The finite checker will compare every grouped coefficient
and prove support coverage; a printed count is not used as an identity.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanTermExponent (t : ℝ × ℤ × ℤ) : ℤ × ℤ := t.2
noncomputable def lowMeanTermCoefficient (terms : List (ℝ × ℤ × ℤ)) (p : ℤ × ℤ) : ℝ :=
  (terms.map fun t => if lowMeanTermExponent t = p then t.1 else 0).sum

theorem lowMean_monomial_add (c d : ℝ) (a b : ℤ) (q : ℝ) :
    lowMeanMonomial (c + d) a b q = lowMeanMonomial c a b q + lowMeanMonomial d a b q := by
  unfold lowMeanMonomial
  ring

/-- Grouping a finite term list by its exponents preserves its exact value. -/
theorem lowMean_monomial_grouped (terms : List (ℝ × ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (q : ℝ)
    (hS : ∀ t ∈ terms, lowMeanTermExponent t ∈ S) :
    (terms.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum =
      ∑ p ∈ S, lowMeanMonomial (lowMeanTermCoefficient terms p) p.1 p.2 q := by
  induction terms with
  | nil => simp [lowMeanTermCoefficient, lowMeanMonomial]
  | cons t ts ih =>
    have htail : ∀ t ∈ ts, lowMeanTermExponent t ∈ S := fun t ht => hS t (List.mem_cons_of_mem _ ht)
    have hs : (∑ p ∈ S, lowMeanMonomial (if lowMeanTermExponent t = p then t.1 else 0) p.1 p.2 q) =
        lowMeanMonomial t.1 t.2.1 t.2.2 q := by
      rw [Finset.sum_eq_single_of_mem (lowMeanTermExponent t) (hS t (List.mem_cons_self))]
      · simp [lowMeanTermExponent]
      · intro p hp hpt
        simp [Ne.symm hpt, lowMeanMonomial]
    simp only [List.map_cons, List.sum_cons, lowMeanTermCoefficient]
    simp_rw [lowMean_monomial_add]
    rw [Finset.sum_add_distrib, hs]
    exact congrArg (fun x => lowMeanMonomial t.1 t.2.1 t.2.2 q + x) (ih htail)

/-- Coefficient equality and exponent coverage prove a transcription's
whole-function identity, not just its value at selected probabilities. -/
theorem lowMean_monomial_identity_of_coefficients
    (source terms : List (ℝ × ℤ × ℤ)) (S : Finset (ℤ × ℤ))
    (hsource : ∀ t ∈ source, lowMeanTermExponent t ∈ S)
    (hterms : ∀ t ∈ terms, lowMeanTermExponent t ∈ S)
    (hcoeff : ∀ p ∈ S, lowMeanTermCoefficient source p = lowMeanTermCoefficient terms p)
    (q : ℝ) :
    (source.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum =
      (terms.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum := by
  rw [lowMean_monomial_grouped source S q hsource, lowMean_monomial_grouped terms S q hterms]
  exact Finset.sum_congr rfl (fun p hp => by rw [hcoeff p hp])

noncomputable def lowMeanCanonicalTerms (M : ℕ) (j : ℤ) (wL wR z : ℝ) : List (ℝ × ℤ × ℤ) :=
  if j = -1 then [(-wR, 0, (M : ℤ)), (z, 0, (M : ℤ))]
  else if j = (M : ℤ) + 1 then [(-wL, (M : ℤ), 0), (z, 0, (M : ℤ))]
  else if 0 ≤ j ∧ j ≤ M then
    [(lowMeanCoeffL M j.toNat wL, j - 1, (M : ℤ) - j + 1),
      (lowMeanCoeffR M j.toNat wR, j + 1, (M : ℤ) - j - 1), (z, 0, (M : ℤ))]
  else [(z, 0, (M : ℤ))]

/-- The exact kernel plus price on every integer rank. -/
theorem lowMean_canonical_identity (M : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (wL wR z : ℝ) :
    (lowMeanCanonicalTerms M j wL wR z |>.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum =
      kernel2 q wL wR M j + z * (1 - q) ^ M := by
  unfold lowMeanCanonicalTerms
  split_ifs with hjneg hjtop hj
  · rw [hjneg, lowMean_kernel_neg_one M hq1]
    simp [lowMeanMonomial]
  · rw [hjtop, lowMean_kernel_top M hq0]
    simp [lowMeanMonomial]
  · have hn : j.toNat ≤ M := by omega
    have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.1
    have hsub : ((M - j.toNat : ℕ) : ℤ) = (M : ℤ) - j := by omega
    have hk := lowMean_kernel_monomials (wL := wL) (wR := wR) hn hq0 hq1
    rw [he, hsub] at hk
    rw [hk]
    simp [lowMeanMonomial]
    ring
  · rw [lowMean_kernel_outside M q wL wR j (by omega)]
    simp [lowMeanMonomial]

theorem lowMean_canonical_exponent (M : ℕ) (j : ℤ) (wL wR z : ℝ)
    {t : ℝ × ℤ × ℤ} (ht : t ∈ lowMeanCanonicalTerms M j wL wR z) : t.2.1 + t.2.2 = M := by
  unfold lowMeanCanonicalTerms at ht
  split_ifs at ht <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  · rcases ht with rfl | rfl <;> simp
  · rcases ht with rfl | rfl <;> simp
  · rcases ht with rfl | rfl | rfl <;> dsimp only <;> omega
  · subst t
    simp

theorem lowMean_support_zero (a b : ℤ) (L H tau q : ℝ) : lowMeanSupport 0 a b L H tau q = 0 := by
  simp [lowMeanSupport, lowMeanPiMax, lowMeanPiA, lowMeanPiB, lowMeanPiC,
    lowMeanQuadMinimum, lowMeanQuad, lowMeanMonomial]

/-- Zero coefficients may be retained in a canonical list without imposing
an artificial nonzero premise or changing the slack budget. -/
theorem lowMean_signedMonomial_support_all (c : ℝ) (a b : ℤ) (hm : 0 ≤ a + b)
    {L H tau q : ℝ} (hL : 0 < L) (hH : H < 1) (hLH : L < H)
    (htau : tau ∈ Set.Icc L H) (hq : q ∈ Set.Icc L H) :
    lowMeanSupport c a b L H tau q ≤ lowMeanMonomial c a b q := by
  by_cases hc : c = 0
  · simp [hc, lowMean_support_zero, lowMeanMonomial]
  · exact lowMean_signedMonomial_support hc a b hm hL hH hLH htau hq

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_monomial_identity_of_coefficients
#print axioms Erdos993Lean.Analytic.V213.lowMean_canonical_identity
#print axioms Erdos993Lean.Analytic.V213.lowMean_signedMonomial_support_all
