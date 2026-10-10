module

public import Erdos993Lean.Analytic.V213.SmallForestAffinePositive

/-!
The complementary coefficient regime of Lemma7.3. The sign at p=0
belongs to the nonnegative branch, exactly as printed. The positive denominator
choose(h,2) is used only for h>=2. No finite arithmetic family is imported.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset

noncomputable def adjusted (p : ℝ) (h : ℕ) : ℝ :=
  if 0 ≤ p then p else p / (h.choose 2 : ℝ)

noncomputable def affineB (a c k : ℕ) (β q : ℕ → ℝ) : ℝ :=
  q 1 + ∑ h ∈ Icc 2 (k + 1),
    (q h * ((c - 2).choose (h - 1) : ℝ) -
      adjusted (β h + q h * ((a : ℝ) - h)) h * ((c - 2).choose (h - 2) : ℝ))

theorem adjusted_of_nonneg (p : ℝ) (h : ℕ) (hp : 0 ≤ p) : adjusted p h = p := by
  simp [adjusted, hp]

theorem adjusted_zero (h : ℕ) : adjusted 0 h = 0 := by simp [adjusted]

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

theorem signed_N_bound (A : Finset (Fin F.n)) {h : ℕ}
    (h2 : 2 ≤ h) (hc : h ≤ (Aᶜ).card) (p : ℝ) :
    p * ((Aᶜ).card.choose h : ℝ) -
      (internalEdges F A : ℝ) * adjusted p h * (((Aᶜ).card - 2).choose (h - 2) : ℝ) ≤
      p * (N F A h : ℝ) := by
  by_cases hp : 0 ≤ p
  · rw [adjusted_of_nonneg p h hp]
    have hb := mul_le_mul_of_nonneg_left (N_lower_real F A h2 hc) hp
    nlinarith only [hb]
  · have hp' : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
    have hb := mul_le_mul_of_nonpos_left (N_upper_real F A h2 hc) hp'
    simp only [adjusted, hp, if_false]
    calc
      p * ((Aᶜ).card.choose h : ℝ) -
          (internalEdges F A : ℝ) * (p / (h.choose 2 : ℝ)) *
            (((Aᶜ).card - 2).choose (h - 2) : ℝ) =
          p * (((Aᶜ).card.choose h : ℝ) -
            (internalEdges F A : ℝ) / (h.choose 2 : ℝ) *
              (((Aᶜ).card - 2).choose (h - 2) : ℝ)) := by ring
      _ ≤ p * (N F A h : ℝ) := hb

theorem row_signed_bound (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hc2 : 2 ≤ (Aᶜ).card) (k h : ℕ) (w β q : ℝ) (h2 : 2 ≤ h) (hq : 0 ≤ q)
    (hline : ∀ m : ℕ, m + h ≤ A.card → β + q * m ≤ G w ((k : ℤ) - h) m) :
    β * ((Aᶜ).card.choose h : ℝ) +
      q * ((A.card : ℝ) - h) * (((Aᶜ).card - 1).choose h : ℝ) +
      (internalEdges F A : ℝ) *
        (q * (((Aᶜ).card - 2).choose (h - 1) : ℝ) -
          adjusted (β + q * ((A.card : ℝ) - h)) h *
            (((Aᶜ).card - 2).choose (h - 2) : ℝ)) ≤ row F A k w h := by
  by_cases hh : h ≤ (Aᶜ).card
  · have hn := signed_N_bound F A h2 hh (β + q * ((A.card : ℝ) - h))
    have he := E_bound_real F A hA hmax h2 hh
    have he1 := (E_one_bounds_real F A hA hmax
      (exists_edge_of_complement_two F A hA hmax hc2)).2
    have ht : (0 : ℝ) ≤ (((Aᶜ).card - 2).choose (h - 1) : ℝ) := by positivity
    have he' := mul_le_mul_of_nonneg_right he1 ht
    have hep : (E F A h : ℝ) ≤
        ((A.card : ℝ) - 1 - (internalEdges F A : ℝ)) *
          (((Aᶜ).card - 2).choose (h - 1) : ℝ) +
        ((A.card : ℝ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℝ) := by
      linarith only [he, he']
    have heq := mul_le_mul_of_nonneg_left hep hq
    have hl := row_line_bound F A hA hmax k h w β q hline
    have hi := affine_binomial_identity A.card (Aᶜ).card h hc2 h2 hh
    have hpas : ((Aᶜ).card.choose h : ℝ) =
        (((Aᶜ).card - 1).choose (h - 1) : ℝ) + (((Aᶜ).card - 1).choose h : ℝ) := by
      have hc : ((Aᶜ).card - 1) + 1 = (Aᶜ).card := by omega
      have hd : (h - 1) + 1 = h := by omega
      have hs := Nat.choose_succ_succ' ((Aᶜ).card - 1) (h - 1)
      rw [hc, hd] at hs
      exact_mod_cast hs
    have halg :
        β * ((Aᶜ).card.choose h : ℝ) +
          q * ((A.card : ℝ) - h) * (((Aᶜ).card - 1).choose h : ℝ) +
          (internalEdges F A : ℝ) *
            (q * (((Aᶜ).card - 2).choose (h - 1) : ℝ) -
              adjusted (β + q * ((A.card : ℝ) - h)) h *
                (((Aᶜ).card - 2).choose (h - 2) : ℝ)) =
        (β + q * ((A.card : ℝ) - h)) * ((Aᶜ).card.choose h : ℝ) -
          (internalEdges F A : ℝ) * adjusted (β + q * ((A.card : ℝ) - h)) h *
            (((Aᶜ).card - 2).choose (h - 2) : ℝ) -
          q * (((A.card : ℝ) - 1 - (internalEdges F A : ℝ)) *
            (((Aᶜ).card - 2).choose (h - 1) : ℝ) +
            ((A.card : ℝ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℝ)) := by
      have hiq := congrArg (fun x : ℝ => q * x) hi
      have hpq := congrArg (fun x : ℝ => q * ((A.card : ℝ) - h) * x) hpas
      nlinarith only [hiq, hpq]
    rw [halg]
    linarith only [hn, heq, hl]
  · have hc : (Aᶜ).card < h := by omega
    have hz : (Aᶜ).card.choose h = 0 := Nat.choose_eq_zero_of_lt hc
    have hz1 : ((Aᶜ).card - 1).choose h = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz2 : ((Aᶜ).card - 2).choose (h - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz3 : ((Aᶜ).card - 2).choose (h - 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [row_zero_above_complement F A k w hc, hz, hz1, hz2, hz3]
    simp

theorem affineB_eq_positive (a c k : ℕ) (β q : ℕ → ℝ)
    (hp : ∀ h ∈ Icc 2 (k + 1), 0 ≤ β h + q h * ((a : ℝ) - h)) :
    affineB a c k β q = affineBPositive a c k β q := by
  unfold affineB affineBPositive
  congr 1
  apply sum_congr rfl
  intro h hh
  rw [adjusted_of_nonneg _ _ (hp h hh)]

/-- The full printed affine-summation lemma, with both signs and closed weight endpoints. -/
theorem affine_summation (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hc : 2 ≤ (Aᶜ).card) {k : ℕ} (hk : 1 ≤ k) (w : ℝ)
    (_hw : 0 ≤ w ∧ w ≤ 1) (β q : ℕ → ℝ)
    (hq : ∀ h ∈ Icc 1 (k + 1), 0 ≤ q h)
    (hline : ∀ h ∈ Icc 1 (k + 1), ∀ m : ℕ, m + h ≤ A.card →
      β h + q h * m ≤ G w ((k : ℤ) - h) m) :
    affineA A.card (Aᶜ).card k w β q +
      affineB A.card (Aᶜ).card k β q * (internalEdges F A : ℝ) ≤ variation F k w := by
  have h1 : 1 ∈ Icc 1 (k + 1) := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hf := row_first_bound F A hA hmax hc k w (β 1) (q 1) (hq 1 h1) (hline 1 h1)
  have hs := sum_le_sum (s := Icc 2 (k + 1)) (fun h hh =>
    row_signed_bound F A hA hmax hc k h w (β h) (q h) (mem_Icc.mp hh).1
      (hq h (mem_Icc.mpr ⟨le_trans (by decide : 1 ≤ 2) (mem_Icc.mp hh).1, (mem_Icc.mp hh).2⟩))
      (hline h (mem_Icc.mpr ⟨le_trans (by decide : 1 ≤ 2) (mem_Icc.mp hh).1, (mem_Icc.mp hh).2⟩)))
  have hi : Icc 1 (k + 1) = insert 1 (Icc 2 (k + 1)) := by
    ext h
    simp only [mem_Icc, mem_insert]
    omega
  rw [variation_eq_empty_add_rows F A hA hk]
  unfold affineA affineB
  rw [hi, sum_insert (by simp), sum_insert (by simp)]
  simp only [sum_add_distrib, ← mul_sum] at hs
  simp only [sum_add_distrib, Nat.cast_one]
  nlinarith only [hf, hs]

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.adjusted_of_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForest.adjusted_of_nonneg
#check Erdos993Lean.Analytic.V213.SmallForest.adjusted_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.adjusted_zero
#check Erdos993Lean.Analytic.V213.SmallForest.signed_N_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.signed_N_bound
#check Erdos993Lean.Analytic.V213.SmallForest.row_signed_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_signed_bound
#check Erdos993Lean.Analytic.V213.SmallForest.affineB_eq_positive
#print axioms Erdos993Lean.Analytic.V213.SmallForest.affineB_eq_positive
#check Erdos993Lean.Analytic.V213.SmallForest.affine_summation
#print axioms Erdos993Lean.Analytic.V213.SmallForest.affine_summation
