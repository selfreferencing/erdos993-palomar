module

public import Erdos993Lean.Analytic.V213.SmallForestAffineIdentity

/-!
The printed affine summation inequality when all higher-level p_h
are nonnegative. This is a partial regime of Lemma 7.3, not a replacement
for its full sign-dependent conclusion. All coefficients and weights are real.
The proof uses no finite arithmetic family.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset

noncomputable def affineA (a c k : ℕ) (w : ℝ) (β q : ℕ → ℝ) : ℝ :=
  G w (k : ℤ) a + ∑ h ∈ Icc 1 (k + 1),
    (β h * (c.choose h : ℝ) + q h * ((a : ℝ) - h) * ((c - 1).choose h : ℝ))

noncomputable def affineBPositive (a c k : ℕ) (β q : ℕ → ℝ) : ℝ :=
  q 1 + ∑ h ∈ Icc 2 (k + 1),
    (q h * ((c - 2).choose (h - 1) : ℝ) -
      (β h + q h * ((a : ℝ) - h)) * ((c - 2).choose (h - 2) : ℝ))

/-- The weighted binomial identity used in the printed constant-term simplification. -/
theorem affine_binomial_identity (a c h : ℕ) (hc : 2 ≤ c) (h2 : 2 ≤ h) (_hh : h ≤ c) :
    ((a : ℝ) - 1) * ((c - 2).choose (h - 1) : ℝ) +
      ((a : ℝ) - c) * ((c - 2).choose (h - 2) : ℝ) =
      ((a : ℝ) - h) * ((c - 1).choose (h - 1) : ℝ) := by
  have cp : c - 2 + 1 = c - 1 := by omega
  have hp : h - 2 + 1 = h - 1 := by omega
  have ps := Nat.choose_succ_succ' (c - 2) (h - 2)
  rw [cp, hp] at ps
  have psR : ((c - 1).choose (h - 1) : ℝ) =
      ((c - 2).choose (h - 2) : ℝ) + ((c - 2).choose (h - 1) : ℝ) := by
    exact_mod_cast ps
  have hm := Nat.choose_mul (n := c - 1) (k := h - 1) (s := 1) (by omega)
  simp only [Nat.choose_one_right, Nat.sub_sub] at hm
  have hmR : ((c - 1).choose (h - 1) : ℝ) * ((h : ℝ) - 1) =
      ((c : ℝ) - 1) * ((c - 2).choose (h - 2) : ℝ) := by
    have hz : ((c - 1).choose (h - 1) : ℝ) * ((h - 1 : ℕ) : ℝ) =
        ((c - 1 : ℕ) : ℝ) * ((c - 2).choose (h - 2) : ℝ) := by
      exact_mod_cast hm
    simpa only [Nat.cast_sub (by omega : 1 ≤ h), Nat.cast_sub (by omega : 1 ≤ c),
      Nat.cast_one] using hz
  rw [psR] at hmR ⊢
  nlinarith

private theorem pascal_real (c h : ℕ) (hc : 1 ≤ c) (hh : 1 ≤ h) :
    (c.choose h : ℝ) = ((c - 1).choose (h - 1) : ℝ) + ((c - 1).choose h : ℝ) := by
  have hc' : c - 1 + 1 = c := by omega
  have hh' : h - 1 + 1 = h := by omega
  have hp := Nat.choose_succ_succ' (c - 1) (h - 1)
  rw [hc', hh'] at hp
  exact_mod_cast hp

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

theorem exists_edge_of_complement_two (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hc : 2 ≤ (Aᶜ).card) : ∃ x y, F.graph.Adj x y := by
  obtain ⟨σ, _, hσ, _⟩ := exists_exposed_matching F A hA hmax
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (Aᶜ).card)
  exact ⟨v, σ v, (hσ v hv).2⟩

theorem row_first_bound (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hc : 2 ≤ (Aᶜ).card) (k : ℕ) (w β q : ℝ) (hq : 0 ≤ q)
    (hline : ∀ m : ℕ, m + 1 ≤ A.card → β + q * m ≤ G w ((k : ℤ) - 1) m) :
    β * ((Aᶜ).card.choose 1 : ℝ) +
      q * ((A.card : ℝ) - 1) * (((Aᶜ).card - 1).choose 1 : ℝ) +
      q * (internalEdges F A : ℝ) ≤ row F A k w 1 := by
  have hl := row_line_bound F A hA hmax k 1 w β q hline
  have he := (E_one_bounds_real F A hA hmax
    (exists_edge_of_complement_two F A hA hmax hc)).2
  have heq := mul_le_mul_of_nonneg_left he hq
  rw [N_one] at hl
  norm_num only [Nat.cast_one] at hl
  simp only [Nat.choose_one_right]
  rw [Nat.cast_sub (by omega : 1 ≤ (Aᶜ).card), Nat.cast_one]
  nlinarith

/-- The higher-row inequality in the positive-p regime, including all zero rows h>c. -/
theorem row_positive_bound (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hc : 2 ≤ (Aᶜ).card) (k h : ℕ) (h2 : 2 ≤ h) (w β q : ℝ)
    (hq : 0 ≤ q) (hp : 0 ≤ β + q * ((A.card : ℝ) - h))
    (hline : ∀ m : ℕ, m + h ≤ A.card → β + q * m ≤ G w ((k : ℤ) - h) m) :
    β * ((Aᶜ).card.choose h : ℝ) +
      q * ((A.card : ℝ) - h) * (((Aᶜ).card - 1).choose h : ℝ) +
      (q * (((Aᶜ).card - 2).choose (h - 1) : ℝ) -
        (β + q * ((A.card : ℝ) - h)) * (((Aᶜ).card - 2).choose (h - 2) : ℝ)) *
          (internalEdges F A : ℝ) ≤ row F A k w h := by
  by_cases hh : h ≤ (Aᶜ).card
  · have hl := row_line_bound F A hA hmax k h w β q hline
    have hn := mul_le_mul_of_nonneg_left (N_lower_real F A h2 hh) hp
    have he := E_bound_real F A hA hmax h2 hh
    have he1 := (E_one_bounds_real F A hA hmax
      (exists_edge_of_complement_two F A hA hmax hc)).2
    have he1m := mul_le_mul_of_nonneg_right he1
      (by positivity : (0 : ℝ) ≤ (((Aᶜ).card - 2).choose (h - 1) : ℝ))
    have hep : (E F A h : ℝ) ≤
        ((A.card : ℝ) - 1 - (internalEdges F A : ℝ)) *
          (((Aᶜ).card - 2).choose (h - 1) : ℝ) +
        ((A.card : ℝ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℝ) := by
      linarith
    have heq := mul_le_mul_of_nonneg_left hep hq
    have hi := affine_binomial_identity A.card (Aᶜ).card h hc h2 hh
    have hpas := pascal_real (Aᶜ).card h (by omega) (by omega)
    have hqi := congrArg (fun x : ℝ => q * x) hi
    have hmain :
        (β + q * ((A.card : ℝ) - h)) *
          (((Aᶜ).card.choose h : ℝ) - (internalEdges F A : ℝ) *
            (((Aᶜ).card - 2).choose (h - 2) : ℝ)) -
          q * (((A.card : ℝ) - 1 - (internalEdges F A : ℝ)) *
            (((Aᶜ).card - 2).choose (h - 1) : ℝ) +
            ((A.card : ℝ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℝ)) ≤
        row F A k w h := by
      linarith only [hl, hn, heq]
    convert hmain using 1
    rw [hpas]
    nlinarith only [hqi]
  · have hh' : (Aᶜ).card < h := by omega
    have z0 := Nat.choose_eq_zero_of_lt hh'
    have z1 : ((Aᶜ).card - 1).choose h = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have z2 : ((Aᶜ).card - 2).choose (h - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have z3 : ((Aᶜ).card - 2).choose (h - 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [row_zero_above_complement F A k w hh', z0, z1, z2, z3]
    simp

/-- Lemma 7.3 on the explicitly stated nonnegative-p subdomain. -/
theorem affine_summation_positive (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hc : 2 ≤ (Aᶜ).card) {k : ℕ} (hk : 1 ≤ k) (w : ℝ)
    (_hw : 0 ≤ w ∧ w ≤ 1) (β q : ℕ → ℝ)
    (hq : ∀ h ∈ Icc 1 (k + 1), 0 ≤ q h)
    (hp : ∀ h ∈ Icc 2 (k + 1), 0 ≤ β h + q h * ((A.card : ℝ) - h))
    (hline : ∀ h ∈ Icc 1 (k + 1), ∀ m : ℕ, m + h ≤ A.card →
      β h + q h * m ≤ G w ((k : ℤ) - h) m) :
    affineA A.card (Aᶜ).card k w β q +
      affineBPositive A.card (Aᶜ).card k β q * (internalEdges F A : ℝ) ≤ variation F k w := by
  have h1 : 1 ∈ Icc 1 (k + 1) := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hf := row_first_bound F A hA hmax hc k w (β 1) (q 1) (hq 1 h1) (hline 1 h1)
  have hrows : ∀ h ∈ Icc 2 (k + 1),
      β h * ((Aᶜ).card.choose h : ℝ) +
        q h * ((A.card : ℝ) - h) * (((Aᶜ).card - 1).choose h : ℝ) +
        (q h * (((Aᶜ).card - 2).choose (h - 1) : ℝ) -
          (β h + q h * ((A.card : ℝ) - h)) * (((Aᶜ).card - 2).choose (h - 2) : ℝ)) *
            (internalEdges F A : ℝ) ≤ row F A k w h := by
    intro h hh
    have hh2 := (mem_Icc.mp hh).1
    have hh1 : h ∈ Icc 1 (k + 1) := mem_Icc.mpr ⟨by omega, (mem_Icc.mp hh).2⟩
    exact row_positive_bound F A hA hmax hc k h hh2 w (β h) (q h)
      (hq h hh1) (hp h hh) (hline h hh1)
  have hs := Finset.sum_le_sum hrows
  have hi : Icc 1 (k + 1) = insert 1 (Icc 2 (k + 1)) := by
    ext h
    simp only [mem_Icc, mem_insert]
    omega
  rw [variation_eq_empty_add_rows F A hA hk]
  unfold affineA affineBPositive
  rw [hi, sum_insert (by simp), sum_insert (by simp)]
  simp only [Nat.cast_one, Finset.sum_add_distrib, ← Finset.sum_mul, add_mul] at hs ⊢
  linarith

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.affine_binomial_identity
#print axioms Erdos993Lean.Analytic.V213.SmallForest.affine_binomial_identity
#check Erdos993Lean.Analytic.V213.SmallForest.exists_edge_of_complement_two
#print axioms Erdos993Lean.Analytic.V213.SmallForest.exists_edge_of_complement_two
#check Erdos993Lean.Analytic.V213.SmallForest.row_first_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_first_bound
#check Erdos993Lean.Analytic.V213.SmallForest.row_positive_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.row_positive_bound
#check Erdos993Lean.Analytic.V213.SmallForest.affine_summation_positive
#print axioms Erdos993Lean.Analytic.V213.SmallForest.affine_summation_positive
