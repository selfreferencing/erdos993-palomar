module

public import Erdos993Lean.Analytic.V213.SmallForestMatching
public import Erdos993Lean.Fiber.InventoryRows

/-!
# Current Section 7: support and matching-excess inventory

The remaining clauses of Lemma 7.2. All statements are all-index graph
inequalities. No finite table, graph enumeration, or final small-forest theorem
is used. Integer excess is kept explicit; real interfaces only transport casts.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

def available (A J : Finset (Fin F.n)) : Finset (Fin F.n) := Zhang.avail F.graph A J

def excess (A J : Finset (Fin F.n)) : ℤ :=
  ((Fiber.nbhdIn F.graph A J).card : ℤ) - J.card

def E (A : Finset (Fin F.n)) (h : ℕ) : ℤ :=
  ∑ J ∈ Fiber.indepSubsets F.graph Aᶜ h, (((Fiber.nbhdIn F.graph A J).card : ℤ) - h)

theorem N_eq_zero (A : Finset (Fin F.n)) {h : ℕ} (hc : (Aᶜ).card < h) : N F A h = 0 := by
  rw [N_eq_card_independent_subsets]
  simp only [Zhang.Rows.indepSets, Finset.powersetCard_eq_empty.mpr hc,
    Finset.filter_empty, Finset.card_empty]

theorem E_eq_zero (A : Finset (Fin F.n)) {h : ℕ} (hc : (Aᶜ).card < h) : E F A h = 0 := by
  simp only [E, Fiber.indepSubsets, Finset.powersetCard_eq_empty.mpr hc,
    Finset.filter_empty, Finset.sum_empty]

theorem E_zero (A : Finset (Fin F.n)) : E F A 0 = 0 := by
  unfold E
  apply Finset.sum_eq_zero
  intro J hJ
  have hcard : J.card = 0 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hJ).1).2
  have hJ0 : J = ∅ := Finset.card_eq_zero.mp hcard
  subst J
  simp [Fiber.nbhdIn, Zhang.avail]

private theorem independent_finset {A : Finset (Fin F.n)}
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) : IsIndepFinset F.graph A := by
  intro x hx y hy hxy
  exact hA (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) (F.graph.ne_of_adj hxy) hxy

theorem excess_eq_card_sub_available (A J : Finset (Fin F.n)) :
    excess F A J = (A.card : ℤ) - J.card - (available F A J).card := by
  have hm := Finset.card_le_card (Zhang.avail_subset F.graph A J)
  unfold excess available
  rw [Fiber.card_nbhdIn, Nat.cast_sub hm]
  ring

theorem E_eq_sum_excess (A : Finset (Fin F.n)) (h : ℕ) :
    E F A h = ∑ J ∈ Fiber.indepSubsets F.graph Aᶜ h, excess F A J := by
  unfold E
  apply Finset.sum_congr rfl
  intro J hJ
  have hcard : J.card = h := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hJ).1).2
  simp only [excess, hcard]

/-- The independent set J ∪ (A\N_A(J)) supplies the exact support bound. -/
theorem support_card_add_le (A J : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hJC : J ⊆ Aᶜ) (hJ : IsIndepFinset F.graph J) :
    J.card + (available F A J).card ≤ A.card := by
  have hind := Zhang.isIndepFinset_union_avail (independent_finset F hA) hJ
    (Finset.Subset.refl (Zhang.avail F.graph A J))
  have hset : F.graph.IsIndepSet ((J ∪ available F A J : Finset (Fin F.n)) : Set (Fin F.n)) := by
    intro x hx y hy _ hxy
    exact hind x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy
  have hd : Disjoint J (available F A J) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.mem_compl.mp (hJC hx) (Zhang.avail_subset F.graph A J hx')
  have bound := hmax (J ∪ available F A J) hset
  rwa [Finset.card_union_of_disjoint hd] at bound

theorem support_real (A J : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hJC : J ⊆ Aᶜ) (hJ : IsIndepFinset F.graph J) :
    0 ≤ ((available F A J).card : ℝ) ∧
      ((available F A J).card : ℝ) ≤ (A.card : ℝ) - J.card := by
  have h : (J.card : ℝ) + (available F A J).card ≤ A.card := by
    exact_mod_cast support_card_add_le F A J hA hmax hJC hJ
  constructor
  · positivity
  · linarith

theorem E_nonneg (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (h : ℕ) : 0 ≤ E F A h := by
  obtain ⟨σ, hinj, hσ, -⟩ := exists_exposed_matching F A hA hmax
  unfold E
  apply Finset.sum_nonneg
  intro J hJ
  have hh := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hJ).1
  have hb := Fiber.card_le_card_nbhdIn hh.1 (fun v hv => (hσ v hv).1)
    (fun v hv => (hσ v hv).2) hinj
  rw [hh.2] at hb
  omega

theorem E_nonneg_real (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (h : ℕ) : 0 ≤ (E F A h : ℝ) := by
  exact_mod_cast E_nonneg F A hA hmax h

/-- Each singleton has a matching neighbor, so its natural excess subtraction is exact. -/
theorem E_one_eq_cross_sub (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card) :
    E F A 1 = ((Fiber.crossEdges F.graph A Aᶜ).card : ℤ) - (Aᶜ).card := by
  obtain ⟨σ, hinj, hσ, -⟩ := exists_exposed_matching F A hA hmax
  have hsum : Fiber.blockerCharge F.graph A Aᶜ 1 + (Aᶜ).card =
      (Fiber.crossEdges F.graph A Aᶜ).card := by
    unfold Fiber.blockerCharge
    rw [Fiber.sum_indepSubsets_one, Fiber.card_crossEdges]
    simp only [Fiber.nbhdIn_singleton]
    have h : (∑ v ∈ Aᶜ, ((A.filter (F.graph.Adj v)).card - 1 + 1)) =
        ∑ v ∈ Aᶜ, (A.filter (F.graph.Adj v)).card := by
      apply Finset.sum_congr rfl
      intro v hv
      have hn : 0 < (A.filter (F.graph.Adj v)).card :=
        Finset.card_pos.mpr ⟨σ v, Finset.mem_filter.mpr (hσ v hv)⟩
      omega
    simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] using h
  have hz : (Fiber.blockerCharge F.graph A Aᶜ 1 : ℤ) + (Aᶜ).card =
      (Fiber.crossEdges F.graph A Aᶜ).card := by exact_mod_cast hsum
  rw [Fiber.blockerCharge_cast (fun v hv => (hσ v hv).1)
    (fun v hv => (hσ v hv).2) hinj 1] at hz
  change E F A 1 + (Aᶜ).card = ((Fiber.crossEdges F.graph A Aᶜ).card : ℤ) at hz
  omega

theorem total_edges_split (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n))) :
    Zhang.Rows.eIn F.graph Finset.univ = internalEdges F A + (Fiber.crossEdges F.graph A Aᶜ).card := by
  have hc : ∑ v ∈ A, (nbrsIn F.graph Aᶜ v).card = (Fiber.crossEdges F.graph A Aᶜ).card := by
    rw [Fiber.card_crossEdges]
    simp only [nbrsIn, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    simp only [F.graph.adj_comm]
  have hd : Disjoint Aᶜ A := by
    rw [Finset.disjoint_left]
    intro v hv hvA
    exact Finset.mem_compl.mp hv hvA
  have hu : Aᶜ ∪ A = Finset.univ := by
    rw [Finset.union_comm, Finset.union_compl]
  have split := Zhang.Rows.eIn_union_indep (G := F.graph) (A := Aᶜ) (B := A)
    hd (independent_finset F hA)
  simpa only [hu, hc, internalEdges] using split

theorem E_one_bounds (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hedge : ∃ x y, F.graph.Adj x y) :
    0 ≤ E F A 1 ∧ E F A 1 ≤ (A.card : ℤ) - 1 - (internalEdges F A : ℤ) := by
  have he := Zhang.Rows.eIn_le_card_sub_one F.isForest (Finset.univ : Finset (Fin F.n))
  rw [Finset.card_univ, Fintype.card_fin, total_edges_split F A hA] at he
  have hc := complement_card_pos_of_edge F A hA hedge
  have hcard : A.card + (Aᶜ).card = F.n := by
    have ha : A.card ≤ F.n := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hE := E_one_eq_cross_sub F A hA hmax
  exact ⟨E_nonneg F A hA hmax 1, by omega⟩

theorem E_one_bounds_real (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hedge : ∃ x y, F.graph.Adj x y) :
    0 ≤ (E F A 1 : ℝ) ∧ (E F A 1 : ℝ) ≤ (A.card : ℝ) - 1 - (internalEdges F A : ℝ) := by
  exact_mod_cast E_one_bounds F A hA hmax hedge

/-- The lower edge-union count is valid without acyclicity or maximality. -/
theorem N_lower_int (A : Finset (Fin F.n)) {h : ℕ} (h2 : 2 ≤ h) :
    ((Aᶜ).card.choose h : ℤ) - (internalEdges F A : ℤ) *
      (((Aᶜ).card - 2).choose (h - 2) : ℤ) ≤ (N F A h : ℤ) := by
  have hb := Fiber.edgeUnion_nonneg (G := F.graph) Aᶜ h2
  have hpair : ((Aᶜ).card.choose 2 : ℤ) - (N F A 2 : ℤ) = (internalEdges F A : ℤ) := by
    have := N_two_int F A
    omega
  change 0 ≤ (N F A h : ℤ) - ((Aᶜ).card.choose h : ℤ) +
    (((Aᶜ).card.choose 2 : ℤ) - (N F A 2 : ℤ)) * (((Aᶜ).card - 2).choose (h - 2) : ℤ) at hb
  rw [hpair] at hb
  linarith

theorem N_lower_real (A : Finset (Fin F.n)) {h : ℕ} (h2 : 2 ≤ h) (_hc : h ≤ (Aᶜ).card) :
    ((Aᶜ).card.choose h : ℝ) - (internalEdges F A : ℝ) *
      (((Aᶜ).card - 2).choose (h - 2) : ℝ) ≤ (N F A h : ℝ) := by
  exact_mod_cast N_lower_int F A h2

/-- Independent-pair counting, with the positive denominator on the printed h-domain. -/
theorem N_upper_real (A : Finset (Fin F.n)) {h : ℕ} (h2 : 2 ≤ h) (_hc : h ≤ (Aᶜ).card) :
    (N F A h : ℝ) ≤ ((Aᶜ).card.choose h : ℝ) -
      ((internalEdges F A : ℝ) / (h.choose 2 : ℝ)) * (((Aᶜ).card - 2).choose (h - 2) : ℝ) := by
  have hp := Fiber.pairExtension_nonneg (G := F.graph) Aᶜ h2
  have hpR : 0 ≤ (((Aᶜ).card - 2).choose (h - 2) : ℝ) * (N F A 2 : ℝ) -
      (h.choose 2 : ℝ) * (N F A h : ℝ) := by exact_mod_cast hp
  have hbin : ((Aᶜ).card.choose h : ℝ) * (h.choose 2 : ℝ) =
      ((Aᶜ).card.choose 2 : ℝ) * (((Aᶜ).card - 2).choose (h - 2) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := (Aᶜ).card) h2
  have hN2 : (N F A 2 : ℝ) = ((Aᶜ).card.choose 2 : ℝ) - (internalEdges F A : ℝ) := by
    exact_mod_cast N_two_int F A
  have hden : 0 < (h.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos h2
  apply (mul_le_mul_iff_of_pos_left hden).mp
  calc
    (h.choose 2 : ℝ) * (N F A h : ℝ) ≤
        (((Aᶜ).card - 2).choose (h - 2) : ℝ) * (N F A 2 : ℝ) := by linarith
    _ = (h.choose 2 : ℝ) * ((Aᶜ).card.choose h : ℝ) -
        (internalEdges F A : ℝ) * (((Aᶜ).card - 2).choose (h - 2) : ℝ) := by
      rw [hN2]
      nlinarith [hbin]
    _ = (h.choose 2 : ℝ) * (((Aᶜ).card.choose h : ℝ) -
        ((internalEdges F A : ℝ) / (h.choose 2 : ℝ)) *
          (((Aᶜ).card - 2).choose (h - 2) : ℝ)) := by
      field_simp [ne_of_gt hden]
      <;> ring

theorem E_bound (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    {h : ℕ} (h2 : 2 ≤ h) (hc : h ≤ (Aᶜ).card) :
    E F A h ≤ E F A 1 * (((Aᶜ).card - 2).choose (h - 1) : ℤ) +
      ((A.card : ℤ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℤ) := by
  obtain ⟨σ, hinj, hσ, hdeg⟩ := exists_exposed_matching F A hA hmax
  have hp := Fiber.matchingExcess_nonneg_of_exposedLeaves hσ hinj hdeg h2 hc
  change 0 ≤ (((Fiber.crossEdges F.graph A Aᶜ).card : ℤ) - (Aᶜ).card) *
      (((Aᶜ).card - 2).choose (h - 1) : ℤ) +
      ((A.card : ℤ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℤ) - E F A h at hp
  rw [← E_one_eq_cross_sub F A hA hmax] at hp
  linarith

theorem E_bound_real (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    {h : ℕ} (h2 : 2 ≤ h) (hc : h ≤ (Aᶜ).card) :
    (E F A h : ℝ) ≤ (E F A 1 : ℝ) * (((Aᶜ).card - 2).choose (h - 1) : ℝ) +
      ((A.card : ℝ) - (Aᶜ).card) * (((Aᶜ).card - 2).choose (h - 2) : ℝ) := by
  exact_mod_cast E_bound F A hA hmax h2 hc

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.N_eq_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_eq_zero
#check Erdos993Lean.Analytic.V213.SmallForest.E_eq_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_eq_zero
#check Erdos993Lean.Analytic.V213.SmallForest.E_zero
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_zero
#check Erdos993Lean.Analytic.V213.SmallForest.excess_eq_card_sub_available
#print axioms Erdos993Lean.Analytic.V213.SmallForest.excess_eq_card_sub_available
#check Erdos993Lean.Analytic.V213.SmallForest.E_eq_sum_excess
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_eq_sum_excess
#check Erdos993Lean.Analytic.V213.SmallForest.support_card_add_le
#print axioms Erdos993Lean.Analytic.V213.SmallForest.support_card_add_le
#check Erdos993Lean.Analytic.V213.SmallForest.support_real
#print axioms Erdos993Lean.Analytic.V213.SmallForest.support_real
#check Erdos993Lean.Analytic.V213.SmallForest.E_nonneg
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_nonneg
#check Erdos993Lean.Analytic.V213.SmallForest.E_nonneg_real
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_nonneg_real
#check Erdos993Lean.Analytic.V213.SmallForest.E_one_eq_cross_sub
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_one_eq_cross_sub
#check Erdos993Lean.Analytic.V213.SmallForest.total_edges_split
#print axioms Erdos993Lean.Analytic.V213.SmallForest.total_edges_split
#check Erdos993Lean.Analytic.V213.SmallForest.E_one_bounds
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_one_bounds
#check Erdos993Lean.Analytic.V213.SmallForest.E_one_bounds_real
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_one_bounds_real
#check Erdos993Lean.Analytic.V213.SmallForest.N_lower_int
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_lower_int
#check Erdos993Lean.Analytic.V213.SmallForest.N_lower_real
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_lower_real
#check Erdos993Lean.Analytic.V213.SmallForest.N_upper_real
#print axioms Erdos993Lean.Analytic.V213.SmallForest.N_upper_real
#check Erdos993Lean.Analytic.V213.SmallForest.E_bound
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_bound
#check Erdos993Lean.Analytic.V213.SmallForest.E_bound_real
#print axioms Erdos993Lean.Analytic.V213.SmallForest.E_bound_real
