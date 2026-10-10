module

public import Erdos993Lean.Analytic.V213.SmallForestCurrentRouting
public import Erdos993Lean.Analytic.V213.SmallForestFiniteConsumers
public import Erdos993Lean.Analytic.V213.SmallForestFamilyLines
public import Erdos993Lean.Analytic.V213.Foundation

/-!
Current-domain forest consequence of the current printed arithmetic and lines.
No supporting-line hypothesis remains in these statements: the family case
uses the nine universal symbolic patterns through current_family_lines.
This file does not assert the final window/unimodality wrapper.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset SmallForestPrinted SmallForestFinite

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

/-- The actual fifteen-family forest result, with the line premises discharged. -/
theorem printed_family_margin (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (r : FamilyInput) (hr : r ∈ familyInputs) (ha : A.card = r.a)
    (hc : (Aᶜ).card ∈ Icc r.lo r.hi) :
    (26 : ℝ) ≤ variation F r.k (r.w : ℝ) := by
  obtain ⟨hq, hl⟩ := current_family_lines r hr
  apply printed_family_margin_of_lines F A hA hmax r hr ha hc hq
  intro h hh m hm
  exact hl h hh m (by simpa only [ha] using hm)

/-- Every current-domain triple gives a strictly positive weighted coefficient
difference through one of the three printed proof routes. -/
theorem currentDomain_positive_variation (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (k : ℕ) (hd : CurrentDomain A.card (Aᶜ).card k) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 0 < variation F k w := by
  rcases currentDomain_route A.card (Aᶜ).card k hd with
    ⟨r, hr, hk, ha, hc⟩ | ⟨r, hr, ha, hc, hk⟩ | ⟨x, hx, ha, hc, hk⟩ | ⟨r, hr, ha, hk, hlo, hhi⟩
  · have hb := printed_rising_strict F A hA r hr ha hc
    rw [hk] at hb
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    simp only [variation, one_mul, sub_self, zero_mul, add_zero]
    exact sub_pos.mpr hb
  · have hb := printed_named_catalan_margin F A hA hmax r hr ha.symm hc.symm
    rw [hk] at hb
    exact ⟨1, by norm_num, by norm_num, lt_of_lt_of_le (by norm_num) hb⟩
  · have hb := printed_newton_catalan_margin F A hA hmax x hx ha hc
    rw [hk]
    exact ⟨1, by norm_num, by norm_num, lt_of_lt_of_le (by norm_num) hb⟩
  · have hb := printed_family_margin F A hA hmax r hr ha.symm (mem_Icc.mpr ⟨hlo, hhi⟩)
    rw [hk] at hb
    rcases current_family_shape r hr with ⟨_, _, _, _, _, _, hw0, hw1⟩
    have hw0' : (0 : ℝ) ≤ (r.w : ℝ) := by exact_mod_cast le_of_lt hw0
    have hw1' : (r.w : ℝ) ≤ 1 := by exact_mod_cast le_of_lt hw1
    exact ⟨(r.w : ℝ), hw0', hw1', lt_of_lt_of_le (by norm_num) hb⟩

/-- Positive weighted variation excludes the paper's equality-inclusive valley. -/
theorem not_coefficientValley_of_positive_variation (k : ℕ) (hk : 1 ≤ k)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp : 0 < variation F k w) :
    ¬ CoefficientValley F (k : ℤ) := by
  rintro ⟨_hk, hleft, hright⟩
  have hpred : (k : ℤ)-1 = ((k-1 : ℕ) : ℤ) := by omega
  have hsucc : (k : ℤ)+1 = ((k+1 : ℕ) : ℤ) := by omega
  rw [hpred, coefficient_nat, coefficient_nat] at hleft
  rw [hsucc, coefficient_nat, coefficient_nat] at hright
  rw [count_eq_indepCount, count_eq_indepCount] at hleft hright
  have hdec : (inferInstance : DecidableRel F.graph.Adj) =
      (fun a b => Classical.propDecidable (F.graph.Adj a b)) := Subsingleton.elim _ _
  rw [← hdec] at hleft hright
  have hleftR : (indepCount F.graph univ k : ℝ) ≤ indepCount F.graph univ (k-1) := by
    exact_mod_cast hleft
  have hrightR : (indepCount F.graph univ k : ℝ) ≤ indepCount F.graph univ (k+1) := by
    exact_mod_cast hright
  have hl := mul_nonpos_of_nonneg_of_nonpos hw0 (sub_nonpos.mpr hleftR)
  have hr := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw1) (sub_nonpos.mpr hrightR)
  unfold variation at hp
  linarith only [hl, hr, hp]

/-- Exact current-domain no-valley conclusion; no finite or analytic premise is
assumed in addition to the actual forest and maximum independent-set context. -/
theorem currentDomain_no_valley (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (k : ℕ) (hd : CurrentDomain A.card (Aᶜ).card k) :
    ¬ CoefficientValley F (k : ℤ) := by
  obtain ⟨w, hw0, hw1, hp⟩ := currentDomain_positive_variation F A hA hmax k hd
  have hk : 1 ≤ k := by have hb := currentDomain_bounds hd; omega
  exact not_coefficientValley_of_positive_variation F k hk w hw0 hw1 hp

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.printed_family_margin
#print axioms Erdos993Lean.Analytic.V213.SmallForest.printed_family_margin
#check Erdos993Lean.Analytic.V213.SmallForest.currentDomain_positive_variation
#print axioms Erdos993Lean.Analytic.V213.SmallForest.currentDomain_positive_variation
#check Erdos993Lean.Analytic.V213.SmallForest.not_coefficientValley_of_positive_variation
#print axioms Erdos993Lean.Analytic.V213.SmallForest.not_coefficientValley_of_positive_variation
#check Erdos993Lean.Analytic.V213.SmallForest.currentDomain_no_valley
#print axioms Erdos993Lean.Analytic.V213.SmallForest.currentDomain_no_valley
