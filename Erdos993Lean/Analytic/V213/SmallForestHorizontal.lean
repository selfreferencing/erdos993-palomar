module

public import Erdos993Lean.Analytic.V213.SmallForestResidual

/-!
The six horizontal lines in (117), and the additional w=2/3 line.
The six floors are the literal display printed with (117).
Small
prefix arithmetic is proved in the kernel. A single interval-of-increments
argument extends those prefix facts to every natural endpoint, without a
forest enumeration or an endpoint catalogue.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

noncomputable def horizontalFloor (j : ℕ) : ℝ :=
  ([-(1/2 : ℝ), -(1/2), -(1/2), -1, -2, -4] : List ℝ).getD (j - 1) 0

private theorem G_endpoint_min (w : ℝ) (hw : w ≤ 1) (j b : ℕ) (hj : 1 ≤ j)
    (floor : ℝ) (hstart : G w (j : ℤ) b < G w (j : ℤ) (b + 1))
    (hprefix : ∀ n : ℕ, n ≤ b → floor ≤ G w (j : ℤ) n) :
    ∀ M m : ℕ, m ≤ M → min floor (G w (j : ℤ) M) ≤ G w (j : ℤ) m := by
  apply SmallForestResidual.endpoint_min_after_positive_step _ b floor _ hstart hprefix
  intro a r c har hrc ha hc
  have hind : (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
  have hga : 0 < G w ((j - 1 : ℕ) : ℤ) a := by
    rw [← hind, ← G_increment]
    linarith only [ha]
  have hgc : 0 < G w ((j - 1 : ℕ) : ℤ) c := by
    rw [← hind, ← G_increment]
    linarith only [hc]
  have hgr := G_positive_interval w hw (j - 1) har hrc hga hgc
  rw [← hind, ← G_increment] at hgr
  linarith only [hgr]

private theorem half_prefix_and_step (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) :
    ∃ b : ℕ, G (1/2 : ℝ) (j : ℤ) b < G (1/2 : ℝ) (j : ℤ) (b + 1) ∧
      ∀ n : ℕ, n ≤ b → horizontalFloor j ≤ G (1/2 : ℝ) (j : ℤ) n := by
  interval_cases j
  · refine ⟨0, ?_, ?_⟩
    · norm_num [G, binom, Int.toNat, Nat.choose]
    · intro n hn
      have : n = 0 := by omega
      subst n
      norm_num [horizontalFloor, G, binom, Int.toNat, Nat.choose]
  · refine ⟨2, ?_, ?_⟩
    · norm_num [G, binom, Int.toNat, Nat.choose]
    · intro n hn
      interval_cases n <;> norm_num [horizontalFloor, G, binom, Int.toNat, Nat.choose]
  · refine ⟨3, ?_, ?_⟩
    · norm_num [G, binom, Int.toNat, Nat.choose]
    · intro n hn
      interval_cases n <;> norm_num [horizontalFloor, G, binom, Int.toNat, Nat.choose]
  · refine ⟨5, ?_, ?_⟩
    · norm_num [G, binom, Int.toNat, Nat.choose]
    · intro n hn
      interval_cases n <;> norm_num [horizontalFloor, G, binom, Int.toNat, Nat.choose]
  · refine ⟨7, ?_, ?_⟩
    · norm_num [G, binom, Int.toNat, Nat.choose]
    · intro n hn
      interval_cases n <;> norm_num [horizontalFloor, G, binom, Int.toNat, Nat.choose]
  · refine ⟨8, ?_, ?_⟩
    · norm_num [G, binom, Int.toNat, Nat.choose]
    · intro n hn
      interval_cases n <;> norm_num [horizontalFloor, G, binom, Int.toNat, Nat.choose]

/-- Exactly (117), including every initial integer interval and all six indices. -/
theorem horizontal_half (j M m : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (hm : m ≤ M) :
    min (horizontalFloor j) (G (1/2 : ℝ) (j : ℤ) M) ≤ G (1/2 : ℝ) (j : ℤ) m := by
  obtain ⟨b, hstart, hprefix⟩ := half_prefix_and_step j hj1 hj6
  exact G_endpoint_min (1/2) (by norm_num) j b hj1 (horizontalFloor j)
    hstart hprefix M m hm

/-- The additional printed line, with both m=0 and m=6 included. -/
theorem horizontal_two_thirds (m : ℕ) (hm : m ≤ 6) :
    -(2/3 : ℝ) ≤ G (2/3 : ℝ) 1 m := by
  have hb := G_endpoint_min (2/3) (by norm_num) 1 0 (by omega) (-(2/3))
    (by norm_num [G, binom, Int.toNat, Nat.choose]) (by
      intro n hn
      have : n = 0 := by omega
      subst n
      norm_num [G, binom, Int.toNat, Nat.choose]) 6 m hm
  have he : G (2/3 : ℝ) 1 6 = (1/3 : ℝ) := by
    norm_num [G, binom, Int.toNat, Nat.choose]
  simp only [Nat.cast_one] at hb
  rw [he, min_eq_left (by norm_num : -(2/3 : ℝ) ≤ (1/3 : ℝ))] at hb
  exact hb

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.horizontal_half
#print axioms Erdos993Lean.Analytic.V213.SmallForest.horizontal_half
#check Erdos993Lean.Analytic.V213.SmallForest.horizontal_two_thirds
#print axioms Erdos993Lean.Analytic.V213.SmallForest.horizontal_two_thirds
