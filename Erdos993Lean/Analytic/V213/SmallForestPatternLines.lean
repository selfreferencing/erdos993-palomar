module

public import Erdos993Lean.Analytic.V213.SmallForestPatternSupporting

/-!
Uniform membership API for the nine literal patterns.
Both signed offsets are explicitly reconstructed after Int.toNat; no truncation
assumption is hidden. The quantified j range is unbounded.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPatterns
open Erdos993Lean.Analytic.V213.SmallForest

def patterns : List PatternInput :=
  [pattern1, pattern2, pattern3, pattern4, pattern5, pattern6, pattern7, pattern8, pattern9]

def PatternLineValid (r : PatternInput) : Prop :=
  ∀ j : ℕ, r.firstIndex ≤ j →
    let ti : ℤ := 2*(j : ℤ)+r.u
    let Mi : ℤ := 2*(j : ℤ)+r.nu
    let t : ℕ := ti.toNat
    let M : ℕ := Mi.toNat
    0 < (r.w : ℝ) ∧ (r.w : ℝ) < 1 ∧
      2 ≤ j ∧ 2 ≤ t ∧ t ≤ M ∧ (t : ℤ)=ti ∧ (M : ℤ)=Mi ∧
      0 < G (r.w : ℝ) ((j : ℤ)-1) (t-1) ∧
      0 < G (r.w : ℝ) ((j : ℤ)-2) (t-2) ∧
      ∀ m : ℕ, m ≤ M →
        G (r.w : ℝ) (j : ℤ) t +
          G (r.w : ℝ) ((j : ℤ)-1) (t-1) * ((m : ℝ)-(t : ℝ)) ≤
          G (r.w : ℝ) (j : ℤ) m

theorem pattern1_line_valid : PatternLineValid pattern1 := by
  intro j hj
  change 7 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+7 := ⟨j-7, by omega⟩
  have ht : ((2 : ℤ)*((n+7 : ℕ) : ℤ)+(-4)).toNat = 2*n+10 := by omega
  have hM : ((2 : ℤ)*((n+7 : ℕ) : ℤ)+(1)).toNat = 2*n+15 := by omega
  dsimp only [pattern1]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+10-1=2*n+9 by omega] using (pattern1_signs n).1
  · simpa only [show 2*n+10-2=2*n+8 by omega] using (pattern1_signs n).2
  · intro m hm
    simpa only [show 2*n+10-1=2*n+9 by omega] using pattern1_supporting_line n m hm

theorem pattern2_line_valid : PatternLineValid pattern2 := by
  intro j hj
  change 4 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+4 := ⟨j-4, by omega⟩
  have ht : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(-3)).toNat = 2*n+5 := by omega
  have hM : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(2)).toNat = 2*n+10 := by omega
  dsimp only [pattern2]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+5-1=2*n+4 by omega] using (pattern2_signs n).1
  · simpa only [show 2*n+5-2=2*n+3 by omega] using (pattern2_signs n).2
  · intro m hm
    simpa only [show 2*n+5-1=2*n+4 by omega] using pattern2_supporting_line n m hm

theorem pattern3_line_valid : PatternLineValid pattern3 := by
  intro j hj
  change 2 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+2 := ⟨j-2, by omega⟩
  have ht : ((2 : ℤ)*((n+2 : ℕ) : ℤ)+(-2)).toNat = 2*n+2 := by omega
  have hM : ((2 : ℤ)*((n+2 : ℕ) : ℤ)+(2)).toNat = 2*n+6 := by omega
  dsimp only [pattern3]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+2-1=2*n+1 by omega] using (pattern3_signs n).1
  · simpa only [show 2*n+2-2=2*n+0 by omega] using (pattern3_signs n).2
  · intro m hm
    simpa only [show 2*n+2-1=2*n+1 by omega] using pattern3_supporting_line n m hm

theorem pattern4_line_valid : PatternLineValid pattern4 := by
  intro j hj
  change 4 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+4 := ⟨j-4, by omega⟩
  have ht : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(-2)).toNat = 2*n+6 := by omega
  have hM : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(3)).toNat = 2*n+11 := by omega
  dsimp only [pattern4]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+6-1=2*n+5 by omega] using (pattern4_signs n).1
  · simpa only [show 2*n+6-2=2*n+4 by omega] using (pattern4_signs n).2
  · intro m hm
    simpa only [show 2*n+6-1=2*n+5 by omega] using pattern4_supporting_line n m hm

theorem pattern5_line_valid : PatternLineValid pattern5 := by
  intro j hj
  change 3 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+3 := ⟨j-3, by omega⟩
  have ht : ((2 : ℤ)*((n+3 : ℕ) : ℤ)+(-1)).toNat = 2*n+5 := by omega
  have hM : ((2 : ℤ)*((n+3 : ℕ) : ℤ)+(1)).toNat = 2*n+7 := by omega
  dsimp only [pattern5]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+5-1=2*n+4 by omega] using (pattern5_signs n).1
  · simpa only [show 2*n+5-2=2*n+3 by omega] using (pattern5_signs n).2
  · intro m hm
    simpa only [show 2*n+5-1=2*n+4 by omega] using pattern5_supporting_line n m hm

theorem pattern6_line_valid : PatternLineValid pattern6 := by
  intro j hj
  change 4 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+4 := ⟨j-4, by omega⟩
  have ht : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(-1)).toNat = 2*n+7 := by omega
  have hM : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(2)).toNat = 2*n+10 := by omega
  dsimp only [pattern6]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+7-1=2*n+6 by omega] using (pattern6_signs n).1
  · simpa only [show 2*n+7-2=2*n+5 by omega] using (pattern6_signs n).2
  · intro m hm
    simpa only [show 2*n+7-1=2*n+6 by omega] using pattern6_supporting_line n m hm

theorem pattern7_line_valid : PatternLineValid pattern7 := by
  intro j hj
  change 4 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+4 := ⟨j-4, by omega⟩
  have ht : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(0)).toNat = 2*n+8 := by omega
  have hM : ((2 : ℤ)*((n+4 : ℕ) : ℤ)+(1)).toNat = 2*n+9 := by omega
  dsimp only [pattern7]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+8-1=2*n+7 by omega] using (pattern7_signs n).1
  · simpa only [show 2*n+8-2=2*n+6 by omega] using (pattern7_signs n).2
  · intro m hm
    simpa only [show 2*n+8-1=2*n+7 by omega] using pattern7_supporting_line n m hm

theorem pattern8_line_valid : PatternLineValid pattern8 := by
  intro j hj
  change 2 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+2 := ⟨j-2, by omega⟩
  have ht : ((2 : ℤ)*((n+2 : ℕ) : ℤ)+(-1)).toNat = 2*n+3 := by omega
  have hM : ((2 : ℤ)*((n+2 : ℕ) : ℤ)+(3)).toNat = 2*n+7 := by omega
  dsimp only [pattern8]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+3-1=2*n+2 by omega] using (pattern8_signs n).1
  · simpa only [show 2*n+3-2=2*n+1 by omega] using (pattern8_signs n).2
  · intro m hm
    simpa only [show 2*n+3-1=2*n+2 by omega] using pattern8_supporting_line n m hm

theorem pattern9_line_valid : PatternLineValid pattern9 := by
  intro j hj
  change 3 ≤ j at hj
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j=n+3 := ⟨j-3, by omega⟩
  have ht : ((2 : ℤ)*((n+3 : ℕ) : ℤ)+(0)).toNat = 2*n+6 := by omega
  have hM : ((2 : ℤ)*((n+3 : ℕ) : ℤ)+(2)).toNat = 2*n+8 := by omega
  dsimp only [pattern9]
  rw [ht, hM]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  refine ⟨by norm_num, by norm_num, by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [show 2*n+6-1=2*n+5 by omega] using (pattern9_signs n).1
  · simpa only [show 2*n+6-2=2*n+4 by omega] using (pattern9_signs n).2
  · intro m hm
    simpa only [show 2*n+6-1=2*n+5 by omega] using pattern9_supporting_line n m hm

/-- Every entry of the exact current nine-row pattern list supplies its actual
positive slope and supporting line for every j above the printed first index. -/
theorem patterns_line_valid (r : PatternInput) (hr : r ∈ patterns) : PatternLineValid r := by
  simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pattern1_line_valid
  · exact pattern2_line_valid
  · exact pattern3_line_valid
  · exact pattern4_line_valid
  · exact pattern5_line_valid
  · exact pattern6_line_valid
  · exact pattern7_line_valid
  · exact pattern8_line_valid
  · exact pattern9_line_valid

end Erdos993Lean.Analytic.V213.SmallForestPatterns

#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_line_valid
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.patterns_line_valid
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.patterns_line_valid
