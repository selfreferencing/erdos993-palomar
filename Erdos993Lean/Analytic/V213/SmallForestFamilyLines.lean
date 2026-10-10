module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula
public import Erdos993Lean.Analytic.V213.SmallForestPatternLines
public import Erdos993Lean.Analytic.V213.SmallForestHorizontal

/-!
Current Table 5 to the nine *universal* printed patterns, then the actual line
hypotheses for every family. The three finite metadata checks read only the
reviewed family/pattern literals. They introduce no list of tangent evaluations.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset SmallForestPrinted SmallForestFinite SmallForestPatterns

def familyShapeCheck (r : FamilyInput) : Bool := decide
  (2 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ r.a ∧ r.k+1 ≤ r.a ∧
    1 ≤ r.k ∧ r.tangents.length < r.k ∧ (0 : ℚ) < r.w ∧ r.w < 1)

def familyPatternMap (r : FamilyInput) : Bool :=
  (List.range r.tangents.length).all fun i =>
    let h := i+1
    let t := r.tangents[i]?.getD 0
    patterns.any fun p => decide
      (r.w = p.w ∧ p.firstIndex ≤ r.k-h ∧
        (t : ℤ) = 2*((r.k-h : ℕ) : ℤ)+p.u ∧
        ((r.a-h : ℕ) : ℤ) ≤ 2*((r.k-h : ℕ) : ℤ)+p.nu ∧ h < r.k ∧ 2 ≤ t)

def familyHorizontalMap (r : FamilyInput) : Bool :=
  (List.range r.k).all fun h => if r.tangents.length < h then decide
    ((r.w = (1/2 : ℚ) ∧ 1 ≤ r.k-h ∧ r.k-h ≤ 6) ∨
      (r.w = (2/3 : ℚ) ∧ r.k-h = 1 ∧ r.a-h = 6)) else true

theorem all_family_shapes : familyInputs.all familyShapeCheck = true := by decide +kernel
theorem all_family_pattern_maps : familyInputs.all familyPatternMap = true := by decide +kernel
theorem all_family_horizontal_maps : familyInputs.all familyHorizontalMap = true := by decide +kernel

theorem current_family_shape (r : FamilyInput) (hr : r ∈ familyInputs) :
    2 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ r.a ∧ r.k+1 ≤ r.a ∧
      1 ≤ r.k ∧ r.tangents.length < r.k ∧ (0 : ℚ) < r.w ∧ r.w < 1 := by
  exact of_decide_eq_true (List.all_eq_true.mp all_family_shapes r hr)

theorem current_family_pattern (r : FamilyInput) (hr : r ∈ familyInputs)
    (h : ℕ) (hh : h ∈ Icc 1 r.tangents.length) :
    ∃ p ∈ patterns, r.w = p.w ∧ p.firstIndex ≤ r.k-h ∧
      ((r.tangents[h-1]?.getD 0 : ℕ) : ℤ) = 2*((r.k-h : ℕ) : ℤ)+p.u ∧
      ((r.a-h : ℕ) : ℤ) ≤ 2*((r.k-h : ℕ) : ℤ)+p.nu ∧ h < r.k ∧
      2 ≤ r.tangents[h-1]?.getD 0 := by
  have hrow := List.all_eq_true.mp all_family_pattern_maps r hr
  have hi : h-1 < r.tangents.length := by have := mem_Icc.mp hh; omega
  have hmap := List.all_eq_true.mp hrow (h-1) (List.mem_range.mpr hi)
  have he : h-1+1=h := by have := (mem_Icc.mp hh).1; omega
  dsimp only [familyPatternMap] at hmap
  rw [he] at hmap
  rcases List.any_eq_true.mp hmap with ⟨p, hp, hc⟩
  exact ⟨p, hp, of_decide_eq_true hc⟩

theorem current_family_horizontal (r : FamilyInput) (hr : r ∈ familyInputs)
    (h : ℕ) (hlo : r.tangents.length < h) (hhi : h < r.k) :
    (r.w = (1/2 : ℚ) ∧ 1 ≤ r.k-h ∧ r.k-h ≤ 6) ∨
      (r.w = (2/3 : ℚ) ∧ r.k-h = 1 ∧ r.a-h = 6) := by
  have hrow := List.all_eq_true.mp all_family_horizontal_maps r hr
  have hmap := List.all_eq_true.mp hrow h (List.mem_range.mpr hhi)
  simp only [familyHorizontalMap, if_pos hlo] at hmap
  exact of_decide_eq_true hmap

/-- The reviewed Rat floor list is exactly the floor list in the universal proof. -/
theorem horizontalQ_cast (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) :
    (horizontalQ j : ℝ) = horizontalFloor j := by
  interval_cases j <;> norm_num [horizontalQ, horizontalFloors, horizontalFloor]

theorem current_family_tangent_line (r : FamilyInput) (hr : r ∈ familyInputs)
    (h : ℕ) (hh : h ∈ Icc 1 r.tangents.length) :
    (0 : ℝ) ≤ ((familyLineQ r h).2 : ℝ) ∧
      ∀ m : ℕ, m+h ≤ r.a →
        ((familyLineQ r h).1 : ℝ) + ((familyLineQ r h).2 : ℝ)*m ≤
          G (r.w : ℝ) ((r.k : ℤ)-h) m := by
  obtain ⟨p, hp, hw, hj, ht, hM, hhk, _ht2⟩ := current_family_pattern r hr h hh
  let t := r.tangents[h-1]?.getD 0
  have hvalid := patterns_line_valid p hp (r.k-h) hj
  rcases hvalid with ⟨_hw0, _hw1, _hj2, _ht2', _htM, hti, hMi, hq, _hprev, hline⟩
  have htEq : (2*((r.k-h : ℕ) : ℤ)+p.u).toNat = t := by dsimp only [t]; omega
  have hji : ((r.k-h : ℕ) : ℤ) = (r.k : ℤ)-h := by omega
  rw [htEq, ← hw, hji] at hq hline
  have hh0 : h ≠ 0 := by have := (mem_Icc.mp hh).1; omega
  have hhlen : h ≤ r.tangents.length := (mem_Icc.mp hh).2
  constructor
  · simpa only [familyLineQ, if_neg hh0, if_pos hhlen, GQ_cast] using le_of_lt hq
  · intro m hm
    have hmM : m ≤ (2*((r.k : ℤ)-h)+p.nu).toNat := by omega
    have hl := hline m hmM
    simp only [familyLineQ, if_neg hh0, if_pos hhlen,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, GQ_cast]
    dsimp only [t] at hl
    nlinarith only [hl]

theorem current_family_horizontal_line (r : FamilyInput) (hr : r ∈ familyInputs)
    (h : ℕ) (hlo : r.tangents.length < h) (hhi : h < r.k) :
    (0 : ℝ) ≤ ((familyLineQ r h).2 : ℝ) ∧
      ∀ m : ℕ, m+h ≤ r.a →
        ((familyLineQ r h).1 : ℝ) + ((familyLineQ r h).2 : ℝ)*m ≤
          G (r.w : ℝ) ((r.k : ℤ)-h) m := by
  have hh0 : h ≠ 0 := by omega
  have hhno : ¬ h ≤ r.tangents.length := by omega
  have hji : ((r.k-h : ℕ) : ℤ) = (r.k : ℤ)-h := by omega
  rcases current_family_horizontal r hr h hlo hhi with ⟨hw, hj1, hj6⟩ | ⟨hw, hj1, hM6⟩
  · constructor
    · simp only [familyLineQ, if_neg hh0, if_neg hhno, if_pos hhi, if_pos hw]
      norm_num
    · intro m hm
      have hmM : m ≤ r.a-h := by omega
      have hb := horizontal_half (r.k-h) (r.a-h) m hj1 hj6 hmM
      simp only [familyLineQ, if_neg hh0, if_neg hhno, if_pos hhi, if_pos hw,
        Rat.cast_min, Rat.cast_zero, zero_mul, add_zero, GQ_cast, horizontalQ_cast _ hj1 hj6]
      simpa only [hw, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, hji] using hb
  · have hwnot : r.w ≠ (1/2 : ℚ) := by rw [hw]; norm_num
    have hji1 : (r.k : ℤ)-h = 1 := by omega
    constructor
    · simp only [familyLineQ, if_neg hh0, if_neg hhno, if_pos hhi, if_neg hwnot]
      norm_num
    · intro m hm
      have hm6 : m ≤ 6 := by omega
      have hb := horizontal_two_thirds m hm6
      have h23half : (2/3 : ℚ) ≠ 1/2 := by norm_num
      simpa only [familyLineQ, if_neg hh0, if_neg hhno, if_pos hhi, if_neg hwnot,
        Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, zero_mul, add_zero,
        hw, hji1, if_neg h23half, neg_div] using hb

theorem G_negative_one (w : ℝ) (m : ℕ) : G w (-1) m = -(1-w) := by
  norm_num [G, binom]

/-- Both nonpositive rank levels retain the exact printed affine constants. -/
theorem current_family_last_lines (r : FamilyInput) (hr : r ∈ familyInputs)
    (h : ℕ) (hh : h ∈ Icc r.k (r.k+1)) :
    (0 : ℝ) ≤ ((familyLineQ r h).2 : ℝ) ∧
      ∀ m : ℕ, m+h ≤ r.a →
        ((familyLineQ r h).1 : ℝ) + ((familyLineQ r h).2 : ℝ)*m ≤
          G (r.w : ℝ) ((r.k : ℤ)-h) m := by
  rcases current_family_shape r hr with ⟨_, _, _, _ha, hk, hlen, _hw0, hw1⟩
  have hh0 : h ≠ 0 := by have := mem_Icc.mp hh; omega
  have hhno : ¬h ≤ r.tangents.length := by have := mem_Icc.mp hh; omega
  have hhhi : ¬h < r.k := by have := (mem_Icc.mp hh).1; omega
  by_cases he : h = r.k
  · subst h
    constructor
    · simp only [familyLineQ, if_neg hh0, if_neg hhno, if_neg hhhi, if_pos rfl]
      norm_num
    · intro m hm
      have hind : (r.k : ℤ)-(r.k : ℤ)=0 := sub_self _
      have hwR : (r.w : ℝ) ≤ 1 := by exact_mod_cast le_of_lt hw1
      have hmR : (m : ℝ)+(r.k : ℝ) ≤ (r.a : ℝ) := by exact_mod_cast hm
      have hp : 0 ≤ (1-(r.w : ℝ))*((r.a : ℝ)-r.k-m) :=
        mul_nonneg (by linarith only [hwR]) (by linarith only [hmR])
      simp only [familyLineQ, if_neg hh0, if_neg hhno, if_neg hhhi, if_pos rfl,
        if_true,
        Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, Rat.cast_zero,
        zero_mul, add_zero, hind, G_zero_index]
      nlinarith only [hp]
  · have he1 : h=r.k+1 := by have := mem_Icc.mp hh; omega
    have hind : (r.k : ℤ)-(h : ℤ) = -1 := by omega
    constructor
    · simp only [familyLineQ, if_neg hh0, if_neg hhno, if_neg hhhi, if_neg he, if_pos he1]
      norm_num
    · intro m _hm
      simp only [familyLineQ, if_neg hh0, if_neg hhno, if_neg hhhi, if_neg he, if_pos he1,
        Rat.cast_neg, Rat.cast_sub, Rat.cast_one, Rat.cast_zero, zero_mul, add_zero, hind, G_negative_one]
      exact le_rfl

/-- The full current (108) line premises, now discharged for all fifteen records. -/
theorem current_family_lines (r : FamilyInput) (hr : r ∈ familyInputs) :
    (∀ h ∈ Icc 1 (r.k+1), (0 : ℝ) ≤ ((familyLineQ r h).2 : ℝ)) ∧
    (∀ h ∈ Icc 1 (r.k+1), ∀ m : ℕ, m+h ≤ r.a →
      ((familyLineQ r h).1 : ℝ) + ((familyLineQ r h).2 : ℝ)*m ≤
        G (r.w : ℝ) ((r.k : ℤ)-h) m) := by
  have pointwise : ∀ h ∈ Icc 1 (r.k+1),
      (0 : ℝ) ≤ ((familyLineQ r h).2 : ℝ) ∧
      ∀ m : ℕ, m+h ≤ r.a →
        ((familyLineQ r h).1 : ℝ)+((familyLineQ r h).2 : ℝ)*m ≤
          G (r.w : ℝ) ((r.k : ℤ)-h) m := by
    intro h hh
    by_cases hlen : h ≤ r.tangents.length
    · exact current_family_tangent_line r hr h (mem_Icc.mpr ⟨(mem_Icc.mp hh).1, hlen⟩)
    · by_cases hhi : h < r.k
      · exact current_family_horizontal_line r hr h (by omega) hhi
      · exact current_family_last_lines r hr h (mem_Icc.mpr ⟨by omega, (mem_Icc.mp hh).2⟩)
  exact ⟨fun h hh => (pointwise h hh).1, fun h hh => (pointwise h hh).2⟩

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.all_family_shapes
#print axioms Erdos993Lean.Analytic.V213.SmallForest.all_family_shapes
#check Erdos993Lean.Analytic.V213.SmallForest.all_family_pattern_maps
#print axioms Erdos993Lean.Analytic.V213.SmallForest.all_family_pattern_maps
#check Erdos993Lean.Analytic.V213.SmallForest.all_family_horizontal_maps
#print axioms Erdos993Lean.Analytic.V213.SmallForest.all_family_horizontal_maps
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_shape
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_shape
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_pattern
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_pattern
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_horizontal
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_horizontal
#check Erdos993Lean.Analytic.V213.SmallForest.horizontalQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForest.horizontalQ_cast
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_tangent_line
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_tangent_line
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_horizontal_line
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_horizontal_line
#check Erdos993Lean.Analytic.V213.SmallForest.G_negative_one
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_negative_one
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_last_lines
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_last_lines
#check Erdos993Lean.Analytic.V213.SmallForest.current_family_lines
#print axioms Erdos993Lean.Analytic.V213.SmallForest.current_family_lines
