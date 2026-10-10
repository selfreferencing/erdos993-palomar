module

public import Erdos993Lean.Analytic.V213.FiberDefinitions
public import Erdos993Lean.Analytic.V213.FiberReflection
public import Erdos993Lean.Analytic.V213.LowMeanKernelIdentities
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Int.Interval

/-!
The literal minimum of F over the full integer rank axis in Eq91.
The finite interval is proved complete using both exact zero-kernel tails,
including M=0. No generator window or truncated mathematical domain is
used. This generic definition supports C116 and later spike averaging.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberMinimum (q mu : ℝ) (M : ℕ) : ℝ := sInf (Set.range (fiberF q mu M))

theorem fiber_F_outside (q mu : ℝ) (M : ℕ) (j : ℤ)
    (hj : j < -1 ∨ (M : ℤ) + 1 < j) :
    fiberF q mu M j = fiberOffset q M j ^ 2 / (fiberVariance q * mu) := by
  unfold fiberF
  rw [lowMean_kernel_outside M q (fiberWeightL q) (fiberWeightR q) j hj,mul_zero,zero_add]

theorem fiber_minimum_left_tail {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) {j : ℤ} (hj : j < -2) :
    fiberF q mu M (-2) ≤ fiberF q mu M j := by
  have hc : (-1 / 2 : ℝ) < q * (M : ℝ) + fiberSkew q / 2 := by
    have hm := Nat.cast_nonneg (α := ℝ) M
    unfold fiberSkew
    nlinarith only [mul_nonneg hq0.le hm,hq0]
  have hjr : (j : ℝ) ≤ -2 := by exact_mod_cast (le_of_lt hj)
  have hsq : ((-2 : ℝ) - q * M - fiberSkew q / 2) ^ 2 ≤
      ((j : ℝ) - q * M - fiberSkew q / 2) ^ 2 := by
    have h1 : 0 ≤ -((-2 : ℝ) - q * M - fiberSkew q / 2) := by linarith only [hc]
    have h2 : 0 ≤ -((j : ℝ) - q * M - fiberSkew q / 2) := by linarith only [hc,hjr]
    have h := (sq_le_sq₀ h1 h2).2 (by linarith only [hjr])
    simpa only [neg_sq] using h
  rw [fiber_F_outside q mu M (-2) (Or.inl (by norm_num)),
    fiber_F_outside q mu M j (Or.inl (by omega))]
  unfold fiberOffset
  norm_num only [Int.cast_neg,Int.cast_ofNat]
  exact div_le_div_of_nonneg_right hsq (mul_nonneg (fiber_variance_pos hq0 hq1).le hmu.le)

theorem fiber_minimum_right_tail {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) {j : ℤ} (hj : (M : ℤ) + 2 < j) :
    fiberF q mu M ((M : ℤ) + 2) ≤ fiberF q mu M j := by
  have hc : q * (M : ℝ) + fiberSkew q / 2 < (M : ℝ) + 1 / 2 := by
    have hm := Nat.cast_nonneg (α := ℝ) M
    unfold fiberSkew
    have hp := mul_nonneg (sub_nonneg.mpr hq1.le) hm
    nlinarith only [hp,hq1]
  have hjr : (M : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast (le_of_lt hj)
  have h1 : 0 ≤ ((M : ℝ) + 2) - q * M - fiberSkew q / 2 := by linarith only [hc]
  have h2 : 0 ≤ (j : ℝ) - q * M - fiberSkew q / 2 := by linarith only [hc,hjr]
  have hsq := (sq_le_sq₀ h1 h2).2 (by linarith only [hjr])
  rw [fiber_F_outside q mu M ((M : ℤ) + 2) (Or.inr (by omega)),
    fiber_F_outside q mu M j (Or.inr (by omega))]
  unfold fiberOffset
  push_cast
  exact div_le_div_of_nonneg_right hsq (mul_nonneg (fiber_variance_pos hq0 hq1).le hmu.le)

theorem fiber_minimum_attained {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) :
    ∃ j : ℤ, -2 ≤ j ∧ j ≤ (M : ℤ) + 2 ∧
      fiberMinimum q mu M = fiberF q mu M j ∧ ∀ k : ℤ, fiberF q mu M j ≤ fiberF q mu M k := by
  let S : Set ℤ := Set.Icc (-2) ((M : ℤ) + 2)
  have hS : S.Finite := Set.finite_Icc _ _
  have hSne : S.Nonempty := ⟨-2,by dsimp [S]; constructor <;> omega⟩
  obtain ⟨j,hj,hmin⟩ := Set.exists_min_image S (fiberF q mu M) hS hSne
  have hglobal (k : ℤ) : fiberF q mu M j ≤ fiberF q mu M k := by
    by_cases hkL : k < -2
    · exact (hmin (-2) (by dsimp [S]; constructor <;> omega)).trans
        (fiber_minimum_left_tail hq0 hq1 hmu M hkL)
    by_cases hkR : (M : ℤ) + 2 < k
    · exact (hmin ((M : ℤ) + 2) (by dsimp [S]; constructor <;> omega)).trans
        (fiber_minimum_right_tail hq0 hq1 hmu M hkR)
    exact hmin k ⟨le_of_not_gt hkL,le_of_not_gt hkR⟩
  have hb : BddBelow (Set.range (fiberF q mu M)) := ⟨fiberF q mu M j,by
    rintro x ⟨k,rfl⟩
    exact hglobal k⟩
  have heq : fiberMinimum q mu M = fiberF q mu M j := by
    unfold fiberMinimum
    apply le_antisymm
    · exact csInf_le hb ⟨j,rfl⟩
    · apply le_csInf (Set.range_nonempty _)
      rintro x ⟨k,rfl⟩
      exact hglobal k
  exact ⟨j,hj.1,hj.2,heq,hglobal⟩

theorem fiber_minimum_lower {q mu L : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (h : ∀ j : ℤ, L ≤ fiberF q mu M j) :
    L ≤ fiberMinimum q mu M := by
  obtain ⟨j,_,_,heq,_⟩ := fiber_minimum_attained hq0 hq1 hmu M
  rw [heq]
  exact h j

theorem fiber_minimum_reflect (q mu : ℝ) (M : ℕ) :
    fiberMinimum (1 - q) mu M = fiberMinimum q mu M := by
  have heq : Set.range (fiberF (1 - q) mu M) = Set.range (fiberF q mu M) := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩
      refine ⟨(M : ℤ) - j,?_⟩
      have h := fiber_F_reflect q mu M ((M : ℤ) - j)
      rw [show (M : ℤ) - ((M : ℤ) - j) = j by ring] at h
      exact h.symm
    · rintro ⟨j,rfl⟩
      exact ⟨(M : ℤ) - j,fiber_F_reflect q mu M j⟩
  unfold fiberMinimum
  rw [heq]

end Erdos993Lean.Analytic.V213
