module

public import Erdos993Lean.Analytic.V213.LowMeanCore
public import Erdos993Lean.Analytic.V213.LowMeanArithmeticFormulas

/-!
Core arithmetic syntax. Exact finite g maxima avoid irrational
root evaluation while remaining equal to the accepted closed maximum.
All binomial and kernel lower-bound leaves are explicit integers.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanShapeBinom (M n : ℕ) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .mul (.mul (lowMeanShapeInt (M.choose n)) (.pow q n))
    (.pow (lowMeanShapeSub (lowMeanShapeInt 1) q) (M - n))
def lowMeanShapeG (M n : ℕ) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .mul (.div (lowMeanShapeInt ((M : ℤ) + 1 - 2 * n)) (lowMeanShapeInt ((M : ℤ) + 1 - n)))
    (lowMeanShapeBinom M n q)
def lowMeanShapeMaximum : List LowMeanIntegerShape → LowMeanIntegerShape
  | [] => lowMeanShapeInt 0
  | s :: ss => .maximum s (lowMeanShapeMaximum ss)
def lowMeanRealMaximum : List ℝ → ℝ
  | [] => 0
  | x :: xs => max x (lowMeanRealMaximum xs)
def lowMeanShapeClosedMaximum (M : ℕ) (q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  lowMeanShapeMaximum ((List.range (M / 2 + 1)).map fun n => lowMeanShapeG M n q)

@[simp] theorem lowMean_shape_binom (M n : ℕ) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeBinom M n q) = binom M (lowMeanIntegerShapeReal q) (n : ℤ) := by
  simp [lowMeanShapeBinom, lowMeanIntegerShapeReal, binom_nat]

@[simp] theorem lowMean_shape_G (M n : ℕ) (q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeG M n q) = lowMeanG M n (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeG, lowMeanIntegerShapeReal, lowMeanG]

@[simp] theorem lowMean_shape_maximum (ss : List LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMaximum ss) = lowMeanRealMaximum (ss.map lowMeanIntegerShapeReal) := by
  induction ss with
  | nil => simp [lowMeanShapeMaximum, lowMeanRealMaximum]
  | cons s ss ih => simp [lowMeanShapeMaximum, lowMeanRealMaximum, lowMeanIntegerShapeReal, ih]

theorem lowMean_realMaximum_le (xs : List ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ x ∈ xs, x ≤ B) :
    lowMeanRealMaximum xs ≤ B := by
  induction xs with
  | nil => exact hB
  | cons x xs ih => exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem lowMean_le_realMaximum (xs : List ℝ) {x : ℝ} (hx : x ∈ xs) : x ≤ lowMeanRealMaximum xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

/-- The finite arithmetic expression is exactly G_M, including M=0. -/
theorem lowMean_shape_closedMaximum (M : ℕ) (q : LowMeanIntegerShape)
    (hq0 : 0 < lowMeanIntegerShapeReal q) (hq1 : lowMeanIntegerShapeReal q < 1) :
    lowMeanIntegerShapeReal (lowMeanShapeClosedMaximum M q) = lowMeanClosedMaximum M (lowMeanIntegerShapeReal q) := by
  simp only [lowMeanShapeClosedMaximum, lowMean_shape_maximum, List.map_map, Function.comp_def, lowMean_shape_G]
  apply le_antisymm
  · apply lowMean_realMaximum_le _ _
    · rw [lowMeanClosedMaximum_eq]
      exact (lowMeanG_pos (by have h := lowMeanMaxIndex_le M (lowMeanIntegerShapeReal q); omega) hq0 hq1).le
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact lowMean_closedMaximum M hq0 hq1 ⟨le_rfl, le_rfl⟩ n (by have hn' := List.mem_range.mp hn; omega)
  · rw [lowMeanClosedMaximum_eq]
    apply lowMean_le_realMaximum
    apply List.mem_map.mpr
    exact ⟨lowMeanMaxIndex M (lowMeanIntegerShapeReal q), List.mem_range.mpr (by
      have h := lowMeanMaxIndex_le M (lowMeanIntegerShapeReal q); omega), rfl⟩


def lowMeanShapeKernelK (M : ℕ) (j : ℤ) (wL wR l h : LowMeanIntegerShape) : LowMeanIntegerShape :=
  if -1 ≤ j ∧ 2 * j < (M : ℤ) - 1 then .mul wR (lowMeanShapeClosedMaximum M l)
  else if j ≤ (M : ℤ) + 1 ∧ (M : ℤ) + 1 < 2 * j then
    .mul wL (lowMeanShapeClosedMaximum M (lowMeanShapeSub (lowMeanShapeInt 1) h))
  else lowMeanShapeInt 0

theorem lowMean_shape_kernelK (M : ℕ) (j : ℤ) (wL wR l h : LowMeanIntegerShape)
    (hl : 0 < lowMeanIntegerShapeReal l) (hh : lowMeanIntegerShapeReal h < 1)
    (hlh : lowMeanIntegerShapeReal l ≤ lowMeanIntegerShapeReal h) :
    lowMeanIntegerShapeReal (lowMeanShapeKernelK M j wL wR l h) =
      lowMeanKernelK M j (lowMeanIntegerShapeReal wL) (lowMeanIntegerShapeReal wR)
        (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal h) := by
  unfold lowMeanShapeKernelK lowMeanKernelK
  split_ifs
  · simp only [lowMeanIntegerShapeReal, lowMean_shape_closedMaximum M l hl (lt_of_le_of_lt hlh hh)]
  · have hq0 : 0 < lowMeanIntegerShapeReal (lowMeanShapeSub (lowMeanShapeInt 1) h) := by simp; linarith
    have hq1 : lowMeanIntegerShapeReal (lowMeanShapeSub (lowMeanShapeInt 1) h) < 1 := by simp; linarith
    simp only [lowMeanIntegerShapeReal, lowMean_shape_closedMaximum M _ hq0 hq1, lowMean_shape_sub, lowMean_shape_int, Int.cast_one]
  · simp

def lowMeanShapeIfLEAnd (x y z u yes no : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .selectLE x y (.selectLE z u yes no) no
@[simp] theorem lowMean_shape_ifLEAnd (x y z u yes no : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeIfLEAnd x y z u yes no) =
      if lowMeanIntegerShapeReal x ≤ lowMeanIntegerShapeReal y ∧ lowMeanIntegerShapeReal z ≤ lowMeanIntegerShapeReal u
      then lowMeanIntegerShapeReal yes else lowMeanIntegerShapeReal no := by
  by_cases hxy : lowMeanIntegerShapeReal x ≤ lowMeanIntegerShapeReal y <;>
    by_cases hzu : lowMeanIntegerShapeReal z ≤ lowMeanIntegerShapeReal u <;>
    simp [lowMeanShapeIfLEAnd, lowMeanIntegerShapeReal, hxy, hzu]

def lowMeanShapeMultiplier (a b q : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (.div (.mul a (lowMeanShapeSub (lowMeanShapeInt 1) q)) q)
    (.div (.mul b q) (lowMeanShapeSub (lowMeanShapeInt 1) q))
def lowMeanShapeMultiplierLower (a b l h : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let zero := lowMeanShapeInt 0
  lowMeanShapeIfLEAnd zero a b zero (lowMeanShapeMultiplier a b h)
    (lowMeanShapeIfLEAnd a zero zero b (lowMeanShapeMultiplier a b l)
      (.add (.div (.mul a (lowMeanShapeSub (lowMeanShapeInt 1) h)) h)
        (.div (.mul b l) (lowMeanShapeSub (lowMeanShapeInt 1) l))))

@[simp] theorem lowMean_shape_multiplier (a b q : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMultiplier a b q) =
      lowMeanMultiplier (lowMeanIntegerShapeReal a) (lowMeanIntegerShapeReal b) (lowMeanIntegerShapeReal q) := by
  simp [lowMeanShapeMultiplier, lowMeanIntegerShapeReal, lowMeanMultiplier]
@[simp] theorem lowMean_shape_multiplierLower (a b l h : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMultiplierLower a b l h) =
      lowMeanMultiplierLower (lowMeanIntegerShapeReal a) (lowMeanIntegerShapeReal b)
        (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal h) := by
  simp [lowMeanShapeMultiplierLower, lowMeanIntegerShapeReal, lowMeanMultiplierLower]

def lowMeanShapeMassMode (M n : ℕ) (l h : LowMeanIntegerShape) : LowMeanIntegerShape :=
  if M = 0 then l else .maximum l (.minimum h (.div (lowMeanShapeInt n) (lowMeanShapeInt M)))
@[simp] theorem lowMean_shape_massMode (M n : ℕ) (l h : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeMassMode M n l h) =
      lowMeanMassMode M n (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal h) := by
  unfold lowMeanShapeMassMode lowMeanMassMode
  split_ifs <;> simp [lowMeanIntegerShapeReal]

def lowMeanShapeKernelL (M n : ℕ) (a b l h : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let k := lowMeanShapeMultiplierLower a b l h
  .selectLE (lowMeanShapeInt 0) k
    (.mul k (.minimum (lowMeanShapeBinom M n l) (lowMeanShapeBinom M n h)))
    (.mul k (lowMeanShapeBinom M n (lowMeanShapeMassMode M n l h)))
@[simp] theorem lowMean_shape_kernelL (M n : ℕ) (a b l h : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeKernelL M n a b l h) =
      lowMeanKernelL M n (lowMeanIntegerShapeReal a) (lowMeanIntegerShapeReal b)
        (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal h) := by
  simp [lowMeanShapeKernelL, lowMeanIntegerShapeReal, lowMeanKernelL]

def lowMeanShapeKernelLInt (M : ℕ) (j : ℤ) (wL wR l h : LowMeanIntegerShape) : LowMeanIntegerShape :=
  if j = -1 then .mul (.neg wR) (.pow (lowMeanShapeSub (lowMeanShapeInt 1) l) M)
  else if j = (M : ℤ) + 1 then .mul (.neg wL) (.pow h M)
  else if 0 ≤ j ∧ j ≤ M then
    lowMeanShapeKernelL M j.toNat
      (.mul wL (.div (lowMeanShapeInt ((M : ℤ) + 1 - 2 * j.toNat)) (lowMeanShapeInt ((M : ℤ) + 1 - j.toNat))))
      (.mul wR (.div (lowMeanShapeInt (2 * (j.toNat : ℤ) + 1 - M)) (lowMeanShapeInt ((j.toNat : ℤ) + 1)))) l h
  else lowMeanShapeInt 0

@[simp] theorem lowMean_shape_kernelLInt (M : ℕ) (j : ℤ) (wL wR l h : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (lowMeanShapeKernelLInt M j wL wR l h) =
      lowMeanKernelLInt M j (lowMeanIntegerShapeReal wL) (lowMeanIntegerShapeReal wR)
        (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal h) := by
  unfold lowMeanShapeKernelLInt lowMeanKernelLInt
  split_ifs <;> simp only [lowMeanIntegerShapeReal, lowMean_shape_sub, lowMean_shape_int,
    lowMean_shape_kernelL, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero]

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_shape_closedMaximum
