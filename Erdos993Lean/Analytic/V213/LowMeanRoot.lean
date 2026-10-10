module

public import Erdos993Lean.Analytic.V213.LowMeanHeat

/-!
The quadratic and the clipped smaller root in equation `r12:eq52`,
version 2.13 of the manuscript, Lemma 6.5. These are analytic identities, not finite certificate
checks. Natural-number ceiling implements the printed clipping at zero.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanRootB (M : ℕ) (q : ℝ) : ℝ := (2 * q + 1) * M + 2 * q - 1
def lowMeanRootC (M : ℕ) (q : ℝ) : ℝ := ((M : ℝ) + 1) * (M * q - 1)
def lowMeanRootP (M : ℕ) (q x : ℝ) : ℝ :=
  2 * x ^ 2 - lowMeanRootB M q * x + lowMeanRootC M q
noncomputable def lowMeanRoot (M : ℕ) (q : ℝ) : ℝ :=
  (lowMeanRootB M q - Real.sqrt ((lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q)) / 4
noncomputable def lowMeanUpperRoot (M : ℕ) (q : ℝ) : ℝ :=
  (lowMeanRootB M q + Real.sqrt ((lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q)) / 4
noncomputable def lowMeanMaxIndex (M : ℕ) (q : ℝ) : ℕ :=
  min (M / 2) (Nat.ceil (lowMeanRoot M q))

theorem lowMeanRoot_midpoint (M : ℕ) (q : ℝ) :
    lowMeanRootP M q (((M : ℝ) - 1) / 2) = -(1 - q) * ((M : ℝ) + 1) := by
  unfold lowMeanRootP lowMeanRootB lowMeanRootC
  ring

theorem lowMeanRoot_discriminant (M : ℕ) {q : ℝ} (hq : q < 1) :
    0 < (lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q := by
  have he : (lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q -
      (lowMeanRootB M q - 4 * (((M : ℝ) - 1) / 2)) ^ 2 =
        8 * (1 - q) * ((M : ℝ) + 1) := by
    unfold lowMeanRootB lowMeanRootC
    ring
  have hp : 0 < 8 * (1 - q) * ((M : ℝ) + 1) := by positivity
  nlinarith [sq_nonneg (lowMeanRootB M q - 4 * (((M : ℝ) - 1) / 2))]

/-- The midpoint lies strictly between the roots, so all compared integer
indices below floor(M/2) lie strictly below the upper root. -/
theorem lowMeanRoot_brackets (M : ℕ) {q : ℝ} (hq : q < 1) :
    lowMeanRoot M q < ((M : ℝ) - 1) / 2 ∧
      ((M : ℝ) - 1) / 2 < lowMeanUpperRoot M q := by
  have hd := lowMeanRoot_discriminant M hq
  have he : (lowMeanRootB M q - 4 * (((M : ℝ) - 1) / 2)) ^ 2 <
      (lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q := by
    have hp : 0 < 8 * (1 - q) * ((M : ℝ) + 1) := by positivity
    have hid : (lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q -
        (lowMeanRootB M q - 4 * (((M : ℝ) - 1) / 2)) ^ 2 =
          8 * (1 - q) * ((M : ℝ) + 1) := by
      unfold lowMeanRootB lowMeanRootC
      ring
    linarith
  have ha : |lowMeanRootB M q - 4 * (((M : ℝ) - 1) / 2)| <
      Real.sqrt ((lowMeanRootB M q) ^ 2 - 8 * lowMeanRootC M q) := by
    apply (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hd.le]
    exact he
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  unfold lowMeanRoot lowMeanUpperRoot
  constructor <;> linarith

theorem lowMeanRoot_factor (M : ℕ) {q : ℝ} (hq : q < 1) (x : ℝ) :
    lowMeanRootP M q x = 2 * (x - lowMeanRoot M q) * (x - lowMeanUpperRoot M q) := by
  have hs := Real.sq_sqrt (lowMeanRoot_discriminant M hq).le
  unfold lowMeanRootP lowMeanRoot lowMeanUpperRoot
  nlinarith

theorem lowMeanRootP_nonneg {M : ℕ} {q x : ℝ} (hq : q < 1)
    (hx : x ≤ ((M : ℝ) - 1) / 2) (hr : x ≤ lowMeanRoot M q) :
    0 ≤ lowMeanRootP M q x := by
  rw [lowMeanRoot_factor M hq]
  have hu := (lowMeanRoot_brackets M hq).2
  exact mul_nonneg_of_nonpos_of_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hr)) (by linarith)

theorem lowMeanRootP_nonpos {M : ℕ} {q x : ℝ} (hq : q < 1)
    (hx : x ≤ ((M : ℝ) - 1) / 2) (hr : lowMeanRoot M q ≤ x) :
    lowMeanRootP M q x ≤ 0 := by
  rw [lowMeanRoot_factor M hq]
  have hu := (lowMeanRoot_brackets M hq).2
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) (sub_nonneg.mpr hr)) (by linarith)

theorem lowMeanMaxIndex_le (M : ℕ) (q : ℝ) : lowMeanMaxIndex M q ≤ M / 2 :=
  min_le_left _ _

theorem lowMeanMaxIndex_left {M n : ℕ} {q : ℝ} (hn : n < lowMeanMaxIndex M q) :
    (n : ℝ) < lowMeanRoot M q := by
  have hc : n < Nat.ceil (lowMeanRoot M q) :=
    lt_of_lt_of_le hn (min_le_right _ _)
  exact Nat.lt_ceil.mp hc

theorem lowMeanMaxIndex_right {M n : ℕ} {q : ℝ}
    (hn : lowMeanMaxIndex M q ≤ n) (hnM : n < M / 2) :
    lowMeanRoot M q ≤ (n : ℝ) := by
  have hc : Nat.ceil (lowMeanRoot M q) ≤ n := by
    unfold lowMeanMaxIndex at hn
    omega
  exact le_trans (Nat.le_ceil _) (by exact_mod_cast hc)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanRoot_brackets
#print axioms Erdos993Lean.Analytic.V213.lowMeanMaxIndex_left
#print axioms Erdos993Lean.Analytic.V213.lowMeanMaxIndex_right
