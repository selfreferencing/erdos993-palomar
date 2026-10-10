module

public import Erdos993Lean.Analytic.V22.Analysis.GaussianCalculus
public import Erdos993Lean.Analytic.V22.Analysis.SymmetricUpper

/-!
# Section 4: Gaussian curvature comparisons and exponent identities

Source: the note (version 5), Lemmas 4.2(a,b) and 4.3(a).
Every final comparison has the source's domain, and the intermediate
derivative hypotheses are immediately consumed by the actual entropy
function. The retained-atom tilt/local bounds are owned by `InteriorKL`.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

private theorem secondDerivative_nonnegative_right {f fp fpp : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hf : ∀ x ∈ Icc (0 : ℝ) b, HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Icc (0 : ℝ) b, HasDerivAt fp (fpp x) x)
    (hfpp : ∀ x ∈ Icc (0 : ℝ) b, 0 ≤ fpp x) (hf0 : f 0 = 0) (hfp0 : fp 0 = 0) :
    0 ≤ f b := by
  have hpc : ContinuousOn fp (Icc (0 : ℝ) b) :=
    fun x hx => (hfp x hx).continuousAt.continuousWithinAt
  have hpm : MonotoneOn fp (Icc (0 : ℝ) b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b) hpc
      (fun x hx => (hfp x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hfpp x (interior_subset hx))
  have hfc : ContinuousOn f (Icc (0 : ℝ) b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfm : MonotoneOn f (Icc (0 : ℝ) b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b) hfc
      (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) b := interior_subset hx
        simpa only [hfp0] using hpm ⟨le_rfl, hb⟩ hx' hx'.1)
  simpa only [hf0] using hfm ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb

private theorem secondDerivative_nonnegative_left {f fp fpp : ℝ → ℝ} {a : ℝ}
    (ha : a ≤ 0) (hf : ∀ x ∈ Icc a (0 : ℝ), HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Icc a (0 : ℝ), HasDerivAt fp (fpp x) x)
    (hfpp : ∀ x ∈ Icc a (0 : ℝ), 0 ≤ fpp x) (hf0 : f 0 = 0) (hfp0 : fp 0 = 0) :
    0 ≤ f a := by
  have hpc : ContinuousOn fp (Icc a (0 : ℝ)) :=
    fun x hx => (hfp x hx).continuousAt.continuousWithinAt
  have hpm : MonotoneOn fp (Icc a (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a 0) hpc
      (fun x hx => (hfp x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hfpp x (interior_subset hx))
  have hfc : ContinuousOn f (Icc a (0 : ℝ)) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfm : AntitoneOn f (Icc a (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a 0) hfc
      (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc a (0 : ℝ) := interior_subset hx
        simpa only [hfp0] using hpm hx' ⟨ha, le_rfl⟩ hx'.2)
  simpa only [hf0] using hfm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha

theorem sharedKLPsi_curvature_difference {r z : ℝ}
    (hrL : -1 < r) (hrR : r < 1) (hzL : -1 < r + z) (hzR : r + z < 1) :
    1 / (1 - (r + z) ^ 2) - 1 / (1 - r ^ 2) =
      z * (2 * r + z) / ((1 - (r + z) ^ 2) * (1 - r ^ 2)) := by
  have hdr := (shared_one_sub_sq_pos hrL hrR).ne'
  have hdz := (shared_one_sub_sq_pos hzL hzR).ne'
  field_simp [hdr, hdz]
  ring

theorem sharedKLPsi_curvature_left {r Z z : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hZ0 : 0 < Z) (hZ1 : Z < 1)
    (hzL : -Z ≤ z) (hzR : z ≤ 0) :
    1 / (1 - (r + z) ^ 2) ≤ 1 / (1 - r ^ 2) +
      z ^ 2 / ((1 - Z ^ 2) * (1 - r ^ 2)) := by
  have hrL : -1 < r := by linarith
  have hxL : -1 < r + z := by linarith
  have hxR : r + z < 1 := by linarith
  have hdr := shared_one_sub_sq_pos hrL hr1
  have hdz := shared_one_sub_sq_pos hxL hxR
  have hdZ := shared_one_sub_sq_pos (by linarith : -1 < Z) hZ1
  have heq := sharedKLPsi_curvature_difference hrL hr1 hxL hxR
  by_cases hc : -2 * r ≤ z
  · have hn : z * (2 * r + z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hzR (by linarith)
    have h := div_nonpos_of_nonpos_of_nonneg hn (mul_pos hdz hdr).le
    have hs : 0 ≤ z ^ 2 / ((1 - Z ^ 2) * (1 - r ^ 2)) :=
      div_nonneg (sq_nonneg z) (mul_pos hdZ hdr).le
    rw [← heq] at h
    linarith
  · have hden : 1 - Z ^ 2 ≤ 1 - (r + z) ^ 2 := by
      have hlow : -Z ≤ r + z := by linarith
      have hupp : r + z ≤ 0 := by linarith
      nlinarith
    have hn : z * (2 * r + z) ≤ z ^ 2 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hr0 hzR]
    have hfirst : z * (2 * r + z) / ((1 - (r + z) ^ 2) * (1 - r ^ 2)) ≤
        z ^ 2 / ((1 - (r + z) ^ 2) * (1 - r ^ 2)) :=
      div_le_div_of_nonneg_right hn (mul_pos hdz hdr).le
    have hsecond : z ^ 2 / ((1 - (r + z) ^ 2) * (1 - r ^ 2)) ≤
        z ^ 2 / ((1 - Z ^ 2) * (1 - r ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg z) (mul_pos hdZ hdr)
        (mul_le_mul_of_nonneg_right hden hdr.le)
    have h := hfirst.trans hsecond
    rw [← heq] at h
    linarith

theorem sharedKLPsi_curvature_right {r Z z : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hZ : 0 < Z) (hrZ : r + Z < 1)
    (hz0 : 0 ≤ z) (hzZ : z ≤ Z) :
    1 / (1 - (r + z) ^ 2) ≤ 1 / (1 - r ^ 2) +
      z * (2 * r + z) / ((1 - (r + Z) ^ 2) * (1 - r ^ 2)) := by
  have hrL : -1 < r := by linarith
  have hxL : -1 < r + z := by linarith
  have hxR : r + z < 1 := by linarith
  have hdr := shared_one_sub_sq_pos hrL hr1
  have hdz := shared_one_sub_sq_pos hxL hxR
  have hdZ := shared_one_sub_sq_pos (by linarith : -1 < r + Z) hrZ
  have hden : 1 - (r + Z) ^ 2 ≤ 1 - (r + z) ^ 2 := by nlinarith
  have hn : 0 ≤ z * (2 * r + z) := mul_nonneg hz0 (by linarith)
  have h := div_le_div_of_nonneg_left hn (mul_pos hdZ hdr)
    (mul_le_mul_of_nonneg_right hden hdr.le)
  rw [← sharedKLPsi_curvature_difference hrL hr1 hxL hxR] at h
  linarith

/-- Exact note Lemma 4.2(a), including negative offsets and its source domain. -/
theorem sharedKLPsi_gaussian_left {r Z z : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hZ0 : 0 < Z) (hZ1 : Z < 1)
    (hzL : -Z ≤ z) (hzR : z ≤ 0) :
    sharedKLPsi r z ≤ z ^ 2 / (2 * (1 - r ^ 2)) +
      z ^ 4 / (12 * (1 - Z ^ 2) * (1 - r ^ 2)) := by
  let A : ℝ := 1 / (2 * (1 - r ^ 2))
  let B : ℝ := 1 / (12 * (1 - Z ^ 2) * (1 - r ^ 2))
  let f : ℝ → ℝ := fun x => A * x ^ 2 + B * x ^ 4 - sharedKLPsi r x
  let fp : ℝ → ℝ := fun x => 2 * A * x + 4 * B * x ^ 3 -
    (Erdos993Lean.Analytic.V22.artanh (r + x) - Erdos993Lean.Analytic.V22.artanh r)
  let fpp : ℝ → ℝ := fun x => 2 * A + 12 * B * x ^ 2 - 1 / (1 - (r + x) ^ 2)
  have hd : ∀ x ∈ Icc z (0 : ℝ), HasDerivAt f (fp x) x := by
    intro x hx
    have hxL : -1 < r + x := by linarith [hx.1]
    have hxR : r + x < 1 := by linarith [hx.2]
    convert (((hasDerivAt_pow 2 x).const_mul A).add
      ((hasDerivAt_pow 4 x).const_mul B)).sub (hasDerivAt_sharedKLPsi hxL hxR) using 1 <;>
      dsimp [f, fp] <;> ring
  have hdp : ∀ x ∈ Icc z (0 : ℝ), HasDerivAt fp (fpp x) x := by
    intro x hx
    have hxL : -1 < r + x := by linarith [hx.1]
    have hxR : r + x < 1 := by linarith [hx.2]
    convert (((hasDerivAt_id x).const_mul (2 * A)).add
      ((hasDerivAt_pow 3 x).const_mul (4 * B))).sub
      (hasDerivAt_sharedKLPsi_derivative hxL hxR) using 1
    · funext y
      dsimp [fp, fpp] <;> ring
    · dsimp [fp, fpp] <;> ring
  have hdd : ∀ x ∈ Icc z (0 : ℝ), 0 ≤ fpp x := by
    intro x hx
    have hc := sharedKLPsi_curvature_left hr0 hr1 hZ0 hZ1 (by linarith [hx.1]) hx.2
    have hdr := (shared_one_sub_sq_pos (by linarith : -1 < r) hr1).ne'
    have hdZ := (shared_one_sub_sq_pos (by linarith : -1 < Z) hZ1).ne'
    have heq : 2 * A + 12 * B * x ^ 2 =
        1 / (1 - r ^ 2) + x ^ 2 / ((1 - Z ^ 2) * (1 - r ^ 2)) := by
      dsimp [A, B]
      field_simp [hdr, hdZ] <;> ring
    dsimp [fpp]
    rw [heq]
    linarith
  have h := secondDerivative_nonnegative_left hzR hd hdp hdd
    (by simp [f]) (by simp [fp])
  dsimp [f, A, B] at h
  simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    (sub_nonneg.mp h)

/-- Exact note Lemma 4.2(b), with both the cubic and quartic error retained. -/
theorem sharedKLPsi_gaussian_right {r Z z : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hZ : 0 < Z) (hrZ : r + Z < 1)
    (hz0 : 0 ≤ z) (hzZ : z ≤ Z) :
    sharedKLPsi r z ≤ z ^ 2 / (2 * (1 - r ^ 2)) +
      (r * z ^ 3 / 3 + z ^ 4 / 12) / ((1 - (r + Z) ^ 2) * (1 - r ^ 2)) := by
  let D : ℝ := (1 - (r + Z) ^ 2) * (1 - r ^ 2)
  let A : ℝ := 1 / (2 * (1 - r ^ 2))
  let C : ℝ := r / (3 * D)
  let B : ℝ := 1 / (12 * D)
  let f : ℝ → ℝ := fun x => A * x ^ 2 + C * x ^ 3 + B * x ^ 4 - sharedKLPsi r x
  let fp : ℝ → ℝ := fun x => 2 * A * x + 3 * C * x ^ 2 + 4 * B * x ^ 3 -
    (Erdos993Lean.Analytic.V22.artanh (r + x) - Erdos993Lean.Analytic.V22.artanh r)
  let fpp : ℝ → ℝ := fun x => 2 * A + 6 * C * x + 12 * B * x ^ 2 - 1 / (1 - (r + x) ^ 2)
  have hdr := (shared_one_sub_sq_pos (by linarith : -1 < r) hr1).ne'
  have hD : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero (shared_one_sub_sq_pos (by linarith : -1 < r + Z) hrZ).ne' hdr
  have hd : ∀ x ∈ Icc (0 : ℝ) z, HasDerivAt f (fp x) x := by
    intro x hx
    have hxL : -1 < r + x := by linarith [hx.1]
    have hxR : r + x < 1 := by linarith [hx.2]
    convert ((((hasDerivAt_pow 2 x).const_mul A).add
      ((hasDerivAt_pow 3 x).const_mul C)).add
      ((hasDerivAt_pow 4 x).const_mul B)).sub (hasDerivAt_sharedKLPsi hxL hxR) using 1 <;>
      dsimp [f, fp] <;> ring
  have hdp : ∀ x ∈ Icc (0 : ℝ) z, HasDerivAt fp (fpp x) x := by
    intro x hx
    have hxL : -1 < r + x := by linarith [hx.1]
    have hxR : r + x < 1 := by linarith [hx.2]
    convert ((((hasDerivAt_id x).const_mul (2 * A)).add
      ((hasDerivAt_pow 2 x).const_mul (3 * C))).add
      ((hasDerivAt_pow 3 x).const_mul (4 * B))).sub
      (hasDerivAt_sharedKLPsi_derivative hxL hxR) using 1
    · funext y
      dsimp [fp, fpp] <;> ring
    · dsimp [fp, fpp] <;> ring
  have hdd : ∀ x ∈ Icc (0 : ℝ) z, 0 ≤ fpp x := by
    intro x hx
    have hc := sharedKLPsi_curvature_right hr0 hr1 hZ hrZ hx.1 (by linarith [hx.2])
    have heq : 2 * A + 6 * C * x + 12 * B * x ^ 2 =
        1 / (1 - r ^ 2) + x * (2 * r + x) / D := by
      dsimp [A, B, C]
      field_simp [hdr, hD]
      ring
    dsimp [fpp]
    rw [heq]
    change 1 / (1 - (r + x) ^ 2) ≤ 1 / (1 - r ^ 2) + x * (2 * r + x) / D at hc
    linarith
  have h := secondDerivative_nonnegative_right hz0 hd hdp hdd
    (by simp [f]) (by simp [fp])
  have hp : A * z ^ 2 + C * z ^ 3 + B * z ^ 4 =
      z ^ 2 / (2 * (1 - r ^ 2)) + (r * z ^ 3 / 3 + z ^ 4 / 12) / D := by
    dsimp [A, B, C]
    field_simp [hdr, hD]
    ring
  dsimp only [f] at h
  rw [hp] at h
  exact sub_nonneg.mp h

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.secondDerivative_nonnegative_right
#print axioms Erdos993Lean.Analytic.V22.Analysis.secondDerivative_nonnegative_right
#check Erdos993Lean.Analytic.V22.Analysis.secondDerivative_nonnegative_left
#print axioms Erdos993Lean.Analytic.V22.Analysis.secondDerivative_nonnegative_left
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_curvature_difference
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_curvature_difference
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_curvature_left
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_curvature_left
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_curvature_right
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_curvature_right
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_gaussian_left
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_gaussian_left
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_gaussian_right
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_gaussian_right
