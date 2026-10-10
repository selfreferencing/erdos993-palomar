module

public import Erdos993Lean.Analytic.V22.Analysis.SharedRoot

/-!
# Section 4: the exact entropy function and skew calculus

Source: the note (version 5), Section 4.1 and Lemma 4.2(d).
Consumers: `InteriorKL`'s retained-binomial-atom midpoint bound and the
Gaussian comparison. The definitions use the shared note's logarithmic
`artanh`, without changing its real totalization or its stated domains.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def sharedKLI (x : ℝ) : ℝ :=
  x * Erdos993Lean.Analytic.V22.artanh x + Real.log (1 - x ^ 2) / 2

noncomputable def sharedKLPsi (r z : ℝ) : ℝ :=
  sharedKLI (r + z) - sharedKLI r - z * Erdos993Lean.Analytic.V22.artanh r

theorem shared_one_sub_sq_pos {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    0 < 1 - x ^ 2 := by
  nlinarith [mul_pos (by linarith : 0 < 1 - x) (by linarith : 0 < 1 + x)]

theorem sharedArtanh_log {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    Erdos993Lean.Analytic.V22.artanh x =
      (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  unfold Erdos993Lean.Analytic.V22.artanh
  rw [Real.log_div (ne_of_gt (by linarith : 0 < 1 + x))
    (ne_of_gt (by linarith : 0 < 1 - x))]

theorem hasDerivAt_sharedArtanh {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    HasDerivAt Erdos993Lean.Analytic.V22.artanh (1 / (1 - x ^ 2)) x := by
  have hp : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hm : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have hd : 1 - x ^ 2 ≠ 0 := (shared_one_sub_sq_pos hxL hxR).ne'
  have hq : (1 + x) / (1 - x) ≠ 0 := div_ne_zero hp hm
  convert (((((hasDerivAt_id x).const_add 1).div
    ((hasDerivAt_id x).const_sub 1) hm).log hq).div_const 2) using 1
  · funext y
    rfl
  · dsimp
    field_simp [hp, hm, hd] <;> ring

theorem hasDerivAt_sharedArtanh_derivative {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    HasDerivAt (fun y : ℝ => 1 / (1 - y ^ 2))
      (2 * x / (1 - x ^ 2) ^ 2) x := by
  have hd : 1 - x ^ 2 ≠ 0 := (shared_one_sub_sq_pos hxL hxR).ne'
  convert (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)) hd using 1 <;> dsimp <;> field_simp [hd] <;> ring

theorem sharedArtanh_convex :
    ConvexOn ℝ (Ico (0 : ℝ) 1) Erdos993Lean.Analytic.V22.artanh := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ico 0 1)
    (f' := fun x : ℝ => 1 / (1 - x ^ 2))
    (f'' := fun x : ℝ => 2 * x / (1 - x ^ 2) ^ 2)
  · intro x hx
    exact (hasDerivAt_sharedArtanh (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hm : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
    exact (hasDerivAt_sharedArtanh (by linarith [hm.1]) hm.2).hasDerivWithinAt
  · intro x hx
    have hm : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
    exact (hasDerivAt_sharedArtanh_derivative (by linarith [hm.1]) hm.2).hasDerivWithinAt
  · intro x hx
    have hm : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
    exact div_nonneg (by linarith [hm.1]) (sq_nonneg _)

theorem hasDerivAt_sharedKLI {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    HasDerivAt sharedKLI (Erdos993Lean.Analytic.V22.artanh x) x := by
  have hd : 1 - x ^ 2 ≠ 0 := (shared_one_sub_sq_pos hxL hxR).ne'
  convert ((hasDerivAt_id x).mul (hasDerivAt_sharedArtanh hxL hxR)).add
    ((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).log hd).div_const 2) using 1
  · funext y
    dsimp [sharedKLI] <;> ring
  · dsimp
    field_simp [hd] <;> ring

theorem hasDerivAt_sharedKLPsi {r z : ℝ} (hzL : -1 < r + z) (hzR : r + z < 1) :
    HasDerivAt (sharedKLPsi r)
      (Erdos993Lean.Analytic.V22.artanh (r + z) - Erdos993Lean.Analytic.V22.artanh r) z := by
  convert (((hasDerivAt_sharedKLI hzL hzR).comp z ((hasDerivAt_id z).const_add r)).sub
    (hasDerivAt_const z (sharedKLI r))).sub
    ((hasDerivAt_id z).mul_const (Erdos993Lean.Analytic.V22.artanh r)) using 1
  · funext y
    rfl
  · simp

theorem hasDerivAt_sharedKLPsi_derivative {r z : ℝ}
    (hzL : -1 < r + z) (hzR : r + z < 1) :
    HasDerivAt (fun y => Erdos993Lean.Analytic.V22.artanh (r + y) - Erdos993Lean.Analytic.V22.artanh r)
      (1 / (1 - (r + z) ^ 2)) z := by
  convert ((hasDerivAt_sharedArtanh hzL hzR).comp z ((hasDerivAt_id z).const_add r)).sub
    (hasDerivAt_const z (Erdos993Lean.Analytic.V22.artanh r)) using 1
  · funext y
    rfl
  · simp

@[simp] theorem sharedArtanh_zero : Erdos993Lean.Analytic.V22.artanh 0 = 0 := by
  simp [Erdos993Lean.Analytic.V22.artanh]

@[simp] theorem sharedKLI_zero : sharedKLI 0 = 0 := by simp [sharedKLI]

@[simp] theorem sharedKLPsi_zero (r : ℝ) : sharedKLPsi r 0 = 0 := by simp [sharedKLPsi]

theorem sharedKLI_even {x : ℝ} (hxL : -1 < x) (hxR : x < 1) : sharedKLI (-x) = sharedKLI x := by
  have hn := sharedArtanh_log (by linarith : -1 < -x) (by linarith : -x < 1)
  have hp := sharedArtanh_log hxL hxR
  unfold sharedKLI
  rw [hn, hp]
  rw [show 1 + -x = 1 - x by ring, show 1 - -x = 1 + x by ring,
    show (-x) ^ 2 = x ^ 2 by ring]
  congr 1 <;> ring

theorem hasDerivAt_sharedAHat {x : ℝ} (hxL : -1 < x) (hxR : x < 1) :
    HasDerivAt Erdos993Lean.Analytic.V22.aHat (x ^ 2 / (1 - x ^ 2)) x := by
  have hd : 1 - x ^ 2 ≠ 0 := (shared_one_sub_sq_pos hxL hxR).ne'
  convert (hasDerivAt_sharedArtanh hxL hxR).sub (hasDerivAt_id x) using 1
  · funext y
    rfl
  · field_simp [hd] <;> ring

/-- Lemma 4.2(d), the two explicit skew inequalities on the exact source domain. -/
theorem sharedAHat_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ Erdos993Lean.Analytic.V22.aHat r ∧
      Erdos993Lean.Analytic.V22.aHat r ≤ r ^ 3 / (3 * (1 - r ^ 2)) := by
  have hdr : 0 < 1 - r ^ 2 := shared_one_sub_sq_pos (by linarith) hr1
  have hd : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt Erdos993Lean.Analytic.V22.aHat (x ^ 2 / (1 - x ^ 2)) x := by
    intro x hx
    exact hasDerivAt_sharedAHat (by linarith [hx.1]) (by linarith [hx.2])
  have hc : ContinuousOn Erdos993Lean.Analytic.V22.aHat (Icc (0 : ℝ) r) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn Erdos993Lean.Analytic.V22.aHat (Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) r := interior_subset hx
        exact div_nonneg (sq_nonneg _) (shared_one_sub_sq_pos
          (by linarith [hx'.1]) (by linarith [hx'.2])).le)
  have hlo := hm ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  simp only [Erdos993Lean.Analytic.V22.aHat, sharedArtanh_zero, sub_zero] at hlo
  let f : ℝ → ℝ := fun x => x ^ 3 / (3 * (1 - r ^ 2)) - Erdos993Lean.Analytic.V22.aHat x
  have hf : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt f (x ^ 2 / (1 - r ^ 2) - x ^ 2 / (1 - x ^ 2)) x := by
    intro x hx
    convert ((hasDerivAt_pow 3 x).div_const (3 * (1 - r ^ 2))).sub (hd x hx) using 1 <;> dsimp <;> field_simp [hdr.ne'] <;> ring
  have hfc : ContinuousOn f (Icc (0 : ℝ) r) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfm : MonotoneOn f (Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hfc
      (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) r := interior_subset hx
        apply sub_nonneg.mpr
        exact div_le_div_of_nonneg_left (sq_nonneg x) hdr (by nlinarith [hx'.1, hx'.2]))
  have hhi := hfm ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  dsimp [f] at hhi
  simp only [zero_pow, zero_div, Erdos993Lean.Analytic.V22.aHat, sharedArtanh_zero, sub_zero] at hhi
  constructor
  · exact hlo
  · change Erdos993Lean.Analytic.V22.artanh r - r ≤ _
    norm_num only [zero_pow, zero_div] at hhi
    linarith

theorem sharedKLI_quadratic_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r ^ 2 / 2 ≤ sharedKLI r := by
  let f : ℝ → ℝ := fun x => sharedKLI x - x ^ 2 / 2
  have hd : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt f (Erdos993Lean.Analytic.V22.aHat x) x := by
    intro x hx
    convert (hasDerivAt_sharedKLI (by linarith [hx.1]) (by linarith [hx.2])).sub
      ((hasDerivAt_pow 2 x).div_const 2) using 1 <;> simp [f, Erdos993Lean.Analytic.V22.aHat]
  have hc : ContinuousOn f (Icc (0 : ℝ) r) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) r := interior_subset hx
        exact (sharedAHat_bounds hx'.1 (by linarith [hx'.2])).1)
  have h := hm ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  dsimp [f] at h
  simp only [sharedKLI_zero, zero_pow, zero_div, sub_zero] at h
  linarith

theorem shared_cr_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ Erdos993Lean.Analytic.V22.cr r := by
  let f := Erdos993Lean.Analytic.V22.cr
  have hd : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt f (Erdos993Lean.Analytic.V22.aHat x / (1 - x ^ 2)) x := by
    intro x hx
    have hxL : -1 < x := by linarith [hx.1]
    have hxR : x < 1 := by linarith [hx.2]
    have hs : 1 - x ^ 2 ≠ 0 := (shared_one_sub_sq_pos hxL hxR).ne'
    convert (((hasDerivAt_sharedArtanh hxL hxR).pow 2).add
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).log hs)).div_const 2 using 1
    · funext y
      dsimp [f, Erdos993Lean.Analytic.V22.cr] <;> ring
    · dsimp [Erdos993Lean.Analytic.V22.aHat]
      field_simp [hs] <;> ring
  have hc : ContinuousOn f (Icc (0 : ℝ) r) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' : x ∈ Icc (0 : ℝ) r := interior_subset hx
        exact div_nonneg (sharedAHat_bounds hx'.1 (by linarith [hx'.2])).1
          (shared_one_sub_sq_pos (by linarith [hx'.1]) (by linarith [hx'.2])).le)
  have h := hm ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  simpa [f, Erdos993Lean.Analytic.V22.cr] using h

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.sharedKLI
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLI
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi
#check Erdos993Lean.Analytic.V22.Analysis.shared_one_sub_sq_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_one_sub_sq_pos
#check Erdos993Lean.Analytic.V22.Analysis.sharedArtanh_log
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedArtanh_log
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedArtanh
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedArtanh
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedArtanh_derivative
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedArtanh_derivative
#check Erdos993Lean.Analytic.V22.Analysis.sharedArtanh_convex
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedArtanh_convex
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedKLI
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedKLI
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedKLPsi
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedKLPsi
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedKLPsi_derivative
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedKLPsi_derivative
#check Erdos993Lean.Analytic.V22.Analysis.sharedArtanh_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedArtanh_zero
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLI_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLI_zero
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLPsi_zero
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLI_even
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLI_even
#check Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedAHat
#print axioms Erdos993Lean.Analytic.V22.Analysis.hasDerivAt_sharedAHat
#check Erdos993Lean.Analytic.V22.Analysis.sharedAHat_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedAHat_bounds
#check Erdos993Lean.Analytic.V22.Analysis.sharedKLI_quadratic_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedKLI_quadratic_lower
#check Erdos993Lean.Analytic.V22.Analysis.shared_cr_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_cr_nonneg
