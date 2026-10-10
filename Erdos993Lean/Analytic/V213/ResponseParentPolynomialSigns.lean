module

public import Erdos993Lean.Analytic.V213.ResponseParentPolynomialRecords
public import Mathlib.Analysis.Convex.Deriv

/-!
Small printed parent polynomial tests in current T7. Expansion and evaluation
are proved in Lean; no translated coefficient dataset is generated externally.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

theorem parentQ_lower {lam : ℝ} (hl : 4/5 ≤ lam) (hu : lam ≤ 13/10) :
    849773/2000 ≤ parentQ lam := by
  let z := lam-4/5
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1/2 := by dsimp [z]; linarith
  have h4 := pow_le_pow_left₀ hz0 hz1 4
  have h5 := pow_le_pow_left₀ hz0 hz1 5
  norm_num at h4 h5
  have he : parentQ lam =
      56228/125+(279216/125)*z+(97636/25)*z^2+(5496/5)*z^3-339*z^4-120*z^5 := by
    dsimp [parentQ,z]
    ring
  rw [he]
  nlinarith [pow_nonneg hz0 2,pow_nonneg hz0 3]

theorem parentQ_pos {lam : ℝ} (hl : 4/5 ≤ lam) (hu : lam ≤ 13/10) :
    0 < parentQ lam := lt_of_lt_of_le (by norm_num) (parentQ_lower hl hu)

theorem parentDMinus_pos {lam : ℝ} (hl : 4/5 ≤ lam) (hu : lam ≤ 1) :
    0 < parentDMinus lam := by
  let z := lam-4/5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have he : lam=4/5+z := by dsimp [z]; ring
  rw [he]
  unfold parentDMinus
  ring_nf
  positivity

theorem parentDPlus_pos {lam : ℝ} (hl : 1 ≤ lam) (hu : lam ≤ 13/10) :
    0 < parentDPlus lam := by
  let z := lam-1
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have he : lam=1+z := by dsimp [z]; ring
  rw [he]
  unfold parentDPlus
  ring_nf
  positivity

theorem parentE1_lower {lam : ℝ} (hl : 13/10 ≤ lam) (hu : lam ≤ 29/20) :
    1949477847/400000 ≤ parentE1 lam := by
  let z := lam-13/10
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 3/20 := by dsimp [z]; linarith
  have h2 := pow_le_pow_left₀ hz0 hz1 2
  have h3 := pow_le_pow_left₀ hz0 hz1 3
  have h4 := pow_le_pow_left₀ hz0 hz1 4
  have h5 := pow_le_pow_left₀ hz0 hz1 5
  norm_num at h2 h3 h4 h5
  have he : lam=13/10+z := by dsimp [z]; ring
  rw [he]
  unfold parentE1
  ring_nf
  nlinarith

theorem parentE1_pos {lam : ℝ} (hl : 13/10 ≤ lam) (hu : lam ≤ 29/20) :
    0 < parentE1 lam := lt_of_lt_of_le (by norm_num) (parentE1_lower hl hu)

theorem parentE2_lower {lam : ℝ} (hl : 29/20 ≤ lam) (hu : lam ≤ 8/5) :
    1208136/625 ≤ parentE2 lam := by
  let z := lam-29/20
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 3/20 := by dsimp [z]; linarith
  have h2 := pow_le_pow_left₀ hz0 hz1 2
  have h3 := pow_le_pow_left₀ hz0 hz1 3
  have h4 := pow_le_pow_left₀ hz0 hz1 4
  have h5 := pow_le_pow_left₀ hz0 hz1 5
  norm_num at h2 h3 h4 h5
  have he : lam=29/20+z := by dsimp [z]; ring
  rw [he]
  unfold parentE2
  ring_nf
  nlinarith

theorem parentE2_pos {lam : ℝ} (hl : 29/20 ≤ lam) (hu : lam ≤ 8/5) :
    0 < parentE2 lam := lt_of_lt_of_le (by norm_num) (parentE2_lower hl hu)

noncomputable def parentHD1 (lam : ℝ) : ℝ :=
  -250*lam^4-76*lam^3+693*lam^2+728*lam+136
noncomputable def parentHD2 (lam : ℝ) : ℝ :=
  -1000*lam^3-228*lam^2+1386*lam+728

theorem parentH_hasDerivAt (lam : ℝ) : HasDerivAt parentH (parentHD1 lam) lam := by
  have h5 := ((hasDerivAt_id lam).pow 5).const_mul (-50)
  have h4 := ((hasDerivAt_id lam).pow 4).const_mul (-19)
  have h3 := ((hasDerivAt_id lam).pow 3).const_mul 231
  have h2 := ((hasDerivAt_id lam).pow 2).const_mul 364
  have h1 := (hasDerivAt_id lam).const_mul 136
  have hh := ((((h5.add h4).add h3).add h2).add h1).add_const (-32)
  convert hh using 1
  · funext w
    dsimp [parentH]
    ring
  · dsimp only [parentHD1,id]
    ring

theorem parentHD1_hasDerivAt (lam : ℝ) : HasDerivAt parentHD1 (parentHD2 lam) lam := by
  have h4 := ((hasDerivAt_id lam).pow 4).const_mul (-250)
  have h3 := ((hasDerivAt_id lam).pow 3).const_mul (-76)
  have h2 := ((hasDerivAt_id lam).pow 2).const_mul 693
  have h1 := (hasDerivAt_id lam).const_mul 728
  have hh := (((h4.add h3).add h2).add h1).add_const 136
  convert hh using 1
  · funext w
    dsimp [parentHD1]
    ring
  · dsimp only [parentHD2,id]
    ring

theorem parentH_concave : ConcaveOn ℝ (Set.Icc (7/4) (7/3)) parentH := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := parentHD1) (f'' := parentHD2)
  · intro lam hl
    exact (parentH_hasDerivAt lam).continuousAt.continuousWithinAt
  · intro lam hl
    exact (parentH_hasDerivAt lam).hasDerivWithinAt
  · intro lam hl
    exact (parentHD1_hasDerivAt lam).hasDerivWithinAt
  · intro lam hl
    have hlow : 7/4 ≤ lam := (interior_subset hl).1
    let z := lam-7/4
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have he : lam=7/4+z := by dsimp [z]; ring
    rw [he]
    unfold parentHD2
    ring_nf
    nlinarith [pow_nonneg hz 2,pow_nonneg hz 3]

theorem parentH_pos {lam : ℝ} (hl : 7/4 ≤ lam) (hu : lam ≤ 7/3) :
    0 < parentH lam := by
  let t := (lam-7/4)/(7/3-7/4)
  have ht0 : 0 ≤ t := by dsimp [t]; norm_num; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; norm_num; linarith
  have h := parentH_concave.2
    (show (7/4:ℝ) ∈ Set.Icc (7/4) (7/3) by norm_num)
    (show (7/3:ℝ) ∈ Set.Icc (7/4) (7/3) by norm_num)
    (show 0 ≤ 1-t by linarith) ht0 (by ring : (1-t)+t=1)
  simp only [smul_eq_mul] at h
  have he : (1-t)*(7/4)+t*(7/3)=lam := by dsimp [t]; ring
  rw [he] at h
  have hp0 : 0 < parentH (7/4) := by norm_num [parentH]
  have hp1 : 0 < parentH (7/3) := by norm_num [parentH]
  have hch : 0 < (1-t)*parentH (7/4)+t*parentH (7/3) := by
    by_cases ht : t=1
    · simpa [ht] using hp1
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hp0) (mul_nonneg ht0 hp1.le)
  exact hch.trans_le h

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentQ_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentQ_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentQ_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentQ_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDMinus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDMinus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDPlus_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentDPlus_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE1_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE1_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE1_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE1_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE2_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE2_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE2_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentE2_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentHD1
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentHD1
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentHD2
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentHD2
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentHD1_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentHD1_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH_concave
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH_concave
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.parentH_pos
