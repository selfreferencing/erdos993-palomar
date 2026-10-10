module

public import Erdos993Lean.Analytic.V213.ResponseRatioBounds

/-!
Current Lemma 5.22: the three positive numerators in the printed child-curve
calculus. These are actual logarithmic functions, not assumed sign predicates.
The proof of B' follows the printed increasing/decreasing split at 1/2 and
the exact accepted log(10/3)>7/6 scalar inequality. No table is used.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Set FreeCountVariance.Envelopes

noncomputable def childD (u : ℝ) : ℝ := u-(1-u)*scalarLog u
noncomputable def childA (u : ℝ) : ℝ := 2*(1-u)^2*scalarLog u+3*u^2-2*u
noncomputable def childB (u : ℝ) : ℝ := 3*u-(3-2*u)*scalarLog u
noncomputable def childBPrime (u : ℝ) : ℝ := 2*scalarLog u-u/(1-u)

theorem childD_pos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 < childD u := by
  have hs := messageRatio_strict_lower hu hu1
  rw [messageRatio_eq_scalarH hu.ne', scalarH] at hs
  have hc := (lt_div_iff₀ (scalarLog_pos hu hu1)).mp hs
  unfold childD
  linarith

theorem childD_hasDerivAt {u : ℝ} (hu1 : u < 1) :
    HasDerivAt childD (scalarLog u) u := by
  have hk : 1-u ≠ 0 := by linarith
  convert (hasDerivAt_id u).sub
    (((hasDerivAt_id u).const_sub 1).mul (hasDerivAt_scalarLog hu1)) using 1 <;>
    (try funext x) <;> dsimp [childD] <;> field_simp [hk] <;> ring

theorem childA_hasDerivAt {u : ℝ} (hu1 : u < 1) :
    HasDerivAt childA (4*childD u) u := by
  have hk : 1-u ≠ 0 := by linarith
  convert ((((((hasDerivAt_id u).const_sub 1).pow 2).const_mul 2).mul
      (hasDerivAt_scalarLog hu1)).add
      ((hasDerivAt_pow 2 u).const_mul 3)).sub ((hasDerivAt_id u).const_mul 2) using 1 <;>
    (try funext x) <;> dsimp [childA,childD] <;> (try simp only [Nat.reduceSub,pow_one]) <;>
    field_simp [hk] <;> ring

theorem childB_hasDerivAt {u : ℝ} (hu1 : u < 1) :
    HasDerivAt childB (childBPrime u) u := by
  have hk : 1-u ≠ 0 := by linarith
  convert ((hasDerivAt_id u).const_mul 3).sub
    ((((hasDerivAt_id u).const_mul 2).const_sub 3).mul
      (hasDerivAt_scalarLog hu1)) using 1 <;>
    (try funext x) <;> dsimp [childB,childBPrime] <;> field_simp [hk] <;> ring

theorem childBPrime_hasDerivAt {u : ℝ} (hu1 : u < 1) :
    HasDerivAt childBPrime ((1-2*u)/(1-u)^2) u := by
  have hk : 1-u ≠ 0 := by linarith
  convert ((hasDerivAt_scalarLog hu1).const_mul 2).sub
    ((hasDerivAt_id u).div ((hasDerivAt_id u).const_sub 1) hk) using 1 <;>
    (try funext x) <;> dsimp [childBPrime] <;> field_simp [hk] <;> ring

theorem childA_pos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 < childA u := by
  have hmono : StrictMonoOn childA (Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x hx
      exact (childA_hasDerivAt (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x ∧ x < u := by simpa only [interior_Icc, mem_Ioo] using hx
      rw [(childA_hasDerivAt (by linarith [hx'.2])).deriv]
      exact mul_pos (by norm_num) (childD_pos hx'.1 (by linarith [hx'.2]))
  have h := hmono ⟨le_rfl,hu.le⟩ ⟨hu.le,le_rfl⟩ hu
  simpa [childA, scalarLog] using h

theorem childBPrime_endpoint : 0 < childBPrime (7/10) := by
  have hl := log_ten_thirds_gt_seven_sixths
  have heq : scalarLog (7/10) = Real.log (10/3) := by
    unfold scalarLog
    rw [show (1-(7/10 : ℝ)) = (10/3)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [childBPrime, heq]
  norm_num
  linarith

theorem childBPrime_pos {u : ℝ} (hu : 0 < u) (hu7 : u ≤ 7/10) :
    0 < childBPrime u := by
  by_cases hh : u ≤ 1/2
  · have hm : StrictMonoOn childBPrime (Icc 0 (1/2)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro x hx
        exact (childBPrime_hasDerivAt (by linarith [hx.2])).continuousAt.continuousWithinAt
      · intro x hx
        have hx' : 0 < x ∧ x < 1/2 := by simpa only [interior_Icc, mem_Ioo] using hx
        rw [(childBPrime_hasDerivAt (by linarith [hx'.2])).deriv]
        exact div_pos (by linarith [hx'.2]) (sq_pos_of_pos (by linarith [hx'.2]))
    have h := hm ⟨le_rfl,by norm_num⟩ ⟨hu.le,hh⟩ hu
    simpa [childBPrime, scalarLog] using h
  · have hm : AntitoneOn childBPrime (Icc (1/2) (7/10)) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (f' := fun x => (1-2*x)/(1-x)^2)
      · intro x hx
        exact (childBPrime_hasDerivAt (by linarith [hx.2])).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (childBPrime_hasDerivAt (by linarith [hx'.2])).hasDerivWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx'.1]) (sq_nonneg _)
    exact childBPrime_endpoint.trans_le (hm ⟨by linarith,hu7⟩ ⟨by norm_num,le_rfl⟩ hu7)

theorem childB_pos {u : ℝ} (hu : 0 < u) (hu7 : u ≤ 7/10) : 0 < childB u := by
  have hm : StrictMonoOn childB (Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x hx
      exact (childB_hasDerivAt (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x ∧ x < u := by simpa only [interior_Icc, mem_Ioo] using hx
      rw [(childB_hasDerivAt (by linarith [hx'.2])).deriv]
      exact childBPrime_pos hx'.1 (by linarith [hx'.2])
  have h := hm ⟨le_rfl,hu.le⟩ ⟨hu.le,le_rfl⟩ hu
  simpa [childB, scalarLog] using h

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.childD
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childD
#check Erdos993Lean.Analytic.V213.VarianceResponse.childA
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childA
#check Erdos993Lean.Analytic.V213.VarianceResponse.childB
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childB
#check Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime
#check Erdos993Lean.Analytic.V213.VarianceResponse.childD_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childD_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.childD_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childD_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childA_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childA_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childB_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childB_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.childA_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childA_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime_endpoint
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime_endpoint
#check Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childBPrime_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.childB_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.childB_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_ten_thirds_gt_seven_sixths
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.log_ten_thirds_gt_seven_sixths
