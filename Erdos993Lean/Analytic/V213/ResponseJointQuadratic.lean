module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightQuadraticDefs

/-! Current Lemma5.28: the determinant cannot cross zero through Xi=0,
and completion of two squares gives the positive quadratic. Continuity and
the determinant premise are exactly the printed conditional inputs. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

open Set

noncomputable def scalarXi (H A2 b1 k : ℝ) : ℝ := 4*A2*k-H*b1^2
noncomputable def scalarDet (H A2 A1 A0 b1 b0 k : ℝ) : ℝ :=
  k*(4*A2*A0-A1^2)-H*(A2*b0^2-A1*b1*b0+A0*b1^2)
noncomputable def scalarQuadratic (H A2 A1 A0 b1 b0 k rho z : ℝ) : ℝ :=
  A2*rho^2+A1*rho+A0+H*(b0+b1*rho)*z+H*k*z^2

theorem scalarDet_relation (H A2 A1 A0 b1 b0 k : ℝ) :
    4*A2*scalarDet H A2 A1 A0 b1 b0 k+H*(2*A2*b0-A1*b1)^2 =
      scalarXi H A2 b1 k*(4*A2*A0-A1^2) := by
  unfold scalarDet scalarXi
  ring

theorem scalarDet_at_zero_Xi {H A2 A1 A0 b1 b0 k : ℝ}
    (hA2 : A2 ≠ 0) (hXi : scalarXi H A2 b1 k=0) :
    scalarDet H A2 A1 A0 b1 b0 k = -H/(4*A2)*(2*A2*b0-A1*b1)^2 := by
  have h := scalarDet_relation H A2 A1 A0 b1 b0 k
  rw [hXi,zero_mul] at h
  field_simp [hA2]
  nlinarith

theorem scalarQuadratic_square {H A2 A1 A0 b1 b0 k : ℝ}
    (hA2 : A2 ≠ 0) (hXi : scalarXi H A2 b1 k ≠ 0) (rho z : ℝ) :
    scalarQuadratic H A2 A1 A0 b1 b0 k rho z =
      A2*(rho+(A1+H*b1*z)/(2*A2))^2+
      H*scalarXi H A2 b1 k/(4*A2)*(z+(2*A2*b0-A1*b1)/(scalarXi H A2 b1 k))^2+
      scalarDet H A2 A1 A0 b1 b0 k/(scalarXi H A2 b1 k) := by
  unfold scalarQuadratic scalarDet scalarXi at *
  have hXn : A2*k*4-H*b1^2 ≠ 0 := by
    intro hz
    apply hXi
    calc
      4*A2*k-H*b1^2 = A2*k*4-H*b1^2 := by ring
      _ = 0 := hz
  field_simp [hA2,hXi]
  all_goals ring_nf
  all_goals field_simp [hXn] <;> ring

theorem scalarQuadratic_pos {H A2 A1 A0 b1 b0 k : ℝ}
    (hH : 0 ≤ H) (hA2 : 0 < A2) (hXi : 0 < scalarXi H A2 b1 k)
    (hDet : 0 < scalarDet H A2 A1 A0 b1 b0 k) (rho z : ℝ) :
    0 < scalarQuadratic H A2 A1 A0 b1 b0 k rho z := by
  rw [scalarQuadratic_square hA2.ne' hXi.ne' rho z]
  have h1 : 0 ≤ A2*(rho+(A1+H*b1*z)/(2*A2))^2 := by positivity
  have h2 : 0 ≤ H*scalarXi H A2 b1 k/(4*A2)*
      (z+(2*A2*b0-A1*b1)/(scalarXi H A2 b1 k))^2 := by positivity
  have h3 : 0 < scalarDet H A2 A1 A0 b1 b0 k/(scalarXi H A2 b1 k) := div_pos hDet hXi
  linarith

theorem scalarXi_positive_on_interval {cap : ℝ} (hcap : 0 ≤ cap)
    (A2 A1 A0 b1 b0 k : ℝ → ℝ)
    (hA2c : ContinuousOn A2 (Icc 0 cap)) (hA1c : ContinuousOn A1 (Icc 0 cap))
    (hA0c : ContinuousOn A0 (Icc 0 cap)) (hb1c : ContinuousOn b1 (Icc 0 cap))
    (hb0c : ContinuousOn b0 (Icc 0 cap)) (hkc : ContinuousOn k (Icc 0 cap))
    (hA2 : ∀ H∈Icc 0 cap, 0 < A2 H) (hk0 : 0 < k 0)
    (hDet : ∀ H∈Icc 0 cap, 0 < scalarDet H (A2 H) (A1 H) (A0 H) (b1 H) (b0 H) (k H)) :
    ∀ H∈Icc 0 cap, 0 < scalarXi H (A2 H) (b1 H) (k H) := by
  let X := fun H : ℝ => scalarXi H (A2 H) (b1 H) (k H)
  have hXc : ContinuousOn X (Icc 0 cap) := by
    unfold X scalarXi
    exact ((continuousOn_const.mul hA2c).mul hkc).sub (continuousOn_id.mul (hb1c.pow 2))
  have hX0 : 0 < X 0 := by
    dsimp [X,scalarXi]
    simpa only [zero_mul,sub_zero] using mul_pos (mul_pos (by norm_num) (hA2 0 ⟨le_rfl,hcap⟩)) hk0
  intro H hH
  by_contra hnot
  have hXH : X H ≤ 0 := le_of_not_gt hnot
  obtain ⟨z,hz,hz0⟩ := intermediate_value_Icc' hH.1
    (hXc.mono (by intro x hx; exact ⟨hx.1,hx.2.trans hH.2⟩))
    (show (0:ℝ)∈Icc (X H) (X 0) from ⟨hXH,hX0.le⟩)
  have hzc : z∈Icc 0 cap := ⟨hz.1,hz.2.trans hH.2⟩
  have hzA := hA2 z hzc
  have hzD := hDet z hzc
  have hid := scalarDet_at_zero_Xi (A1 := A1 z) (A0 := A0 z) (b0 := b0 z) hzA.ne' hz0
  have hneg : -z/(4*A2 z)*(2*A2 z*b0 z-A1 z*b1 z)^2 ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.1) (by positivity)
    · exact sq_nonneg _
  linarith

/-- Printed conditional connectedness lemma, including its closed sign claim. -/
theorem joint_quadratic_connectedness {cap : ℝ} (hcap : 0 ≤ cap)
    (A2 A1 A0 b1 b0 k : ℝ → ℝ)
    (hA2c : ContinuousOn A2 (Icc 0 cap)) (hA1c : ContinuousOn A1 (Icc 0 cap))
    (hA0c : ContinuousOn A0 (Icc 0 cap)) (hb1c : ContinuousOn b1 (Icc 0 cap))
    (hb0c : ContinuousOn b0 (Icc 0 cap)) (hkc : ContinuousOn k (Icc 0 cap))
    (hA2 : ∀ H∈Icc 0 cap, 0 < A2 H) (hk0 : 0 < k 0)
    (hDet : ∀ H∈Icc 0 cap, 0 < scalarDet H (A2 H) (A1 H) (A0 H) (b1 H) (b0 H) (k H)) :
    (∀ H∈Icc 0 cap, 0 < scalarXi H (A2 H) (b1 H) (k H)) ∧
    (∀ H∈Ioc 0 cap, ∀ rho z : ℝ,
      0 < scalarQuadratic H (A2 H) (A1 H) (A0 H) (b1 H) (b0 H) (k H) rho z) := by
  have hX := scalarXi_positive_on_interval hcap A2 A1 A0 b1 b0 k hA2c hA1c hA0c hb1c hb0c hkc hA2 hk0 hDet
  refine ⟨hX,?_⟩
  intro H hH rho z
  exact scalarQuadratic_pos hH.1.le (hA2 H ⟨hH.1.le,hH.2⟩)
    (hX H ⟨hH.1.le,hH.2⟩) (hDet H ⟨hH.1.le,hH.2⟩) rho z

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarXi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarXi
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarDet
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarDet
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarQuadratic
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarQuadratic
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarDet_relation
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarDet_relation
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarDet_at_zero_Xi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarDet_at_zero_Xi
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarQuadratic_square
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarQuadratic_square
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarQuadratic_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarQuadratic_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarXi_positive_on_interval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.scalarXi_positive_on_interval
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.joint_quadratic_connectedness
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.joint_quadratic_connectedness
