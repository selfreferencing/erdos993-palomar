module

public import Erdos993Lean.Analytic.V213.ResponseControlSupport
public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlSemantics
public import Erdos993Lean.Analytic.V213.ResponseHalfLightProductShapeDefs

/-! Eight concrete ProductShape inputs suffice for all original control
lengths. Homogeneous and shifted lengths are structural and need no concrete
coefficient reduction. No gate truth or actual coefficient sign is used. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG

theorem uni_sumRange_length_le (f : ℕ → Uni) (n L : ℕ)
    (h : ∀ i<n, (f i).length ≤ L) : (Uni.sumRange f n).length ≤ L := by
  induction n with
  | zero => simp [Uni.sumRange]
  | succ n ih =>
      rw [Uni.sumRange,Uni.length_add]
      exact max_le (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
        (h n (Nat.lt_succ_self n))

theorem bi_getD_length_le (p : Bi) (L : ℕ)
    (h : ∀ row ∈ p, row.length ≤ L) (j : ℕ) : (p.getD j []).length ≤ L := by
  induction p generalizing j with
  | nil => simp
  | cons row p ih =>
      cases j with
      | zero => exact h row (by simp)
      | succ j =>
          exact ih (fun v hv => h v (by simp only [List.mem_cons]; exact Or.inr hv)) j

theorem bernControl_length_le (n : ℕ) (p : Bi) (j L : ℕ)
    (h : ∀ row ∈ p, row.length ≤ L) : (bernControl n p j).length ≤ L := by
  unfold bernControl
  apply (uni_trim_length_le _).trans
  apply uni_sumRange_length_le
  intro b hb
  rw [Uni.length_scale]
  exact bi_getD_length_le p L h b

/-- The executable homogeneous formula always has at most N+1 coefficients.
Its equality with the complete source polynomial still requires the separate
source-length premise of homogenizeUni_sound. -/
theorem homogenizeUni_length_le (N : ℕ) (p : Uni) :
    (homogenizeUni N p).length ≤ N+1 := by
  unfold homogenizeUni
  apply (uni_trim_length_le _).trans
  apply uni_sumRange_length_le
  intro a ha
  rw [Uni.length_scale]
  have he := Uni.outerhomogeneous_length N a (0:ℚ) (1:ℚ) (by omega)
  have hid : (Uni.mul (Uni.pow [0,1] a) (Uni.pow [1,-1] (N-a))).length = N+1 := by
    simpa only [sub_zero] using he
  exact hid.le

/-- No separate kernel reduction of the original control list is needed. -/
theorem controlPolynomial_length_of_shape (c : Fin 97)
    (h : ProductShape (controlSpec c).product) :
    (controlPolynomial c).length ≤ (productSpec (controlSpec c).product).degreeLambda+1 := by
  rw [controlPolynomial_eq_bernControl]
  exact bernControl_length_le _ _ _ _ h.2

theorem normalizedControl_length (c : Fin 97) :
    (normalizedControl c).length ≤ (productSpec (controlSpec c).product).degreeLambda+1 := by
  rw [normalizedControl_eq_homogenizeUni]
  exact homogenizeUni_length_le _ _

/-- Trimming the affine composition removes the structural trailing zero. -/
theorem shiftedControl_length (c : Fin 97) :
    (shiftedControl c).length ≤ (productSpec (controlSpec c).product).degreeLambda+1 := by
  exact (trim_comp_affine_length_le (normalizedControl c)
    (qCenter (controlSpec c).product) 1).trans (normalizedControl_length c)

/-- The outer and all inner bounds consumed by the semantic reconstruction,
with every finite input grouped by one of the eight actual products. -/
theorem control_lengths_from_product_shapes (h : ∀ r : Fin 8, ProductShape r) :
    (∀ r : Fin 8, (trimmedDeterminant r).length ≤ (productSpec r).degreeXi+1) ∧
    (∀ c : Fin 97, (controlPolynomial c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1) ∧
    (∀ c : Fin 97, (normalizedControl c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1) ∧
    (∀ c : Fin 97, (shiftedControl c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1) := by
  exact ⟨fun r => (h r).1,fun c => controlPolynomial_length_of_shape c (h _),
    normalizedControl_length,shiftedControl_length⟩

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

-- Declaration and axiom audits.
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_sumRange_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.uni_sumRange_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bi_getD_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bi_getD_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.bernControl_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni_length_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.homogenizeUni_length_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_length_of_shape
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_length_of_shape
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl_length
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl_length
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_length
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_length
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_lengths_from_product_shapes
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.control_lengths_from_product_shapes
#check Erdos993Lean.BCFG.Uni.length_add
#print axioms Erdos993Lean.BCFG.Uni.length_add
#check Erdos993Lean.BCFG.Uni.length_scale
#print axioms Erdos993Lean.BCFG.Uni.length_scale
#check Erdos993Lean.BCFG.Uni.outerhomogeneous_length
#print axioms Erdos993Lean.BCFG.Uni.outerhomogeneous_length
