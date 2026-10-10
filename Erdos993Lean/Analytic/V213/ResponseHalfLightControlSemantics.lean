module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlDefs
public import Erdos993Lean.Analytic.V213.ResponseBernsteinControlSemantics

/-! Exact links from the retained operands to generic full-list semantics.
All degree/coverage hypotheses here are explicit finite obligations. These
lemmas do not prove any one of the 277 numerical gates or 97 shape bounds. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG
open scoped BigOperators

theorem controlPolynomial_eq_bernControl (c : Fin 97) :
    controlPolynomial c = bernControl
      (productSpec (controlSpec c).product).degreeXi
      (trimmedDeterminant (controlSpec c).product) (controlSpec c).index := rfl

theorem controlPolynomial_eval (c : Fin 97) (lam : ℝ) :
    Uni.evalReal (controlPolynomial c) lam =
      ∑ b ∈ Finset.range ((controlSpec c).index+1),
        (((controlSpec c).index.choose b : ℝ)/
          ((productSpec (controlSpec c).product).degreeXi.choose b : ℝ))*
            Uni.evalReal ((trimmedDeterminant (controlSpec c).product).getD b []) lam := by
  rw [controlPolynomial_eq_bernControl,bernControl_eval]

theorem normalizedControl_eq_homogenizeUni (c : Fin 97) :
    normalizedControl c = homogenizeUni
      (productSpec (controlSpec c).product).degreeLambda (controlPolynomial c) := rfl

theorem normalizedControl_sound (c : Fin 97)
    (hlen : (controlPolynomial c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1)
    (q : ℝ) (hq : q ≠ 1) :
    Uni.evalReal (normalizedControl c) q =
      (1-q)^(productSpec (controlSpec c).product).degreeLambda*
        Uni.evalReal (controlPolynomial c) (q/(1-q)) := by
  rw [normalizedControl_eq_homogenizeUni]
  exact homogenizeUni_sound _ _ hlen q hq

theorem shiftedControl_sound (c : Fin 97) (t : ℝ) :
    Uni.evalReal (shiftedControl c) t =
      Uni.evalReal (normalizedControl c) ((qCenter (controlSpec c).product : ℝ)+t) := by
  exact affine_shift_eval _ _ t

theorem shiftedControl_homogeneous (c : Fin 97)
    (hlen : (controlPolynomial c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1)
    (t : ℝ) (hq : (qCenter (controlSpec c).product : ℝ)+t ≠ 1) :
    Uni.evalReal (shiftedControl c) t =
      (1-((qCenter (controlSpec c).product : ℝ)+t))^
          (productSpec (controlSpec c).product).degreeLambda*
        Uni.evalReal (controlPolynomial c)
          (((qCenter (controlSpec c).product : ℝ)+t)/
            (1-((qCenter (controlSpec c).product : ℝ)+t))) := by
  rw [shiftedControl_sound]
  exact normalizedControl_sound c hlen _ hq

theorem shiftedControl_eval_sum (c : Fin 97)
    (hlen : (shiftedControl c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1) (t : ℝ) :
    Uni.evalReal (shiftedControl c) t =
      ∑ i ∈ Finset.range ((productSpec (controlSpec c).product).degreeLambda+1),
        (shiftedCoefficient c i : ℝ)*t^i := by
  exact uni_eval_sum_of_length_le _ _ hlen t

theorem determinant_control_reconstruction (r : Fin 8)
    (hlen : (trimmedDeterminant r).length ≤ (productSpec r).degreeXi+1)
    (xi lam : ℝ) :
    Bi.evalReal (HalfLightPolys.determinantPolynomial r) xi lam =
      bernsteinSum (productSpec r).degreeXi
        (fun j => Uni.evalReal
          (bernControl (productSpec r).degreeXi (trimmedDeterminant r) j) lam) xi := by
  have he := bernControl_reconstruct (productSpec r).degreeXi
    (trimmedDeterminant r) hlen xi lam
  simpa only [trimmedDeterminant,Bi.evalReal_trim] using he

theorem determinant_positive_of_controls (r : Fin 8)
    (hlen : (trimmedDeterminant r).length ≤ (productSpec r).degreeXi+1)
    (hcover : ∀ j ≤ (productSpec r).degreeXi, ∃ c : Fin 97,
      (controlSpec c).product = r ∧ (controlSpec c).index = j)
    {xi lam : ℝ} (hxi : 0 ≤ xi ∧ xi ≤ 1)
    (hc : ∀ c : Fin 97, (controlSpec c).product = r →
      0 < Uni.evalReal (controlPolynomial c) lam) :
    0 < Bi.evalReal (HalfLightPolys.determinantPolynomial r) xi lam := by
  rw [determinant_control_reconstruction r hlen xi lam]
  refine bernsteinSum_pos _ _ ?_ hxi
  intro j hj
  obtain ⟨c,hcr,hcj⟩ := hcover j hj
  have hp := hc c hcr
  rw [controlPolynomial_eq_bernControl,hcr,hcj] at hp
  exact hp

theorem controlPolynomial_pos_of_normalized (c : Fin 97)
    (hlen : (controlPolynomial c).length ≤
      (productSpec (controlSpec c).product).degreeLambda+1)
    {q : ℝ} (hq : q < 1) (hpos : 0 < Uni.evalReal (normalizedControl c) q) :
    0 < Uni.evalReal (controlPolynomial c) (q/(1-q)) := by
  rw [normalizedControl_sound c hlen q (ne_of_lt hq)] at hpos
  exact (mul_pos_iff_of_pos_left (pow_pos (sub_pos.mpr hq) _)).mp hpos

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

/-! Actual declaration and inherited-helper audits; no numerical computation. -/
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_eq_bernControl
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_eq_bernControl
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_eval
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_eval
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl_eq_homogenizeUni
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl_eq_homogenizeUni
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl_sound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalizedControl_sound
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_sound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_sound
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_homogeneous
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_homogeneous
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_eval_sum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.shiftedControl_eval_sum
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.determinant_control_reconstruction
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.determinant_control_reconstruction
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.determinant_positive_of_controls
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.determinant_positive_of_controls
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_pos_of_normalized
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlPolynomial_pos_of_normalized
#check Erdos993Lean.BCFG.Bi.evalReal_trim
#print axioms Erdos993Lean.BCFG.Bi.evalReal_trim
