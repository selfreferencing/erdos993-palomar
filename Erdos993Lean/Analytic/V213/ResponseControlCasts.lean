module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlSemantics
public import Erdos993Lean.Analytic.V213.ResponseControlShape

/-! Exact Rat-to-Real interpretation of the current C/D/S operands. These
identities do not test coefficients or gates and retain the finite length
premise required to identify the whole shifted polynomial. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG
open scoped BigOperators

theorem tailNorm_cast (c : Fin 97) :
    (tailNorm c : ℝ)=HalfLightShape.tailNorm ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) ((qRadius (controlSpec c).product : ℝ)) := by
  simp [tailNorm,HalfLightShape.tailNorm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi3 : 3 ≤ i <;> simp [hi3]

theorem lowerCurvature_cast (c : Fin 97) :
    (lowerCurvature c : ℝ)=HalfLightShape.lowerK ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) ((qRadius (controlSpec c).product : ℝ)) := by
  simp [lowerCurvature,HalfLightShape.lowerK,tailNorm_cast]

theorem lowerQuadratic_cast (c : Fin 97) (t : ℚ) :
    (lowerQuadratic c t : ℝ)=HalfLightShape.lowerQ ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) ((qRadius (controlSpec c).product : ℝ)) (t:ℝ) := by
  simp [lowerQuadratic,HalfLightShape.lowerQ,lowerCurvature_cast]

theorem slopeBound_cast (c : Fin 97) :
    (slopeBound c : ℝ)=(shiftedCoefficient c 1:ℝ)+
      2*|HalfLightShape.lowerK ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) ((qRadius (controlSpec c).product : ℝ))| *((qRadius (controlSpec c).product : ℝ)) := by
  simp [slopeBound,lowerCurvature_cast]

theorem upperCurvature_cast (c : Fin 97) :
    (upperCurvature c : ℝ)=HalfLightShape.upperCurvature ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) ((qRadius (controlSpec c).product : ℝ)) := by
  simp [upperCurvature,HalfLightShape.upperCurvature]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi3 : 3 ≤ i <;> simp [hi3]

theorem q_center_endpoints (r : Fin 8) :
    qCenter r-qRadius r=qLow r ∧ qCenter r+qRadius r=qHigh r := by
  unfold qCenter qRadius
  constructor <;> ring

theorem centeredValue_eq_shifted (c : Fin 97)
    (hlen : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1) (t : ℝ) :
    HalfLightShape.centeredValue ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) t=Uni.evalReal (shiftedControl c) t := by
  exact (shiftedControl_eval_sum c hlen t).symm

theorem centeredValue_endpoints (c : Fin 97)
    (hlen : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1) :
    HalfLightShape.centeredValue ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) (-((qRadius (controlSpec c).product : ℝ)))=
      (ratEval (normalizedControl c) (qLow (controlSpec c).product):ℝ) ∧
    HalfLightShape.centeredValue ((productSpec (controlSpec c).product).degreeLambda) ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) ((qRadius (controlSpec c).product : ℝ))=
      (ratEval (normalizedControl c) (qHigh (controlSpec c).product):ℝ) := by
  have he := q_center_endpoints (controlSpec c).product
  have hlo := congrArg (fun x:ℚ=>(x:ℝ)) he.1
  have hhi := congrArg (fun x:ℚ=>(x:ℝ)) he.2
  push_cast at hlo hhi
  constructor
  · rw [centeredValue_eq_shifted c hlen,shiftedControl_sound,ratEval_cast]
    congr 1 <;> linarith
  · rw [centeredValue_eq_shifted c hlen,shiftedControl_sound,ratEval_cast]
    rw [hhi]

theorem centered_argument_mem {r : Fin 8} {q : ℝ}
    (hq : (qLow r:ℝ)≤q ∧ q≤(qHigh r:ℝ)) :
    |q-(qCenter r:ℝ)|≤(qRadius r:ℝ) := by
  have he := q_center_endpoints r
  have hlo := congrArg (fun x:ℚ=>(x:ℝ)) he.1
  have hhi := congrArg (fun x:ℚ=>(x:ℝ)) he.2
  push_cast at hlo hhi
  apply abs_le.mpr
  constructor <;> linarith [hq.1,hq.2]

theorem normalized_control_C_positive (c : Fin 97)
    (hN : 2≤(productSpec (controlSpec c).product).degreeLambda) (hlen : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1)
    {q : ℝ} (hq : (qLow (controlSpec c).product:ℝ)≤q ∧ q≤(qHigh (controlSpec c).product:ℝ))
    (hk : lowerCurvature c<0)
    (hl : 0<lowerQuadratic c (-qRadius (controlSpec c).product))
    (hu : 0<lowerQuadratic c (qRadius (controlSpec c).product)) :
    0<Uni.evalReal (normalizedControl c) q := by
  have ht := centered_argument_mem hq
  have hr : 0≤(qRadius (controlSpec c).product : ℝ) := (abs_nonneg _).trans ht
  have hk' : (lowerCurvature c:ℝ)<0 := by exact_mod_cast hk
  have hl' : (0:ℝ)<(lowerQuadratic c (-qRadius (controlSpec c).product):ℝ) := by exact_mod_cast hl
  have hu' : (0:ℝ)<(lowerQuadratic c (qRadius (controlSpec c).product):ℝ) := by exact_mod_cast hu
  rw [lowerCurvature_cast] at hk'
  rw [lowerQuadratic_cast,Rat.cast_neg] at hl'
  rw [lowerQuadratic_cast] at hu'
  have hh := HalfLightShape.control_C_positive hN ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) hr ht hk' hl' hu'
  rw [centeredValue_eq_shifted c hlen,shiftedControl_sound] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem normalized_control_D_positive (c : Fin 97)
    (hN : 2≤(productSpec (controlSpec c).product).degreeLambda) (hlen : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1)
    {q : ℝ} (hq : (qLow (controlSpec c).product:ℝ)≤q ∧ q≤(qHigh (controlSpec c).product:ℝ))
    (hs : slopeBound c<0) (hu : 0<lowerQuadratic c (qRadius (controlSpec c).product)) :
    0<Uni.evalReal (normalizedControl c) q := by
  have ht := centered_argument_mem hq
  have hr : 0≤(qRadius (controlSpec c).product : ℝ) := (abs_nonneg _).trans ht
  have hs' : (slopeBound c:ℝ)<0 := by exact_mod_cast hs
  have hu' : (0:ℝ)<(lowerQuadratic c (qRadius (controlSpec c).product):ℝ) := by exact_mod_cast hu
  rw [slopeBound_cast] at hs'
  rw [lowerQuadratic_cast] at hu'
  have hh := HalfLightShape.control_D_positive hN ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) hr ht hs' hu'
  rw [centeredValue_eq_shifted c hlen,shiftedControl_sound] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem normalized_control_S_positive (c : Fin 97)
    (hN : 2≤(productSpec (controlSpec c).product).degreeLambda) (hlen : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1)
    {q : ℝ} (hq : (qLow (controlSpec c).product:ℝ)≤q ∧ q≤(qHigh (controlSpec c).product:ℝ))
    (hU : upperCurvature c<0)
    (hl : 0<ratEval (normalizedControl c) (qLow (controlSpec c).product))
    (hu : 0<ratEval (normalizedControl c) (qHigh (controlSpec c).product)) :
    0<Uni.evalReal (normalizedControl c) q := by
  have ht := centered_argument_mem hq
  have hr : 0≤(qRadius (controlSpec c).product : ℝ) := (abs_nonneg _).trans ht
  have hU' : (upperCurvature c:ℝ)<0 := by exact_mod_cast hU
  have hl' : (0:ℝ)<(ratEval (normalizedControl c) (qLow (controlSpec c).product):ℝ) := by exact_mod_cast hl
  have hu' : (0:ℝ)<(ratEval (normalizedControl c) (qHigh (controlSpec c).product):ℝ) := by exact_mod_cast hu
  rw [upperCurvature_cast] at hU'
  rw [←(centeredValue_endpoints c hlen).1] at hl'
  rw [←(centeredValue_endpoints c hlen).2] at hu'
  have hh := HalfLightShape.control_S_positive hN ((fun i : ℕ => (shiftedCoefficient c i : ℝ))) hr ht hU' hl' hu'
  rw [centeredValue_eq_shifted c hlen,shiftedControl_sound] at hh
  convert hh using 1 <;> congr 1 <;> ring

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.tailNorm_cast
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.tailNorm_cast
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerCurvature_cast
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerCurvature_cast
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerQuadratic_cast
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.lowerQuadratic_cast
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.slopeBound_cast
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.slopeBound_cast
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.upperCurvature_cast
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.upperCurvature_cast
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.q_center_endpoints
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.q_center_endpoints
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.centeredValue_eq_shifted
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.centeredValue_eq_shifted
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.centeredValue_endpoints
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.centeredValue_endpoints
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.centered_argument_mem
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.centered_argument_mem
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_C_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_C_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_D_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_D_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_S_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_S_positive
