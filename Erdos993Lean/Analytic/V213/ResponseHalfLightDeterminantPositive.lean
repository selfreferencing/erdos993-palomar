module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightFiniteFacts
public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlLengths
public import Erdos993Lean.Analytic.V213.ResponseHalfLightGateConsumer
public import Erdos993Lean.Analytic.V213.ResponseHalfLightPolynomialProduct

/-! Final current Eq19/control/gate assembly. The public determinant theorem
has only the printed row, phase and closed half-light-domain hypotheses.
All finite shape/index/gate facts are obtained from their actual unconditional
kernel theorems; the positive clearing factor is the exact printed factor.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG

theorem printed_determinantPolynomial_positive (r : Fin 8) {lam xi : ℝ}
    (hrow : inRow (productSpec r).rowIndex lam) (hxi : 0≤xi ∧ xi≤1) :
    0<Bi.evalReal (HalfLightPolys.determinantPolynomial r) xi lam := by
  exact determinantPolynomial_positive_of_gates r (productShape_all r).1
    (control_indices_complete r)
    (fun c=>degreeLambda_at_least_two (controlSpec c).product)
    (fun c=>controlPolynomial_length_of_shape c (productShape_all (controlSpec c).product))
    (fun c=>shiftedControl_length c)
    controlGateCoverage_all gateHolds_all hxi hrow

theorem half_light_xi_coordinates {lam H : ℝ} (hl : 0<lam)
    (hH : 0≤H) (hcap : H≤childQ lam/2) :
    0≤2*H/childQ lam ∧ 2*H/childQ lam≤1 ∧
      lam*(2*H/childQ lam)/(2*(1+lam))=H := by
  have hq : 0<childQ lam := div_pos hl (by linarith)
  refine ⟨div_nonneg (by linarith) hq.le,(div_le_one hq).2 (by linarith),?_⟩
  unfold childQ
  field_simp [hl.ne',show 1+lam≠0 by positivity]

theorem printed_jointDeterminant_positive {i : Fin 4} {phase : ℕ} {lam H : ℝ}
    (hrow : inRow i lam) (hphase : phase=1 ∨ phase=2)
    (hH : 0≤H) (hcap : H≤childQ lam/2) :
    0<HalfLight.jointDeterminant i phase lam H := by
  have hlo : (0:ℝ)<((rowData i).low:ℝ) := by
    exact_mod_cast (row_interval_positive i).1
  have hl : 0<lam := hlo.trans_le hrow.1
  obtain ⟨r,hri,hrphase⟩ := product_row_phase_cover i phase hphase
  have hx := half_light_xi_coordinates hl hH hcap
  have hr : inRow (productSpec r).rowIndex lam := by simpa only [hri] using hrow
  have hp : 0<HalfLightPolys.evaluate lam (2*H/childQ lam)
      (HalfLightPolys.determinantPolynomial r) :=
    printed_determinantPolynomial_positive r hr ⟨hx.1,hx.2.1⟩
  rw [HalfLightPolys.polynomial_eq_printed_product r hl hx.1 hx.2.1,
    hri,hrphase,hx.2.2] at hp
  exact (mul_pos_iff_of_pos_left
    (HalfLightPolys.weightedClearingFactor_positive r hl hx.1 hx.2.1)).mp hp

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.printed_determinantPolynomial_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.printed_determinantPolynomial_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.half_light_xi_coordinates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.half_light_xi_coordinates
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.printed_jointDeterminant_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.printed_jointDeterminant_positive
