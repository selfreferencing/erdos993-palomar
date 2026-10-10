module

public import Erdos993Lean.Analytic.V213.ResponseControlCasts

/-! Exact required-gate coverage for each actual control kind. Coverage is
not proved by this generic module: the literal 97-control/277-reference
finite mapping is an explicit input, separate from gate truth. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

open Erdos993Lean.BCFG

def HasGate (c : Fin 97) (quantity : GateQuantity) : Prop :=
  ∃ g : Fin 277, (gateSpec g).control=c ∧ (gateSpec g).quantity=quantity

def ControlGateCoverage (c : Fin 97) : Prop :=
  match (controlSpec c).kind with
  | .C => HasGate c .k ∧ HasGate c .qMinus ∧ HasGate c .qPlus
  | .D => HasGate c .slope ∧ HasGate c .qPlus
  | .S => HasGate c .upperCurvature ∧ HasGate c .polyLow ∧ HasGate c .polyHigh

instance hasGateDecidable (c : Fin 97) (quantity : GateQuantity) : Decidable (HasGate c quantity) := by
  unfold HasGate
  infer_instance

instance controlGateCoverageDecidable (c : Fin 97) : Decidable (ControlGateCoverage c) := by
  unfold ControlGateCoverage
  split <;> infer_instance

theorem gate_k_negative {c : Fin 97} (hcov : HasGate c .k) (hall : ∀g,gateHolds g) :
    lowerCurvature c<0 := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  simpa only [gateHolds,hq,gateValue,hq,hc] using h

theorem gate_qMinus_positive {c : Fin 97} (hcov : HasGate c .qMinus) (hall : ∀g,gateHolds g) :
    0<lowerQuadratic c (-qRadius (controlSpec c).product) := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  have he : (10:ℚ)^(productSpec (controlSpec c).product).floorPower<
      lowerQuadratic c (-qRadius (controlSpec c).product) := by
    simpa only [gateHolds,hq,gateValue,hq,hc] using h
  exact (pow_pos (by norm_num : (0:ℚ)<10) _).trans he

theorem gate_qPlus_positive {c : Fin 97} (hcov : HasGate c .qPlus) (hall : ∀g,gateHolds g) :
    0<lowerQuadratic c (qRadius (controlSpec c).product) := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  have he : (10:ℚ)^(productSpec (controlSpec c).product).floorPower<
      lowerQuadratic c (qRadius (controlSpec c).product) := by
    simpa only [gateHolds,hq,gateValue,hq,hc] using h
  exact (pow_pos (by norm_num : (0:ℚ)<10) _).trans he

theorem gate_slope_negative {c : Fin 97} (hcov : HasGate c .slope) (hall : ∀g,gateHolds g) :
    slopeBound c<0 := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  simpa only [gateHolds,hq,gateValue,hq,hc] using h

theorem gate_upperCurvature_negative {c : Fin 97} (hcov : HasGate c .upperCurvature)
    (hall : ∀g,gateHolds g) : upperCurvature c<0 := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  simpa only [gateHolds,hq,gateValue,hq,hc] using h

theorem gate_polyLow_positive {c : Fin 97} (hcov : HasGate c .polyLow) (hall : ∀g,gateHolds g) :
    0<ratEval (normalizedControl c) (qLow (controlSpec c).product) := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  have he : (10:ℚ)^(productSpec (controlSpec c).product).floorPower<
      ratEval (normalizedControl c) (qLow (controlSpec c).product) := by
    simpa only [gateHolds,hq,gateValue,hq,hc] using h
  exact (pow_pos (by norm_num : (0:ℚ)<10) _).trans he

theorem gate_polyHigh_positive {c : Fin 97} (hcov : HasGate c .polyHigh) (hall : ∀g,gateHolds g) :
    0<ratEval (normalizedControl c) (qHigh (controlSpec c).product) := by
  obtain ⟨g,hc,hq⟩ := hcov
  have h := hall g
  have he : (10:ℚ)^(productSpec (controlSpec c).product).floorPower<
      ratEval (normalizedControl c) (qHigh (controlSpec c).product) := by
    simpa only [gateHolds,hq,gateValue,hq,hc] using h
  exact (pow_pos (by norm_num : (0:ℚ)<10) _).trans he

theorem normalized_control_positive_of_gates (c : Fin 97)
    (hN : 2≤(productSpec (controlSpec c).product).degreeLambda)
    (hlen : (shiftedControl c).length≤(productSpec (controlSpec c).product).degreeLambda+1)
    (hcov : ControlGateCoverage c) (hall : ∀g,gateHolds g) {q : ℝ}
    (hq : (qLow (controlSpec c).product:ℝ)≤q ∧ q≤(qHigh (controlSpec c).product:ℝ)) :
    0<Uni.evalReal (normalizedControl c) q := by
  cases hk : (controlSpec c).kind with
  | C =>
      have hc : HasGate c .k ∧ HasGate c .qMinus ∧ HasGate c .qPlus := by
        simpa only [ControlGateCoverage,hk] using hcov
      exact normalized_control_C_positive c hN hlen hq (gate_k_negative hc.1 hall)
        (gate_qMinus_positive hc.2.1 hall) (gate_qPlus_positive hc.2.2 hall)
  | D =>
      have hc : HasGate c .slope ∧ HasGate c .qPlus := by
        simpa only [ControlGateCoverage,hk] using hcov
      exact normalized_control_D_positive c hN hlen hq (gate_slope_negative hc.1 hall)
        (gate_qPlus_positive hc.2 hall)
  | S =>
      have hc : HasGate c .upperCurvature ∧ HasGate c .polyLow ∧ HasGate c .polyHigh := by
        simpa only [ControlGateCoverage,hk] using hcov
      exact normalized_control_S_positive c hN hlen hq (gate_upperCurvature_negative hc.1 hall)
        (gate_polyLow_positive hc.2.1 hall) (gate_polyHigh_positive hc.2.2 hall)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.HasGate
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.HasGate
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ControlGateCoverage
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.ControlGateCoverage
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.hasGateDecidable
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.hasGateDecidable
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlGateCoverageDecidable
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.controlGateCoverageDecidable
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_k_negative
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_k_negative
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_qMinus_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_qMinus_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_qPlus_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_qPlus_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_slope_negative
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_slope_negative
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_upperCurvature_negative
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_upperCurvature_negative
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_polyLow_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_polyLow_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_polyHigh_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.gate_polyHigh_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_positive_of_gates
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightGates.normalized_control_positive_of_gates
