module

public import Erdos993Lean.Analytic.V213.Theorem51.TableBinding
public import Erdos993Lean.Analytic.V213.ResponseHalfLightDefs

/-! Exact scalar bindings between the unified contract and the accepted
parent payment. The source equality uses physical vacancy feasibility. The
reserve equality uses the contract's admissible zero-mass convention. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.Theorem51

open VarianceResponse

theorem one_sub_parentH (Y : ℝ) :
    1 - F4Unified.parentH Y = Real.exp (-Y) := by
  unfold F4Unified.parentH
  ring

theorem parentH_pos {Y : ℝ} (hY : 0 < Y) : 0 < F4Unified.parentH Y := by
  have he : Real.exp (-Y) < 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_lt_exp.mpr (show -Y < (0 : ℝ) by linarith)
  unfold F4Unified.parentH
  linarith

theorem parentH_lt_one (Y : ℝ) : F4Unified.parentH Y < 1 := by
  have he := Real.exp_pos (-Y)
  unfold F4Unified.parentH
  linarith

theorem p_eq_halfParent (lam Y : ℝ) :
    F4Unified.p lam Y = ParentRows.halfParent lam (F4Unified.parentH Y) := by
  simp only [F4Unified.p, ParentRows.halfParent, chartParent, one_sub_parentH]

theorem parentY_parentH (Y : ℝ) :
    ParentRows.parentY (F4Unified.parentH Y) = Y := by
  rw [ParentRows.parentY, one_sub_parentH, Real.log_exp]
  ring

theorem p_pos {lam Y : ℝ} (hl : 0 < lam) : 0 < F4Unified.p lam Y := by
  unfold F4Unified.p
  positivity

theorem p_bounds {lam Y : ℝ} (hl : 0 < lam) (hY : 0 ≤ Y) :
    0 < F4Unified.p lam Y ∧ F4Unified.p lam Y ≤ actQ lam ∧
      F4Unified.p lam Y < 1 := by
  have he : Real.exp (-Y) ≤ 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show -Y ≤ (0 : ℝ) by linarith)
  exact chartParent_bounds hl (Real.exp_pos (-Y)) he

theorem lowerVacancy_eq_rhoMin (lam Y : ℝ) :
    F4Unified.lowerVacancy lam Y = rhoMin lam (F4Unified.p lam Y) := rfl

theorem contract_childH_eq_messageRatio (u : ℝ) :
    F4Unified.childH u = messageRatio u := by
  by_cases hu : u = 0
  · simp only [F4Unified.childH, messageRatio, if_pos hu]
  · simp only [F4Unified.childH, F4Unified.phi, messageRatio, if_neg hu]

theorem contract_childJ_eq_childJ (lam u : ℝ) :
    F4Unified.childJ lam u = VarianceResponse.childJ lam u := by
  by_cases hu : u = 0
  · subst u
    rw [F4Unified.childJ, if_pos rfl, childJ_zero]
  · simp only [F4Unified.childJ, if_neg hu, contract_childH_eq_messageRatio,
      VarianceResponse.childJ, childLog]

theorem contract_cavH {lam Y : ℝ} (hl : 0 < lam) :
    O2.cavH lam (F4Unified.p lam Y) = F4Unified.childCap lam Y := by
  simpa only [F4Unified.p, chartParent, F4Unified.childCap,
    F4Unified.parentH, q_eq_actQ] using
      chart_cavity_cap hl (Real.exp_pos (-Y))

theorem contract_mUp {lam Y rho : ℝ} (hl : 0 < lam) :
    O2.mUp lam (F4Unified.p lam Y) rho =
      max (1 - rho) ((1 - F4Unified.p lam Y * rho) * F4Unified.childCap lam Y) := by
  rw [O2.mUp, contract_cavH hl]

theorem contract_source_second {lam Y rho : ℝ} (hl : 0 < lam) :
    F4Unified.source lam Y rho =
      (1 + O2.fq (actQ lam) (F4Unified.p lam Y * rho) -
        O2.fq (actQ lam) (O2.mUp lam (F4Unified.p lam Y) rho)) / 2 := by
  simp only [F4Unified.source, f_eq_fq, contract_mUp hl]

theorem contract_source_le {lam Y rho : ℝ} (hl : 0 < lam) :
    F4Unified.source lam Y rho ≤ O2.src lam (F4Unified.p lam Y) rho := by
  rw [contract_source_second hl, O2.src]
  exact le_max_right _ _

theorem contract_source_eq {lam Y rho : ℝ} (hl : 0 < lam) (hY : 0 ≤ Y)
    (hr : F4Unified.FeasibleVacancy lam Y rho) :
    F4Unified.source lam Y rho = O2.src lam (F4Unified.p lam Y) rho := by
  have hp := p_bounds hl hY
  have hrmin : rhoMin lam (F4Unified.p lam Y) ≤ rho := hr.1
  rw [source_eq_second hl hp.1 hp.2.1 hrmin hr.2]
  exact contract_source_second hl

theorem contract_parentP_eq {r : F4Unified.Row} {lam Y rho : ℝ} (hl : 0 < lam) :
    F4Unified.parentP r lam Y rho =
      ParentRows.parentP (parentRowIndex r) lam (F4Unified.parentH Y) rho := by
  have hp := p_pos (Y := Y) hl
  simp only [F4Unified.parentP, ParentRows.parentP, ← p_eq_halfParent lam Y,
    ← gamma_eq r lam, messageRatio_of_ne_zero hp.ne']
  ring

theorem contract_reserve_eq {r : F4Unified.Row} {lam u y : ℝ}
    (ha : F4Unified.Admissible lam u y) :
    F4Unified.reserve r lam u y =
      ParentRows.delta (parentRowIndex r) lam * (messageRatio u - y)^2 /
        VarianceResponse.childJ lam u := by
  rcases ha with hJ | ⟨hJ, _⟩
  · rw [F4Unified.reserve, if_pos hJ, delta_eq,
      contract_childH_eq_messageRatio, contract_childJ_eq_childJ]
  · have hJ' : VarianceResponse.childJ lam u = 0 :=
      (contract_childJ_eq_childJ lam u).symm.trans hJ
    rw [F4Unified.reserve, if_neg (not_lt_of_ge hJ.le)]
    simp only [hJ', div_zero]

theorem payment_eq_parentPayment {r : F4Unified.Row} {lam Y rho u y : ℝ}
    (hl : 0 < lam) (hY : 0 ≤ Y) (hr : F4Unified.FeasibleVacancy lam Y rho)
    (ha : F4Unified.Admissible lam u y) :
    F4Unified.payment r lam Y rho u y =
      ParentRows.parentPayment (parentRowIndex r) lam (F4Unified.parentH Y) rho u y := by
  simp only [F4Unified.payment, ParentRows.parentPayment, responseQuadratic,
    ParentRows.parentA, ParentRows.parentB, ParentRows.parentC, ParentRows.parentD,
    ← p_eq_halfParent lam Y, parentY_parentH, price_eq r lam,
    ← alpha_eq r lam, ← beta_eq r lam, ← gamma_eq r lam, ← delta_eq r lam,
    ← contract_parentP_eq (r := r) (Y := Y) (rho := rho) hl,
    ← contract_source_eq hl hY hr, contract_childH_eq_messageRatio,
    contract_reserve_eq ha]
  unfold F4Unified.parentN
  ring

end Erdos993Lean.Analytic.V213.Theorem51

#check Erdos993Lean.Analytic.V213.Theorem51.one_sub_parentH
#print axioms Erdos993Lean.Analytic.V213.Theorem51.one_sub_parentH
#check Erdos993Lean.Analytic.V213.Theorem51.parentH_pos
#print axioms Erdos993Lean.Analytic.V213.Theorem51.parentH_pos
#check Erdos993Lean.Analytic.V213.Theorem51.parentH_lt_one
#print axioms Erdos993Lean.Analytic.V213.Theorem51.parentH_lt_one
#check Erdos993Lean.Analytic.V213.Theorem51.p_eq_halfParent
#print axioms Erdos993Lean.Analytic.V213.Theorem51.p_eq_halfParent
#check Erdos993Lean.Analytic.V213.Theorem51.parentY_parentH
#print axioms Erdos993Lean.Analytic.V213.Theorem51.parentY_parentH
#check Erdos993Lean.Analytic.V213.Theorem51.p_pos
#print axioms Erdos993Lean.Analytic.V213.Theorem51.p_pos
#check Erdos993Lean.Analytic.V213.Theorem51.p_bounds
#print axioms Erdos993Lean.Analytic.V213.Theorem51.p_bounds
#check Erdos993Lean.Analytic.V213.Theorem51.lowerVacancy_eq_rhoMin
#print axioms Erdos993Lean.Analytic.V213.Theorem51.lowerVacancy_eq_rhoMin
#check Erdos993Lean.Analytic.V213.Theorem51.contract_childH_eq_messageRatio
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_childH_eq_messageRatio
#check Erdos993Lean.Analytic.V213.Theorem51.contract_childJ_eq_childJ
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_childJ_eq_childJ
#check Erdos993Lean.Analytic.V213.Theorem51.contract_cavH
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_cavH
#check Erdos993Lean.Analytic.V213.Theorem51.contract_mUp
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_mUp
#check Erdos993Lean.Analytic.V213.Theorem51.contract_source_second
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_source_second
#check Erdos993Lean.Analytic.V213.Theorem51.contract_source_le
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_source_le
#check Erdos993Lean.Analytic.V213.Theorem51.contract_source_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_source_eq
#check Erdos993Lean.Analytic.V213.Theorem51.contract_parentP_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_parentP_eq
#check Erdos993Lean.Analytic.V213.Theorem51.contract_reserve_eq
#print axioms Erdos993Lean.Analytic.V213.Theorem51.contract_reserve_eq
#check Erdos993Lean.Analytic.V213.Theorem51.payment_eq_parentPayment
#print axioms Erdos993Lean.Analytic.V213.Theorem51.payment_eq_parentPayment
