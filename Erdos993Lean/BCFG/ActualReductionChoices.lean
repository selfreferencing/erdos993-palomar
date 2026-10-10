module

public import Erdos993Lean.BCFG.ReductionChoices
public import Erdos993Lean.Analytic.V213.ResponseOneVertex
public import Erdos993Lean.Analytic.V213.ResponseFeasibleMessages

/-! The scalar comparison choices at actual generated forest records.
No scalar payment positivity or transfer premise is asserted here. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem reduction_actual_occupation (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    occupation lam (Real.exp (-Tmass G lam s v)) = rootProb G lam s v := by
  simpa only [occupation, msg] using (message_recursion hG hl hs hv).symm

theorem reduction_actual_logMass (lam : ℝ) (s : Finset V) (v : V) :
    logMass (Real.exp (-Tmass G lam s v)) = Tmass G lam s v := by
  simp only [logMass, Real.log_exp, neg_neg]

theorem reduction_actual_feasible {r : AnalyticRow} {lam : ℝ}
    (hrow : InRow r lam) (hG : G.IsAcyclic)
    {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ}
    (hrec : RootRecord G lam K r0 s v rho t) :
    Feasible r lam (Real.exp (-Tmass G lam s v)) rho := by
  have hl := activity_pos hrow
  have hs := rootRecord_connected hG hK hr0 hrec
  have hv := rootRecord_mem hr0 hrec
  have hp := feasible_message_range hG hl hK hr0 hrec
  refine ⟨hrow, Real.exp_pos _, ?_, ?_, hp.2.2.2⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Tmass_nonneg hG hl hs hv))
  · rw [← reduction_rho_identity hl (Real.exp_pos _), reduction_actual_occupation hG hl hs hv]
    exact hp.2.2.1

theorem reduction_actual_T0 (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    messageRatio (rootProb G lam s v) ≤ cubicEnvelope (rootProb G lam s v) :=
  reduction_cubic_bound (rootProb_pos hl s v).le (rootProb_lt_one hl.le hv)

theorem reduction_actual_massLine {r : AnalyticRow} {lam : ℝ}
    (hrow : InRow r lam) (hG : G.IsAcyclic)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    massLine r lam ≤ messageRatio (O2.cavH lam (rootProb G lam s v)) := by
  have hl := activity_pos hrow
  have hw1 : Real.exp (-Tmass G lam s v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Tmass_nonneg hG hl hs hv))
  have h := reduction_massLine_cavity hrow (Real.exp_pos (-Tmass G lam s v)) hw1
  rwa [reduction_actual_occupation hG hl hs hv] at h

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.reduction_actual_occupation
#print axioms Erdos993Lean.BCFG.Analytic.reduction_actual_occupation
#check Erdos993Lean.BCFG.Analytic.reduction_actual_logMass
#print axioms Erdos993Lean.BCFG.Analytic.reduction_actual_logMass
#check Erdos993Lean.BCFG.Analytic.reduction_actual_feasible
#print axioms Erdos993Lean.BCFG.Analytic.reduction_actual_feasible
#check Erdos993Lean.BCFG.Analytic.reduction_actual_T0
#print axioms Erdos993Lean.BCFG.Analytic.reduction_actual_T0
#check Erdos993Lean.BCFG.Analytic.reduction_actual_massLine
#print axioms Erdos993Lean.BCFG.Analytic.reduction_actual_massLine
