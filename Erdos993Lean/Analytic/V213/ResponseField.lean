module

public import Erdos993Lean.Analytic.O2.Source

/-!
Current Lemma 5.7 of version 2.13 of the manuscript and equation (5.3), f4:lem2.6/f4:eq3.
The affine branches and the actual marginal field are bound explicitly below.
The inherited generic finite-law and graph proofs have the same formulas;
no old band payment or certificate is used. These statements hold for every
finite simple graph, and therefore in particular for every printed forest.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

theorem response_fq_formula (q x : ℝ) :
    O2.fq q x = max ((1+q)*x/(2*q))
      ((1+q)*x/(2*q^2)+(q-1)/(2*q)) := rfl

theorem response_fq_monotone {q x y : ℝ} (hq : 0 < q) (hxy : x ≤ y) :
    O2.fq q x ≤ O2.fq q y := O2.fq_mono hq hxy

theorem response_fq_range {q x : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) : 0 ≤ O2.fq q x ∧ O2.fq q x ≤ 1 :=
  ⟨O2.fq_nonneg hq hx0, O2.fq_le_one hq hq1 hxq⟩

/-- The printed two-edge-hypothesis implication, with no added sign restriction on x,y. -/
theorem response_fq_edge {q x y : ℝ} (hq : 0 < q)
    (hxy : x+q*y ≤ q) (hyx : y+q*x ≤ q) : O2.fq q x+O2.fq q y ≤ 1 :=
  O2.fq_edge hq hxy hyx

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The printed field; nbrMax is max(0,max over neighbours), including isolated vertices. -/
noncomputable def responseField (lam : ℝ) (v : V) : ℝ :=
  (1+O2.fq (actQ lam) (O2.gMarg G lam v)-O2.nbrMax G lam v)/2

theorem responseField_eq_sRef (lam : ℝ) (v : V) :
    responseField G lam v = O2.sRef G lam v := rfl

theorem response_marginal_nonneg {lam : ℝ} (hl : 0 < lam) (v : V) :
    0 ≤ O2.gMarg G lam v := O2.gMarg_nonneg hl.le v

theorem response_marginal_le_q {lam : ℝ} (hl : 0 < lam) (v : V) :
    O2.gMarg G lam v ≤ actQ lam := O2.gMarg_le_actQ hl.le v

theorem response_marginal_edge {lam : ℝ} (hl : 0 < lam) {u v : V}
    (huv : G.Adj u v) : O2.gMarg G lam u+actQ lam*O2.gMarg G lam v ≤ actQ lam :=
  O2.gMarg_edge hl huv

/-- The whole chain in the printed vertex conclusion. -/
theorem responseField_vertex {lam : ℝ} (hl : 0 < lam) (v : V) :
    0 ≤ O2.fq (actQ lam) (O2.gMarg G lam v) ∧
    O2.fq (actQ lam) (O2.gMarg G lam v) ≤ responseField G lam v ∧
    responseField G lam v ≤ 1 :=
  ⟨O2.fq_gMarg_nonneg hl v, O2.fq_le_sRef hl v, O2.sRef_le_one hl v⟩

theorem responseField_nonneg {lam : ℝ} (hl : 0 < lam) (v : V) :
    0 ≤ responseField G lam v := O2.sRef_nonneg hl v

theorem responseField_edge {lam : ℝ} (hl : 0 < lam) {u v : V}
    (huv : G.Adj u v) : responseField G lam u+responseField G lam v ≤ 1 :=
  O2.sRef_edge huv

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_formula
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_formula
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_monotone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_monotone
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_range
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_range
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_edge
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_fq_edge
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseField
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseField
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseField_eq_sRef
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseField_eq_sRef
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_marginal_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_marginal_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_marginal_le_q
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_marginal_le_q
#check Erdos993Lean.Analytic.V213.VarianceResponse.response_marginal_edge
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_marginal_edge
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseField_vertex
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseField_vertex
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseField_nonneg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseField_nonneg
#check Erdos993Lean.Analytic.V213.VarianceResponse.responseField_edge
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.responseField_edge
