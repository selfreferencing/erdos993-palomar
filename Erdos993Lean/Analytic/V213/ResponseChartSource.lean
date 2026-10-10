module

public import Erdos993Lean.Analytic.V213.ResponseField
public import Erdos993Lean.Analytic.V213.ResponseFeasibleMessages

/-! Current Lemma 5.23: the actual source and its affine branches.
The physical scalar inequalities are proved from the literal parent range.
No chart, old band certificate, or source-selection hypothesis is assumed. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

noncomputable def sourceSlopeA (q : ℝ) : ℝ := (1+q)/(2*q)
noncomputable def sourceSlopeB (q : ℝ) : ℝ := (1+q)/(2*q^2)
noncomputable def sourceIntercept (q : ℝ) : ℝ := (q-1)/(2*q)
noncomputable def sourceSwitch (q : ℝ) : ℝ := q/(1+q)
noncomputable def rhoMin (lam p : ℝ) : ℝ := 1/(1+lam*(1-p))
noncomputable def rhoStar (lam p : ℝ) : ℝ := sourceSwitch (actQ lam)/p

theorem fq_branches (q x : ℝ) :
    O2.fq q x = max (sourceSlopeA q*x) (sourceSlopeB q*x+sourceIntercept q) := by
  unfold O2.fq sourceSlopeA sourceSlopeB sourceIntercept
  congr 1 <;> ring

theorem fq_branch_gap {q : ℝ} (hq : 0 < q) (x : ℝ) :
    sourceSlopeB q*x+sourceIntercept q-sourceSlopeA q*x =
      (1-q)*((1+q)*x-q)/(2*q^2) := by
  unfold sourceSlopeA sourceSlopeB sourceIntercept
  field_simp [hq.ne']
  ring

theorem fq_lower_branch {q x : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hx : x ≤ sourceSwitch q) : O2.fq q x = sourceSlopeA q*x := by
  have hh := (le_div_iff₀ (show 0 < 1+q by linarith)).mp hx
  have hg : sourceSlopeB q*x+sourceIntercept q-sourceSlopeA q*x ≤ 0 := by
    rw [fq_branch_gap hq]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)) (by positivity)
  rw [fq_branches, max_eq_left (by linarith)]

theorem fq_upper_branch {q x : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hx : sourceSwitch q ≤ x) :
    O2.fq q x = sourceSlopeB q*x+sourceIntercept q := by
  have hh := (div_le_iff₀ (show 0 < 1+q by linarith)).mp hx
  have hg : 0 ≤ sourceSlopeB q*x+sourceIntercept q-sourceSlopeA q*x := by
    rw [fq_branch_gap hq]
    exact div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by positivity)
  rw [fq_branches, max_eq_right (by linarith)]

theorem rhoMin_q_identity {lam p : ℝ} (hl : 0 < lam) (hp1 : p < 1) :
    rhoMin lam p*(1-actQ lam*p) = 1-actQ lam := by
  have h1 : 1+lam ≠ 0 := by positivity
  have hpm : 0 < 1-p := sub_pos.mpr hp1
  have h2 : 1+lam*(1-p) ≠ 0 := by positivity
  unfold rhoMin actQ
  field_simp [h1,h2]
  ring

/-- The two literal edge bounds for both proposed neighbouring marginals. -/
theorem source_physical_edges {lam p rho : ℝ} (hl : 0 < lam)
    (hp : 0 < p) (hpq : p ≤ actQ lam) (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1) :
    p*rho+actQ lam*(1-rho) ≤ actQ lam ∧
    (1-rho)+actQ lam*(p*rho) ≤ actQ lam ∧
    p*rho+actQ lam*((1-p*rho)*O2.cavH lam p) ≤ actQ lam ∧
    (1-p*rho)*O2.cavH lam p+actQ lam*(p*rho) ≤ actQ lam := by
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have hq1 : actQ lam < 1 := (div_lt_one (by linarith : 0 < 1+lam)).2 (by linarith)
  have hp1 := hpq.trans_lt hq1
  have hpm : 0 < 1-p := sub_pos.mpr hp1
  have hr0 : 0 < rho := (one_div_pos.mpr (by positivity : 0 < 1+lam*(1-p))).trans_le hr
  have hpi : p*rho ≤ p := by nlinarith
  have hpi1 : p*rho < 1 := hpi.trans_lt hp1
  have hqp : actQ lam*p < 1 := by nlinarith
  have hrphys := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ 1-actQ lam*p)
  rw [rhoMin_q_identity hl hp1] at hrphys
  have hHq : O2.cavH lam p ≤ actQ lam := min_le_left _ _
  have hHbound : O2.cavH lam p ≤ 1-p/(lam*(1-p)) := min_le_right _ _
  have hH0 : 0 ≤ O2.cavH lam p := by
    apply le_min hq.le
    have hb := (le_div_iff₀ (show 0 < 1+lam by linarith)).mp hpq
    have hdiv : p/(lam*(1-p)) ≤ 1 :=
      (div_le_one (mul_pos hl (by linarith))).2 (by nlinarith)
    linarith
  have hqH : 0 < 1-actQ lam*O2.cavH lam p := by
    have hh := mul_le_mul_of_nonneg_left hHq hq.le
    nlinarith
  have hpcap : p*(1-actQ lam*O2.cavH lam p) ≤ actQ lam*(1-O2.cavH lam p) := by
    have hx : p ≤ (1-O2.cavH lam p)*(lam*(1-p)) := by
      apply (div_le_iff₀ (mul_pos hl (by linarith))).mp
      linarith
    have hi : actQ lam*(1-O2.cavH lam p)-p*(1-actQ lam*O2.cavH lam p) =
        ((1-O2.cavH lam p)*(lam*(1-p))-p)/(1+lam) := by
      unfold actQ
      field_simp [ne_of_gt (show 0 < 1+lam by linarith)]
      ring
    have hn : 0 ≤ actQ lam*(1-O2.cavH lam p)-p*(1-actQ lam*O2.cavH lam p) := by
      rw [hi]
      exact div_nonneg (by linarith) (by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_right hpi hqH.le
  have hn := mul_nonneg (show 0 ≤ 1-p*rho by linarith) (sub_nonneg.mpr hHq)
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

theorem source_eq_second {lam p rho : ℝ} (hl : 0 < lam)
    (hp : 0 < p) (hpq : p ≤ actQ lam) (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1) :
    O2.src lam p rho =
      (1+O2.fq (actQ lam) (p*rho)-O2.fq (actQ lam) (O2.mUp lam p rho))/2 := by
  rcases source_physical_edges hl hp hpq hr hr1 with ⟨h11,h12,h21,h22⟩
  have hm1 : p*rho+actQ lam*O2.mUp lam p rho ≤ actQ lam := by
    unfold O2.mUp
    rcases le_total (1-rho) ((1-p*rho)*O2.cavH lam p) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hm2 : O2.mUp lam p rho+actQ lam*(p*rho) ≤ actQ lam := by
    unfold O2.mUp
    rcases le_total (1-rho) ((1-p*rho)*O2.cavH lam p) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  have he := response_fq_edge hq hm1 hm2
  exact max_eq_right (by linarith)

private theorem source_sub_max (k a b : ℝ) :
    (k-max a b)/2 = min ((k-a)/2) ((k-b)/2) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]
  · rw [max_eq_left h, min_eq_left (by linarith)]

theorem fq_max {q a b : ℝ} (hq : 0 < q) :
    O2.fq q (max a b) = max (O2.fq q a) (O2.fq q b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (response_fq_monotone hq h)]
  · rw [max_eq_left h, max_eq_left (response_fq_monotone hq h)]

/-- The literal four source faces; no phase-specific branch has yet been selected. -/
theorem source_four_faces {lam p rho : ℝ} (hl : 0 < lam)
    (hp : 0 < p) (hpq : p ≤ actQ lam) (hr : rhoMin lam p ≤ rho) (hr1 : rho ≤ 1) :
    let q := actQ lam
    let f := O2.fq q (p*rho)
    let m1 := 1-rho
    let m2 := (1-p*rho)*O2.cavH lam p
    O2.src lam p rho = min
      (min ((1+f-sourceSlopeA q*m1)/2) ((1+f-sourceSlopeB q*m1-sourceIntercept q)/2))
      (min ((1+f-sourceSlopeA q*m2)/2) ((1+f-sourceSlopeB q*m2-sourceIntercept q)/2)) := by
  dsimp only
  have hq : 0 < actQ lam := div_pos hl (by linarith)
  rw [source_eq_second hl hp hpq hr hr1, O2.mUp, fq_max hq,
    source_sub_max, fq_branches (actQ lam) (1-rho),
    fq_branches (actQ lam) ((1-p*rho)*O2.cavH lam p),
    source_sub_max, source_sub_max]
  congr 2 <;> ring

theorem source_actual_eq_second {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsAcyclic) {lam : ℝ}
    (hl : 0 < lam) {K : Finset V} (hK : ConnectedIn G K) {r0 : V} (hr0 : r0 ∈ K)
    {s : Finset V} {v : V} {rho t : ℝ} (hrec : RootRecord G lam K r0 s v rho t) :
    O2.src lam (Tail.rootProb G lam s v) rho =
      (1+O2.fq (actQ lam) (Tail.rootProb G lam s v*rho)-
        O2.fq (actQ lam) (O2.mUp lam (Tail.rootProb G lam s v) rho))/2 := by
  rcases feasible_message_range hG hl hK hr0 hrec with ⟨hp,hpq,hr,hr1⟩
  exact source_eq_second hl hp hpq hr hr1

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.sourceSlopeA
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.sourceSlopeA
#check Erdos993Lean.Analytic.V213.VarianceResponse.sourceSlopeB
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.sourceSlopeB
#check Erdos993Lean.Analytic.V213.VarianceResponse.sourceIntercept
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.sourceIntercept
#check Erdos993Lean.Analytic.V213.VarianceResponse.sourceSwitch
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.sourceSwitch
#check Erdos993Lean.Analytic.V213.VarianceResponse.rhoMin
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rhoMin
#check Erdos993Lean.Analytic.V213.VarianceResponse.rhoStar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rhoStar
#check Erdos993Lean.Analytic.V213.VarianceResponse.fq_branches
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.fq_branches
#check Erdos993Lean.Analytic.V213.VarianceResponse.fq_branch_gap
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.fq_branch_gap
#check Erdos993Lean.Analytic.V213.VarianceResponse.fq_lower_branch
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.fq_lower_branch
#check Erdos993Lean.Analytic.V213.VarianceResponse.fq_upper_branch
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.fq_upper_branch
#check Erdos993Lean.Analytic.V213.VarianceResponse.rhoMin_q_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.rhoMin_q_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.source_physical_edges
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_physical_edges
#check Erdos993Lean.Analytic.V213.VarianceResponse.source_eq_second
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_eq_second
#check Erdos993Lean.Analytic.V213.VarianceResponse.fq_max
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.fq_max
#check Erdos993Lean.Analytic.V213.VarianceResponse.source_four_faces
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_four_faces
#check Erdos993Lean.Analytic.V213.VarianceResponse.source_actual_eq_second
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.source_actual_eq_second
