module

public import Erdos993Lean.F4U.Light.Construction.ChartDenominators

/-! Original row-coordinate coverage. Both lambda and q(lambda) are retained;
charts are exact affine round trips within their original endpoint sets. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem row_lambda_endpoints (r : Row) :
    0 < (rowData r).lo ∧ (rowData r).lo < (rowData r).hi := by
  cases r <;> norm_num [rowData]

 theorem row_q_endpoints (r : Row) :
    0 < q (rowData r).lo ∧ q (rowData r).lo < q (rowData r).hi ∧
      q (rowData r).hi < 1 := by
  cases r <;> norm_num [rowData,q]

 theorem activity_lambda_coverage {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    (rowData r).lo ≤ lam ∧ lam ≤ (rowData r).hi := hlam

 theorem activity_q_coverage {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    q (rowData r).lo ≤ q lam ∧ q lam ≤ q (rowData r).hi :=
  inRow_q_endpoint_bounds hlam

 theorem interval_affine_roundtrip {a b x : ℝ} (hab : a < b)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x=a+(b-a)*u := by
  have hd : 0 < b-a := sub_pos.mpr hab
  refine ⟨(x-a)/(b-a),div_nonneg (sub_nonneg.mpr hax) hd.le,?_,?_⟩
  · rw [div_le_one hd]
    linarith
  · field_simp [hd.ne']
    <;> ring

 theorem activity_lambda_chart_exists {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      lam=(rowData r).lo+((rowData r).hi-(rowData r).lo)*u :=
  interval_affine_roundtrip (row_lambda_endpoints r).2 hlam.1 hlam.2

 theorem activity_q_chart_exists {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      q lam=q (rowData r).lo+(q (rowData r).hi-q (rowData r).lo)*u :=
  interval_affine_roundtrip (row_q_endpoints r).2.1
    (activity_q_coverage hlam).1 (activity_q_coverage hlam).2

 theorem inverse_q_positive {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < x/(1-x) := div_pos hx0 (sub_pos.mpr hx1)

 theorem q_of_inverse_q {x : ℝ} (hx1 : x < 1) : q (x/(1-x))=x := by
  have hd : 1-x ≠ 0 := (sub_pos.mpr hx1).ne'
  have he : 1+x/(1-x)=1/(1-x) := by field_simp [hd]; ring
  unfold q
  rw [he]
  field_simp [hd]

 theorem inverse_q_of_activity {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    q lam/(1-q lam)=lam := lambda_from_q lam (inRow_lambda_bounds hlam).1

 theorem q_activity_roundtrip {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    q (q lam/(1-q lam))=q lam := by
  rw [inverse_q_of_activity hlam]

 theorem lambda_activity_restores_primitive {r : Row} {lam : ℝ}
    (hlam : InRow r lam) :
    (rowData r).lo ≤ q lam/(1-q lam) ∧
      q lam/(1-q lam) ≤ (rowData r).hi := by
  rw [inverse_q_of_activity hlam]
  exact hlam

#print axioms row_lambda_endpoints
#print axioms row_q_endpoints
#print axioms activity_lambda_coverage
#print axioms activity_q_coverage
#print axioms interval_affine_roundtrip
#print axioms activity_lambda_chart_exists
#print axioms activity_q_chart_exists
#print axioms inverse_q_positive
#print axioms q_of_inverse_q
#print axioms inverse_q_of_activity
#print axioms q_activity_roundtrip
#print axioms lambda_activity_restores_primitive

end
end F4Unified.LightConstruction
