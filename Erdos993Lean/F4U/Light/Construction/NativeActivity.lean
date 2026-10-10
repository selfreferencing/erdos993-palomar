module

public import Erdos993Lean.F4U.Light.Construction.ActivityCharts
public import Erdos993Lean.F4U.Light.Construction.DenominatorOrientation

/-! Lossless native activity domain, including the inverse q coordinate. The
orientation consumer takes nonvanishing only on the original lambda/row domain
and a positive base point of that same retained polynomial/rectangle. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

def nativeInput (r : Row) (lam : ℝ) : ℝ :=
  match r with | .D | .H => q lam | .E1 | .E2 => lam

def nativeLo (r : Row) : ℝ := nativeInput r (rowData r).lo
def nativeHi (r : Row) : ℝ := nativeInput r (rowData r).hi

 theorem native_endpoints (r : Row) : nativeLo r < nativeHi r := by
  cases r
  · exact (row_q_endpoints .D).2.1
  · exact (row_lambda_endpoints .E1).2
  · exact (row_lambda_endpoints .E2).2
  · exact (row_q_endpoints .H).2.1

 theorem nativeInput_coverage {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    nativeLo r ≤ nativeInput r lam ∧ nativeInput r lam ≤ nativeHi r := by
  cases r
  · exact activity_q_coverage hlam
  · exact hlam
  · exact hlam
  · exact activity_q_coverage hlam

 theorem q_order_iff_nonnegative {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    q a ≤ q b ↔ a ≤ b := by
  have ha1 : 0 < 1+a := by linarith
  have hb1 : 0 < 1+b := by linarith
  unfold q
  rw [div_le_div_iff₀ ha1 hb1]
  constructor <;> intro h <;> nlinarith

 theorem inverse_q_inRow {r : Row} {x : ℝ}
    (hx0 : q (rowData r).lo ≤ x) (hx1 : x ≤ q (rowData r).hi) :
    InRow r (x/(1-x)) ∧ q (x/(1-x))=x := by
  have hxpos : 0 < x := (row_q_endpoints r).1.trans_le hx0
  have hxlt : x < 1 := hx1.trans_lt (row_q_endpoints r).2.2
  have hinv := inverse_q_positive hxpos hxlt
  have he := q_of_inverse_q hxlt
  refine ⟨⟨?_,?_⟩,he⟩
  · apply (q_order_iff_nonnegative (row_lambda_endpoints r).1.le hinv.le).mp
    simpa only [he] using hx0
  · have hhipos : 0 ≤ (rowData r).hi :=
      (row_lambda_endpoints r).1.le.trans (row_lambda_endpoints r).2.le
    apply (q_order_iff_nonnegative hinv.le hhipos).mp
    simpa only [he] using hx1

 theorem nativeInput_surjective_on_row (r : Row) {x : ℝ}
    (hx0 : nativeLo r ≤ x) (hx1 : x ≤ nativeHi r) :
    ∃ lam : ℝ, InRow r lam ∧ nativeInput r lam=x := by
  cases r
  · obtain ⟨hi,he⟩ := inverse_q_inRow (r:=.D) hx0 hx1
    exact ⟨x/(1-x),hi,he⟩
  · exact ⟨x,⟨hx0,hx1⟩,rfl⟩
  · exact ⟨x,⟨hx0,hx1⟩,rfl⟩
  · obtain ⟨hi,he⟩ := inverse_q_inRow (r:=.H) hx0 hx1
    exact ⟨x/(1-x),hi,he⟩

 theorem nativeLo_original_row (r : Row) :
    InRow r (rowData r).lo ∧ nativeInput r (rowData r).lo=nativeLo r := by
  exact ⟨⟨le_rfl,(row_lambda_endpoints r).2.le⟩,rfl⟩

 theorem denominator_positive_on_row
    (r : Row) (D : F4U.Light.Linking.Polynomial2.Rows)
    (hNZ : ∀ lam t, InRow r lam → 0 ≤ t → t ≤ 1 →
      F4U.Light.Linking.Polynomial2.eval D (nativeInput r lam) t ≠ 0)
    (hbase : 0 < F4U.Light.Linking.Polynomial2.eval D (nativeLo r) 0)
    {lam t : ℝ} (hlam : InRow r lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < F4U.Light.Linking.Polynomial2.eval D (nativeInput r lam) t := by
  have hnzrect : ∀ x t, nativeLo r ≤ x → x ≤ nativeHi r → 0 ≤ t → t ≤ 1 →
      F4U.Light.Linking.Polynomial2.eval D x t ≠ 0 := by
    intro x t hx0 hx1 ht0 ht1
    obtain ⟨lam,hlam,he⟩ := nativeInput_surjective_on_row r hx0 hx1
    rw [←he]
    exact hNZ lam t hlam ht0 ht1
  exact denominator_positive_of_left_base D (native_endpoints r).le hnzrect hbase
    (nativeInput_coverage hlam).1 (nativeInput_coverage hlam).2 ht0 ht1

#print axioms nativeInput
#print axioms nativeLo
#print axioms nativeHi
#print axioms native_endpoints
#print axioms nativeInput_coverage
#print axioms q_order_iff_nonnegative
#print axioms inverse_q_inRow
#print axioms nativeInput_surjective_on_row
#print axioms nativeLo_original_row
#print axioms denominator_positive_on_row

end
end F4Unified.LightConstruction
