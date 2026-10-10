module

public import Erdos993Lean.BCFG.Generated.FHeavyH2.Checks
public import Erdos993Lean.BCFG.DirectRowCertificate

/-! Final supplied-polynomial statement, with explicit direct-row
normalization premise, using the lower/interval/cover checks. -/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.FHeavyH2

theorem positive {lambda y : Real}
    (hlambda : (l : Real) ≤ lambda ∧ lambda ≤ (h : Real))
    (hy : (a : Real) ≤ y ∧ y ≤ (a : Real)+(b : Real)) :
    0 < Bi.sourceEval N p lambda y := by
  exact sourceEval_pos_of_direct_row_certificate N M p A lower intervals l h a b
    row_nonnegative row_nondegenerate chart_width_positive normalization_rows_checked
    lower_checked intervals_checked cover_checked hlambda hy

end Erdos993Lean.BCFG.CertData.FHeavyH2

