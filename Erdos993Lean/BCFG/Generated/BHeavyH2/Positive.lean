module

public import Erdos993Lean.BCFG.Generated.BHeavyH2.Checks
public import Erdos993Lean.BCFG.DirectRowCertificate

/-! Generated transcription of B.heavy.h2
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.BHeavyH2

/-- Closed-domain positivity of this specified data polynomial.
The positive clearing identity connecting it to an analytic function is separate. -/
theorem positive {lambda y : Real}
    (hlambda : (l : Real) ≤ lambda ∧ lambda ≤ (h : Real))
    (hy : (a : Real) ≤ y ∧ y ≤ (a : Real)+(b : Real)) :
    0 < Bi.sourceEval N p lambda y := by
  exact sourceEval_pos_of_direct_row_certificate N M p A lower intervals l h a b
    row_nonnegative row_nondegenerate chart_width_positive normalization_rows_checked
    lower_checked intervals_checked cover_checked hlambda hy

end Erdos993Lean.BCFG.CertData.BHeavyH2
