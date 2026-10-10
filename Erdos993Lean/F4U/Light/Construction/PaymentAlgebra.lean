module

public import Erdos993Lean.F4U.Light.Construction.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Exact, object-preserving identities used by the light structural proof.
The parent replacement retains the original source value and all responses.
The auxiliary-logarithm identity retains the full quadratic payment. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

/-- Original payment with only its parent P field made explicit. -/
def paymentWithParentP (r : Row) (lam Y rho u y P : ℝ) : ℝ :=
  p lam Y * ((rowData r).price / (1 + lam) * rho * source lam Y rho +
    alpha r lam * (1-rho) - P) / Y +
  p lam Y * beta r lam * rho * childH u +
  p lam Y * (2*P-alpha r lam-beta r lam) * y +
  (gamma r lam-delta r lam-p lam Y*Y*P)*y^2 + reserve r lam u y

 theorem paymentWithParentP_original (r : Row) (lam Y rho u y : ℝ) :
    paymentWithParentP r lam Y rho u y (parentP r lam Y rho) =
      payment r lam Y rho u y := by
  rfl

 theorem correlated_parent_replacement (r : Row) (lam Y rho u y P Q : ℝ)
    (hY : Y ≠ 0) :
    paymentWithParentP r lam Y rho u y Q - paymentWithParentP r lam Y rho u y P =
      -(p lam Y / Y) * (Q-P) * (1-Y*y)^2 := by
  unfold paymentWithParentP
  field_simp
  <;> ring

 theorem correlated_parent_replacement_le (r : Row) (lam Y rho u y P Q : ℝ)
    (hY : 0 < Y) (hp : 0 ≤ p lam Y) (hPQ : P ≤ Q) :
    paymentWithParentP r lam Y rho u y Q ≤ paymentWithParentP r lam Y rho u y P := by
  have hid := correlated_parent_replacement r lam Y rho u y P Q hY.ne'
  have hscale : 0 ≤ (p lam Y / Y) * (Q-P) * (1-Y*y)^2 := by positivity
  linarith

 theorem scaledPayment_log_chord_identity (r : Row) (phase : SourcePhase)
    (lam H rho z0 z1 h y L t : ℝ) :
    scaledPayment r phase lam H rho ((1-t)*z0+t*z1) h y L -
      ((1-t)*scaledPayment r phase lam H rho z0 h y L +
        t*scaledPayment r phase lam H rho z1 h y L) =
    parentPPlus r lam H rho * y^2 * t * (1-t) * (z1-z0)^2 := by
  unfold scaledPayment
  ring

 theorem scaledPayment_log_chord_le (r : Row) (phase : SourcePhase)
    (lam H rho z0 z1 h y L t : ℝ)
    (hP : 0 ≤ parentPPlus r lam H rho) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*scaledPayment r phase lam H rho z0 h y L +
        t*scaledPayment r phase lam H rho z1 h y L ≤
      scaledPayment r phase lam H rho ((1-t)*z0+t*z1) h y L := by
  have hid := scaledPayment_log_chord_identity r phase lam H rho z0 z1 h y L t
  have hnonneg : 0 ≤ parentPPlus r lam H rho * y^2 * t * (1-t) * (z1-z0)^2 := by
    positivity
  linarith

 theorem W_child_bernstein_identity (r : Row) (phase : SourcePhase)
    (lam H rho z t : ℝ) :
    W r phase lam H rho z (hMinus r H + t*(hCross r lam-hMinus r H))
      (supportLine r .first lam (hMinus r H + t*(hCross r lam-hMinus r H))) =
    (1-t)^2*childV0 r .B phase lam H rho z +
      2*t*(1-t)*childM0 r phase lam H rho z + t^2*childV1 r phase lam H rho z := by
  simp only [childV0, childM0, childV1, supportLine, W]
  ring

#print axioms paymentWithParentP
#print axioms paymentWithParentP_original
#print axioms correlated_parent_replacement
#print axioms correlated_parent_replacement_le
#print axioms scaledPayment_log_chord_identity
#print axioms scaledPayment_log_chord_le
#print axioms W_child_bernstein_identity

end
end F4Unified.LightConstruction
