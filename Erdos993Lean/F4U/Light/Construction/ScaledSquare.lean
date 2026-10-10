module

public import Erdos993Lean.F4U.Light.Construction.PaymentAlgebra

/-! Exact completion of the full scaled response payment from its literal W
numerator. The parent, source, child h, support L and response y are retained. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 theorem response_square_algebra (p N B c d delta z h y L : ℝ)
    (hp : p ≠ 0) (hL : L ≠ 0) (hG : delta+d*L ≠ 0) :
    N+z*B*h+z*c/p*y+z*d/p*y^2+z*delta/(p*L)*(h-y)^2 =
      (4*(delta+d*L)*(p*N+z*p*B*h)+4*delta*z*(c*h+d*h^2)-z*L*c^2) /
        (4*p*(delta+d*L)) +
      z*(delta+d*L)/(p*L)*(y-(2*delta*h-L*c)/(2*(delta+d*L)))^2 := by
  field_simp [hp,hL,hG]
  <;> ring

 theorem scaledPayment_complete_square (r : Row) (phase : SourcePhase)
    (lam H rho z h y L : ℝ) (hp : pH lam H ≠ 0) (hL : L ≠ 0)
    (hG : delta r lam+responseD r lam H rho z*L ≠ 0) :
    scaledPayment r phase lam H rho z h y L =
      W r phase lam H rho z h L /
        (4*pH lam H*(delta r lam+responseD r lam H rho z*L)) +
      z*(delta r lam+responseD r lam H rho z*L)/(pH lam H*L) *
        (y-(2*delta r lam*h-L*responseC r lam H rho)/
          (2*(delta r lam+responseD r lam H rho z*L)))^2 := by
  calc
    scaledPayment r phase lam H rho z h y L =
      parentNHat r phase lam H rho+z*(beta r lam*rho)*h+
        z*responseC r lam H rho/pH lam H*y+
        z*responseD r lam H rho z/pH lam H*y^2+
        z*delta r lam/(pH lam H*L)*(h-y)^2 := by
          unfold scaledPayment responseC responseD
          field_simp [hp]
          <;> ring
    _ = _ := by
      simpa only [W, mul_assoc] using response_square_algebra (pH lam H)
        (parentNHat r phase lam H rho) (beta r lam*rho) (responseC r lam H rho)
        (responseD r lam H rho z) (delta r lam) z h y L hp hL hG

 theorem scaledPayment_pos_of_W (r : Row) (phase : SourcePhase)
    (lam H rho z h y L : ℝ) (hp : 0 < pH lam H) (hL : 0 < L)
    (hG : 0 < delta r lam+responseD r lam H rho z*L) (hz : 0 ≤ z)
    (hW : 0 < W r phase lam H rho z h L) :
    0 < scaledPayment r phase lam H rho z h y L := by
  rw [scaledPayment_complete_square r phase lam H rho z h y L hp.ne' hL.ne' hG.ne']
  have hc : 0 < W r phase lam H rho z h L /
      (4*pH lam H*(delta r lam+responseD r lam H rho z*L)) := by positivity
  have hcoef : 0 ≤ z*(delta r lam+responseD r lam H rho z*L)/(pH lam H*L) := by positivity
  exact add_pos_of_pos_of_nonneg hc (mul_nonneg hcoef (sq_nonneg _))

#print axioms response_square_algebra
#print axioms scaledPayment_complete_square
#print axioms scaledPayment_pos_of_W

end
end F4Unified.LightConstruction
