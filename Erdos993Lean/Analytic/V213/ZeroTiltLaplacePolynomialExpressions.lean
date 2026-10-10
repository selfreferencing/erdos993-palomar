module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceSignPolynomials

/-!
Polynomial expressions derived algebraically from the printed rational
clearings. The expressions are over any commutative ring, so later exact Rat
polynomial arithmetic can use the same expressions. No coefficient vector is
reconstructed in Python and no finite coefficient sign is asserted here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

namespace PolynomialExpression

/-- Negative DeltaJ times Jminus(wMinus;d), after canceling denominators. -/
def minus {R : Type*} [CommRing R] (q d : R) : R :=
  -100*q*(2-q)*(1-q)*(1+2*q)^2*(1+q-q^2)+
  q*(2-q)*(1+2*q)*(1+q-q^2)*(1+3*q)*(1+2*q+q*(1+q))+
  q^2*(2-q)*(1+2*q)^2*(100*(1-q)-(1+3*q))+
  (2-q)*(1+2*q)^2*(1+q-q^2)*(1+3*q)+
  200*q*(1+2*q)*(1-q)^2*(1+q-q^2)*(1+q)+
  100*d*(2-q)*(1-q)*(1+q-q^2)*(1+q)^2

def plus {R : Type*} [CommRing R] (q d : R) : R :=
  -minus q d+(2-q)*(1+2*q)*(1+q-q^2)*(1+3*q)*(1+q)^2

/-- DeltaE times the printed leaf rational lower bound. -/
def leaf {R : Type*} [CommRing R] (q d : R) : R :=
  4*q*(2-q)*(1-q)*(1+q)*(1+q-q^2)*(100*(1-q)-(1+3*q))*(3*(2+q)^2+q^2)-
  3*(1+3*q)*q^2*(2-q)^2*(1+q)*(2+q)^3-
  1200*q*(1+2*q)*(1-q)^3*(2+q)^3-
  600*d*(2-q)*(1-q)^2*(1+q)*(2+q)^3

def interior {R : Type*} [CommRing R] (q u d : R) : R :=
  q*(1+q)^2*(2-q)*((101+3*q)*(1-q)^2+q*(1+3*q)*(2-q)*u^2)*(1+q*u^2)^2-
  (100*q*(1-q)^2*(2+q)*(1+2*q)+50*d*(1-q)*(1+q)*(2-q)*(2+q))*
    (1-q+q*u^2)*(1+q*u+q*u^2-q*u^3)

def leafSlope {R : Type*} [CommRing R] (q u d : R) : R :=
  q*(1+q)*(100-101*q-3*q^2+q*(1+3*q)*u^2)*(1+q*u^2)^2-
  (100*q*(1+2*q)*(1-q)+50*d*(1+q)*(2-q))*(1-q+q*u^2)*(1+q*u+q*u^2-q*u^3)

end PolynomialExpression

theorem minus_polynomial_identity {q : ℝ} (hq : QDomain q) (d : ℝ) :
    PolynomialExpression.minus q d = -deltaJ q*diagonalJMinus q (wMinus q) d := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have hc : 0<1+2*q := by positivity
  unfold PolynomialExpression.minus deltaJ diagonalJMinus wMinus aQ rateR
  field_simp [h0.ne',h1.ne',hp.ne',h2.ne',hf.ne',hc.ne'] <;> ring

theorem plus_polynomial_identity {q : ℝ} (hq : QDomain q) (d : ℝ) :
    PolynomialExpression.plus q d = deltaJ q*diagonalJPlus q (wMinus q) d := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have hc : 0<1+2*q := by positivity
  unfold PolynomialExpression.plus
  rw [minus_polynomial_identity hq]
  unfold diagonalJPlus deltaJ wMinus aQ
  field_simp [h0.ne',h1.ne',hc.ne'] <;> ring

theorem leaf_polynomial_identity {q : ℝ} (hq : QDomain q) (d : ℝ) :
    PolynomialExpression.leaf q d = polyE q d := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  unfold PolynomialExpression.leaf polyE deltaE leafRationalLower aQ wPlus rateR
  field_simp [h1.ne',hp.ne',h2.ne',h2p.ne',hf.ne'] <;> ring

theorem interior_polynomial_identity (q u d : ℝ) :
    PolynomialExpression.interior q u d=polyI q u d := by
  rfl

theorem leafSlope_polynomial_identity (q u d : ℝ) :
    PolynomialExpression.leafSlope q u d=polyJ q u d := by
  rfl

theorem printed_minus_identity {q : ℝ} (hq : QDomain q) :
    PolynomialExpression.minus q (-1/125)=polyMinus q := by
  exact minus_polynomial_identity hq _

theorem printed_plus_identity {q : ℝ} (hq : QDomain q) :
    PolynomialExpression.plus q (3/1250)=polyPlus q := by
  exact plus_polynomial_identity hq _

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

--
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.minus_polynomial_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.minus_polynomial_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.plus_polynomial_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.plus_polynomial_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_polynomial_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leaf_polynomial_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_polynomial_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interior_polynomial_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leafSlope_polynomial_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leafSlope_polynomial_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.printed_minus_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.printed_minus_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.printed_plus_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.printed_plus_identity
