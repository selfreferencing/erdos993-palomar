module

public import Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.Positive
public import Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.Positive
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialSigns

/-! Exact closed-domain routing of the ten printed polynomial certificates.
This file becomes usable only after all ten generated identities and lower
checks have been accepted. It does not introduce any new numerical premise. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

open Erdos993Lean.Analytic.V213.P04Bernstein

theorem printed_minus_positive {q : ℝ} (hq : QDomain q) : 0<polyMinus q := by
  have h := R01Minus.positive (q:=q) (u:=0)
    (by simpa [R01Minus.lo,R01Minus.hi,QDomain] using hq)
    (by norm_num [R01Minus.v,R01Minus.w])
  simpa [R01Minus.expr,minusExpr_sound,printed_minus_identity hq] using h

theorem printed_plus_positive {q : ℝ} (hq : QDomain q) : 0<polyPlus q := by
  have h := R02Plus.positive (q:=q) (u:=0)
    (by simpa [R02Plus.lo,R02Plus.hi,QDomain] using hq)
    (by norm_num [R02Plus.v,R02Plus.w])
  simpa [R02Plus.expr,plusExpr_sound,printed_plus_identity hq] using h

theorem printed_leaf_low {q : ℝ} (hq : LowClosedDomain q) : 0<polyE q (-1/125) := by
  have hQ : QDomain q := ⟨hq.1,by linarith [hq.2]⟩
  have h := R03Leaf.positive (q:=q) (u:=0)
    (by simpa [R03Leaf.lo,R03Leaf.hi,LowClosedDomain] using hq)
    (by norm_num [R03Leaf.v,R03Leaf.w])
  simpa [R03Leaf.expr,leafExpr_sound,leaf_polynomial_identity hQ] using h

theorem printed_leaf_high {q : ℝ} (hq : HighDomain q) : 0<polyE q (3/1250) := by
  have hQ : QDomain q := ⟨by linarith [hq.1],hq.2⟩
  have h := R04Leaf.positive (q:=q) (u:=0)
    (by simpa [R04Leaf.lo,R04Leaf.hi,HighDomain] using hq)
    (by norm_num [R04Leaf.v,R04Leaf.w])
  simpa [R04Leaf.expr,leafExpr_sound,leaf_polynomial_identity hQ] using h

theorem printed_interior_low {q u : ℝ} (hq : LowClosedDomain q)
    (hu0 : 0≤u) (hu1 : u≤1) : 0<polyI q u (-1/125) := by
  by_cases hh : u≤1/2
  · have h := R05Interior.positive (q:=q) (u:=u)
      (by simpa [R05Interior.lo,R05Interior.hi,LowClosedDomain] using hq)
      (by simpa [R05Interior.v,R05Interior.w] using And.intro hu0 hh)
    simpa [R05Interior.expr,interiorExpr_sound,interior_polynomial_identity] using h
  · have hh' : (1/2:ℝ)≤u := le_of_lt (lt_of_not_ge hh)
    have h := R06Interior.positive (q:=q) (u:=u)
      (by simpa [R06Interior.lo,R06Interior.hi,LowClosedDomain] using hq)
      (by simpa [R06Interior.v,R06Interior.w] using And.intro hh' hu1)
    simpa [R06Interior.expr,interiorExpr_sound,interior_polynomial_identity] using h

theorem printed_interior_high {q u : ℝ} (hq : HighDomain q)
    (hu0 : 0≤u) (hu1 : u≤1) : 0<polyI q u (3/1250) := by
  by_cases hh : u≤1/2
  · have h := R07Interior.positive (q:=q) (u:=u)
      (by simpa [R07Interior.lo,R07Interior.hi,HighDomain] using hq)
      (by simpa [R07Interior.v,R07Interior.w] using And.intro hu0 hh)
    simpa [R07Interior.expr,interiorExpr_sound,interior_polynomial_identity] using h
  · have hh' : (1/2:ℝ)≤u := le_of_lt (lt_of_not_ge hh)
    have h := R08Interior.positive (q:=q) (u:=u)
      (by simpa [R08Interior.lo,R08Interior.hi,HighDomain] using hq)
      (by simpa [R08Interior.v,R08Interior.w] using And.intro hh' hu1)
    simpa [R08Interior.expr,interiorExpr_sound,interior_polynomial_identity] using h

theorem printed_leafSlope_low {q u : ℝ} (hq : LowClosedDomain q)
    (hu0 : 0≤u) (hu1 : u≤1) : 0<polyJ q u (-1/125) := by
  have h := R09LeafSlope.positive (q:=q) (u:=u)
    (by simpa [R09LeafSlope.lo,R09LeafSlope.hi,LowClosedDomain] using hq)
    (by simpa [R09LeafSlope.v,R09LeafSlope.w] using And.intro hu0 hu1)
  simpa [R09LeafSlope.expr,leafSlopeExpr_sound,leafSlope_polynomial_identity] using h

theorem printed_leafSlope_high {q u : ℝ} (hq : HighDomain q)
    (hu0 : 0≤u) (hu1 : u≤1) : 0<polyJ q u (3/1250) := by
  have h := R10LeafSlope.positive (q:=q) (u:=u)
    (by simpa [R10LeafSlope.lo,R10LeafSlope.hi,HighDomain] using hq)
    (by simpa [R10LeafSlope.v,R10LeafSlope.w] using And.intro hu0 hu1)
  simpa [R10LeafSlope.expr,leafSlopeExpr_sound,leafSlope_polynomial_identity] using h

/-- Actual delta uses the high branch at q=3/7. The low certificate also
holds at that endpoint, but it is not substituted for the actual high rate. -/
theorem current_polynomial_signs : CurrentPolynomialSigns := by
  refine ⟨fun q hq => printed_minus_positive hq,
    fun q hq => printed_plus_positive hq, ?_, ?_, ?_⟩
  · intro q u hq hu0 hu1
    by_cases hlow : q<3/7
    · simpa [delta,hlow] using printed_interior_low ⟨hq.1,hlow.le⟩ hu0 hu1
    · simpa [delta,hlow] using printed_interior_high ⟨le_of_not_gt hlow,hq.2⟩ hu0 hu1
  · intro q u hq hu0 hu1
    by_cases hlow : q<3/7
    · simpa [delta,hlow] using printed_leafSlope_low ⟨hq.1,hlow.le⟩ hu0 hu1
    · simpa [delta,hlow] using printed_leafSlope_high ⟨le_of_not_gt hlow,hq.2⟩ hu0 hu1
  · intro q hq
    by_cases hlow : q<3/7
    · simpa [delta,hlow] using (printed_leaf_low ⟨hq.1,hlow.le⟩).le
    · simpa [delta,hlow] using (printed_leaf_high ⟨le_of_not_gt hlow,hq.2⟩).le

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_minus_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_minus_positive
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_plus_positive
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_plus_positive
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leaf_low
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leaf_low
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leaf_high
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leaf_high
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_interior_low
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_interior_low
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_interior_high
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_interior_high
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leafSlope_low
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leafSlope_low
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leafSlope_high
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.printed_leafSlope_high
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.current_polynomial_signs
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.current_polynomial_signs
