module

public import Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.Identity
public import Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.Lower

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

theorem positive {q u : ℝ}
    (hq : (lo : ℝ)≤q ∧ q≤(hi : ℝ))
    (hu : (v : ℝ)≤u ∧ u≤(w : ℝ)) : 0<Expr.eval expr q u := by
  exact checked_rectangle_positive expr n m lo hi v w lower
    (by norm_num [lo,hi]) (by norm_num [v,w])
    reconstruction_checked lower_checked hq hu

end Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior

#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.positive
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.positive
