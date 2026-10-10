module

public import Erdos993Lean.BCFG.PacketAggregate
public import Erdos993Lean.BCFG.WholePolynomial

/-!
Corollary for the entire 28 dense polynomials. All arithmetic/positivity is
reused from PacketAggregate; the row count is reused from each Shape module.
The frozen generated sources and PacketAggregate are not changed.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Packet

open CertData

/-- Each bounded positivity theorem includes all rows of its actual list. -/
theorem all_polynomials_rows (k : PolynomialId) :
    (data k).p.length = (data k).N+1 := by
  cases k with
  | bHeavyB0 => exact BHeavyB0.p_rows
  | bHeavyB3 => exact BHeavyB3.p_rows
  | bHeavyH1 => exact BHeavyH1.p_rows
  | bHeavyH2 => exact BHeavyH2.p_rows
  | bLightCurvature => exact BLightCurvature.p_rows
  | bLightLeft => exact BLightLeft.p_rows
  | bLightRight => exact BLightRight.p_rows
  | cHeavyB0 => exact CHeavyB0.p_rows
  | cHeavyB3 => exact CHeavyB3.p_rows
  | cHeavyH1 => exact CHeavyH1.p_rows
  | cHeavyH2 => exact CHeavyH2.p_rows
  | cLightCurvature => exact CLightCurvature.p_rows
  | cLightLeft => exact CLightLeft.p_rows
  | cLightRight => exact CLightRight.p_rows
  | fHeavyB0 => exact FHeavyB0.p_rows
  | fHeavyB3 => exact FHeavyB3.p_rows
  | fHeavyH1 => exact FHeavyH1.p_rows
  | fHeavyH2 => exact FHeavyH2.p_rows
  | fLightCurvature => exact FLightCurvature.p_rows
  | fLightLeft => exact FLightLeft.p_rows
  | fLightRight => exact FLightRight.p_rows
  | gHeavyB0 => exact GHeavyB0.p_rows
  | gHeavyB3 => exact GHeavyB3.p_rows
  | gHeavyH1 => exact GHeavyH1.p_rows
  | gHeavyH2 => exact GHeavyH2.p_rows
  | gLightCurvature => exact GLightCurvature.p_rows
  | gLightLeft => exact GLightLeft.p_rows
  | gLightRight => exact GLightRight.p_rows

/-- All 28 full dense polynomials are positive on their original closed domains.
The external JSON transcription and analytic clearing/forest transfer remain
separate provenance and mathematical obligations, respectively. -/
theorem all_whole_polynomials_positive (k : PolynomialId) {lambda y : Real}
    (hlambda : ((data k).l : Real) ≤ lambda ∧ lambda ≤ ((data k).h : Real))
    (hy : ((data k).a : Real) ≤ y ∧ y ≤ ((data k).a : Real)+((data k).b : Real)) :
    0 < Bi.evalReal (data k).p lambda y := by
  have hpos := all_polynomials_positive k hlambda hy
  rw [Bi.sourceEval_eq_evalReal (data k).N (data k).p (all_polynomials_rows k)] at hpos
  exact hpos

end Erdos993Lean.BCFG.Packet
