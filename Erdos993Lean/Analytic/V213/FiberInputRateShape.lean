module

public import Erdos993Lean.Analytic.V213.FiberInputRateData

/-!
Canonical F11 logarithms and affine rate guards. Every tree is
bound to the actual accepted N44 upper endpoint and its printed dyadic
exponent. The guard formula retains actual input ell0 and weight leaves.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberFractionSub (x y : lowMeanFraction) : lowMeanFraction :=
  lowMeanFractionAdd x (lowMeanFractionNeg y)

theorem fiber_fraction_sub_valid {x y : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) :
    lowMeanFractionValid (fiberFractionSub x y) := Nat.mul_pos hx hy

theorem fiber_fraction_sub_real {x y : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hy : lowMeanFractionValid y) :
    lowMeanFractionReal (fiberFractionSub x y) = lowMeanFractionReal x - lowMeanFractionReal y := by
  have hn : lowMeanFractionValid (lowMeanFractionNeg y) := hy
  rw [fiberFractionSub,lowMean_fraction_add hx hn,lowMean_fraction_neg]
  rfl

def fiberAnalyticEndFraction (id : FiberAnalyticInputIdentity) : lowMeanFraction :=
  let r := fiberInputRouteById (fiberAnalyticInput id)
  let w := fiberWeightById (fiberAnalyticWeight id)
  if lowMeanFractionLE r.ts (fiberProfileTimeCapFraction w.profile) then r.ts
  else fiberProfileTimeCapFraction w.profile

def fiberInputLogShape (id : FiberAnalyticInputIdentity) : LowMeanIntegerShape :=
  FiberRootLineFormula.logarithm (fiberInputLogById id).n
    (.add (.atom (1,1)) (.atom (fiberInputHiFraction (fiberAnalyticInput id))))

noncomputable def fiberInputLogValue (id : FiberAnalyticInputIdentity) : ℝ :=
  fiberDyadicLog (fiberInputLogById id).n
    (1 + lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id)))

def fiberInputGuardFraction (id : FiberAnalyticInputIdentity) (t : lowMeanFraction) : lowMeanFraction :=
  let r := fiberInputRouteById (fiberAnalyticInput id)
  let w := fiberWeightById (fiberAnalyticWeight id)
  lowMeanFractionAdd (fiberFractionSub r.ell0 w.ell_w)
    (lowMeanFractionMul (fiberFractionSub w.L_w (fiberInputLogById id).upper) t)

def fiberInputRateFraction (id : FiberAnalyticInputIdentity) (t : lowMeanFraction) : lowMeanFraction :=
  fiberFractionSub (fiberInputRouteById (fiberAnalyticInput id)).ell0
    (lowMeanFractionMul (fiberInputLogById id).upper t)

theorem fiber_input_log_shape_real (id : FiberAnalyticInputIdentity) :
    lowMeanIntegerShapeReal (fiberInputLogShape id) = fiberInputLogValue id := by
  simp only [fiberInputLogShape,fiber_root_line_log_formula_real,
    lowMeanIntegerShapeReal,lowMeanFractionReal,Int.cast_one,Nat.cast_one,div_one,fiberInputLogValue]

theorem fiber_input_guard_fraction_real (id : FiberAnalyticInputIdentity) {t : lowMeanFraction}
    (he : lowMeanFractionValid (fiberInputRouteById (fiberAnalyticInput id)).ell0)
    (hl : lowMeanFractionValid (fiberWeightById (fiberAnalyticWeight id)).ell_w)
    (hL : lowMeanFractionValid (fiberWeightById (fiberAnalyticWeight id)).L_w)
    (hU : lowMeanFractionValid (fiberInputLogById id).upper)
    (ht : lowMeanFractionValid t) :
    lowMeanFractionReal (fiberInputGuardFraction id t) =
      lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 -
        lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).ell_w +
      (lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).L_w -
        lowMeanFractionReal (fiberInputLogById id).upper) * lowMeanFractionReal t := by
  have hm : lowMeanFractionValid (lowMeanFractionMul
      (fiberFractionSub (fiberWeightById (fiberAnalyticWeight id)).L_w (fiberInputLogById id).upper) t) :=
    Nat.mul_pos (fiber_fraction_sub_valid hL hU) ht
  dsimp [fiberInputGuardFraction]
  rw [lowMean_fraction_add (fiber_fraction_sub_valid he hl) hm,
    lowMean_fraction_mul,fiber_fraction_sub_real he hl,fiber_fraction_sub_real hL hU]

theorem fiber_input_rate_fraction_real (id : FiberAnalyticInputIdentity) {t : lowMeanFraction}
    (he : lowMeanFractionValid (fiberInputRouteById (fiberAnalyticInput id)).ell0)
    (hU : lowMeanFractionValid (fiberInputLogById id).upper) (ht : lowMeanFractionValid t) :
    lowMeanFractionReal (fiberInputRateFraction id t) =
      lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 -
        lowMeanFractionReal (fiberInputLogById id).upper * lowMeanFractionReal t := by
  have hm : lowMeanFractionValid (lowMeanFractionMul (fiberInputLogById id).upper t) := Nat.mul_pos hU ht
  unfold fiberInputRateFraction
  rw [fiber_fraction_sub_real he hm,lowMean_fraction_mul]

end Erdos993Lean.Analytic.V213
