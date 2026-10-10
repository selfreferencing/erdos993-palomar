module

public import Erdos993Lean.Analytic.V213.FiberInputRateInterval
public import Erdos993Lean.Analytic.V213.FiberOuterRegionData

/-!
Actual target lines for the accepted F06 classes. Central and wing
classes have zero target. Outer classes use the already accepted exact
F05 b/beta fields. On every analytic input the target is dominated by
its printed profile target, with that profile target nonpositive.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberInputOuterClass : FiberInputClass → Option FiberOuterClassIdentity
  | .c1 => some .c1
  | .c2 => some .c2
  | .c3 => some .c3
  | .c4 => some .c4
  | .c5 => some .c5
  | .c6 => some .c6
  | .c7 => some .c7
  | .c8 => some .c8
  | _ => none

def fiberInputClassB (kind : FiberInputClass) : lowMeanFraction :=
  match fiberInputOuterClass kind with
  | none => (0,1)
  | some id => (fiberOuterClassById id).b

def fiberInputClassBeta (kind : FiberInputClass) : lowMeanFraction :=
  match fiberInputOuterClass kind with
  | none => (0,1)
  | some id => (fiberOuterClassById id).beta_prime

noncomputable def fiberInputTarget (id : FiberInputIdentity) (t : ℝ) : ℝ :=
  lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind) +
    lowMeanFractionReal (fiberInputClassBeta (fiberInputRouteById id).kind) * (t-1)

theorem fiber_analytic_input_target (id : FiberAnalyticInputIdentity) {t : ℝ}
    (hcap : t ≤ fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight id)).profile) :
    let p := fiberRationalProfileById (fiberWeightById (fiberAnalyticWeight id)).profile
    fiberInputTarget (fiberAnalyticInput id) t ≤ lowMeanFractionReal p.b + lowMeanFractionReal p.beta*(t-1) ∧
      lowMeanFractionReal p.b + lowMeanFractionReal p.beta*(t-1) ≤ 0 := by
  cases id <;>
    norm_num [fiberInputTarget,fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,
      fiberInputRouteById,fiberAnalyticInput,fiberAnalyticWeight,fiberWeightById,
      fiberRationalProfileById,fiberOuterClassById,lowMeanFractionReal,fiberProfileTimeCap] at hcap ⊢ <;>
    linarith only [hcap]

theorem fiber_analytic_input_cut (id : FiberAnalyticInputIdentity) :
    lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).c = 1/3 := by
  cases id <;> norm_num [fiberInputRouteById,fiberAnalyticInput,lowMeanFractionReal]

theorem fiber_input_analytic_guard_time (id : FiberAnalyticInputIdentity) {t : ℝ}
    (ht : 1/3 ≤ t)
    (hts : t ≤ lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ts)
    (hcap : t ≤ fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight id)).profile) :
    lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_lo ≤ t ∧
      t ≤ lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_hi := by
  have h := fiber_input_rate_facts id
  have hl := (lowMean_fraction_le_iff h.1.2.2.2.2.2.2.2.1 h.1.2.2.2.2.2.2.2.2.2.2.1).mp
    h.2.1.2.2.2.2.2.2.2.2.2.2.1
  rw [fiber_analytic_input_cut] at hl
  have hh := (lowMean_fraction_le_iff h.1.2.2.2.2.2.2.2.2.2.2.2.1 h.1.2.2.2.2.2.2.2.2.1).mp
    h.2.1.2.2.2.2.2.2.2.2.2.2.2
  have htend : t ≤ lowMeanFractionReal (fiberAnalyticEndFraction id) := by
    rw [fiber_analytic_end_real]; exact le_min hts hcap
  exact ⟨hl.trans ht,htend.trans hh⟩

end Erdos993Lean.Analytic.V213
