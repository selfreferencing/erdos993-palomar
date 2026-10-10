module

public import Erdos993Lean.Analytic.V213.FiberInputHighDomain
public import Erdos993Lean.Analytic.V213.FiberCentralComparison

/-!
Actual all55 high-width comparisons. Each wing is joined on
its closed start interval to the central theorem at t=3/5; outer classes
use the literal accepted target line for all t>=their printed start.
Every natural width and integer rank is retained, with original q.
Sources: Theorems6.14/6.16/6.18.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_input_wing_central_join (id : FiberWingIdentity) {q mu : ℝ}
    (hq : q ∈ Set.Icc (1/4 : ℝ) (3/4)) (hmu19 : 19 ≤ mu)
    (hmu : lowMeanFractionReal (fiberWingById id).mu_W ≤ mu)
    (hra : lowMeanFractionReal (fiberWingById id).skew_lower ≤ |fiberSkew q|)
    (hrb : |fiberSkew q| ≤ lowMeanFractionReal (fiberWingById id).skew_upper)
    (M : ℕ) (j : ℤ) (ht : lowMeanFractionReal (fiberWingById id).tau ≤ (M : ℝ)/mu) :
    fiberPsi ((M : ℝ)/mu) ≤ fiberF q mu M j := by
  by_cases hthi : (M : ℝ)/mu ≤ 3/5
  · exact fiber_wing_comparison id hmu hra hrb M j ht hthi
  · exact fiber_central_comparison hq.1 hq.2 hmu19 M (le_of_lt (lt_of_not_ge hthi)) j

theorem fiber_input_class_high_comparison (kind : FiberInputClass) {q mu : ℝ}
    (hq : q ∈ Set.Icc (1/4 : ℝ) (3/4)) (hmu19 : 19 ≤ mu)
    (hmu : lowMeanFractionReal (fiberInputHighMean (fiberInputHighOfClass kind)) ≤ mu)
    (hra : lowMeanFractionReal (fiberInputHighLo (fiberInputHighOfClass kind)) ≤ |fiberSkew q|)
    (hrb : |fiberSkew q| ≤ lowMeanFractionReal (fiberInputHighHi (fiberInputHighOfClass kind)))
    (M : ℕ) (j : ℤ) (ht : lowMeanFractionReal (fiberInputHighTau (fiberInputHighOfClass kind)) ≤ (M : ℝ)/mu) :
    fiberPsi ((M : ℝ)/mu) + lowMeanFractionReal (fiberInputClassB kind) +
      lowMeanFractionReal (fiberInputClassBeta kind)*((M : ℝ)/mu-1) ≤ fiberF q mu M j := by
  cases kind with
  | c1 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c1 hmu hra hrb ht j)
  | c2 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c2 hmu hra hrb ht j)
  | central =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    have ht' : (3/5 : ℝ) ≤ (M : ℝ)/mu := by simpa [lowMeanFractionReal] using ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_central_comparison hq.1 hq.2 hmu19 M ht' j)
  | w1 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_input_wing_central_join .w1 hq hmu19 hmu hra hrb M j ht)
  | w2 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_input_wing_central_join .w2 hq hmu19 hmu hra hrb M j ht)
  | w3 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_input_wing_central_join .w3 hq hmu19 hmu hra hrb M j ht)
  | c3 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c3 hmu hra hrb ht j)
  | c4 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c4 hmu hra hrb ht j)
  | c5 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c5 hmu hra hrb ht j)
  | c6 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c6 hmu hra hrb ht j)
  | c7 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c7 hmu hra hrb ht j)
  | c8 =>
    simp only [fiberInputHighOfClass,fiberInputHighMean,fiberInputHighLo,fiberInputHighHi,fiberInputHighTau] at hmu hra hrb ht
    simpa [fiberInputClassB,fiberInputClassBeta,fiberInputOuterClass,lowMeanFractionReal] using (fiber_outer_class_comparison .c8 hmu hra hrb ht j)

theorem fiber_input_high_comparison (id : FiberInputIdentity) {lambda mu : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu)
    (M : ℕ) (j : ℤ) (ht : lowMeanFractionReal (fiberInputRouteById id).ts ≤ (M : ℝ)/mu) :
    fiberPsi ((M : ℝ)/mu) + fiberInputTarget id ((M : ℝ)/mu) ≤
      fiberF (FreeCountVariance.q lambda) mu M j := by
  have hs := fiber_input_high_skew id hl hh
  have htime : lowMeanFractionReal (fiberInputHighTau (fiberInputHighOfClass (fiberInputRouteById id).kind)) ≤ (M : ℝ)/mu := by
    rw [fiber_input_high_tau]; exact ht
  have h := fiber_input_class_high_comparison (fiberInputRouteById id).kind
    (fiber_input_probability_domain id hl hh) (fiber_input_mean_nineteen id hmu)
    (fiber_input_high_mean id hmu) hs.1 hs.2 M j htime
  simpa only [fiberInputTarget,add_assoc] using h

end Erdos993Lean.Analytic.V213
