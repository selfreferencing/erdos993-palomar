module

public import Erdos993Lean.Analytic.V213.FiberProfileControlCheck
public import Erdos993Lean.Analytic.V213.FiberProfileEndpoint

/-!
Actual endpoint quadratic bounds from all accepted F10 E/V tests.
The canonical checker binds each coefficient to the actual profile;
both selected test minima are positive. These bounds hold throughout
the complete printed skew interval, rather than only at sampled points.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_profile_control_test_positive (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) (hr : role = .firstTest ∨ role = .secondTest) :
    0 < fiberProfileControlValue id role := by
  have h := fiber_profile_control_test_bound id role hr
  exact h.2.trans_le h.1

theorem fiber_profile_control_endpoint_bound (id : FiberProfileControlIdentity) {u : ℝ}
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberProfileControlEnvelope id u < lowMeanFractionReal (fiberProfileControlById id).z := by
  have hc1 := fiber_profile_control_c1_positive id
  have hfirst := fiber_profile_control_test_positive id .firstTest (Or.inl rfl)
  have hsecond := fiber_profile_control_test_positive id .secondTest (Or.inr rfl)
  rw [fiber_profile_control_polynomial]
  by_cases hE : (fiberProfileControlById id).increasing = true
  · simp only [fiberProfileControlValue,hE,if_true] at hfirst hsecond
    apply fiber_profile_endpoint_E hc1.le (hu.trans huR) hu huR hfirst.le
    linarith only [hsecond]
  · have hV : (fiberProfileControlById id).increasing = false := Bool.eq_false_iff.mpr hE
    simp [fiberProfileControlValue,hV] at hfirst hsecond
    exact fiber_profile_endpoint_V (by linarith only [hfirst]) (by nlinarith only [hsecond])

end Erdos993Lean.Analytic.V213
