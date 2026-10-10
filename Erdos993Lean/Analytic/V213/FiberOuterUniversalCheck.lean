module

public import Erdos993Lean.Analytic.V213.FiberOuterRegionData

/-!
Accepted F05 universal-region constants. The grouped singleton check
binds every printed field, the canonical Phi endpoint and the coarse
negative-root budget, using only explicit Int/Nat denominators. Real
soundness preserves the exact printed endpoint surplus 3032/4215.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def fiberOuterUniversalExpected : FiberOuterUniversalRow :=
  ⟨"F05:universal_outer_region:r12:lem20(i)", (26,1),(3,5),(1,4),(1,2),(0,1),(2,5),
    (0,1),(1,1),(5,3),(2,5),(1,3),(12,13),(23,18),(79,90),(7,15),
    (251,2700),(4169,675),(5173,10800),(3032,4215),(8,25),(25,33),(41,45)⟩

def fiberOuterUniversalFields (r : FiberOuterUniversalRow) : List lowMeanFraction :=
  [r.minimum_N,r.minimum_t,r.skew_lower,r.skew_upper,r.b_lower,r.b_upper,
    r.beta_lower,r.beta_upper,r.delta_lower,r.phi_lower,r.rho_lower,r.eta,
    r.negative_omega_upper,r.v,r.f_at_start_upper,r.D_star,r.C_half,r.phi_at_start,
    r.endpoint_gap,r.exp_negative_argument,r.exp_upper,r.exp_upper_next]

def fiberOuterUniversalCheck : Bool :=
  let r := fiberOuterUniversal
  decide (r.printed = fiberOuterUniversalExpected.printed ∧
    fiberOuterUniversalFields r = fiberOuterUniversalFields fiberOuterUniversalExpected ∧
    (fiberOuterUniversalFields r).all (fun x => decide (lowMeanFractionValid x)) = true ∧
    lowMeanFractionEq r.phi_at_start (lowMeanFractionAdd r.D_star (lowMeanFractionMul (1,16) r.C_half)) ∧
    lowMeanFractionLT r.phi_lower r.phi_at_start ∧
    lowMeanFractionEq (lowMeanFractionMul (6241,25290)
      (lowMeanFractionAdd (4,1) (lowMeanFractionNeg r.v))) (lowMeanFractionPow r.v 2) ∧
    lowMeanFractionEq r.endpoint_gap (lowMeanFractionAdd
      (lowMeanFractionAdd (8,3) (lowMeanFractionNeg (lowMeanFractionMul (6,1) (6241,25290))))
      (lowMeanFractionNeg r.f_at_start_upper)) ∧
    lowMeanFractionLT (0,1) r.endpoint_gap ∧ lowMeanFractionLT r.exp_upper r.exp_upper_next)

theorem fiber_outer_universal_checks : (List.range 1).all (fun _ => fiberOuterUniversalCheck) = true := by
  decide +kernel

theorem fiber_outer_universal_checked : fiberOuterUniversalCheck = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_outer_universal_checks 0 (by decide +kernel)

theorem fiber_outer_universal_fields :
    fiberOuterUniversal.printed = fiberOuterUniversalExpected.printed ∧
      fiberOuterUniversalFields fiberOuterUniversal = fiberOuterUniversalFields fiberOuterUniversalExpected := by
  have h := of_decide_eq_true fiber_outer_universal_checked
  exact ⟨h.1,h.2.1⟩

theorem fiber_outer_universal_phi_scalar :
    lowMeanFractionReal fiberOuterUniversal.phi_lower <
      lowMeanFractionReal fiberOuterUniversal.phi_at_start := by
  have h := of_decide_eq_true fiber_outer_universal_checked
  exact (lowMean_fraction_lt_iff (by decide +kernel) (by decide +kernel)).mp h.2.2.2.2.1

theorem fiber_outer_universal_gap_scalar : 0 < lowMeanFractionReal fiberOuterUniversal.endpoint_gap := by
  have h := of_decide_eq_true fiber_outer_universal_checked
  have hp := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1))
    (by decide +kernel : lowMeanFractionValid fiberOuterUniversal.endpoint_gap)).mp h.2.2.2.2.2.2.2.1
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hp

theorem fiber_outer_universal_gap_identity :
    (8 / 3 : ℝ) - 6 * ((79 / 90) ^ 2 / (4 - 79 / 90)) - 7 / 15 =
      lowMeanFractionReal fiberOuterUniversal.endpoint_gap := by
  have h := of_decide_eq_true fiber_outer_universal_checked
  have hh := (lowMean_fraction_eq_iff
    (by decide +kernel : lowMeanFractionValid (lowMeanFractionMul (6241,25290)
      (lowMeanFractionAdd (4,1) (lowMeanFractionNeg fiberOuterUniversal.v))))
    (by decide +kernel : lowMeanFractionValid (lowMeanFractionPow fiberOuterUniversal.v 2))).mp h.2.2.2.2.2.1
  have hg := (lowMean_fraction_eq_iff
    (by decide +kernel : lowMeanFractionValid fiberOuterUniversal.endpoint_gap)
    (by decide +kernel : lowMeanFractionValid (lowMeanFractionAdd
      (lowMeanFractionAdd (8,3) (lowMeanFractionNeg (lowMeanFractionMul (6,1) (6241,25290))))
      (lowMeanFractionNeg fiberOuterUniversal.f_at_start_upper)))).mp h.2.2.2.2.2.2.1
  norm_num [fiberOuterUniversal,lowMeanFractionReal,lowMeanFractionMul,lowMeanFractionAdd,
    lowMeanFractionNeg,lowMeanFractionPow] at hh hg ⊢

end Erdos993Lean.Analytic.V213
