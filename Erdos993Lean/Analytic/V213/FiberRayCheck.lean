module

public import Erdos993Lean.Analytic.V213.FiberRayShape

/-!
Kernel checks of all 36 accepted F08 canonical expressions.
Every check binds printed identity, all parameter leaves, full shape,
and the exact strict gap/root relation. No Rat evaluator is used.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberRayParameters (r : FiberRayRow) : List lowMeanFraction :=
  [r.R, r.m_f, r.N_f, r.rho_f, r.k_f, r.beta_f, r.d_f, r.s, r.v, r.minimum_gap, r.rho_minus, r.k_plus, r.E_plus]

def fiberRayExpectedParameters : FiberRayIdentity → List lowMeanFraction
  | .a => [(1, 4), (8, 1), (10, 1), (63, 100), (17, 6), (24, 5), (21, 10), (19, 6), (19, 18), (7, 10000), (22699, 35640), (5722, 2025), (5329, 4050)]
  | .b => [(1, 8), (8, 1), (10, 1), (69, 100), (14, 5), (13, 2), (13, 10), (19, 6), (19, 18), (3, 1000), (417559, 598752), (23698, 8505), (61097, 71442)]
  | .d => [(1, 6), (8, 1), (10, 1), (17, 25), (14, 5), (6, 1), (29, 20), (19, 6), (19, 18), (1, 1000), (7088, 10395), (1468, 525), (2431, 2450)]
  | .h => [(7, 25), (14, 1), (16, 1), (143, 200), (14, 5), (10, 1), (4, 5), (4, 1), (31, 30), (1, 1000), (78931613, 110160000), (231763, 82944), (788009, 442368)]

def fiberRayRelation (id : FiberRayIdentity) (role : FiberRayRole) (v : lowMeanFraction) : Prop :=
  let row := fiberRayById id
  match role with
  | .rho => lowMeanFractionValid row.rho_minus ∧ lowMeanFractionEq v row.rho_minus
  | .kappa => lowMeanFractionValid row.k_plus ∧ lowMeanFractionEq v row.k_plus
  | .error => lowMeanFractionValid row.E_plus ∧ lowMeanFractionEq v row.E_plus
  | .rhoGap | .kappaGap | .betaGap | .squareGap =>
      lowMeanFractionValid row.minimum_gap ∧ lowMeanFractionLT row.minimum_gap v
  | .sqrtS | .sqrtV => lowMeanFractionLE (0,1) v

instance fiberRayRelationDecidable (id : FiberRayIdentity) (role : FiberRayRole) (v : lowMeanFraction) :
    Decidable (fiberRayRelation id role v) := by
  cases role <;> dsimp [fiberRayRelation] <;> infer_instance

def fiberRayCheck (id : FiberRayIdentity) (role : FiberRayRole) : Bool :=
  let row := fiberRayById id
  let e := fiberRayExpr id role
  lowMeanIntegerShapeCheck e (fiberRayShape id role) &&
    decide (row.printed = fiberRayPrinted id ∧ fiberRayParameters row = fiberRayExpectedParameters id ∧
      fiberRayRelation id role (lowMeanIntegerExprValue e))

theorem fiber_ray_checks :
    (List.range 36).all (fun k => fiberRayCheck (fiberRayIdentityAt (k / 9)) (fiberRayRoleAt (k % 9))) = true := by
  decide +kernel

theorem fiber_ray_index_checked {k : ℕ} (hk : k < 36) :
    fiberRayCheck (fiberRayIdentityAt (k / 9)) (fiberRayRoleAt (k % 9)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_ray_checks k hk

theorem fiber_ray_named_checked (id : FiberRayIdentity) (role : FiberRayRole) :
    fiberRayCheck id role = true := by
  cases id <;> cases role <;> decide +kernel

theorem fiber_ray_shape_sound (id : FiberRayIdentity) (role : FiberRayRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberRayExpr id role)) ∧
      fiberRayValue id role = lowMeanFractionReal (lowMeanIntegerExprValue (fiberRayExpr id role)) := by
  have h := fiber_ray_named_checked id role
  simp only [fiberRayCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_ray_shape_real] at hs
  exact hs

theorem fiber_ray_gap_checked (id : FiberRayIdentity) (role : FiberRayRole)
    (hr : role = .rhoGap ∨ role = .kappaGap ∨ role = .betaGap ∨ role = .squareGap) :
    lowMeanFractionReal (fiberRayById id).minimum_gap < fiberRayValue id role := by
  have h := fiber_ray_named_checked id role
  simp only [fiberRayCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_ray_shape_sound id role
  rw [hs.2]
  rcases hr with rfl | rfl | rfl | rfl <;>
    exact (lowMean_fraction_lt_iff hd.2.2.1 hs.1).mp hd.2.2.2

theorem fiber_ray_root_checked (id : FiberRayIdentity) (role : FiberRayRole)
    (hr : role = .sqrtS ∨ role = .sqrtV) : 0 ≤ fiberRayValue id role := by
  have h := fiber_ray_named_checked id role
  simp only [fiberRayCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_ray_shape_sound id role
  rw [hs.2]
  rcases hr with rfl | rfl <;>
    have hc := (lowMean_fraction_le_iff (by decide +kernel : lowMeanFractionValid (0,1)) hs.1).mp hd.2.2
  all_goals simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hc

end Erdos993Lean.Analytic.V213
