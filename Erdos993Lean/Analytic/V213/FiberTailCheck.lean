module

public import Erdos993Lean.Analytic.V213.FiberTailShape
public import Erdos993Lean.Analytic.V213.FiberCornerCheck

/-!
Grouped whole-number Eq104 checks, all thirteen printed rows.
Complete operation trees and the ordinary maximum branch are checked;
all logarithm domains, parameter identities and strict positive minima
are retained. No Rat kernel comparison is used.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberTailRoleIndex : FiberTailRole → ℕ
  | .smallLog => 0 | .smallGap => 1 | .largeLog => 2 | .largeGap => 3

def fiberTailRoleAt : ℕ → FiberTailRole
  | 0 => .smallLog | 1 => .smallGap | 2 => .largeLog | _ => .largeGap

def fiberTailRecordedValue (id : FiberTailIdentity) : FiberTailRole → lowMeanFraction
  | .smallLog => (fiberTailById id).upper_a
  | .smallGap => (fiberTailById id).gap_a
  | .largeLog => (fiberTailById id).upper_s
  | .largeGap => (fiberTailById id).gap_s

def fiberTailParameterTests (id : FiberTailIdentity) : Prop :=
  let r := fiberTailById id
  let base := lowMeanFractionMul (51,200) r.C
  r.printed = fiberTailPrinted id ∧
  [r.C,r.mu,r.m,r.c,r.ell,r.d,r.Z_a,r.Z_small,r.A_t,r.B_t,r.x_a,r.x_s,
    r.y_a,r.y_s,r.upper_a,r.upper_s,r.gap_a,r.gap_s,r.epsilon_a,r.epsilon_s].all
      (fun v => decide (lowMeanFractionValid v)) = true ∧
  lowMeanFractionLT (0,1) r.C ∧ lowMeanFractionLE (19,1) r.mu ∧
  lowMeanFractionLE r.mu r.m ∧ lowMeanFractionLT (0,1) r.c ∧
  lowMeanFractionLE r.c (27,50) ∧ lowMeanFractionLT (0,1) r.ell ∧
  lowMeanFractionLT (0,1) r.d ∧ lowMeanFractionLT (0,1) r.Z_a ∧
  lowMeanFractionLT (0,1) r.Z_small ∧ lowMeanFractionLT (0,1) r.A_t ∧
  lowMeanFractionLT (0,1) r.B_t ∧ lowMeanFractionLT (3,2) r.x_a ∧
  lowMeanFractionLT (7,2) r.x_s ∧
  lowMeanFractionLE (8,1) (lowMeanFractionMul r.m r.c) ∧
  (lowMeanFractionEq r.m r.mu ∨ lowMeanFractionEq (lowMeanFractionMul r.m r.c) (8,1)) ∧
  lowMeanFractionEq r.B_t (lowMeanFractionMul (81,5000) r.C) ∧
  lowMeanFractionEq r.x_s (lowMeanFractionMul r.m r.d) ∧
  lowMeanFractionEq (lowMeanFractionMul r.y_a (lowMeanFractionPow r.Z_a 2))
    (lowMeanFractionMul (lowMeanFractionPow r.A_t 2) (lowMeanFractionPow r.mu 3)) ∧
  lowMeanFractionEq (lowMeanFractionMul r.y_s (lowMeanFractionPow r.Z_small 2))
    (lowMeanFractionMul (lowMeanFractionPow r.B_t 2) (lowMeanFractionPow r.m 3)) ∧
  r.epsilon_a = (1,100) ∧ r.epsilon_s = (1,1000) ∧
  lowMeanFractionLE r.epsilon_a r.gap_a ∧ lowMeanFractionLE r.epsilon_s r.gap_s ∧
  (match r.weight with
    | some wid =>
      let w := fiberWeightById wid
      let guard := r.smallGuard.getD (0,1)
      r.h_i = none ∧ r.smallGuard = some guard ∧ lowMeanFractionValid guard ∧
      lowMeanFractionEq (lowMeanFractionMul guard r.mu) (7,1) ∧ r.ell = w.ell_w ∧
      lowMeanFractionEq r.A_t (lowMeanFractionMul base (lowMeanFractionPow (27,40) 7)) ∧
      lowMeanFractionEq r.x_a (lowMeanFractionAdd (lowMeanFractionMul r.mu w.ell_w)
        (lowMeanFractionNeg (lowMeanFractionMul (7,1) w.L_w)))
    | none =>
      let h := r.h_i.getD (1,1)
      let factor := lowMeanFractionMul (27,40) h
      r.smallGuard = none ∧ r.h_i = some h ∧ lowMeanFractionValid h ∧
      lowMeanFractionLT (0,1) h ∧
      (if r.geometricOne then lowMeanFractionLE factor (1,1)
       else lowMeanFractionLE (1,1) factor) ∧
      lowMeanFractionEq r.A_t (lowMeanFractionMul base
        (if r.geometricOne then (1,1) else lowMeanFractionPow factor 7)) ∧
      lowMeanFractionEq r.x_a (lowMeanFractionMul r.mu r.ell))

instance fiberTailParameterTestsDecidable (id : FiberTailIdentity) :
    Decidable (fiberTailParameterTests id) := by
  unfold fiberTailParameterTests
  dsimp only
  cases hw : (fiberTailById id).weight <;> simp only [hw] <;> infer_instance

def fiberTailTests (id : FiberTailIdentity) (role : FiberTailRole) : Prop :=
  let r := fiberTailById id
  fiberTailParameterTests id ∧
  lowMeanFractionLE ((2 : ℤ)^r.n_a,1) r.y_a ∧
  lowMeanFractionLT r.y_a ((2 : ℤ)^(r.n_a+1),1) ∧
  lowMeanFractionLE ((2 : ℤ)^r.n_s,1) r.y_s ∧
  lowMeanFractionLT r.y_s ((2 : ℤ)^(r.n_s+1),1) ∧
  fiberCornerEquality (fiberTailExpr id role) (fiberTailRecordedValue id role)

instance fiberTailTestsDecidable (id : FiberTailIdentity) (role : FiberTailRole) :
    Decidable (fiberTailTests id role) := by unfold fiberTailTests; infer_instance

def fiberTailCheck (id : FiberTailIdentity) (role : FiberTailRole) : Bool :=
  lowMeanIntegerShapeCheck (fiberTailExpr id role) (fiberTailShape id role) &&
    decide (fiberTailTests id role)

theorem fiber_tail_checks :
    (List.range 52).all (fun k => fiberTailCheck (fiberTailIdentityAt (k/4)) (fiberTailRoleAt (k%4))) = true := by
  decide +kernel

theorem fiber_tail_checked (id : FiberTailIdentity) (role : FiberTailRole) :
    fiberTailCheck id role = true := by
  let k := fiberTailIndex id*4+fiberTailRoleIndex role
  have hk : k < 52 := by cases id <;> cases role <;> decide +kernel
  have hi : fiberTailIdentityAt (k/4) = id ∧ fiberTailRoleAt (k%4) = role := by
    cases id <;> cases role <;> norm_num [k,fiberTailIndex,fiberTailRoleIndex,fiberTailIdentityAt,fiberTailRoleAt]
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_tail_checks k hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_tail_facts (id : FiberTailIdentity) (role : FiberTailRole) :
    fiberTailTests id role := by
  have h := fiber_tail_checked id role
  simp only [fiberTailCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

theorem fiber_tail_value_recorded (id : FiberTailIdentity) (role : FiberTailRole) :
    fiberTailValue id role = lowMeanFractionReal (fiberTailRecordedValue id role) := by
  have h := fiber_tail_checked id role
  simp only [fiberTailCheck,Bool.and_eq_true] at h
  have ht := of_decide_eq_true h.2
  have hv := ht.2.2.2.2.2
  rw [← fiber_tail_shape_real]
  exact fiber_corner_equality_real h.1 hv

end Erdos993Lean.Analytic.V213
