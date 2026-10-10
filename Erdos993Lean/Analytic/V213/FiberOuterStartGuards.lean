module

public import Erdos993Lean.Analytic.V213.FiberOuterStartCheck
public import Erdos993Lean.Analytic.V213.FiberOuterEndpointGuards

/-!
Parameter guards for the four accepted F05 printed start identities.
The finite check uses only Int/Nat cross products. Its full real meaning
includes the positive cutoff, global cap margin and negative-root domain;
range indices only enumerate the named rows and named guard roles.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

inductive FiberOuterGuardRole where
  | nMin | aPos | aMax | naMin | sigmaPos | sigmaMax | pMin | dMin
  | RPos | vMin | vMax | omegaMax | bMin | bMax | betaMin | betaMax

def fiberOuterGuardRoleAt (k : ℕ) : FiberOuterGuardRole :=
  match k with
  | 0 => .nMin | 1 => .aPos | 2 => .aMax | 3 => .naMin
  | 4 => .sigmaPos | 5 => .sigmaMax | 6 => .pMin | 7 => .dMin
  | 8 => .RPos | 9 => .vMin | 10 => .vMax | 11 => .omegaMax
  | 12 => .bMin | 13 => .bMax | 14 => .betaMin | _ => .betaMax

def fiberOuterGuardSides (id : FiberOuterStartIdentity) (role : FiberOuterGuardRole) :
    lowMeanFraction × lowMeanFraction × Bool :=
  let r := fiberOuterStartById id
  match role with
  | .nMin => ((17,1),r.n,false)
  | .aPos => ((0,1),r.a,true)
  | .aMax => (r.a,(2,5),false)
  | .naMin => ((18,5),lowMeanFractionMul (lowMeanFractionAdd r.n (1,1)) r.a,false)
  | .sigmaPos => ((0,1),r.sigma,true)
  | .sigmaMax => (r.sigma,(1,1),true)
  | .pMin => ((1,6),r.p_star,true)
  | .dMin => ((1,2),r.d_star,true)
  | .RPos => ((0,1),r.R_star,true)
  | .vMin => ((0,1),r.v_star,false)
  | .vMax => (r.v_star,(3,1),true)
  | .omegaMax => (lowMeanFractionAdd (lowMeanFractionMul (5,2) r.logUpper)
      (lowMeanFractionNeg r.p_star),r.v_star,false)
  | .bMin => ((0,1),r.b0,false)
  | .bMax => (r.b0,(2,5),false)
  | .betaMin => ((0,1),r.beta0,false)
  | .betaMax => (r.beta0,(1,1),false)

def fiberOuterGuardCheck (id : FiberOuterStartIdentity) (role : FiberOuterGuardRole) : Bool :=
  let s := fiberOuterGuardSides id role
  decide (lowMeanFractionValid s.1 ∧ lowMeanFractionValid s.2.1 ∧
    (if s.2.2 then lowMeanFractionLT s.1 s.2.1 else lowMeanFractionLE s.1 s.2.1))

theorem fiber_outer_start_guard_checks :
    (List.range 64).all (fun k => fiberOuterGuardCheck
      (fiberOuterStartIdentityAt (k / 16)) (fiberOuterGuardRoleAt (k % 16))) = true := by
  decide +kernel

theorem fiber_outer_start_guard_index {k : ℕ} (hk : k < 64) :
    fiberOuterGuardCheck (fiberOuterStartIdentityAt (k / 16)) (fiberOuterGuardRoleAt (k % 16)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_outer_start_guard_checks k hk

theorem fiber_outer_start_guard_named (id : FiberOuterStartIdentity) (role : FiberOuterGuardRole) :
    fiberOuterGuardCheck id role = true := by
  cases id <;> cases role <;> decide +kernel

noncomputable def fiberOuterGuardMeaning (id : FiberOuterStartIdentity) (role : FiberOuterGuardRole) : Prop :=
  let r := fiberOuterStartById id
  let n := lowMeanFractionReal r.n
  let a := lowMeanFractionReal r.a
  let sigma := lowMeanFractionReal r.sigma
  let p := lowMeanFractionReal r.p_star
  let d := lowMeanFractionReal r.d_star
  let R := lowMeanFractionReal r.R_star
  let v := lowMeanFractionReal r.v_star
  let L := lowMeanFractionReal r.logUpper
  let b := lowMeanFractionReal r.b0
  let beta := lowMeanFractionReal r.beta0
  match role with
  | .nMin => 17 ≤ n | .aPos => 0 < a | .aMax => a ≤ 2 / 5
  | .naMin => 18 / 5 ≤ (n + 1) * a
  | .sigmaPos => 0 < sigma | .sigmaMax => sigma < 1
  | .pMin => 1 / 6 < p | .dMin => 1 / 2 < d | .RPos => 0 < R
  | .vMin => 0 ≤ v | .vMax => v < 3 | .omegaMax => 5 / 2 * L - p ≤ v
  | .bMin => 0 ≤ b | .bMax => b ≤ 2 / 5
  | .betaMin => 0 ≤ beta | .betaMax => beta ≤ 1

theorem fiber_outer_start_guard_sound (id : FiberOuterStartIdentity) (role : FiberOuterGuardRole) :
    fiberOuterGuardMeaning id role := by
  have hd := of_decide_eq_true (fiber_outer_start_guard_named id role)
  change lowMeanFractionValid (fiberOuterGuardSides id role).1 ∧
    lowMeanFractionValid (fiberOuterGuardSides id role).2.1 ∧ _ at hd
  have hreal : if (fiberOuterGuardSides id role).2.2 then
      lowMeanFractionReal (fiberOuterGuardSides id role).1 <
        lowMeanFractionReal (fiberOuterGuardSides id role).2.1 else
      lowMeanFractionReal (fiberOuterGuardSides id role).1 ≤
        lowMeanFractionReal (fiberOuterGuardSides id role).2.1 := by
    split <;> rename_i hs
    · exact (lowMean_fraction_lt_iff hd.1 hd.2.1).mp (by simpa only [hs,ite_true] using hd.2.2)
    · exact (lowMean_fraction_le_iff hd.1 hd.2.1).mp (by simpa only [hs,Bool.false_eq_true,ite_false] using hd.2.2)
  have hn : lowMeanFractionValid (fiberOuterStartById id).n := by
    cases id <;> decide +kernel
  have h1 : lowMeanFractionValid (1,1) := by decide +kernel
  have hmul : lowMeanFractionValid (lowMeanFractionMul (5,2) (fiberOuterStartById id).logUpper) := by
    cases id <;> decide +kernel
  have hneg : lowMeanFractionValid (lowMeanFractionNeg (fiberOuterStartById id).p_star) := by
    cases id <;> decide +kernel
  cases role <;> simp only [fiberOuterGuardSides,fiberOuterGuardMeaning,Bool.false_eq_true,
    eq_self,ite_false,ite_true,lowMean_fraction_mul,lowMean_fraction_neg,
    lowMean_fraction_add hn h1,lowMean_fraction_add hmul hneg] at hreal ⊢
    <;> norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,
      Int.cast_one,Nat.cast_one,zero_div,one_div,div_self] at hreal ⊢
    <;> first | exact hreal | linarith only [hreal]

end Erdos993Lean.Analytic.V213
