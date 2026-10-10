module

public import Erdos993Lean.Analytic.V213.FiberWingCheck

/-!
Named Int/Nat guards for all accepted F04 start rows. The two small
skew starts explicitly require the improved gain domain. Every actual
closed skew, positive start and negative root guard is proved by the
kernel and cast soundly to reals. Numerical indices only enumerate.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWingImproved : FiberWingIdentity → Bool
  | .w1 | .w2 => true
  | .w3 => false

inductive FiberWingGuardRole where
  | nMin
  | aPos
  | bMax
  | aSkew
  | skewB
  | skewPos
  | skewMax
  | muPos
  | tauPos
  | tauMax
  | pPos
  | dPos
  | RPos
  | s0Min
  | s0Max
  | sqrtPos
  | aImproved
  | bImproved
  | muMin

def fiberWingGuardRoleAt : ℕ → FiberWingGuardRole
  | 0 => .nMin
  | 1 => .aPos
  | 2 => .bMax
  | 3 => .aSkew
  | 4 => .skewB
  | 5 => .skewPos
  | 6 => .skewMax
  | 7 => .muPos
  | 8 => .tauPos
  | 9 => .tauMax
  | 10 => .pPos
  | 11 => .dPos
  | 12 => .RPos
  | 13 => .s0Min
  | 14 => .s0Max
  | 15 => .sqrtPos
  | 16 => .aImproved
  | 17 => .bImproved
  | _ => .muMin

def fiberWingGuardSides (id : FiberWingIdentity) (role : FiberWingGuardRole) :
    lowMeanFraction × lowMeanFraction × Bool :=
  let r := fiberWingById id
  match role with
  | .nMin => ((13,1),r.N0,false)
  | .aPos => ((0,1),r.a,true)
  | .bMax => (r.b,(1,5),false)
  | .aSkew => (r.a,r.skew_lower,false)
  | .skewB => (r.skew_upper,r.b,false)
  | .skewPos => ((0,1),r.skew_lower,true)
  | .skewMax => (r.skew_upper,(1,2),false)
  | .muPos => ((0,1),r.mu_W,true)
  | .tauPos => ((0,1),r.tau,true)
  | .tauMax => (r.tau,(3,5),false)
  | .pPos => ((0,1),r.p,true)
  | .dPos => ((0,1),r.d,true)
  | .RPos => ((0,1),r.R,true)
  | .s0Min => ((-1,1),r.s0,true)
  | .s0Max => (r.s0,(0,1),true)
  | .sqrtPos => ((0,1),r.sqrtUpper,true)
  | .aImproved => if fiberWingImproved id then ((1,20),r.a,false) else ((0,1),(0,1),false)
  | .bImproved => if fiberWingImproved id then (r.b,(3,25),false) else ((0,1),(0,1),false)
  | .muMin => ((19,1),r.mu_W,false)

def fiberWingGuardCheck (id : FiberWingIdentity) (role : FiberWingGuardRole) : Bool :=
  let s := fiberWingGuardSides id role
  decide (lowMeanFractionValid s.1 ∧ lowMeanFractionValid s.2.1 ∧
    (if s.2.2 then lowMeanFractionLT s.1 s.2.1 else lowMeanFractionLE s.1 s.2.1))

theorem fiber_wing_guard_checks :
    (List.range 57).all (fun k => fiberWingGuardCheck
      (fiberWingIdentityAt (k / 19)) (fiberWingGuardRoleAt (k % 19))) = true := by
  decide +kernel

theorem fiber_wing_guard_index {k : ℕ} (hk : k < 57) :
    fiberWingGuardCheck (fiberWingIdentityAt (k / 19)) (fiberWingGuardRoleAt (k % 19)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_wing_guard_checks k hk

theorem fiber_wing_guard_named (id : FiberWingIdentity) (role : FiberWingGuardRole) :
    fiberWingGuardCheck id role = true := by
  cases id <;> cases role <;> decide +kernel

noncomputable def fiberWingGuardMeaning (id : FiberWingIdentity) (role : FiberWingGuardRole) : Prop :=
  let r := fiberWingById id
  let n := lowMeanFractionReal r.N0
  let a := lowMeanFractionReal r.a
  let b := lowMeanFractionReal r.b
  let rl := lowMeanFractionReal r.skew_lower
  let rh := lowMeanFractionReal r.skew_upper
  let mu := lowMeanFractionReal r.mu_W
  let t := lowMeanFractionReal r.tau
  let p := lowMeanFractionReal r.p
  let d := lowMeanFractionReal r.d
  let rate := lowMeanFractionReal r.R
  let s := lowMeanFractionReal r.s0
  let root := lowMeanFractionReal r.sqrtUpper
  match role with
  | .nMin => 13 ≤ n
  | .aPos => 0 < a
  | .bMax => b ≤ 1 / 5
  | .aSkew => a ≤ rl
  | .skewB => rh ≤ b
  | .skewPos => 0 < rl
  | .skewMax => rh ≤ 1 / 2
  | .muPos => 0 < mu
  | .tauPos => 0 < t
  | .tauMax => t ≤ 3 / 5
  | .pPos => 0 < p
  | .dPos => 0 < d
  | .RPos => 0 < rate
  | .s0Min => -1 < s
  | .s0Max => s < 0
  | .sqrtPos => 0 < root
  | .aImproved => if fiberWingImproved id then 1 / 20 ≤ a else True
  | .bImproved => if fiberWingImproved id then b ≤ 3 / 25 else True
  | .muMin => 19 ≤ mu

theorem fiber_wing_guard_sound (id : FiberWingIdentity) (role : FiberWingGuardRole) :
    fiberWingGuardMeaning id role := by
  have hd := of_decide_eq_true (fiber_wing_guard_named id role)
  change lowMeanFractionValid (fiberWingGuardSides id role).1 ∧
    lowMeanFractionValid (fiberWingGuardSides id role).2.1 ∧ _ at hd
  have hreal : if (fiberWingGuardSides id role).2.2 then
      lowMeanFractionReal (fiberWingGuardSides id role).1 <
        lowMeanFractionReal (fiberWingGuardSides id role).2.1 else
      lowMeanFractionReal (fiberWingGuardSides id role).1 ≤
        lowMeanFractionReal (fiberWingGuardSides id role).2.1 := by
    split <;> rename_i hs
    · exact (lowMean_fraction_lt_iff hd.1 hd.2.1).mp (by simpa only [hs,ite_true] using hd.2.2)
    · exact (lowMean_fraction_le_iff hd.1 hd.2.1).mp (by simpa only [hs,Bool.false_eq_true,ite_false] using hd.2.2)
  cases role <;> (try cases id) <;>
    simp only [fiberWingGuardSides,fiberWingGuardMeaning,fiberWingImproved,Bool.false_eq_true,
      eq_self,ite_false,ite_true] at hreal ⊢ <;>
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_neg,Int.cast_zero,
      Int.cast_one,Nat.cast_one,zero_div,one_div,div_self] at hreal ⊢ <;>
    first | exact hreal | linarith only [hreal]

end Erdos993Lean.Analytic.V213
