module

public import Erdos993Lean.Analytic.V213.FiberProfileChordData

/-!
Named consecutive-control geometry. Only explicit Int/Nat checks
are reduced; source profile/ray/endpoint bindings are checked before
real interval or nonnegative chord conclusions are used.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

instance fiberProfileIdentityDecidableEq : DecidableEq FiberRationalProfileIdentity := by
  intro a b
  cases a <;> cases b <;> first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

def fiberProfileChordCheck (id : FiberProfileChordIdentity) : Bool :=
  let c := fiberProfileChordById id
  let l := fiberProfileControlById c.left
  let h := fiberProfileControlById c.right
  let p := fiberRootLineById c.piece
  let R := (fiberRayById (fiberRationalProfileRay c.profile)).R
  decide (l.profile = some c.profile ∧ h.profile = some c.profile ∧ l.R = R ∧ h.R = R ∧
    lowMeanFractionValid l.t ∧ lowMeanFractionValid h.t ∧
    lowMeanFractionValid l.z ∧ lowMeanFractionValid h.z ∧
    lowMeanFractionValid p.lo ∧ lowMeanFractionValid p.hi ∧
    lowMeanFractionLT l.t h.t ∧ lowMeanFractionLE p.lo l.t ∧ lowMeanFractionLE h.t p.hi ∧
    lowMeanFractionLE (0,1) l.z ∧ lowMeanFractionLE (0,1) h.z)

theorem fiber_profile_chord_checks :
    (List.range 12).all (fun k => fiberProfileChordCheck (fiberProfileChordIdentityAt k)) = true := by
  decide +kernel

theorem fiber_profile_chord_checked (id : FiberProfileChordIdentity) :
    fiberProfileChordCheck id = true := by
  have hk : fiberProfileChordIndex id < 12 := by cases id <;> decide +kernel
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_profile_chord_checks
    (fiberProfileChordIndex id) hk
  have hb : fiberProfileChordIdentityAt (fiberProfileChordIndex id) = id := by cases id <;> rfl
  rwa [hb] at h

theorem fiber_profile_chord_geometry (id : FiberProfileChordIdentity) :
    let c := fiberProfileChordById id
    let l := fiberProfileControlById c.left
    let h := fiberProfileControlById c.right
    let p := fiberRootLineById c.piece
    let R := (fiberRayById (fiberRationalProfileRay c.profile)).R
    l.profile = some c.profile ∧ h.profile = some c.profile ∧ l.R = R ∧ h.R = R ∧
      lowMeanFractionReal l.t < lowMeanFractionReal h.t ∧
      lowMeanFractionReal p.lo ≤ lowMeanFractionReal l.t ∧
      lowMeanFractionReal h.t ≤ lowMeanFractionReal p.hi ∧
      0 ≤ lowMeanFractionReal l.z ∧ 0 ≤ lowMeanFractionReal h.z := by
  have hd := of_decide_eq_true (fiber_profile_chord_checked id)
  rcases hd with ⟨hpL,hpR,hRL,hRR,hlt,hht,hlz,hhz,hpl,hph,horder,hlo,hhi,hzl,hzh⟩
  have hz : lowMeanFractionValid (0,1) := by decide +kernel
  exact ⟨hpL,hpR,hRL,hRR,(lowMean_fraction_lt_iff hlt hht).mp horder,
    (lowMean_fraction_le_iff hpl hlt).mp hlo,(lowMean_fraction_le_iff hht hph).mp hhi,
    by simpa [lowMeanFractionReal] using (lowMean_fraction_le_iff hz hlz).mp hzl,
    by simpa [lowMeanFractionReal] using (lowMean_fraction_le_iff hz hhz).mp hzh⟩

end Erdos993Lean.Analytic.V213
