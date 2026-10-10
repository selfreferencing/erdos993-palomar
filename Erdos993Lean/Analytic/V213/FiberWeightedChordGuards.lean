module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordCheck
public import Erdos993Lean.Analytic.V213.FiberWeightedChord

/-!
Real guards and exact chord identity from the checked printed F12
records. The named Eq89 argument and the exceptional derivative guard
are interpreted before either price route is used.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_weighted_chord_scalar_guards (id : FiberWeightedChordIdentity) :
    let r := fiberWeightedChordById id
    let w := fiberWeightById r.weight
    let p := fiberWeightedChordParameters id
    0 < p.1 ∧ 0 < p.2.2.1 ∧ 0 < lowMeanFractionReal w.eta_w ∧
    0 < lowMeanFractionReal r.epsilon ∧
    (2 : ℝ)^r.n ≤ p.2.2.2.2 ∧ p.2.2.2.2 < (2 : ℝ)^(r.n+1) := by
  have hm := fiber_weighted_chord_metadata id
  simp only [fiberWeightedChordMetadata] at hm
  rcases hm with ⟨_,_,_,_,_,hs,_,hk,_,hy,_,_,heps,heta,hsp,hkp,hetap,hepsp,hlo,hhi,_⟩
  have hz : lowMeanFractionValid (0,1) := by decide +kernel
  have hv (n : ℕ) : lowMeanFractionValid ((2 : ℤ)^n,1) := by norm_num [lowMeanFractionValid]
  rw [fiber_weighted_chord_stored_parameters]
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [lowMeanFractionReal] using (lowMean_fraction_lt_iff hz hs).mp hsp
  · simpa [lowMeanFractionReal] using (lowMean_fraction_lt_iff hz hk).mp hkp
  · simpa [lowMeanFractionReal] using (lowMean_fraction_lt_iff hz heta).mp hetap
  · simpa [lowMeanFractionReal] using (lowMean_fraction_lt_iff hz heps).mp hepsp
  · simpa [lowMeanFractionReal] using (lowMean_fraction_le_iff (hv _) hy).mp hlo
  · simpa [lowMeanFractionReal] using (lowMean_fraction_lt_iff hy (hv _)).mp hhi

theorem fiber_weighted_chord_endpoint_guard (id : FiberWeightedChordIdentity)
    (hroute : (fiberWeightedChordById id).endpointRoute = true) :
    let r := fiberWeightedChordById id
    let p := fiberWeightedChordParameters id
    1 ≤ p.2.2.1 * lowMeanFractionReal (fiberProfileControlById
      (fiberProfileChordById r.chord).right).z - p.1 := by
  have hm := fiber_weighted_chord_metadata id
  simp only [fiberWeightedChordMetadata] at hm
  rcases hm with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hend⟩
  have hz : lowMeanFractionValid (lowMeanFractionAdd
      (lowMeanFractionMul (fiberWeightedChordById id).k
        (fiberProfileControlById (fiberProfileChordById (fiberWeightedChordById id).chord).right).z)
      (lowMeanFractionNeg (fiberWeightedChordById id).s)) := by
    cases id <;> decide +kernel
  have h := (lowMean_fraction_le_iff (by decide +kernel : lowMeanFractionValid (1,1)) hz).mp (hend hroute)
  have hkV : lowMeanFractionValid (fiberWeightedChordById id).k := by cases id <;> decide +kernel
  have hsV : lowMeanFractionValid (fiberWeightedChordById id).s := by cases id <;> decide +kernel
  have hzV : lowMeanFractionValid (fiberProfileControlById
      (fiberProfileChordById (fiberWeightedChordById id).chord).right).z := by cases id <;> decide +kernel
  have hmulV : lowMeanFractionValid (lowMeanFractionMul (fiberWeightedChordById id).k
      (fiberProfileControlById (fiberProfileChordById (fiberWeightedChordById id).chord).right).z) :=
    Nat.mul_pos hkV hzV
  have hnegV : lowMeanFractionValid (lowMeanFractionNeg (fiberWeightedChordById id).s) := hsV
  rw [lowMean_fraction_add hmulV hnegV,lowMean_fraction_mul,
    lowMean_fraction_neg] at h
  rw [fiber_weighted_chord_stored_parameters]
  simpa [lowMeanFractionReal,sub_eq_add_neg] using h

theorem fiber_weighted_chord_linear_identity (id : FiberWeightedChordIdentity) (t : ℝ) :
    let p := fiberWeightedChordParameters id
    p.1 * (p.2.1 - t) = fiberProfileChordValue (fiberWeightedChordById id).chord t := by
  have hg := fiber_profile_chord_geometry (fiberWeightedChordById id).chord
  have hlt := hg.2.2.2.2.1
  have hd : lowMeanFractionReal (fiberProfileControlById
      (fiberProfileChordById (fiberWeightedChordById id).chord).right).t -
      lowMeanFractionReal (fiberProfileControlById
      (fiberProfileChordById (fiberWeightedChordById id).chord).left).t ≠ 0 := by
    linarith only [hlt]
  have hs := (fiber_weighted_chord_scalar_guards id).1.ne'
  dsimp only [fiberWeightedChordParameters] at hs ⊢
  have hnum := (div_ne_zero_iff.mp hs).1
  unfold fiberProfileChordValue
  field_simp [hnum,hd]
  ring

end Erdos993Lean.Analytic.V213
