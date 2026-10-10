module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordGuards

/-!
Literal Eq98--99 consumers for each printed weighted chord.
The whole-half-line and the two increasing-endpoint routes use the
actual Eq89 bound and a checked positive strict gap. The final theorem
bounds the actual D/E profiles on the entire closed chord interval.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

theorem fiber_weighted_chord_named_price (id : FiberWeightedChordIdentity) {t : ℝ}
    (ht : t ∈ Icc
      (lowMeanFractionReal (fiberProfileControlById (fiberProfileChordById (fiberWeightedChordById id).chord).left).t)
      (lowMeanFractionReal (fiberProfileControlById (fiberProfileChordById (fiberWeightedChordById id).chord).right).t)) :
    Real.exp (-(lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).mu_w *
        (lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).ell_w -
         lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).L_w * t))) *
      fiberProfileChordValue (fiberWeightedChordById id).chord t <
      lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).eta_w := by
  let r := fiberWeightedChordById id
  let w := fiberWeightById r.weight
  let c := fiberProfileChordById r.chord
  let h := fiberProfileControlById c.right
  let p := fiberWeightedChordParameters id
  rcases fiber_weighted_chord_scalar_guards id with ⟨hs,hk,heta,heps,hy,_⟩
  change 0 < p.1 at hs
  change 0 < p.2.2.1 at hk
  change 0 < lowMeanFractionReal w.eta_w at heta
  change 0 < lowMeanFractionReal r.epsilon at heps
  change (2 : ℝ)^r.n ≤ p.2.2.2.2 at hy
  have hlog := fiber_dyadic_log_bound r.n hy
  have hlogValue := fiber_weighted_chord_log_value id
  have hgap := lt_of_lt_of_le heps (fiber_weighted_chord_gap_value id)
  change 0 < fiberWeightedChordValue id .gap at hgap
  have hprice : fiberWeightedChord p.1 p.2.1 p.2.2.1 p.2.2.2.1 t <
      lowMeanFractionReal w.eta_w := by
    by_cases hr : r.endpointRoute = true
    · have hyEq : p.2.2.2.2 = lowMeanFractionReal h.z / lowMeanFractionReal w.eta_w := by
        simp [p,fiberWeightedChordParameters,r,w,c,h,hr]
      have hlog' : Real.log (lowMeanFractionReal h.z / lowMeanFractionReal w.eta_w) ≤
          lowMeanFractionReal r.upper := by
        rw [← hyEq]
        exact hlog.trans hlogValue.le
      have hgap' : lowMeanFractionReal r.upper < p.2.2.2.1 - p.2.2.1 * lowMeanFractionReal h.t := by
        have hgEq : fiberWeightedChordValue id .gap =
            p.2.2.2.1 - p.2.2.1 * lowMeanFractionReal h.t - lowMeanFractionReal r.upper := by
          simp only [fiberWeightedChordValue,r,w,c,h,p,hr,ite_true] at hlogValue ⊢
          rw [hlogValue]
        rw [hgEq] at hgap
        linarith only [hgap]
      have hend := fiber_weighted_chord_endpoint_guard id hr
      change 1 ≤ p.2.2.1 * lowMeanFractionReal h.z - p.1 at hend
      have hzh : 0 < lowMeanFractionReal h.z := by
        by_contra hn
        have hmul := mul_nonpos_of_nonneg_of_nonpos hk.le (le_of_not_gt hn)
        linarith only [hend,hs,hmul]
      have hden : lowMeanFractionReal h.t -
          lowMeanFractionReal (fiberProfileControlById c.left).t ≠ 0 := by
        have hh := (fiber_profile_chord_geometry r.chord).2.2.2.2.1
        change lowMeanFractionReal (fiberProfileControlById c.left).t < lowMeanFractionReal h.t at hh
        linarith only [hh]
      have hzEq : p.1 * (p.2.1 - lowMeanFractionReal h.t) = lowMeanFractionReal h.z := by
        rw [fiber_weighted_chord_linear_identity]
        simp [fiberProfileChordValue,r,c,h,hden]
      have hend' : 1 ≤ p.2.2.1 * p.1 * (p.2.1 - lowMeanFractionReal h.t) - p.1 := by
        rw [mul_assoc,hzEq]
        exact hend
      apply fiber_weighted_chord_endpoint_price (U := lowMeanFractionReal r.upper) hs hk heta ht.2
        (by rwa [hzEq]) hend'
      · change Real.log (p.1 * (p.2.1-lowMeanFractionReal h.t) / lowMeanFractionReal w.eta_w) ≤
          lowMeanFractionReal r.upper
        rw [hzEq]
        exact hlog'
      · exact hgap'
    · have hr' : r.endpointRoute = false := Bool.eq_false_iff.mpr hr
      have hyEq : p.2.2.2.2 = p.1 / (p.2.2.1 * lowMeanFractionReal w.eta_w) := by
        simp [p,fiberWeightedChordParameters,r,w,hr']
      have hlog' : Real.log (p.1 / (p.2.2.1 * lowMeanFractionReal w.eta_w)) ≤
          lowMeanFractionReal r.upper := by
        rw [← hyEq]
        exact hlog.trans hlogValue.le
      have hgap' : lowMeanFractionReal r.upper < p.2.2.2.1 + 1 - p.2.2.1 * p.2.1 := by
        have hgEq : fiberWeightedChordValue id .gap =
            p.2.2.2.1 + 1 - p.2.2.1 * p.2.1 - lowMeanFractionReal r.upper := by
          simp only [fiberWeightedChordValue,r,p,hr',Bool.false_eq_true,ite_false] at hlogValue ⊢
          rw [hlogValue]
        rw [hgEq] at hgap
        linarith only [hgap]
      exact fiber_weighted_chord_price hs hk heta hlog' hgap'
  have hprod : Real.exp (-(lowMeanFractionReal w.mu_w *
      (lowMeanFractionReal w.ell_w - lowMeanFractionReal w.L_w*t))) *
      fiberProfileChordValue r.chord t = fiberWeightedChord p.1 p.2.1 p.2.2.1 p.2.2.2.1 t := by
    rw [← fiber_weighted_chord_linear_identity id t]
    unfold fiberWeightedChord
    have he : -(lowMeanFractionReal w.mu_w *
        (lowMeanFractionReal w.ell_w - lowMeanFractionReal w.L_w*t)) = p.2.2.1*t-p.2.2.2.1 := by
      dsimp [p,fiberWeightedChordParameters,w,r]
      ring
    rw [he]
    ring
  change Real.exp (-(lowMeanFractionReal w.mu_w *
      (lowMeanFractionReal w.ell_w-lowMeanFractionReal w.L_w*t))) *
      fiberProfileChordValue r.chord t < lowMeanFractionReal w.eta_w
  rwa [hprod]

theorem fiber_weighted_profile_chord_price (id : FiberWeightedChordIdentity) {t u : ℝ}
    (ht : t ∈ Icc
      (lowMeanFractionReal (fiberProfileControlById (fiberProfileChordById (fiberWeightedChordById id).chord).left).t)
      (lowMeanFractionReal (fiberProfileControlById (fiberProfileChordById (fiberWeightedChordById id).chord).right).t))
    (hu : 0 ≤ u)
    (huR : u ≤ lowMeanFractionReal (fiberRayById (fiberRationalProfileRay
      (fiberProfileChordById (fiberWeightedChordById id).chord).profile)).R) :
    Real.exp (-(lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).mu_w *
        (lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).ell_w -
         lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).L_w*t))) *
      max 0 (max (fiberNamedProfile (fiberProfileChordById (fiberWeightedChordById id).chord).profile t u
        (fiberRayAroot t)) (fiberProfileE t u (fiberRayAroot t))) <
      lowMeanFractionReal (fiberWeightById (fiberWeightedChordById id).weight).eta_w := by
  exact (mul_le_mul_of_nonneg_left (fiber_profile_chord_bound _ ht hu huR)
    (Real.exp_pos _).le).trans_lt (fiber_weighted_chord_named_price id ht)

end Erdos993Lean.Analytic.V213
