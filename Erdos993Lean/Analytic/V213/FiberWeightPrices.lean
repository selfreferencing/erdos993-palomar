module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordPrices

/-!
Literal Eq99 on every complete named profile interval. Seven
weights use all eighteen checked chords. Weight E uses the printed
D/F interpolation, with its affine gap proved on the whole closed
interval. Original-input rate/size routing is a separate consumer.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

noncomputable def fiberWeightExponent (id : FiberWeightIdentity) (t : ℝ) : ℝ :=
  lowMeanFractionReal (fiberWeightById id).mu_w *
    (lowMeanFractionReal (fiberWeightById id).ell_w - lowMeanFractionReal (fiberWeightById id).L_w*t)

theorem fiber_weighted_chord_cover (wid : FiberWeightIdentity) (hw : wid ≠ .e) {t : ℝ}
    (ht : 1 / 3 ≤ t) (hcap : t ≤ fiberProfileTimeCap (fiberWeightById wid).profile) :
    ∃ id : FiberWeightedChordIdentity, (fiberWeightedChordById id).weight = wid ∧
      t ∈ Icc (lowMeanFractionReal (fiberProfileControlById
        (fiberProfileChordById (fiberWeightedChordById id).chord).left).t)
        (lowMeanFractionReal (fiberProfileControlById
        (fiberProfileChordById (fiberWeightedChordById id).chord).right).t) := by
  cases wid with
  | a =>
      by_cases h1 : t ≤ 21 / 50
      · refine ⟨.a_third_p042,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht h1
      · by_cases h2 : t ≤ 1 / 2
        · refine ⟨.a_p042_half,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h1)) h2
        · refine ⟨.a_half_p06,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h2)) hcap
  | b =>
      by_cases h1 : t ≤ 21 / 50
      · refine ⟨.b_third_p042,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht h1
      · by_cases h2 : t ≤ 1 / 2
        · refine ⟨.b_p042_half,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h1)) h2
        · refine ⟨.b_half_p06,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h2)) hcap
  | c =>
      by_cases h1 : t ≤ 21 / 50
      · refine ⟨.c_third_p042,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht h1
      · by_cases h2 : t ≤ 1 / 2
        · refine ⟨.c_p042_half,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h1)) h2
        · refine ⟨.c_half_p06,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h2)) hcap
  | d =>
      by_cases h1 : t ≤ 21 / 50
      · refine ⟨.d_third_p042,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht h1
      · by_cases h2 : t ≤ 1 / 2
        · refine ⟨.d_p042_half,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h1)) h2
        · refine ⟨.d_half_p052,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h2)) hcap
  | f =>
      by_cases h1 : t ≤ 21 / 50
      · refine ⟨.f_third_p042,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht h1
      · by_cases h2 : t ≤ 1 / 2
        · refine ⟨.f_p042_half,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h1)) h2
        · refine ⟨.f_half_p052,rfl,?_⟩
          simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h2)) hcap
  | g =>
      by_cases h1 : t ≤ 21 / 50
      · refine ⟨.g_third_p042,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht h1
      · refine ⟨.g_p042_p044,rfl,?_⟩
        simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro (le_of_lt (lt_of_not_ge h1)) hcap
  | h =>
      refine ⟨.h_third_p038,rfl,?_⟩
      simpa [fiberWeightedChordById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal,fiberWeightById,fiberProfileTimeCap] using And.intro ht hcap
  | e => exact (hw rfl).elim

theorem fiber_weight_profile_binding (id : FiberWeightedChordIdentity) :
    (fiberProfileChordById (fiberWeightedChordById id).chord).profile =
      (fiberWeightById (fiberWeightedChordById id).weight).profile := by
  have hm := fiber_weighted_chord_metadata id
  simp only [fiberWeightedChordMetadata] at hm
  exact hm.2.2.2.1

theorem fiber_weight_price_except_E (wid : FiberWeightIdentity) (hw : wid ≠ .e) {t u : ℝ}
    (ht : 1 / 3 ≤ t) (hcap : t ≤ fiberProfileTimeCap (fiberWeightById wid).profile)
    (hu : 0 ≤ u)
    (huR : u ≤ lowMeanFractionReal (fiberRayById (fiberRationalProfileRay (fiberWeightById wid).profile)).R) :
    Real.exp (-fiberWeightExponent wid t) *
      max 0 (max (fiberNamedProfile (fiberWeightById wid).profile t u (fiberRayAroot t))
        (fiberProfileE t u (fiberRayAroot t))) < lowMeanFractionReal (fiberWeightById wid).eta_w := by
  obtain ⟨id,hwid,hmem⟩ := fiber_weighted_chord_cover wid hw ht hcap
  have hp := fiber_weight_profile_binding id
  rw [hwid] at hp
  have hb := fiber_weighted_profile_chord_price id hmem hu (by rwa [hp])
  rw [hwid,hp] at hb
  exact hb

theorem fiber_weight_E_interpolation {t : ℝ} (ht : t ∈ Icc (1/3) (13/25)) :
    (fiberWeightExponent .d t + fiberWeightExponent .f t)/2 ≤ fiberWeightExponent .e t := by
  norm_num [fiberWeightExponent,fiberWeightById,lowMeanFractionReal]
  linarith only [ht.2]

theorem fiber_weight_E_interpolation_endpoints :
    fiberWeightExponent .e (1/3) - (fiberWeightExponent .d (1/3) + fiberWeightExponent .f (1/3))/2 = 13613/60000 ∧
    fiberWeightExponent .e (13/25) - (fiberWeightExponent .d (13/25) + fiberWeightExponent .f (13/25))/2 = 42961/500000 := by
  norm_num [fiberWeightExponent,fiberWeightById,lowMeanFractionReal]

theorem fiber_weight_E_price {t u : ℝ}
    (ht : 1 / 3 ≤ t) (hcap : t ≤ 13/25) (hu : 0 ≤ u) (huR : u ≤ 1/6) :
    Real.exp (-fiberWeightExponent .e t) *
      max 0 (max (fiberNamedProfile .d t u (fiberRayAroot t)) (fiberProfileE t u (fiberRayAroot t))) < 1/10 := by
  have hD := fiber_weight_price_except_E .d (by intro h; cases h) ht
    (by simpa [fiberWeightById,fiberProfileTimeCap] using hcap) hu
    (by simpa [fiberWeightById,fiberRationalProfileRay,fiberRayById,lowMeanFractionReal] using huR)
  have hF := fiber_weight_price_except_E .f (by intro h; cases h) ht
    (by simpa [fiberWeightById,fiberProfileTimeCap] using hcap) hu
    (by simpa [fiberWeightById,fiberRationalProfileRay,fiberRayById,lowMeanFractionReal] using huR)
  simp only [fiberWeightById,lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one] at hD hF
  exact fiber_weight_interpolation_price (fiber_weight_E_interpolation ⟨ht,hcap⟩)
    (le_max_left _ _) hD hF

theorem fiber_weight_price (wid : FiberWeightIdentity) {t u : ℝ}
    (ht : 1 / 3 ≤ t) (hcap : t ≤ fiberProfileTimeCap (fiberWeightById wid).profile)
    (hu : 0 ≤ u)
    (huR : u ≤ lowMeanFractionReal (fiberRayById (fiberRationalProfileRay (fiberWeightById wid).profile)).R) :
    Real.exp (-fiberWeightExponent wid t) *
      max 0 (max (fiberNamedProfile (fiberWeightById wid).profile t u (fiberRayAroot t))
        (fiberProfileE t u (fiberRayAroot t))) < lowMeanFractionReal (fiberWeightById wid).eta_w := by
  by_cases hw : wid = .e
  · subst wid
    simpa [fiberWeightById,fiberProfileTimeCap,fiberRationalProfileRay,fiberRayById,lowMeanFractionReal] using
      fiber_weight_E_price ht (by simpa [fiberWeightById,fiberProfileTimeCap] using hcap) hu
        (by simpa [fiberWeightById,fiberRationalProfileRay,fiberRayById,lowMeanFractionReal] using huR)
  · exact fiber_weight_price_except_E wid hw ht hcap hu huR

end Erdos993Lean.Analytic.V213
