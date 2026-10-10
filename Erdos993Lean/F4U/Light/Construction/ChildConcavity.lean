module

public import Erdos993Lean.F4U.Light.Construction.IntegralH
public import Erdos993Lean.F4U.Light.Construction.FixedLogs
public import Erdos993Lean.F4U.Light.Construction.Definitions
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Tactic.Positivity

/-! Concavity of the literal child-response function follows by integrating
pointwise real-power concavity. The fixed logarithm comparisons then supply
the manuscript's two endpoint chords; no support or positivity input is assumed. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section
open MeasureTheory Set

 theorem childH_intervalIntegrable {u : ℝ} (hu1 : u < 1) :
    IntervalIntegrable (fun t : ℝ => (1-u)^t) volume 0 1 := by
  exact (Real.continuous_const_rpow (by linarith : 1-u ≠ 0)).intervalIntegrable 0 1

 theorem concaveOn_childH : ConcaveOn ℝ (Ico 0 1) F4Unified.childH := by
  refine ⟨convex_Ico 0 1, ?_⟩
  intro u hu v hv a b ha hb hab
  have hz := (convex_Ico (0 : ℝ) 1) hu hv ha hb hab
  simp only [smul_eq_mul] at hz ⊢
  have hiu := childH_intervalIntegrable hu.2
  have hiv := childH_intervalIntegrable hv.2
  have hiz := childH_intervalIntegrable hz.2
  rw [childH_eq_integral hu.1 hu.2, childH_eq_integral hv.1 hv.2,
    childH_eq_integral hz.1 hz.2]
  calc
    a * (∫ t : ℝ in (0 : ℝ)..1, (1-u)^t) +
      b * (∫ t : ℝ in (0 : ℝ)..1, (1-v)^t) =
      ∫ t : ℝ in (0 : ℝ)..1, a*(1-u)^t+b*(1-v)^t := by
        rw [intervalIntegral.integral_add (hiu.const_mul a) (hiv.const_mul b)]
        simp only [intervalIntegral.integral_const_mul]
    _ ≤ ∫ t : ℝ in (0 : ℝ)..1, (1-(a*u+b*v))^t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((hiu.const_mul a).add (hiv.const_mul b)) hiz
      intro t ht
      have hpow := (Real.concaveOn_rpow ht.1 ht.2).2
        (show 1-u ∈ Ici (0 : ℝ) from sub_nonneg.mpr hu.2.le)
        (show 1-v ∈ Ici (0 : ℝ) from sub_nonneg.mpr hv.2.le) ha hb hab
      simp only [smul_eq_mul] at hpow
      have hbase : 1-(a*u+b*v)=a*(1-u)+b*(1-v) := by nlinarith [hab]
      simpa only [hbase] using hpow

 theorem childH_chord_from_zero {b u : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hu0 : 0 ≤ u) (hub : u ≤ b) :
    (1-u/b)+(u/b)*F4Unified.childH b ≤ F4Unified.childH u := by
  have hw0 : 0 ≤ u/b := div_nonneg hu0 hb0.le
  have hw1 : u/b ≤ 1 := (div_le_one hb0).2 hub
  have hcombo : (1-u/b)*0+(u/b)*b = u := by
    rw [mul_zero, zero_add, div_mul_cancel₀ u hb0.ne']
  have hh := concaveOn_childH.2 (by norm_num : (0 : ℝ) ∈ Ico 0 1)
    (show b ∈ Ico 0 1 from ⟨hb0.le,hb1⟩)
    (by linarith : 0 ≤ 1-u/b) hw0 (by ring : (1-u/b)+u/b=1)
  have hh0 : F4Unified.childH 0 = 1 := by simp [F4Unified.childH]
  simpa only [smul_eq_mul, hcombo, hh0, mul_one] using hh

 theorem childH_8_13_lower : (25 : ℝ)/39 < F4Unified.childH (8/13) := by
  have hlo : 0 < Real.log ((13 : ℝ)/5) := Real.log_pos (by norm_num)
  have heq : F4Unified.childH ((8 : ℝ)/13) = (8/13)/Real.log (13/5) := by
    norm_num [F4Unified.childH, F4Unified.phi]
    rw [show (5 : ℝ)/13 = ((13 : ℝ)/5)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [heq, lt_div_iff₀ hlo]
  nlinarith [log_13_5_lt_24_25]

 theorem childH_7_10_lower : (29 : ℝ)/50 < F4Unified.childH (7/10) := by
  have hlo : 0 < Real.log ((10 : ℝ)/3) := Real.log_pos (by norm_num)
  have heq : F4Unified.childH ((7 : ℝ)/10) = (7/10)/Real.log (10/3) := by
    norm_num [F4Unified.childH, F4Unified.phi]
    rw [show (3 : ℝ)/10 = ((10 : ℝ)/3)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [heq, lt_div_iff₀ hlo]
  nlinarith [log_10_3_lt_35_29]

 theorem childH_lower_D_E {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 8/13) :
    1-(7/12 : ℝ)*u ≤ F4Unified.childH u := by
  have hc := childH_chord_from_zero (b := (8 : ℝ)/13) (by norm_num) (by norm_num) hu0 hu1
  have hm := mul_le_mul_of_nonneg_left (le_of_lt childH_8_13_lower)
    (show 0 ≤ u/((8 : ℝ)/13) by positivity)
  norm_num at hc hm
  nlinarith [childH_8_13_lower]

 theorem childH_lower_H {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 7/10) :
    1-(3/5 : ℝ)*u ≤ F4Unified.childH u := by
  have hc := childH_chord_from_zero (b := (7 : ℝ)/10) (by norm_num) (by norm_num) hu0 hu1
  have hm := mul_le_mul_of_nonneg_left (le_of_lt childH_7_10_lower)
    (show 0 ≤ u/((7 : ℝ)/10) by positivity)
  norm_num at hc hm
  nlinarith [childH_7_10_lower]

#print axioms childH_intervalIntegrable
#print axioms concaveOn_childH
#print axioms childH_chord_from_zero
#print axioms childH_8_13_lower
#print axioms childH_7_10_lower
#print axioms childH_lower_D_E
#print axioms childH_lower_H

end
end F4Unified.LightConstruction
