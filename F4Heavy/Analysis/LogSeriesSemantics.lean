module

public import F4Heavy.Finite.LogArithmetic
public import F4Heavy.Analysis.FractionSemantics
public import F4Heavy.Analysis.LogSeriesRemainder

@[expose] public section
set_option autoImplicit false
open Finset

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem fraction_num_ne_zero_of_value (a : Fraction) (h : fractionValue a ≠ 0) : a.num ≠ 0 := by
  intro hn
  apply h
  simp [fractionValue, hn]

theorem list_range_real_sum (n : Nat) (f : Nat → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

def fractionAtanhSum (v : Fraction) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 2) (Fraction.sum ((List.range n).map fun j =>
    Fraction.div (Fraction.pow v (2 * j + 1)) (Fraction.ofInt (2 * j + 1))))

theorem fractionAtanhSum_den_pos (v : Fraction) (n : Nat) (hv : 0 < v.den) :
    0 < (fractionAtanhSum v n).den := by
  apply fraction_mul_den_pos _ _ (by decide)
  apply fraction_sum_den_pos
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  apply fraction_div_den_pos _ _ (pow_pos hv _)
  simp [Fraction.ofInt]
  omega

theorem fractionAtanhSum_value (v : Fraction) (n : Nat) (hv : 0 < v.den) :
    fractionValue (fractionAtanhSum v n) =
      2 * (∑ j ∈ Finset.range n, fractionValue v ^ (2 * j + 1) / (2 * j + 1)) := by
  have hden : ∀ a ∈ (List.range n).map (fun j =>
      Fraction.div (Fraction.pow v (2 * j + 1)) (Fraction.ofInt (2 * j + 1))), 0 < a.den := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    apply fraction_div_den_pos _ _ (pow_pos hv _)
    simp [Fraction.ofInt]
    omega
  unfold fractionAtanhSum
  rw [fractionValue_mul (Fraction.ofInt 2) _ (by decide) (fraction_sum_den_pos _ hden),
    fractionValue_ofInt, fractionValue_sum _ hden, List.map_map]
  have hm : ((List.range n).map (fun j => fractionValue
      (Fraction.div (Fraction.pow v (2 * j + 1)) (Fraction.ofInt (2 * j + 1))))) =
      (List.range n).map (fun j : Nat => fractionValue v ^ (2 * j + 1) / (2 * (j : ℝ) + 1)) := by
    apply List.map_congr_left
    intro j hj
    have hn : (Fraction.ofInt (2 * j + 1)).num ≠ 0 := by simp [Fraction.ofInt]; omega
    rw [fractionValue_div _ _ (pow_pos hv _) hn, fractionValue_pow, fractionValue_ofInt]
    push_cast
    rfl
  simp only [Function.comp_def, Int.cast_ofNat]
  rw [hm, list_range_real_sum]

def logFractionArgument (z : Fraction) : Fraction :=
  Fraction.div (Fraction.sub z Fraction.one) (Fraction.add z Fraction.one)

theorem logFractionArgument_properties (z : Fraction) (hz : 0 < z.den) (hz1 : 1 ≤ fractionValue z) :
    0 < (logFractionArgument z).den ∧
    fractionValue (logFractionArgument z) = (fractionValue z - 1) / (fractionValue z + 1) ∧
    0 ≤ fractionValue (logFractionArgument z) ∧ fractionValue (logFractionArgument z) < 1 := by
  have hsub := fraction_sub_den_pos z Fraction.one hz (by decide)
  have hadd := fraction_add_den_pos z Fraction.one hz (by decide)
  have hvadd : fractionValue (Fraction.add z Fraction.one) = fractionValue z + 1 := by
    rw [fractionValue_add z Fraction.one hz (by decide), fractionValue_one]
  have hn := fraction_num_ne_zero_of_value (Fraction.add z Fraction.one)
    (by rw [hvadd]; linarith)
  have hval : fractionValue (logFractionArgument z) = (fractionValue z - 1) / (fractionValue z + 1) := by
    rw [logFractionArgument, fractionValue_div _ _ hsub hn,
      fractionValue_sub z Fraction.one hz (by decide), fractionValue_one, hvadd]
  have hd : 0 < fractionValue z + 1 := by linarith
  refine ⟨fraction_div_den_pos _ _ hsub hn, hval, ?_, ?_⟩
  · rw [hval]
    exact div_nonneg (by linarith) hd.le
  · rw [hval]
    exact (div_lt_one hd).2 (by linarith)

theorem logFractionArgument_ratio (z : Fraction) (hz : 0 < z.den) (hz1 : 1 ≤ fractionValue z) :
    (1 + fractionValue (logFractionArgument z)) / (1 - fractionValue (logFractionArgument z)) =
      fractionValue z := by
  rw [(logFractionArgument_properties z hz hz1).2.1]
  have hd : fractionValue z + 1 ≠ 0 := by linarith
  field_simp
  ring

def fractionAtanhRemainder (v : Fraction) : Fraction :=
  Fraction.div (Fraction.mul (Fraction.ofInt 2) (Fraction.pow v 65))
    (Fraction.mul (Fraction.ofInt 65) (Fraction.sub Fraction.one (Fraction.mul v v)))

theorem fractionAtanhRemainder_properties (v : Fraction) (hv : 0 < v.den)
    (hv0 : 0 ≤ fractionValue v) (hv1 : fractionValue v < 1) :
    0 < (fractionAtanhRemainder v).den ∧
    fractionValue (fractionAtanhRemainder v) =
      2 * fractionValue v ^ 65 / (65 * (1 - fractionValue v ^ 2)) := by
  have hvv := fraction_mul_den_pos v v hv hv
  have hsub := fraction_sub_den_pos Fraction.one _ (by decide) hvv
  have hvalsub : fractionValue (Fraction.sub Fraction.one (Fraction.mul v v)) =
      1 - fractionValue v ^ 2 := by
    rw [fractionValue_sub Fraction.one _ (by decide) hvv, fractionValue_one,
      fractionValue_mul v v hv hv, pow_two]
  have hvalden : fractionValue (Fraction.mul (Fraction.ofInt 65)
      (Fraction.sub Fraction.one (Fraction.mul v v))) = 65 * (1 - fractionValue v ^ 2) := by
    rw [fractionValue_mul (Fraction.ofInt 65) _ (by decide) hsub, fractionValue_ofInt, hvalsub]
    norm_num
  have hgap : 0 < 1 - fractionValue v ^ 2 := by
    have h := mul_pos (sub_pos.mpr hv1) (show 0 < 1 + fractionValue v by linarith)
    nlinarith only [h]
  have hn := fraction_num_ne_zero_of_value
    (Fraction.mul (Fraction.ofInt 65) (Fraction.sub Fraction.one (Fraction.mul v v)))
    (by rw [hvalden]; positivity)
  have hnum := fraction_mul_den_pos (Fraction.ofInt 2) (Fraction.pow v 65) (by decide) (pow_pos hv 65)
  refine ⟨fraction_div_den_pos _ _ hnum hn, ?_⟩
  unfold fractionAtanhRemainder
  rw [fractionValue_div _ _ hnum hn,
    fractionValue_mul (Fraction.ofInt 2) (Fraction.pow v 65) (by decide) (pow_pos hv 65),
    fractionValue_ofInt, fractionValue_pow, hvalden]
  norm_num

theorem smallLogSeries_den_pos (z : Fraction) (hz : 0 < z.den) (hz1 : 1 ≤ fractionValue z) :
    0 < (smallLogSeries z).1.den ∧ 0 < (smallLogSeries z).2.den := by
  have hv := logFractionArgument_properties z hz hz1
  have hl := fractionAtanhSum_den_pos (logFractionArgument z) 32 hv.1
  have hr := fractionAtanhRemainder_properties (logFractionArgument z) hv.1 hv.2.2.1 hv.2.2.2
  exact ⟨hl, fraction_add_den_pos _ _ hl hr.1⟩

theorem smallLogSeries_sound (z : Fraction) (hz : 0 < z.den) (hz1 : 1 ≤ fractionValue z) :
    fractionValue (smallLogSeries z).1 ≤ Real.log (fractionValue z) ∧
      Real.log (fractionValue z) ≤ fractionValue (smallLogSeries z).2 := by
  have hv := logFractionArgument_properties z hz hz1
  have hl := fractionAtanhSum_den_pos (logFractionArgument z) 32 hv.1
  have hr := fractionAtanhRemainder_properties (logFractionArgument z) hv.1 hv.2.2.1 hv.2.2.2
  have hlog := log_series_enclosure 32 (fractionValue (logFractionArgument z)) hv.2.2.1 hv.2.2.2
  rw [logFractionArgument_ratio z hz hz1] at hlog
  change fractionValue (fractionAtanhSum (logFractionArgument z) 32) ≤ _ ∧
    _ ≤ fractionValue (Fraction.add (fractionAtanhSum (logFractionArgument z) 32)
      (fractionAtanhRemainder (logFractionArgument z)))
  rw [fractionValue_add _ _ hl hr.1, fractionAtanhSum_value _ 32 hv.1, hr.2]
  convert hlog using 1
  norm_num

def scaledLogSeries (t : Fraction) (k : Nat) : Fraction × Fraction :=
  (Fraction.add (smallLogSeries t).1
    (Fraction.mul (Fraction.ofInt k) (smallLogSeries (Fraction.ofInt 2)).1),
   Fraction.add (smallLogSeries t).2
    (Fraction.mul (Fraction.ofInt k) (smallLogSeries (Fraction.ofInt 2)).2))

theorem scaledLogSeries_sound (t : Fraction) (k : Nat) (ht : 0 < t.den) (ht1 : 1 ≤ fractionValue t) :
    fractionValue (scaledLogSeries t k).1 ≤ Real.log (fractionValue t) + (k : ℝ) * Real.log 2 ∧
    Real.log (fractionValue t) + (k : ℝ) * Real.log 2 ≤ fractionValue (scaledLogSeries t k).2 := by
  have htwo : (1 : ℝ) ≤ fractionValue (Fraction.ofInt 2) := by rw [fractionValue_ofInt]; norm_num
  have htd := smallLogSeries_den_pos t ht ht1
  have h2d := smallLogSeries_den_pos (Fraction.ofInt 2) (by decide) htwo
  have htt := smallLogSeries_sound t ht ht1
  have h22 := smallLogSeries_sound (Fraction.ofInt 2) (by decide) htwo
  rw [fractionValue_ofInt] at h22
  norm_num only [Int.cast_ofNat] at h22
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · change fractionValue (Fraction.add (smallLogSeries t).1
      (Fraction.mul (Fraction.ofInt k) (smallLogSeries (Fraction.ofInt 2)).1)) ≤ _
    rw [fractionValue_add _ _ htd.1 (fraction_mul_den_pos _ _ Nat.zero_lt_one h2d.1),
      fractionValue_mul (Fraction.ofInt k) _ Nat.zero_lt_one h2d.1, fractionValue_ofInt, Int.cast_natCast]
    exact add_le_add htt.1 (mul_le_mul_of_nonneg_left h22.1 hk)
  · change _ ≤ fractionValue (Fraction.add (smallLogSeries t).2
      (Fraction.mul (Fraction.ofInt k) (smallLogSeries (Fraction.ofInt 2)).2))
    rw [fractionValue_add _ _ htd.2 (fraction_mul_den_pos _ _ Nat.zero_lt_one h2d.2),
      fractionValue_mul (Fraction.ofInt k) _ Nat.zero_lt_one h2d.2, fractionValue_ofInt, Int.cast_natCast]
    exact add_le_add htt.2 (mul_le_mul_of_nonneg_left h22.2 hk)

theorem logSeriesCheck_sound (z lo hi : Fraction) (k : Nat)
    (hcheck : logSeriesCheck z lo hi k = true) :
    fractionValue lo ≤ Real.log (fractionValue z) ∧ Real.log (fractionValue z) ≤ fractionValue hi := by
  let inverted := Fraction.lt z Fraction.one
  let w := if inverted then Fraction.inv z else z
  let t := Fraction.div w (Fraction.ofInt ((2 : Int) ^ k))
  have hc : Fraction.positive z = true ∧ Fraction.le Fraction.one t = true ∧
      Fraction.lt t (Fraction.ofInt 2) = true ∧
      (if inverted then
        Fraction.eq lo (Fraction.neg (scaledLogSeries t k).2) &&
          Fraction.eq hi (Fraction.neg (scaledLogSeries t k).1)
       else Fraction.eq lo (scaledLogSeries t k).1 && Fraction.eq hi (scaledLogSeries t k).2) = true := by
    simpa only [logSeriesCheck, scaledLogSeries, inverted, w, t, Bool.and_eq_true, and_assoc] using hcheck
  have hz : 0 < z.den ∧ 0 < z.num := by simpa [Fraction.positive] using hc.1
  have hzv := fraction_positive_sound z hc.1
  have htden : 0 < t.den := by
    have h : 0 < Fraction.one.den ∧ 0 < t.den ∧
        Fraction.one.num * (t.den : Int) ≤ t.num * (Fraction.one.den : Int) := by
      simpa [Fraction.le, and_assoc] using hc.2.1
    exact h.2.1
  have ht1 : 1 ≤ fractionValue t := by
    simpa only [fractionValue_one] using fraction_le_sound Fraction.one t hc.2.1
  have hwd : 0 < w.den := by
    dsimp [w]
    split
    · exact fraction_inv_den_pos z (ne_of_gt hz.2)
    · exact hz.1
  have hwv : 0 < fractionValue w := by
    dsimp [w]
    split
    · rw [fractionValue_inv]
      exact inv_pos.mpr hzv
    · exact hzv
  have htv : fractionValue t = fractionValue w / (2 : ℝ) ^ k := by
    dsimp only [t]
    rw [fractionValue_div w (Fraction.ofInt ((2 : Int) ^ k)) hwd
      (by simp [Fraction.ofInt]), fractionValue_ofInt]
    push_cast
    rfl
  have hlog : Real.log (fractionValue t) + (k : ℝ) * Real.log 2 = Real.log (fractionValue w) := by
    rw [htv, Real.log_div (ne_of_gt hwv) (pow_ne_zero k (by norm_num)), Real.log_pow]
    ring
  have hs := scaledLogSeries_sound t k htden ht1
  rw [hlog] at hs
  by_cases hinv : inverted = true
  · have he : Fraction.eq lo (Fraction.neg (scaledLogSeries t k).2) = true ∧
        Fraction.eq hi (Fraction.neg (scaledLogSeries t k).1) = true := by
      simpa [hinv] using hc.2.2.2
    have hlo := fraction_eq_sound _ _ he.1
    have hhi := fraction_eq_sound _ _ he.2
    rw [fractionValue_neg] at hlo hhi
    have hw : fractionValue w = (fractionValue z)⁻¹ := by simp [w, hinv, fractionValue_inv]
    rw [hw, Real.log_inv] at hs
    constructor <;> linarith only [hlo, hhi, hs.1, hs.2]
  · have he : Fraction.eq lo (scaledLogSeries t k).1 = true ∧
        Fraction.eq hi (scaledLogSeries t k).2 = true := by
      simpa [hinv] using hc.2.2.2
    have hlo := fraction_eq_sound _ _ he.1
    have hhi := fraction_eq_sound _ _ he.2
    have hw : w = z := by simp [w, hinv]
    rw [hw] at hs
    rw [hlo, hhi]
    exact hs

end F4Heavy.Analysis
