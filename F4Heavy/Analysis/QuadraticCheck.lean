module

public import F4Heavy.Analysis.UnivariateBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem quadratic_interval_positive (a b c r x : ℝ) (hxr : |x| ≤ r)
    (hl : 0 < a * r ^ 2 - b * r + c) (hu : 0 < a * r ^ 2 + b * r + c)
    (hi : 0 < a → |b| < 2 * a * r → 0 < 4 * a * c - b ^ 2) :
    0 < a * x ^ 2 + b * x + c := by
  have hx := abs_le.mp hxr
  have hr : 0 ≤ r := (abs_nonneg x).trans hxr
  by_cases ha : 0 < a
  · by_cases hb : |b| < 2 * a * r
    · exact quadratic_positive a b c x ha (hi ha hb)
    · have hb' : 2 * a * r ≤ |b| := le_of_not_gt hb
      by_cases hbp : 0 ≤ b
      · rw [abs_of_nonneg hbp] at hb'
        have hf : 0 ≤ a * (x - r) + b := by
          have hm := mul_nonneg ha.le (show 0 ≤ x + r by linarith)
          nlinarith only [hm, hb']
        have hm := mul_nonneg (show 0 ≤ x + r by linarith) hf
        nlinarith only [hl, hm]
      · rw [abs_of_nonpos (le_of_not_ge hbp)] at hb'
        have hf : a * (x + r) + b ≤ 0 := by
          have hm := mul_nonpos_of_nonneg_of_nonpos ha.le (show x - r ≤ 0 by linarith)
          nlinarith only [hm, hb']
        have hm := mul_nonneg_of_nonpos_of_nonpos (show x - r ≤ 0 by linarith) hf
        nlinarith only [hu, hm]
  · have ha' : a ≤ 0 := le_of_not_gt ha
    have hsq : x ^ 2 - r ^ 2 ≤ 0 := by
      have hm := mul_nonneg (show 0 ≤ r - x by linarith) (show 0 ≤ r + x by linarith)
      nlinarith only [hm]
    have hcurv := mul_nonneg_of_nonpos_of_nonpos ha' hsq
    by_cases hb : 0 ≤ b
    · have hm := mul_nonneg hb (show 0 ≤ x + r by linarith)
      nlinarith only [hl, hm, hcurv]
    · have hm := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hb) (show x - r ≤ 0 by linarith)
      nlinarith only [hu, hm, hcurv]

theorem fractionCoeff_den_pos (p : List Fraction) (i : Nat) (hp : ∀ a ∈ p, 0 < a.den) :
    0 < (p[i]?.getD Fraction.zero).den := by
  cases h : p[i]? with
  | none => exact Nat.zero_lt_one
  | some a => exact hp a (List.mem_of_getElem? h)

theorem realHorner_split_three (p : List Fraction) (x : ℝ) :
    realHorner (p.map fractionValue) x = fractionValue (p[0]?.getD Fraction.zero) +
      fractionValue (p[1]?.getD Fraction.zero) * x +
      fractionValue (p[2]?.getD Fraction.zero) * x ^ 2 +
      x ^ 3 * realHorner ((p.drop 3).map fractionValue) x := by
  cases p with
  | nil => simp [realHorner, fractionValue_zero]
  | cons a p =>
    cases p with
    | nil => simp [realHorner, fractionValue_zero]
    | cons b p =>
      cases p with
      | nil => simp [realHorner, fractionValue_zero]; ring
      | cons c p => simp [realHorner_cons]; ring

theorem quadraticOperands_valid (p : List Fraction) (r : Fraction)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) :
    0 < (quadraticOperands p r).1.den ∧
      0 < (quadraticOperands p r).2.1.den ∧ 0 < (quadraticOperands p r).2.2.den := by
  exact ⟨fraction_sub_den_pos _ _ (fractionCoeff_den_pos p 2 hp)
    (fraction_mul_den_pos _ _ hr (tailNorm_den_pos p r 3 hp hr)),
    fractionCoeff_den_pos p 1 hp,
    fraction_mul_den_pos _ _ (by decide) (fractionCoeff_den_pos p 0 hp)⟩

theorem quadraticOperands_value (p : List Fraction) (r : Fraction)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) :
    fractionValue (quadraticOperands p r).1 = fractionValue (p[2]?.getD Fraction.zero) -
      fractionValue r * realHorner ((p.drop 3).map fun a => |fractionValue a|) (fractionValue r) ∧
    fractionValue (quadraticOperands p r).2.1 = fractionValue (p[1]?.getD Fraction.zero) ∧
    fractionValue (quadraticOperands p r).2.2 = (199 / 200 : ℝ) * fractionValue (p[0]?.getD Fraction.zero) := by
  have ht := tailNorm_den_pos p r 3 hp hr
  refine ⟨?_, rfl, ?_⟩
  · change fractionValue (Fraction.sub (p[2]?.getD Fraction.zero) (Fraction.mul r (tailNorm p r 3))) = _
    rw [fractionValue_sub _ (Fraction.mul r (tailNorm p r 3)) (fractionCoeff_den_pos p 2 hp)
      (fraction_mul_den_pos _ _ hr ht), fractionValue_mul r _ hr ht, tailNorm_value p r 3 hp hr]
  · change fractionValue (Fraction.mul ⟨199, 200⟩ (p[0]?.getD Fraction.zero)) = _
    rw [fractionValue_mul ⟨199, 200⟩ _ (by decide) (fractionCoeff_den_pos p 0 hp)]
    have hc : fractionValue ⟨199, 200⟩ = (199 / 200 : ℝ) := by norm_num [fractionValue]
    rw [hc]

theorem quadraticOperands_lower (p : List Fraction) (r : Fraction) (x : ℝ)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) (hxr : |x| ≤ fractionValue r)
    (h0 : 0 ≤ fractionValue (p[0]?.getD Fraction.zero)) :
    fractionValue (quadraticOperands p r).1 * x ^ 2 +
      fractionValue (quadraticOperands p r).2.1 * x + fractionValue (quadraticOperands p r).2.2 ≤
        realHorner (p.map fractionValue) x := by
  have hv := quadraticOperands_value p r hp hr
  rw [hv.1, hv.2.1, hv.2.2, realHorner_split_three]
  have htail := realHorner_centered_lower 0 ((p.drop 3).map fractionValue) x (fractionValue r) hxr
  simp only [realHorner_cons, zero_add, zero_sub, List.map_map, Function.comp_def] at htail
  have hm := mul_le_mul_of_nonneg_right htail (sq_nonneg x)
  nlinarith only [hm, h0]

theorem fraction_positive_of_value (a : Fraction) (hd : 0 < a.den) (hv : 0 < fractionValue a) :
    Fraction.positive a = true := by
  have hdR : (0 : ℝ) < a.den := by exact_mod_cast hd
  have hnR : (0 : ℝ) < a.num := (div_pos_iff_of_pos_right hdR).mp hv
  have hn : 0 < a.num := by exact_mod_cast hnR
  simp [Fraction.positive, hd, hn]

theorem fraction_quadratic_endpoint (a b c r : Fraction) (ha : 0 < a.den)
    (hb : 0 < b.den) (hc : 0 < c.den) (hr : 0 < r.den) :
    fractionValue (Fraction.add (Fraction.sub (Fraction.mul a (Fraction.pow r 2))
      (Fraction.mul b r)) c) =
      fractionValue a * fractionValue r ^ 2 - fractionValue b * fractionValue r + fractionValue c ∧
    fractionValue (Fraction.add (Fraction.add (Fraction.mul a (Fraction.pow r 2))
      (Fraction.mul b r)) c) =
      fractionValue a * fractionValue r ^ 2 + fractionValue b * fractionValue r + fractionValue c := by
  have har := fraction_mul_den_pos a (Fraction.pow r 2) ha (pow_pos hr 2)
  have hbr := fraction_mul_den_pos b r hb hr
  have hvalar := fractionValue_mul a (Fraction.pow r 2) ha (pow_pos hr 2)
  rw [fractionValue_pow] at hvalar
  constructor
  · rw [fractionValue_add _ c (fraction_sub_den_pos _ _ har hbr) hc,
      fractionValue_sub _ _ har hbr, hvalar, fractionValue_mul b r hb hr]
  · rw [fractionValue_add _ c (fraction_add_den_pos _ _ har hbr) hc,
      fractionValue_add _ _ har hbr, hvalar, fractionValue_mul b r hb hr]

theorem fraction_quadratic_discriminant (a b c : Fraction)
    (ha : 0 < a.den) (hb : 0 < b.den) (hc : 0 < c.den) :
    fractionValue (Fraction.sub (Fraction.mul (Fraction.ofInt 4) (Fraction.mul a c))
      (Fraction.pow b 2)) = 4 * fractionValue a * fractionValue c - fractionValue b ^ 2 := by
  have hac := fraction_mul_den_pos a c ha hc
  rw [fractionValue_sub _ (Fraction.pow b 2) (fraction_mul_den_pos _ _ (by decide) hac)
    (pow_pos hb 2), fractionValue_mul (Fraction.ofInt 4) _ (by decide) hac,
    fractionValue_ofInt, fractionValue_mul a c ha hc, fractionValue_pow]
  norm_num
  ring

theorem quadraticCheck_sound (p : List Fraction) (r : Fraction) (x : ℝ)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) (hxr : |x| ≤ fractionValue r)
    (hcheck : quadraticCheck p r = true) : 0 < realHorner (p.map fractionValue) x := by
  let a := (quadraticOperands p r).1
  let b := (quadraticOperands p r).2.1
  let c := (quadraticOperands p r).2.2
  have hvalid := quadraticOperands_valid p r hp hr
  have ha : 0 < a.den := hvalid.1
  have hb : 0 < b.den := hvalid.2.1
  have hc : 0 < c.den := hvalid.2.2
  have hchecks : Fraction.positive (p[0]?.getD Fraction.zero) = true ∧
      Fraction.positive (Fraction.add (Fraction.sub (Fraction.mul a (Fraction.pow r 2))
        (Fraction.mul b r)) c) = true ∧
      Fraction.positive (Fraction.add (Fraction.add (Fraction.mul a (Fraction.pow r 2))
        (Fraction.mul b r)) c) = true ∧
      (!(Fraction.positive a && Fraction.lt (Fraction.abs b)
        (Fraction.mul (Fraction.ofInt 2) (Fraction.mul a r))) ||
        Fraction.positive (Fraction.sub (Fraction.mul (Fraction.ofInt 4) (Fraction.mul a c))
          (Fraction.pow b 2))) = true := by
    simpa only [quadraticCheck, a, b, c, Bool.and_eq_true, and_assoc] using hcheck
  have hleft := fraction_positive_sound _ hchecks.2.1
  have hright := fraction_positive_sound _ hchecks.2.2.1
  have hev := fraction_quadratic_endpoint a b c r ha hb hc hr
  rw [hev.1] at hleft
  rw [hev.2] at hright
  have hquad : 0 < fractionValue a * x ^ 2 + fractionValue b * x + fractionValue c := by
    apply quadratic_interval_positive _ _ _ _ x hxr hleft hright
    intro hap hbp
    have hpa := fraction_positive_of_value a ha hap
    have har := fraction_mul_den_pos a r ha hr
    have htw : fractionValue (Fraction.mul (Fraction.ofInt 2) (Fraction.mul a r)) =
        2 * fractionValue a * fractionValue r := by
      rw [fractionValue_mul (Fraction.ofInt 2) _ (by decide) har,
        fractionValue_ofInt, fractionValue_mul a r ha hr]
      norm_num
      ring
    have hlt : Fraction.lt (Fraction.abs b) (Fraction.mul (Fraction.ofInt 2) (Fraction.mul a r)) = true := by
      apply fraction_lt_complete (Fraction.abs b) (Fraction.mul (Fraction.ofInt 2) (Fraction.mul a r))
        hb (fraction_mul_den_pos (Fraction.ofInt 2) _ (by decide) har)
      rw [fractionValue_abs, htw]
      exact hbp
    have hdisc : Fraction.positive (Fraction.sub (Fraction.mul (Fraction.ofInt 4) (Fraction.mul a c))
        (Fraction.pow b 2)) = true := by
      simpa [hpa, hlt] using hchecks.2.2.2
    have hpos := fraction_positive_sound _ hdisc
    rw [fraction_quadratic_discriminant a b c ha hb hc] at hpos
    exact hpos
  exact lt_of_lt_of_le hquad (quadraticOperands_lower p r x hp hr hxr
    (fraction_positive_sound _ hchecks.1).le)

end F4Heavy.Analysis
