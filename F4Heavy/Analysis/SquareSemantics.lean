module

public import F4Heavy.Analysis.DensePolynomialSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem realHorner_positive_of_checks (p : List Fraction) (x : ℝ) (hne : p ≠ [])
    (hx : 0 ≤ x) (hp : ∀ c ∈ p, Fraction.positive c = true) :
    0 < realHorner (p.map fractionValue) x := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons a p =>
    apply realHorner_positive _ _ x (fraction_positive_sound a (hp a (by simp))) hx
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact (fraction_positive_sound b (hp b (by simp [hb]))).le

theorem squareReconstruction_sound (p quot : List Fraction) (center a0 a1 : Fraction) (x : ℝ)
    (hq : ∀ c ∈ quot, 0 < c.den) (hc : 0 < center.den) (h0 : 0 < a0.den) (h1 : 0 < a1.den)
    (hcheck : squareReconstruction p quot center a0 a1 = true) :
    realHorner (p.map fractionValue) x = fractionValue a0 + fractionValue a1 * (x-fractionValue center) +
      (x-fractionValue center)^2 * realHorner (quot.map fractionValue) x := by
  let sq := [Fraction.pow center 2, Fraction.neg (Fraction.mul (Fraction.ofInt 2) center), Fraction.one]
  let aff := [Fraction.sub a0 (Fraction.mul center a1), a1]
  have htwo : 0 < (Fraction.mul (Fraction.ofInt 2) center).den :=
    fraction_mul_den_pos _ _ Nat.zero_lt_one hc
  have hs : ∀ c ∈ sq, 0 < c.den := by
    intro c h
    simp only [sq, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact pow_pos hc 2
    · exact htwo
    · exact Nat.zero_lt_one
  have ha : ∀ c ∈ aff, 0 < c.den := by
    intro c h
    simp only [aff, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact fraction_sub_den_pos _ _ h0 (fraction_mul_den_pos _ _ hc h1)
    · exact h1
  have heq : Fraction.allEq p (polynomialAdd aff (polynomialMul sq quot)) = true := by
    simp only [squareReconstruction, Bool.and_eq_true] at hcheck
    tauto
  have hv := congrArg (fun z => realHorner z x) (fraction_allEq_sound _ _ heq)
  rw [polynomialAdd_value aff _ x ha (polynomialMul_den_pos sq quot hs hq),
    polynomialMul_value sq quot x hs hq] at hv
  simp only [aff, sq, List.map_cons, List.map_nil, realHorner_cons, realHorner_nil,
    mul_zero, add_zero, fractionValue_pow, fractionValue_neg, fractionValue_one] at hv
  rw [fractionValue_sub a0 _ h0 (fraction_mul_den_pos _ _ hc h1),
    fractionValue_mul center a1 hc h1,
    fractionValue_mul (Fraction.ofInt 2) center Nat.zero_lt_one hc, fractionValue_ofInt] at hv
  norm_num only [Int.cast_ofNat, mul_one] at hv
  rw [hv]
  ring

theorem squareDiscriminant_value (quot : List Fraction) (a0 a1 : Fraction)
    (hq : ∀ c ∈ quot, 0 < c.den) (h0 : 0 < a0.den) (h1 : 0 < a1.den) :
    fractionValue (squareDiscriminant quot a0 a1) =
      4 * fractionValue (quot[0]?.getD Fraction.zero) * fractionValue a0 - fractionValue a1^2 := by
  have hh := fractionGet_den_pos quot 0 hq
  unfold squareDiscriminant
  rw [fractionValue_sub _ _
      (fraction_mul_den_pos _ _ Nat.zero_lt_one (fraction_mul_den_pos _ _ hh h0)) (pow_pos h1 2),
    fractionValue_mul _ _ Nat.zero_lt_one (fraction_mul_den_pos _ _ hh h0),
    fractionValue_mul _ _ hh h0, fractionValue_ofInt, fractionValue_pow]
  push_cast
  ring

theorem square_expression_positive (a0 a1 c q0 q x : ℝ)
    (hq0 : 0 < q0) (hqq : q0 ≤ q) (hdisc : 0 < 4*q0*a0-a1^2) :
    0 < a0+a1*(x-c)+(x-c)^2*q := by
  have hquad := quadratic_positive q0 a1 a0 (x-c) hq0 hdisc
  have hrem := mul_nonneg (sq_nonneg (x-c)) (sub_nonneg.mpr hqq)
  nlinarith only [hquad, hrem]

theorem squareReconstruction_positive (p quot : List Fraction) (center a0 a1 : Fraction) (x : ℝ)
    (hq : ∀ c ∈ quot, 0 < c.den) (hc : 0 < center.den) (h0 : 0 < a0.den) (h1 : 0 < a1.den)
    (hne : quot ≠ []) (hx : 0 ≤ x)
    (hpos : ∀ c ∈ quot, Fraction.positive c = true)
    (hdisc : Fraction.positive (squareDiscriminant quot a0 a1) = true)
    (hcheck : squareReconstruction p quot center a0 a1 = true) :
    0 < realHorner (p.map fractionValue) x := by
  rw [squareReconstruction_sound p quot center a0 a1 x hq hc h0 h1 hcheck]
  have hd := fraction_positive_sound _ hdisc
  rw [squareDiscriminant_value quot a0 a1 hq h0 h1] at hd
  have hq0 : 0 < fractionValue (quot[0]?.getD Fraction.zero) := by
    cases quot with
    | nil => exact (hne rfl).elim
    | cons a q => exact fraction_positive_sound a (hpos a (by simp))
  apply square_expression_positive _ _ _ _ _ x hq0 _ hd
  cases quot with
  | nil => simp [fractionValue_zero, realHorner]
  | cons a q =>
    apply realHorner_constant_lower _ _ x hx
    intro c hc'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
    exact (fraction_positive_sound b (hpos b (by simp [hb]))).le

end F4Heavy.Analysis
