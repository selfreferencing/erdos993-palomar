module

public import F4Heavy.Analysis.FractionSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem interval_add {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a+c ≤ x+y ∧ x+y ≤ b+d := ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem interval_neg {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    -b ≤ -x ∧ -x ≤ -a := ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem interval_sub {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a-d ≤ x-y ∧ x-y ≤ b-c := ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

theorem interval_mul_upper {a b c d x y M : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a*c ≤ M) (had : a*d ≤ M) (hbc : b*c ≤ M) (hbd : b*d ≤ M) : x*y ≤ M := by
  rcases le_total 0 x with hx0 | hx0
  · have hxy := mul_le_mul_of_nonneg_left hy.2 hx0
    rcases le_total 0 d with hd0 | hd0
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hd0).trans hbd)
    · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 hd0).trans had)
  · have hxy := mul_le_mul_of_nonpos_left hy.1 hx0
    rcases le_total 0 c with hc0 | hc0
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hc0).trans hbc)
    · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 hc0).trans hac)

theorem interval_mul {a b c d x y L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : L ≤ a*c ∧ L ≤ a*d ∧ L ≤ b*c ∧ L ≤ b*d)
    (hu : a*c ≤ U ∧ a*d ≤ U ∧ b*c ≤ U ∧ b*d ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  refine ⟨?_, interval_mul_upper hx hy hu.1 hu.2.1 hu.2.2.1 hu.2.2.2⟩
  have h := interval_mul_upper (interval_neg hx) hy
    (by simpa only [neg_mul] using neg_le_neg hl.2.2.1)
    (by simpa only [neg_mul] using neg_le_neg hl.2.2.2)
    (by simpa only [neg_mul] using neg_le_neg hl.1)
    (by simpa only [neg_mul] using neg_le_neg hl.2.1)
  simpa only [neg_mul, neg_le_neg_iff] using h

theorem interval_inv_positive {a b x : ℝ} (ha : 0 < a) (hx : a ≤ x ∧ x ≤ b) :
    1/b ≤ 1/x ∧ 1/x ≤ 1/a := by
  have hx0 := ha.trans_le hx.1
  exact ⟨div_le_div_of_nonneg_left (by norm_num) hx0 hx.2,
    div_le_div_of_nonneg_left (by norm_num) ha hx.1⟩

theorem interval_square_upper {a b x U : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : a^2 ≤ U) (hb : b^2 ≤ U) : 0 ≤ x^2 ∧ x^2 ≤ U := by
  refine ⟨sq_nonneg x, ?_⟩
  rcases le_total 0 x with hx0 | hx0
  · exact (pow_le_pow_left₀ hx0 hx.2 2).trans hb
  · have h := pow_le_pow_left₀ (neg_nonneg.mpr hx0) (neg_le_neg hx.1) 2
    simpa only [neg_sq] using h.trans (by simpa only [neg_sq] using ha)

end F4Heavy.Analysis
