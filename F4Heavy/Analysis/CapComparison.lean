module

public import F4Heavy.Analysis.CapAttainment

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
noncomputable section

theorem cap_point_response_coordinates (a b c d delta J h y : ℝ) (hh : h ≠ 0) :
    a + capPointValue b c d delta h (1 - y / h) (h / J) =
      responsePolynomial a b c d delta J h y := by
  unfold capPointValue responsePolynomial
  field_simp
  <;> ring

theorem cap_point_stationary_coordinates (c d delta J h y : ℝ) (hh : h ≠ 0)
    (hs : c + 2 * d * y - 2 * delta / J * (h - y) = 0) :
    c + 2 * d * (h * (1 - (1 - y / h))) -
      2 * delta * (h / J) * (1 - y / h) = 0 := by
  have hid : c + 2 * d * (h * (1 - (1 - y / h))) -
      2 * delta * (h / J) * (1 - y / h) =
      c + 2 * d * y - 2 * delta / J * (h - y) := by
    field_simp
    <;> ring
  exact hid.trans hs

/-- Compare two stationary responses using only the two scalar increments. -/
theorem cap_stationary_response_gain (a b c d delta J1 J2 h1 h2 y1 y2 eps : ℝ)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (ht : h2 ≤ h1)
    (hJ1 : 0 < J1) (hJ2 : 0 < J2) (hd : 0 ≤ delta)
    (hy10 : 0 ≤ y1) (hy11 : y1 ≤ h1) (hy20 : 0 ≤ y2) (hy21 : y2 ≤ h2)
    (hs1 : c + 2 * d * y1 - 2 * delta / J1 * (h1 - y1) = 0)
    (hs2 : c + 2 * d * y2 - 2 * delta / J2 * (h2 - y2) = 0)
    (hb : eps * (h1 - h2) ≤ b * (h1 - h2))
    (hw : eps * (h1 - h2) ≤ b * (h1 - h2) + delta * (h1 ^ 2 / J1 - h2 ^ 2 / J2)) :
    eps * (h1 - h2) ≤ responsePolynomial a b c d delta J1 h1 y1 -
      responsePolynomial a b c d delta J2 h2 y2 := by
  have hz1 : 0 ≤ 1 - y1 / h1 ∧ 1 - y1 / h1 ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr ((div_le_one hh1).mpr hy11)
    · linarith only [div_nonneg hy10 hh1.le]
  have hz2 : 0 ≤ 1 - y2 / h2 ∧ 1 - y2 / h2 ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr ((div_le_one hh2).mpr hy21)
    · linarith only [div_nonneg hy20 hh2.le]
  have hw' : eps * (h1 - h2) ≤ b * (h1 - h2) +
      delta * (h1 * (h1 / J1) - h2 * (h2 / J2)) := by
    convert hw using 1 <;> ring
  have hg := cap_stationary_two_point_gain b c d delta h1 h2 (1 - y1 / h1)
    (1 - y2 / h2) (h1 / J1) (h2 / J2) eps ht hd
    (div_nonneg hh1.le hJ1.le) (div_nonneg hh2.le hJ2.le) hz1.1 hz1.2 hz2.1 hz2.2
    (cap_point_stationary_coordinates c d delta J1 h1 y1 (ne_of_gt hh1) hs1)
    (cap_point_stationary_coordinates c d delta J2 h2 y2 (ne_of_gt hh2) hs2) hb hw'
  rw [← cap_point_response_coordinates a b c d delta J1 h1 y1 (ne_of_gt hh1),
    ← cap_point_response_coordinates a b c d delta J2 h2 y2 (ne_of_gt hh2)]
  linarith only [hg]

/-- The comparison holds for every response at the first child. -/
theorem cap_attained_response_gain (a b c d delta J1 J2 h1 h2 y eps : ℝ)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (ht : h2 ≤ h1)
    (hJ1 : 0 < J1) (hJ2 : 0 < J2) (hd : 0 ≤ delta)
    (hK1 : 0 < 2 * delta * h1 - c * J1) (hK2 : 0 < 2 * delta * h2 - c * J2)
    (hr1 : 0 < c + 2 * d * h1) (hr2 : 0 < c + 2 * d * h2)
    (hb : eps * (h1 - h2) ≤ b * (h1 - h2))
    (hw : eps * (h1 - h2) ≤ b * (h1 - h2) + delta * (h1 ^ 2 / J1 - h2 ^ 2 / J2)) :
    responsePolynomial a b c d delta J2 h2 (capResponse c d delta J2 h2) +
      eps * (h1 - h2) ≤ responsePolynomial a b c d delta J1 h1 y := by
  have hG1 := cap_response_curvature c d delta J1 h1 hh1 hJ1 hK1 hr1
  have hG2 := cap_response_curvature c d delta J2 h2 hh2 hJ2 hK2 hr2
  have hy1 := cap_response_interior c d delta J1 h1 hh1 hJ1 hK1 hr1
  have hy2 := cap_response_interior c d delta J2 h2 hh2 hJ2 hK2 hr2
  have hg := cap_stationary_response_gain a b c d delta J1 J2 h1 h2
    (capResponse c d delta J1 h1) (capResponse c d delta J2 h2) eps
    hh1 hh2 ht hJ1 hJ2 hd hy1.1.le hy1.2.le hy2.1.le hy2.2.le
    (cap_response_stationary c d delta J1 h1 (ne_of_gt hJ1) (ne_of_gt hG1))
    (cap_response_stationary c d delta J2 h2 (ne_of_gt hJ2) (ne_of_gt hG2)) hb hw
  have hl := cap_response_attained_lower a b c d delta J1 h1 y hJ1 hG1
  linarith only [hg, hl]

theorem cap_attained_forced_gain (a b c d delta J h eps : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hJ : 0 < J) (hd : 0 ≤ delta)
    (hK : 0 < 2 * delta * h - c * J) (hr : 0 < c + 2 * d * h)
    (hr0 : 0 ≤ c + 2 * d) (hb : eps ≤ b) :
    responsePolynomial a b c d delta J h (capResponse c d delta J h) +
      eps * (1 - h) ≤ a + b + c + d := by
  have hG := cap_response_curvature c d delta J h hh0 hJ hK hr
  have hy := cap_response_interior c d delta J h hh0 hJ hK hr
  have hs := cap_response_stationary c d delta J h (ne_of_gt hJ) (ne_of_gt hG)
  have hs' : c + 2 * d * capResponse c d delta J h -
      2 * delta * (1 / J) * (h - capResponse c d delta J h) = 0 := by
    convert hs using 1 <;> ring
  have hg := cap_forced_endpoint_gain a b c d delta h (capResponse c d delta J h)
    (1 / J) eps hh1 hy.2.le hd (one_div_nonneg.mpr hJ.le) hr0 hb hs'
  unfold responsePolynomial
  convert (le_sub_iff_add_le.mp hg) using 1 <;> ring

end
end F4Heavy.Analysis
