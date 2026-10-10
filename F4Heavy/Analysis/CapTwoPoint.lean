module

public import F4Heavy.Analysis.Quadratic

-- Adapted from round12_selected/Cap_Two_Point.lean; checked locally, unlike the supplied candidate.
@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
noncomputable section

def capPointValue (b c d delta h z v : ℝ) : ℝ :=
  b * h + c * (h * (1 - z)) + d * (h * (1 - z)) ^ 2 +
    delta * h * v * z ^ 2

/-- Setting both stationarity residuals to zero gives the finite difference. -/
theorem cap_two_point_residual (b c d delta h1 h2 z1 z2 v1 v2 : ℝ) :
    2 * (capPointValue b c d delta h1 z1 v1 -
        capPointValue b c d delta h2 z2 v2 - b * (h1 - h2) -
        delta * (z1 * z2) * (h1 * v1 - h2 * v2) -
        delta * (h1 - h2) *
          (v1 * z1 * (1 - z2) + v2 * z2 * (1 - z1))) =
      (h1 * (1 - z1) - h2 * (1 - z2)) *
        ((c + 2 * d * (h1 * (1 - z1)) - 2 * delta * v1 * z1) +
         (c + 2 * d * (h2 * (1 - z2)) - 2 * delta * v2 * z2)) := by
  unfold capPointValue
  ring

/-- Both scalar increments have the same margin, so their blend has it too. -/
theorem cap_two_point_gain (b delta t v1 v2 z1 z2 w eps : ℝ)
    (ht : 0 ≤ t) (hd : 0 ≤ delta) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hz10 : 0 ≤ z1) (hz11 : z1 ≤ 1) (hz20 : 0 ≤ z2) (hz21 : z2 ≤ 1)
    (hb : eps * t ≤ b * t) (hw : eps * t ≤ b * t + delta * w) :
    eps * t ≤ (1 - z1 * z2) * (b * t) +
      (z1 * z2) * (b * t + delta * w) +
      delta * t * (v1 * z1 * (1 - z2) + v2 * z2 * (1 - z1)) := by
  have heta : 0 ≤ z1 * z2 := mul_nonneg hz10 hz20
  have hprod : z1 * z2 ≤ z1 * 1 :=
    mul_le_mul_of_nonneg_left hz21 hz10
  have hcomp : 0 ≤ 1 - z1 * z2 := by linarith
  have hrest : 0 ≤ delta * t *
      (v1 * z1 * (1 - z2) + v2 * z2 * (1 - z1)) :=
    mul_nonneg (mul_nonneg hd ht)
      (add_nonneg
        (mul_nonneg (mul_nonneg hv1 hz10) (sub_nonneg.mpr hz21))
        (mul_nonneg (mul_nonneg hv2 hz20) (sub_nonneg.mpr hz11)))
  calc
    eps * t = (1 - z1 * z2) * (eps * t) + (z1 * z2) * (eps * t) := by ring
    _ ≤ (1 - z1 * z2) * (b * t) +
        (z1 * z2) * (b * t + delta * w) :=
      add_le_add (mul_le_mul_of_nonneg_left hb hcomp)
        (mul_le_mul_of_nonneg_left hw heta)
    _ ≤ (1 - z1 * z2) * (b * t) + (z1 * z2) * (b * t + delta * w) +
        delta * t * (v1 * z1 * (1 - z2) + v2 * z2 * (1 - z1)) :=
      le_add_of_nonneg_right hrest

/-- The first point has the original forced response and zero reserve. -/
theorem cap_forced_endpoint_residual (a b c d delta h y jinv : ℝ) :
    2 * ((a + b + c + d) -
        (a + b * h + c * y + d * y ^ 2 + delta * jinv * (h - y) ^ 2) -
        b * (1 - h) - (c + 2 * d) / 2 * (1 - y) -
        delta * jinv * (h - y) * (1 - h)) =
      (1 - y) * (c + 2 * d * y - 2 * delta * jinv * (h - y)) := by
  ring

/-- An attained child minimum gives the closed endpoint gain algebraically. -/
theorem cap_forced_endpoint_gain (a b c d delta h y jinv eps : ℝ)
    (hh : h ≤ 1) (hy : y ≤ h) (hd : 0 ≤ delta) (hj : 0 ≤ jinv)
    (hr : 0 ≤ c + 2 * d) (hb : eps ≤ b)
    (hstationary : c + 2 * d * y - 2 * delta * jinv * (h - y) = 0) :
    eps * (1 - h) ≤ (a + b + c + d) -
      (a + b * h + c * y + d * y ^ 2 + delta * jinv * (h - y) ^ 2) := by
  have h1 : 0 ≤ (c + 2 * d) / 2 * (1 - y) :=
    mul_nonneg (div_nonneg hr (by norm_num))
      (sub_nonneg.mpr (le_trans hy hh))
  have h2 : 0 ≤ delta * jinv * (h - y) * (1 - h) :=
    mul_nonneg (mul_nonneg (mul_nonneg hd hj) (sub_nonneg.mpr hy))
      (sub_nonneg.mpr hh)
  have hbase : eps * (1 - h) ≤ b * (1 - h) :=
    mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hh)
  have hid := cap_forced_endpoint_residual a b c d delta h y jinv
  rw [hstationary, mul_zero] at hid
  linarith

end
end F4Heavy.Analysis
