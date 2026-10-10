module

public import F4Heavy.Analysis.LowerResponse

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem lower_response_zero_positive (a b c d delta s h0 h : ℝ)
    (hdelta : 0 < delta) (hs : 0 ≤ s) (hb : 0 ≤ b) (hh : h0 ≤ h) (hh1 : h ≤ 1)
    (hc : 0 < c+2*d) (hB : 0 < a+(b+c)*h0+d*h0^2)
    (hF : 0 ≤ 4*delta*(b+c+2*d*h0)-s*(c+2*d*h0)^2) :
    0 < responsePolynomial a b c d delta 0 h h := by
  rw [response_zero_envelope]
  have ht : 0 ≤ h-h0 := sub_nonneg.mpr hh
  by_cases hd : 0 ≤ d
  · have hr : 0 ≤ 4*delta*(b+c+2*d*h0) := by
      have hsq := mul_nonneg hs (sq_nonneg (c+2*d*h0))
      linarith only [hF, hsq]
    have hcoef : 0 ≤ b+c+2*d*h0 :=
      nonneg_of_mul_nonneg_right hr (by positivity : 0 < 4*delta)
    have hlin := mul_nonneg ht hcoef
    have hquad := mul_nonneg hd (sq_nonneg (h-h0))
    nlinarith only [hB, hlin, hquad]
  · have hd' : d ≤ 0 := le_of_not_ge hd
    have hgap : 0 ≤ d*(h+h0-2) :=
      mul_nonneg_of_nonpos_of_nonpos hd' (by linarith only [hh, hh1])
    have hcoef : 0 ≤ b+c+d*(h+h0) := by linarith only [hb, hc, hgap]
    have hlin := mul_nonneg ht hcoef
    nlinarith only [hB, hlin]

theorem lower_response_closed_positive (a b c d delta s h0 h L y : ℝ)
    (hdelta : 0 < delta) (hs : 0 ≤ s) (hb : 0 ≤ b) (hh0 : (1/2 : ℝ) ≤ h0)
    (hh : h0 ≤ h) (hh1 : h ≤ 1) (hL : 0 ≤ L) (hLs : L ≤ s*(h-h0))
    (hy : L = 0 → y = h) (hc : 0 < c+2*d) (hC : 0 < 4*delta-s*c)
    (hB : 0 < a+(b+c)*h0+d*h0^2)
    (hF : 0 ≤ 4*delta*(b+c+2*d*h0)-s*(c+2*d*h0)^2) :
    0 < responsePolynomial a b c d delta L h y := by
  by_cases hzero : L = 0
  · rw [hy hzero, hzero]
    exact lower_response_zero_positive a b c d delta s h0 h hdelta hs hb hh hh1 hc hB hF
  · exact lower_response_positive a b c d delta s h0 h L y hdelta hs hb hh0 hh hh1
      (lt_of_le_of_ne hL (Ne.symm hzero)) hLs hc hC hB hF

end F4Heavy.Analysis
