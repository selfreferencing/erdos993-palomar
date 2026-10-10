module

public import F4Heavy.Analysis.Quadratic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem lower_response_nonnegative_square (a b c d delta s h0 h L y : ℝ) (hL : L ≠ 0) :
    4*delta*L*(responsePolynomial a b c d delta L h y-(a+(b+c)*h0+d*h0^2)) =
      L*(h-h0)*(4*delta*(b+c+2*d*h0)-s*(c+2*d*h0)^2)+
      L*(s*(h-h0)-L)*(c+2*d*h0)^2+4*delta*L*d*(y-h0)^2+
      (2*delta*(y-h)+L*(c+2*d*h0))^2 := by
  unfold responsePolynomial
  field_simp [hL]
  ring

theorem lower_response_nonnegative_positive (a b c d delta s h0 h L y : ℝ)
    (hdelta : 0 < delta) (hL : 0 < L) (hd : 0 ≤ d) (hh : h0 ≤ h)
    (hLs : L ≤ s*(h-h0)) (hB : 0 < a+(b+c)*h0+d*h0^2)
    (hF : 0 ≤ 4*delta*(b+c+2*d*h0)-s*(c+2*d*h0)^2) :
    0 < responsePolynomial a b c d delta L h y := by
  have hid := lower_response_nonnegative_square a b c d delta s h0 h L y (ne_of_gt hL)
  have hh0 : 0 ≤ h-h0 := sub_nonneg.mpr hh
  have hgap : 0 ≤ s*(h-h0)-L := sub_nonneg.mpr hLs
  have hsum : 0 ≤ L*(h-h0)*(4*delta*(b+c+2*d*h0)-s*(c+2*d*h0)^2)+
      L*(s*(h-h0)-L)*(c+2*d*h0)^2+4*delta*L*d*(y-h0)^2+
      (2*delta*(y-h)+L*(c+2*d*h0))^2 := by positivity
  rw [← hid] at hsum
  have hp : 0 < 4*delta*L := by positivity
  have hbound := nonneg_of_mul_nonneg_right hsum hp
  linarith only [hbound, hB]

theorem lower_response_negative_gain_identity (c e delta s h0 h L : ℝ) :
    4*(delta-e*L) = (4*delta-s*c)+s*(c-2*e)+2*s*e*(2*h0-1)+
      4*e*(s*(h-h0)-L)+4*s*e*(1-h) := by ring

theorem lower_response_negative_shape_identity (c e delta s h0 h : ℝ) :
    4*delta*(c-e*(h+h0))-s*(c-2*e*h0)^2 =
      (4*delta-s*c)*(c-e*(h+h0))+s*e*c*((1-h)+(1-h0)*(2*h0-1))+
      2*s*e*h0^2*(c-2*e) := by ring

theorem lower_response_negative_numerator_identity (a b c e delta s h0 h L : ℝ) :
    responseNumerator a b c (-e) delta L h =
      4*(delta-e*L)*(a+(b+c)*h0-e*h0^2+b*(h-h0))+
      (h-h0)*(4*delta*(c-e*(h+h0))-s*(c-2*e*h0)^2)+
      (s*(h-h0)-L)*(c-2*e*h0)^2 := by
  unfold responseNumerator
  ring

theorem lower_response_negative_positive (a b c e delta s h0 h L y : ℝ)
    (he : 0 ≤ e) (hs : 0 ≤ s) (hb : 0 ≤ b) (hh0 : (1/2 : ℝ) ≤ h0)
    (hh : h0 ≤ h) (hh1 : h ≤ 1) (hL : 0 < L) (hLs : L ≤ s*(h-h0))
    (hc : 0 < c-2*e) (hC : 0 < 4*delta-s*c)
    (hB : 0 < a+(b+c)*h0-e*h0^2) :
    0 < responsePolynomial a b c (-e) delta L h y := by
  have ht : 0 ≤ h-h0 := sub_nonneg.mpr hh
  have hgap : 0 ≤ s*(h-h0)-L := sub_nonneg.mpr hLs
  have h0half : 0 ≤ 2*h0-1 := by linarith
  have hh01 : 0 ≤ 1-h0 := by linarith
  have hh11 : 0 ≤ 1-h := by linarith
  have hc0 : 0 ≤ c := by linarith only [hc, he]
  have hG : 0 < delta-e*L := by
    have hid := lower_response_negative_gain_identity c e delta s h0 h L
    have hrest : 0 ≤ s*(c-2*e)+2*s*e*(2*h0-1)+4*e*(s*(h-h0)-L)+4*s*e*(1-h) := by positivity
    linarith only [hid, hrest, hC]
  have hA : 0 ≤ c-e*(h+h0) := by
    have hrest : 0 ≤ e*((1-h)+(1-h0)) := by positivity
    nlinarith only [hrest, hc]
  have hshape : 0 ≤ 4*delta*(c-e*(h+h0))-s*(c-2*e*h0)^2 := by
    rw [lower_response_negative_shape_identity]
    positivity
  have hbase : 0 < a+(b+c)*h0-e*h0^2+b*(h-h0) :=
    add_pos_of_pos_of_nonneg hB (mul_nonneg hb ht)
  have hW : 0 < responseNumerator a b c (-e) delta L h := by
    rw [lower_response_negative_numerator_identity a b c e delta s h0 h L]
    positivity
  apply response_positive a b c (-e) delta L h y hL
  · simpa only [neg_mul, sub_eq_add_neg] using hG
  · exact hW

theorem lower_response_positive (a b c d delta s h0 h L y : ℝ)
    (hdelta : 0 < delta) (hs : 0 ≤ s) (hb : 0 ≤ b) (hh0 : (1/2 : ℝ) ≤ h0)
    (hh : h0 ≤ h) (hh1 : h ≤ 1) (hL : 0 < L) (hLs : L ≤ s*(h-h0))
    (hc : 0 < c+2*d) (hC : 0 < 4*delta-s*c)
    (hB : 0 < a+(b+c)*h0+d*h0^2)
    (hF : 0 ≤ 4*delta*(b+c+2*d*h0)-s*(c+2*d*h0)^2) :
    0 < responsePolynomial a b c d delta L h y := by
  by_cases hd : 0 ≤ d
  · exact lower_response_nonnegative_positive a b c d delta s h0 h L y hdelta hL hd hh hLs hB hF
  · have he : 0 ≤ -d := by linarith only [le_of_not_ge hd]
    have hc' : 0 < c-2*(-d) := by linarith only [hc]
    have hB' : 0 < a+(b+c)*h0-(-d)*h0^2 := by nlinarith only [hB]
    simpa only [neg_neg] using lower_response_negative_positive a b c (-d) delta s h0 h L y
      he hs hb hh0 hh hh1 hL hLs hc' hC hB'

end F4Heavy.Analysis
