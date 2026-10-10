module

public import Erdos993Lean.F4U.Light.Construction.PaymentAlgebra
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
Generic derivative algebra for the same explicit minimized response function.
No finite guard or support hypothesis is postulated as an axiom. -/

@[expose] public section

namespace F4Unified.LightConstruction
noncomputable section

 def supportMinimum (a b c d delta slope intercept h : ℝ) : ℝ :=
  a+b*h+(delta*(c*h+d*h^2)-(slope*h+intercept)*c^2/4)/
    (delta+d*(slope*h+intercept))

 theorem supportMinimum_hasDerivAt (a b c d delta slope intercept h : ℝ)
    (hG : delta+d*(slope*h+intercept) ≠ 0) :
    HasDerivAt (supportMinimum a b c d delta slope intercept)
      (b+((delta*(c+2*d*h)-slope*c^2/4)*(delta+d*(slope*h+intercept))-
        d*slope*(delta*(c*h+d*h^2)-(slope*h+intercept)*c^2/4))/
        (delta+d*(slope*h+intercept))^2) h := by
  have hL := ((hasDerivAt_id h).const_mul slope).add_const intercept
  have hN := (((hasDerivAt_id h).const_mul c).add
    (((hasDerivAt_id h).pow 2).const_mul d)).const_mul delta
  have hnum := hN.sub (hL.const_mul (c^2/4))
  have hden := (hL.const_mul d).const_add delta
  convert ((hasDerivAt_const h a).add ((hasDerivAt_id h).const_mul b)).add
    (hnum.div hden hG) using 1 <;>
    first | (ext x; try dsimp [supportMinimum]; ring) | (try dsimp [supportMinimum]; ring)

 theorem support_derivative_identity (c d delta intercept h : ℝ)
    (hd : delta ≠ 0) (hG : delta+d*((3/10)*h+intercept) ≠ 0) :
    ((delta*(c+2*d*h)-(3/10)*c^2/4)*(delta+d*((3/10)*h+intercept))-
        d*(3/10)*(delta*(c*h+d*h^2)-((3/10)*h+intercept)*c^2/4))/
        (delta+d*((3/10)*h+intercept))^2 =
      delta*(c+2*d*h)/(delta+d*((3/10)*h+intercept)) -
      3*(delta*(c+2*d*h)/(delta+d*((3/10)*h+intercept)))^2/(40*delta) := by
  field_simp [hd,hG]
  <;> ring

 theorem support_derivative_pos (b delta G r : ℝ)
    (hb : 0 ≤ b) (hd : 0 < delta) (hr : 0 < r) (hrG : r < 10*G) :
    0 < b+delta*r/G-3*(delta*r/G)^2/(40*delta) := by
  have hG : 0 < G := by linarith
  have hn : 0 < delta*r/G := div_pos (mul_pos hd hr) hG
  have hn10 : delta*r/G < 10*delta := by
    apply (div_lt_iff₀ hG).2
    nlinarith [mul_lt_mul_of_pos_left hrG hd]
  have hid : b+delta*r/G-3*(delta*r/G)^2/(40*delta) =
      b+(delta*r/G)/4+3*(delta*r/G)*(10*delta-delta*r/G)/(40*delta) := by
    field_simp [hd.ne',hG.ne']
    <;> ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hb (by positivity))
    (by positivity)

 theorem supportMinimum_second_hasDerivAt (a b c d delta intercept h : ℝ)
    (hd : delta ≠ 0) (hG : delta+d*((3/10)*h+intercept) ≠ 0) :
    HasDerivAt (supportMinimum a b c d delta (3/10) intercept)
      (b+delta*(c+2*d*h)/(delta+d*((3/10)*h+intercept))-
        3*(delta*(c+2*d*h)/(delta+d*((3/10)*h+intercept)))^2/(40*delta)) h := by
  have hh := supportMinimum_hasDerivAt a b c d delta (3/10) intercept h hG
  simpa only [support_derivative_identity c d delta intercept h hd hG,
    add_sub_assoc] using hh

 theorem supportMinimum_strictMonoOn (a b c d delta intercept h0 h1 : ℝ)
    (hb : 0 ≤ b) (hd : 0 < delta)
    (hguards : ∀ h ∈ Set.Icc h0 h1,
      0 < c+2*d*h ∧ c+2*d*h < 10*(delta+d*((3/10)*h+intercept))) :
    StrictMonoOn (supportMinimum a b c d delta (3/10) intercept) (Set.Icc h0 h1) := by
  have hG : ∀ h ∈ Set.Icc h0 h1, 0 < delta+d*((3/10)*h+intercept) := by
    intro h hh
    have hg := hguards h hh
    linarith
  have hder : ∀ h ∈ Set.Icc h0 h1,
      HasDerivAt (supportMinimum a b c d delta (3/10) intercept)
        (b+delta*(c+2*d*h)/(delta+d*((3/10)*h+intercept))-
          3*(delta*(c+2*d*h)/(delta+d*((3/10)*h+intercept)))^2/(40*delta)) h := by
    intro h hh
    exact supportMinimum_second_hasDerivAt a b c d delta intercept h hd.ne' (hG h hh).ne'
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc h0 h1)
    (fun h hh => (hder h hh).continuousAt.continuousWithinAt)
  · intro h hh
    exact (hder h (interior_subset hh)).hasDerivWithinAt
  · intro h hh
    exact support_derivative_pos b delta _ _ hb hd
      (hguards h (interior_subset hh)).1 (hguards h (interior_subset hh)).2

 theorem supportMinimum_pos_from_left (a b c d delta intercept h0 h1 h : ℝ)
    (hb : 0 ≤ b) (hd : 0 < delta)
    (hguards : ∀ h ∈ Set.Icc h0 h1,
      0 < c+2*d*h ∧ c+2*d*h < 10*(delta+d*((3/10)*h+intercept)))
    (hh0 : h0 ≤ h) (hh1 : h ≤ h1)
    (hstart : 0 < supportMinimum a b c d delta (3/10) intercept h0) :
    0 < supportMinimum a b c d delta (3/10) intercept h := by
  have hm := (supportMinimum_strictMonoOn a b c d delta intercept h0 h1 hb hd hguards).monotoneOn
  have hstartmem : h0 ∈ Set.Icc h0 h1 := ⟨le_rfl,hh0.trans hh1⟩
  exact lt_of_lt_of_le hstart (hm hstartmem ⟨hh0,hh1⟩ hh0)

 theorem supportMinimum_cleared_identity (a b c d delta slope intercept h : ℝ)
    (hG : delta+d*(slope*h+intercept) ≠ 0) :
    4*(delta+d*(slope*h+intercept))*supportMinimum a b c d delta slope intercept h =
      4*(delta+d*(slope*h+intercept))*(a+b*h)+4*delta*(c*h+d*h^2)-
        (slope*h+intercept)*c^2 := by
  unfold supportMinimum
  field_simp [hG]
  <;> ring

#print axioms supportMinimum
#print axioms supportMinimum_hasDerivAt
#print axioms support_derivative_identity
#print axioms support_derivative_pos
#print axioms supportMinimum_second_hasDerivAt
#print axioms supportMinimum_strictMonoOn
#print axioms supportMinimum_pos_from_left
#print axioms supportMinimum_cleared_identity

end
end F4Unified.LightConstruction
