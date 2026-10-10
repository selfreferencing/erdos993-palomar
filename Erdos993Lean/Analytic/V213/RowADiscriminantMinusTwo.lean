module

public import Erdos993Lean.Analytic.V213.RowADiscriminantDefinitions
public import Erdos993Lean.Analytic.V213.RowAFloorFirstSigns

/-!
Algebraic proof of the literal Row A Step 4 lower bound for (minus,2).
All expansion is delegated to kernel-checked algebraic tactics. There is no
unprinted rational coefficient array or external coefficient computation.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

theorem discriminant_minus_two_lower {t : ℝ} (ht : 0 ≤ t) :
    floorPolynomial 2 t ≤
      discriminantGamma 2*piMinus (fractionalX t)*discriminantMinus (fractionalX t) 2/
        (discriminantScale 2*(1-fractionalX t)^8) := by
  have hu : 0 < 1+t := by linarith
  have hA : 0 < 4+36*t+27*t^2 := by positivity
  have hd : 0 < 2+3*t := by linarith
  rw [piMinus_fractional ht,one_sub_fractional ht]
  unfold discriminantMinus discriminant bernsteinK bernsteinM
  rw [kappaMinus_fractional ht,tauMinus_fractional ht]
  have hfloor_row : floorCoefficients 2 =
      ![583,1984,2413,175,-2605,-2246,345,1300,480] := rfl
  have hgamma_val : discriminantGamma 2 = 2764800 := rfl
  norm_num [nuMinus,fractionalX,hgamma_val,discriminantScale,
    floorPolynomial,hfloor_row,Fin.sum_univ_succ]
  apply sub_nonneg.mp
  field_simp [hu.ne',hA.ne',hd.ne']
  ring_nf
  positivity

theorem discriminant_minus_two_positive {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < discriminantMinus x 2 := by
  let t := x/(1-x)
  have ht : 0 ≤ t := div_nonneg hx (sub_pos.mpr hx1).le
  have he : fractionalX t = x := fractionalX_inverse hx1
  have hlow := discriminant_minus_two_lower ht
  rw [he] at hlow
  have hfloor := floor_minus_two_positive ht
  have hquot := lt_of_lt_of_le hfloor hlow
  have hscale : 0 < discriminantScale 2 := by norm_num [discriminantScale]
  have hgamma : 0 < discriminantGamma 2 := by
    change (0 : ℝ) < 2764800
    norm_num
  have hden : 0 < discriminantScale 2*(1-x)^8 :=
    mul_pos hscale (pow_pos (sub_pos.mpr hx1) _)
  have hprod : 0 < discriminantGamma 2*piMinus x*discriminantMinus x 2 := by
    simpa only [zero_mul] using (lt_div_iff₀ hden).1 hquot
  exact pos_of_mul_pos_right hprod (mul_pos hgamma (piMinus_pos hx hx1)).le

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_minus_two_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_minus_two_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_minus_two_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_minus_two_positive
