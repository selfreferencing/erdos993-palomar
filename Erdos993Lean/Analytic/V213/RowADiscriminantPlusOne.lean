module

public import Erdos993Lean.Analytic.V213.RowADiscriminantDefinitions
public import Erdos993Lean.Analytic.V213.RowAFloorFinalSigns

/-!
Algebraic proof of the literal Row A Step 4 lower bound for (plus,1).
All expansion is delegated to kernel-checked algebraic tactics. There is no
unprinted rational coefficient array or external coefficient computation.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

theorem discriminant_plus_one_lower {t : ℝ} (ht : 0 ≤ t) :
    floorPolynomial 4 t ≤
      discriminantGamma 4*piPlus (fractionalX t)*discriminantPlus (fractionalX t) 1/
        (discriminantScale 4*(1-fractionalX t)^8) := by
  have hu : 0 < 1+t := by linarith
  have hA : 0 < 16+120*t+75*t^2 := by positivity
  have hd : 0 < 4+5*t := by linarith
  rw [piPlus_fractional ht,one_sub_fractional ht]
  unfold discriminantPlus discriminant bernsteinK bernsteinM
  rw [kappaPlus_fractional ht,tauPlus_fractional ht]
  have hfloor_row : floorCoefficients 4 =
      ![478,974,1211,2300,3008,1874,554,157,55] := rfl
  have hgamma_val : discriminantGamma 4 = 92160000 := rfl
  norm_num [nuPlus,fractionalX,hgamma_val,discriminantScale,
    floorPolynomial,hfloor_row,Fin.sum_univ_succ]
  apply sub_nonneg.mp
  field_simp [hu.ne',hA.ne',hd.ne']
  ring_nf
  positivity

theorem discriminant_plus_one_positive {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < discriminantPlus x 1 := by
  let t := x/(1-x)
  have ht : 0 ≤ t := div_nonneg hx (sub_pos.mpr hx1).le
  have he : fractionalX t = x := fractionalX_inverse hx1
  have hlow := discriminant_plus_one_lower ht
  rw [he] at hlow
  have hfloor := floor_plus_one_positive ht
  have hquot := lt_of_lt_of_le hfloor hlow
  have hscale : 0 < discriminantScale 4 := by norm_num [discriminantScale]
  have hgamma : 0 < discriminantGamma 4 := by
    change (0 : ℝ) < 92160000
    norm_num
  have hden : 0 < discriminantScale 4*(1-x)^8 :=
    mul_pos hscale (pow_pos (sub_pos.mpr hx1) _)
  have hprod : 0 < discriminantGamma 4*piPlus x*discriminantPlus x 1 := by
    simpa only [zero_mul] using (lt_div_iff₀ hden).1 hquot
  exact pos_of_mul_pos_right hprod (mul_pos hgamma (piPlus_pos hx hx1)).le

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_plus_one_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_plus_one_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_plus_one_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminant_plus_one_positive
