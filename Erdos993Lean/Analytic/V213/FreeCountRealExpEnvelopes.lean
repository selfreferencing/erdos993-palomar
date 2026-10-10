module

public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-!
Current T1's Taylor lower sums and exact [4/4],
[3/3] Padé envelopes. All variables are Real. No finite worksheet is replayed;
the positive denominator and derivative signs are proved on a continuum.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

open Real Set Finset

noncomputable def expPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), x^k / (Nat.factorial k : ℝ)

theorem expPartial_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expPartial n x ≤ exp x := Real.sum_le_exp_of_nonneg hx (n+1)

theorem exp_one_gt_eight_thirds : (8/3 : ℝ) < exp 1 := by
  have h := expPartial_le_exp 4 (x := 1) (by norm_num)
  norm_num [expPartial, Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_three_gt_twenty : (20 : ℝ) < exp 3 := by
  have h := expPartial_le_exp 9 (x := 3) (by norm_num)
  norm_num [expPartial, Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_five_fourths_gt_ten_thirds : (10/3 : ℝ) < exp (5/4) := by
  have h := expPartial_le_exp 4 (x := 5/4) (by norm_num)
  norm_num [expPartial, Finset.sum_range_succ, Nat.factorial] at h
  linarith

noncomputable def polyP3 (x : ℝ) : ℝ := 120+60*x+12*x^2+x^3
noncomputable def polyP4 (x : ℝ) : ℝ := 1680+840*x+180*x^2+20*x^3+x^4
noncomputable def polyQ3 (x : ℝ) : ℝ := polyP3 (-x)
noncomputable def polyQ4 (x : ℝ) : ℝ := polyP4 (-x)
noncomputable def expLower (y : ℝ) : ℝ := (polyP4 (y/4)/polyQ4 (y/4))^4
noncomputable def expUpper (y : ℝ) : ℝ := (polyP3 (y/4)/polyQ3 (y/4))^4

theorem polyP3_pos {x : ℝ} (hx : 0 ≤ x) : 0 < polyP3 x := by
  unfold polyP3
  positivity

theorem polyP4_pos {x : ℝ} (hx : 0 ≤ x) : 0 < polyP4 x := by
  unfold polyP4
  positivity

theorem polyQ3_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 59 ≤ polyQ3 x := by
  have h3 : x^3 ≤ 1 := by simpa using pow_le_pow_left₀ hx hx1 3
  unfold polyQ3 polyP3
  nlinarith [sq_nonneg x]

theorem polyQ4_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 820 ≤ polyQ4 x := by
  have h3 : x^3 ≤ 1 := by simpa using pow_le_pow_left₀ hx hx1 3
  unfold polyQ4 polyP4
  nlinarith [sq_nonneg x, sq_nonneg (x^2)]

theorem hasDerivAt_polyP3 (x : ℝ) :
    HasDerivAt polyP3 (60+24*x+3*x^2) x := by
  convert ((((hasDerivAt_const x (120 : ℝ)).add ((hasDerivAt_id x).const_mul 60)).add
    ((hasDerivAt_pow 2 x).const_mul 12)).add (hasDerivAt_pow 3 x)) using 1 <;>
    (try funext t) <;> dsimp [polyP3] <;> ring

theorem hasDerivAt_polyP4 (x : ℝ) :
    HasDerivAt polyP4 (840+360*x+60*x^2+4*x^3) x := by
  convert (((((hasDerivAt_const x (1680 : ℝ)).add ((hasDerivAt_id x).const_mul 840)).add
    ((hasDerivAt_pow 2 x).const_mul 180)).add ((hasDerivAt_pow 3 x).const_mul 20)).add
    (hasDerivAt_pow 4 x)) using 1 <;> (try funext t) <;> dsimp [polyP4] <;> ring

theorem hasDerivAt_polyQ3 (x : ℝ) :
    HasDerivAt polyQ3 (-60+24*x-3*x^2) x := by
  convert (hasDerivAt_polyP3 (-x)).comp x (hasDerivAt_neg x) using 1 <;>
    (try funext t) <;> (try dsimp [polyQ3]) <;> ring

theorem hasDerivAt_polyQ4 (x : ℝ) :
    HasDerivAt polyQ4 (-840+360*x-60*x^2+4*x^3) x := by
  convert (hasDerivAt_polyP4 (-x)).comp x (hasDerivAt_neg x) using 1 <;>
    (try funext t) <;> (try dsimp [polyQ4]) <;> ring

/-- The printed P3'Q3-P3Q3'-P3Q3=x^6 identity in derivative form. -/
theorem hasDerivAt_pade3_weighted {x : ℝ} (hq : polyQ3 x ≠ 0) :
    HasDerivAt (fun t => polyP3 t / polyQ3 t * exp (-t))
      (exp (-x) * x^6 / (polyQ3 x)^2) x := by
  have he : HasDerivAt (fun t : ℝ => exp (-t)) (-exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) using 1 <;>
      (try funext t) <;> (try dsimp) <;> ring
  convert ((hasDerivAt_polyP3 x).div (hasDerivAt_polyQ3 x) hq).mul he using 1
  dsimp
  field_simp [hq]
  dsimp [polyQ3, polyP3]
  ring

/-- The printed P4'Q4-P4Q4'-P4Q4=-x^8 identity in derivative form. -/
theorem hasDerivAt_pade4_weighted {x : ℝ} (hq : polyQ4 x ≠ 0) :
    HasDerivAt (fun t => polyP4 t / polyQ4 t * exp (-t))
      (-(exp (-x) * x^8 / (polyQ4 x)^2)) x := by
  have he : HasDerivAt (fun t : ℝ => exp (-t)) (-exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) using 1 <;>
      (try funext t) <;> (try dsimp) <;> ring
  convert ((hasDerivAt_polyP4 x).div (hasDerivAt_polyQ4 x) hq).mul he using 1
  dsimp
  field_simp [hq]
  dsimp [polyQ4, polyP4]
  ring

theorem pade3_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    exp x ≤ polyP3 x / polyQ3 x := by
  have hgap : 0 ≤ polyP3 x / polyQ3 x * exp (-x) - 1 := by
    apply zero_le_value_of_nonneg_deriv (f := fun t => polyP3 t/polyQ3 t*exp (-t)-1)
      (f' := fun t => exp (-t)*t^6/(polyQ3 t)^2) hx
    · norm_num [polyP3, polyQ3]
    · intro t ht
      have hq : 0 < polyQ3 t := lt_of_lt_of_le (by norm_num) (polyQ3_lower ht.1 (ht.2.trans hx1))
      exact (hasDerivAt_pade3_weighted hq.ne').sub_const 1
    · intro t ht
      positivity
  have he : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_right (show 1 ≤ polyP3 x/polyQ3 x*exp (-x) by linarith)
    (Real.exp_pos x).le
  simpa only [one_mul, mul_assoc, he, mul_one] using h

theorem pade4_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    polyP4 x / polyQ4 x ≤ exp x := by
  have hgap : 0 ≤ 1 - polyP4 x / polyQ4 x * exp (-x) := by
    apply zero_le_value_of_nonneg_deriv (f := fun t => 1-polyP4 t/polyQ4 t*exp (-t))
      (f' := fun t => exp (-t)*t^8/(polyQ4 t)^2) hx
    · norm_num [polyP4, polyQ4]
    · intro t ht
      have hq : 0 < polyQ4 t := lt_of_lt_of_le (by norm_num) (polyQ4_lower ht.1 (ht.2.trans hx1))
      convert (hasDerivAt_pade4_weighted hq.ne').const_sub 1 using 1 <;> ring
    · intro t ht
      positivity
  have he : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_right (show polyP4 x/polyQ4 x*exp (-x) ≤ 1 by linarith)
    (Real.exp_pos x).le
  simpa only [one_mul, mul_assoc, he, mul_one] using h

/-- The paper uses y≤3; the same proof works on the larger [0,4]. -/
theorem exp_envelopes {y : ℝ} (hy : 0 ≤ y) (hy3 : y ≤ 3) :
    expLower y ≤ exp y ∧ exp y ≤ expUpper y := by
  have hx : 0 ≤ y/4 := by positivity
  have hx1 : y/4 ≤ 1 := by linarith
  have hq4 : 0 < polyQ4 (y/4) := lt_of_lt_of_le (by norm_num) (polyQ4_lower hx hx1)
  have hp4 : 0 ≤ polyP4 (y/4)/polyQ4 (y/4) := (div_pos (polyP4_pos hx) hq4).le
  have hl := pow_le_pow_left₀ hp4 (pade4_lower hx hx1) 4
  have hu := pow_le_pow_left₀ (Real.exp_pos (y/4)).le (pade3_upper hx hx1) 4
  have he : exp (y/4)^4 = exp y := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hl hu
  exact ⟨hl, hu⟩

end Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.expPartial_le_exp
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.expPartial_le_exp
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_one_gt_eight_thirds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_one_gt_eight_thirds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_three_gt_twenty
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_three_gt_twenty
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_five_fourths_gt_ten_thirds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_five_fourths_gt_ten_thirds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP3_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP3_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP4_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyP4_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyQ3_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyQ3_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyQ4_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.polyQ4_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyP3
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyP3
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyP4
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyP4
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyQ3
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyQ3
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyQ4
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_polyQ4
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_pade3_weighted
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_pade3_weighted
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_pade4_weighted
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.hasDerivAt_pade4_weighted
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.pade3_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.pade3_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.pade4_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.pade4_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_envelopes
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.exp_envelopes
