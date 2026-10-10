module

public import Erdos993Lean.Analytic.V213.RowADefinitions

/-!
The literal three degree-two Bernstein quadratics in Step 3 of the current
Row A proof. No coefficient table is consumed here. The
index is Fin 3, so its three values are exactly the printed j = 0,1,2.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

noncomputable def bernsteinK (kappa nu q0 x : ℝ) (j : Fin 3) : ℝ :=
  kappa-nu+(1-q0*x)*(3*(j.val:ℝ)/16)

noncomputable def bernsteinM (kappa tau sigma0 x : ℝ) (j : Fin 3) : ℝ :=
  kappa-13/6+tau+sigma0*x+
    (1-tau-2*sigma0*x)*(3*(j.val:ℝ)/16)+
    sigma0*x*(9*(j.val:ℝ)*((j.val:ℝ)-1)/128)

noncomputable def bernsteinQ (kappa tau nu sigma0 q0 x : ℝ)
    (j : Fin 3) (z : ℝ) : ℝ :=
  bernsteinK kappa nu q0 x j*z^2+(13/6-2*kappa)*z+
    bernsteinM kappa tau sigma0 x j

theorem bernsteinK_eq (kappa nu q0 x : ℝ) (j : Fin 3) :
    bernsteinK kappa nu q0 x j = kappa-nu+(1-q0*x)*(3*(j.val:ℝ)/16) := rfl

theorem bernsteinM_zero (kappa tau sigma0 x : ℝ) :
    bernsteinM kappa tau sigma0 x 0 = kappa-13/6+tau+sigma0*x := by
  simp [bernsteinM]

theorem bernsteinM_one (kappa tau sigma0 x : ℝ) :
    bernsteinM kappa tau sigma0 x 1 = kappa-13/6+tau+sigma0*x+
      (3/16)*(1-tau-2*sigma0*x) := by
  norm_num [bernsteinM]
  ring

theorem bernsteinM_two (kappa tau sigma0 x : ℝ) :
    bernsteinM kappa tau sigma0 x 2 = kappa-13/6+tau+sigma0*x+
      (1-tau-2*sigma0*x)*(3/8)+sigma0*x*(3/8)^2 := by
  norm_num [bernsteinM]

theorem quad_bernstein (kappa tau nu sigma0 q0 x r z : ℝ) :
    quad kappa tau nu sigma0 q0 x r z =
      (1-8*r/3)^2*bernsteinQ kappa tau nu sigma0 q0 x 0 z+
      2*(8*r/3)*(1-8*r/3)*bernsteinQ kappa tau nu sigma0 q0 x 1 z+
      (8*r/3)^2*bernsteinQ kappa tau nu sigma0 q0 x 2 z := by
  norm_num [quad,bernsteinQ,bernsteinK,bernsteinM]
  ring

theorem quad_positive_of_bernstein {kappa tau nu sigma0 q0 x r z : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 3/8)
    (hp : ∀ j : Fin 3, 0 < bernsteinQ kappa tau nu sigma0 q0 x j z) :
    0 < quad kappa tau nu sigma0 q0 x r z := by
  have hu0 : 0 ≤ 8*r/3 := by positivity
  have hu1 : 8*r/3 ≤ 1 := by linarith
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  rw [quad_bernstein]
  have hn1 : 0 ≤ 2*(8*r/3)*(1-8*r/3)*bernsteinQ kappa tau nu sigma0 q0 x 1 z :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hu1)) h1.le
  have hn2 : 0 ≤ (8*r/3)^2*bernsteinQ kappa tau nu sigma0 q0 x 2 z :=
    mul_nonneg (sq_nonneg _) h2.le
  by_cases hu : 8*r/3 < 1
  · have ht : 0 < (1-8*r/3)^2*bernsteinQ kappa tau nu sigma0 q0 x 0 z :=
      mul_pos (sq_pos_of_pos (sub_pos.mpr hu)) h0
    linarith
  · have he : 8*r/3 = 1 := le_antisymm hu1 (le_of_not_gt hu)
    simpa [he] using h2

/-- The sign-continuation argument used in the printed Step 4. -/
theorem positive_leading_from_discriminant
    {k m ell : ℝ → ℝ}
    (hc : ContinuousOn k (Set.Ico 0 1)) (h0 : 0 < k 0)
    (hd : ∀ x ∈ Set.Ico (0:ℝ) 1, 0 < 4*k x*m x-(ell x)^2)
    {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) : 0 < k x := by
  by_contra hn
  have hkx : k x ≤ 0 := le_of_not_gt hn
  have hcc : ContinuousOn k (Set.Icc 0 x) :=
    hc.mono (fun y hy => ⟨hy.1,lt_of_le_of_lt hy.2 hx.2⟩)
  obtain ⟨y,hy,hky⟩ :=
    (intermediate_value_Icc' hx.1 hcc) ⟨hkx,h0.le⟩
  have hdy := hd y ⟨hy.1,lt_of_le_of_lt hy.2 hx.2⟩
  rw [hky] at hdy
  nlinarith [sq_nonneg (ell y)]

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinK
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinK
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinQ
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinQ
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinK_eq
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinK_eq
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM_zero
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM_zero
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM_two
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.bernsteinM_two
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad_bernstein
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad_bernstein
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad_positive_of_bernstein
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad_positive_of_bernstein
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.positive_leading_from_discriminant
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.positive_leading_from_discriminant
