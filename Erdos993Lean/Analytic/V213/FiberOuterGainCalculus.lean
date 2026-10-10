module

public import Erdos993Lean.Analytic.V213.FiberOuterDefinitions

/-!
Exact P_N derivatives on m=N+1>2,y<1. Rational normal forms
are proved equal to the printed D_*+y*C_sqrt(y); they are not new
certificate premises. The printed second derivative and its negative
sign are proved on the entire closed N>=17,y in[0,4/25] domain.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberOuterPK1 (m : ℝ) : ℝ := 8 * (m - 3) ^ 2 / (9 * m)
noncomputable def fiberOuterPK2 (m : ℝ) : ℝ := (m - 3) * (2 * m - 5) / (6 * (m - 2))
noncomputable def fiberOuterPK3 (m : ℝ) : ℝ :=
  (65 * m ^ 3 - 340 * m ^ 2 + 909 * m - 1098) / (180 * m * (m - 2))

noncomputable def fiberOuterPPrimeM (m y : ℝ) : ℝ :=
  fiberOuterPK1 m - fiberOuterPK2 m / (1 - y) ^ 2 - m / (18 * (1 - y) ^ 3)

noncomputable def fiberOuterPSecondM (m y : ℝ) : ℝ :=
  -2 * fiberOuterPK2 m / (1 - y) ^ 3 - m / (6 * (1 - y) ^ 4)

theorem fiber_outer_P_rational_form {m y : ℝ} (hm : 2 < m) (hy : y < 1) :
    fiberGainD m + y * fiberOuterC m y =
      fiberOuterPK1 m * y - fiberOuterPK2 m / (1 - y) -
        m / (36 * (1 - y) ^ 2) + fiberOuterPK3 m := by
  have hm0 : 0 < m := by linarith only [hm]
  have hm2 : 0 < m - 2 := by linarith only [hm]
  have ha : 0 < 1 - y := by linarith only [hy]
  unfold fiberGainD fiberOuterC fiberOuterPK1 fiberOuterPK2 fiberOuterPK3
  field_simp [hm0.ne',hm2.ne',ha.ne']
  ring

theorem fiber_hasDerivAt_outer_P {N y : ℝ} (hN : 1 < N) (hy : y < 1) :
    HasDerivAt (fiberOuterP N) (fiberOuterPPrimeM (N + 1) y) y := by
  let m := N + 1
  have hm : 2 < m := by dsimp [m]; linarith only [hN]
  have ha : 0 < 1 - y := by linarith only [hy]
  have h1 := (hasDerivAt_id y).const_mul (fiberOuterPK1 m)
  have h2 := (hasDerivAt_const y (fiberOuterPK2 m)).div ((hasDerivAt_id y).const_sub 1) ha.ne'
  have h3 := (hasDerivAt_const y m).div ((((hasDerivAt_id y).const_sub 1).pow 2).const_mul 36) (by dsimp; positivity)
  have h := ((h1.sub h2).sub h3).add_const (fiberOuterPK3 m)
  have he : HasDerivAt (fun x => fiberOuterPK1 m * x - fiberOuterPK2 m / (1 - x) -
      m / (36 * (1 - x) ^ 2) + fiberOuterPK3 m) (fiberOuterPPrimeM m y) y := by
    convert h using 1
    · funext x
      dsimp
    · dsimp [fiberOuterPPrimeM]
      field_simp [ha.ne']
      ring
  apply he.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hy] with x hx
  exact fiber_outer_P_rational_form hm hx

theorem fiber_hasDerivAt_outer_PPrime {m y : ℝ} (hy : y < 1) :
    HasDerivAt (fiberOuterPPrimeM m) (fiberOuterPSecondM m y) y := by
  have ha : 0 < 1 - y := by linarith only [hy]
  have h2 := (hasDerivAt_const y (fiberOuterPK2 m)).div (((hasDerivAt_id y).const_sub 1).pow 2) (by dsimp; positivity)
  have h3 := (hasDerivAt_const y m).div ((((hasDerivAt_id y).const_sub 1).pow 3).const_mul 18) (by dsimp; positivity)
  have h := (((h2.const_sub (fiberOuterPK1 m)).sub h3))
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberOuterPSecondM]
    field_simp [ha.ne']
    ring

theorem fiber_outer_PSecond_printed {m y : ℝ} (hm : 2 < m) (hy : y < 1) :
    fiberOuterPSecondM m y =
      (m ^ 2 * (4 * y - 5) + m * (24 - 22 * y) + 30 * y - 30) /
        (6 * (m - 2) * (1 - y) ^ 4) := by
  have hm2 : 0 < m - 2 := by linarith only [hm]
  have ha : 0 < 1 - y := by linarith only [hy]
  unfold fiberOuterPSecondM fiberOuterPK2
  field_simp [hm2.ne',ha.ne']
  ring

theorem fiber_outer_PSecond_negative {m y : ℝ} (hm : 18 ≤ m) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    fiberOuterPSecondM m y < 0 := by
  have hm0 : 0 < m := by linarith only [hm]
  have hm2 : 0 < m - 2 := by linarith only [hm]
  have ha : 0 < 1 - y := by linarith only [hyh]
  have hk : 0 < fiberOuterPK2 m := by
    unfold fiberOuterPK2
    have h3 : 0 < m - 3 := by linarith only [hm]
    have h5 : 0 < 2 * m - 5 := by linarith only [hm]
    positivity
  unfold fiberOuterPSecondM
  have h1 : 0 < 2 * fiberOuterPK2 m / (1 - y) ^ 3 := by positivity
  have h2 : 0 < m / (6 * (1 - y) ^ 4) := by positivity
  simp only [neg_mul,neg_div]
  linarith only [h1,h2]

theorem fiber_outer_PPrime_antitone {m : ℝ} (hm : 18 ≤ m) :
    AntitoneOn (fiberOuterPPrimeM m) (Icc 0 (4 / 25 : ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fiberOuterPSecondM m) (convex_Icc _ _)
  · intro y hy
    exact (fiber_hasDerivAt_outer_PPrime (m := m) (by linarith only [hy.2])).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Icc 0 (4 / 25 : ℝ) := interior_subset hy
    exact (fiber_hasDerivAt_outer_PPrime (m := m) (by linarith only [hy'.2])).hasDerivWithinAt
  · intro y hy
    have hy' : y ∈ Icc 0 (4 / 25 : ℝ) := interior_subset hy
    exact (fiber_outer_PSecond_negative hm hy'.1 hy'.2).le

theorem fiber_outer_PPrime_edge {m : ℝ} (hm : 2 < m) :
    fiberOuterPPrimeM m (4 / 25) =
      (53801 / 166698 : ℝ) * m - 1391 / 378 + 8 / m - 625 / (2646 * (m - 2)) := by
  have hm0 : 0 < m := by linarith only [hm]
  have hm2 : 0 < m - 2 := by linarith only [hm]
  unfold fiberOuterPPrimeM fiberOuterPK1 fiberOuterPK2
  norm_num
  field_simp [hm0.ne',hm2.ne']
  ring

end Erdos993Lean.Analytic.V213
