module

public import Erdos993Lean.Analytic.V213.FiberProfileDefinitions

/-!
Actual derivatives of the rational root coefficients and their
whole-domain increase. Both printed C' cases retain their exact constants
and closed lower root endpoints.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set
open scoped Topology

noncomputable def fiberProfileCPrime (cf df a : ℝ) : ℝ :=
  -6 + (df - 11 / 10 + cf * (3 - 2 * a) / (2 - a) ^ 2) / (1 - a) ^ 2

theorem fiber_profile_G0_hasDerivAt {a : ℝ} (ha : a < 1) :
    HasDerivAt fiberProfileG0 (a * (2 - a) / (1 - a) ^ 2) a := by
  have hd : 1 - a ≠ 0 := by linarith only [ha]
  have h := ((hasDerivAt_id a).pow 2).div
    ((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)) hd
  convert h using 1
  · rfl
  · dsimp
    field_simp [hd]
    ring

theorem fiber_profile_G0_increases : MonotoneOn fiberProfileG0 (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun a => a * (2 - a) / (1 - a) ^ 2) (convex_Ico _ _)
  · intro a ha
    exact (fiber_profile_G0_hasDerivAt ha.2).continuousAt.continuousWithinAt
  · intro a ha
    exact (fiber_profile_G0_hasDerivAt (interior_subset ha).2).hasDerivWithinAt
  · intro a ha
    have ha' := interior_subset ha
    exact div_nonneg (mul_nonneg ha'.1 (by linarith only [ha'.2])) (sq_nonneg _)

theorem fiber_profile_C_hasDerivAt (cf df : ℝ) {a : ℝ} (ha : a < 1) :
    HasDerivAt (fiberProfileC cf df) (fiberProfileCPrime cf df a) a := by
  have hd1 : 1 - a ≠ 0 := by linarith only [ha]
  have hd2 : 2 - a ≠ 0 := by linarith only [ha]
  have h1 := (hasDerivAt_const a (1 : ℝ)).div
    ((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)) hd1
  have h2 := (hasDerivAt_const a (1 : ℝ)).div
    ((hasDerivAt_const a (2 : ℝ)).sub (hasDerivAt_id a)) hd2
  have hl := ((hasDerivAt_id a).const_mul (-6)).sub_const 2
  have h := (hl.add ((h1.sub_const 1).const_mul (df - 11 / 10))).add
    ((h1.sub h2).const_mul cf)
  have heqOn : (fun x => -6 * x - 2 + (df - 11 / 10) * (1 / (1 - x) - 1) +
      cf * (1 / (1 - x) - 1 / (2 - x))) =ᶠ[𝓝 a] fiberProfileC cf df := by
    filter_upwards [Iio_mem_nhds ha] with x hx
    change x < 1 at hx
    exact (fiber_profile_C_reciprocal (by linarith only [hx]) (by linarith only [hx])).symm
  have h' := h.congr_of_eventuallyEq heqOn.symm
  convert h' using 1
  dsimp [fiberProfileCPrime]
  field_simp [hd1,hd2]
  ring

theorem fiber_profile_root_quotient_half {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    8 / 9 ≤ (3 - 2 * a) / (2 - a) ^ 2 := by
  have hd : 0 < (2 - a) ^ 2 := sq_pos_of_pos (by linarith only [ha1])
  apply (le_div_iff₀ hd).2
  have hp : 0 ≤ (2 * a - 1) * (5 - 4 * a) := by
    exact mul_nonneg (by linarith only [ha]) (by linarith only [ha1])
  nlinarith only [hp]

theorem fiber_profile_root_quotient_three_quarters {a : ℝ}
    (ha : 3 / 4 ≤ a) (ha1 : a < 1) :
    24 / 25 ≤ (3 - 2 * a) / (2 - a) ^ 2 := by
  have hd : 0 < (2 - a) ^ 2 := sq_pos_of_pos (by linarith only [ha1])
  apply (le_div_iff₀ hd).2
  have hp : 0 ≤ (4 * a - 3) * (7 - 6 * a) := by
    exact mul_nonneg (by linarith only [ha]) (by linarith only [ha1])
  nlinarith only [hp]

theorem fiber_profile_CPrime_lower {cf df a a0 q0 : ℝ}
    (ha0 : a0 ≤ a) (ha1 : a < 1) (hcf : 0 ≤ cf)
    (hq : q0 ≤ (3 - 2 * a) / (2 - a) ^ 2)
    (hbase : 6 * (1 - a0) ^ 2 < df - 11 / 10 + cf * q0) :
    0 < fiberProfileCPrime cf df a := by
  have hd : 0 < (1 - a) ^ 2 := sq_pos_of_pos (by linarith only [ha1])
  have hs : (1 - a) ^ 2 ≤ (1 - a0) ^ 2 := by nlinarith only [ha0,ha1]
  have hmul := mul_le_mul_of_nonneg_left hq hcf
  have hn : 6 * (1 - a) ^ 2 < df - 11 / 10 + cf * (3 - 2 * a) / (2 - a) ^ 2 := by
    have he : cf * ((3 - 2 * a) / (2 - a) ^ 2) = cf * (3 - 2 * a) / (2 - a) ^ 2 := by ring
    rw [he] at hmul
    linarith only [hbase,hs,hmul]
  have hdiv := (lt_div_iff₀ hd).2 hn
  unfold fiberProfileCPrime
  linarith only [hdiv]

theorem fiber_profile_CPrime_common {df a : ℝ} (hd : 13 / 10 ≤ df)
    (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    0 < fiberProfileCPrime (2601 / 1100) df a := by
  apply fiber_profile_CPrime_lower ha ha1 (by norm_num)
    (fiber_profile_root_quotient_half ha ha1)
  linarith only [hd]

theorem fiber_profile_CPrime_H {a : ℝ} (ha : 3 / 4 ≤ a) (ha1 : a < 1) :
    0 < fiberProfileCPrime (408321 / 333200) (4 / 5) a := by
  apply fiber_profile_CPrime_lower ha ha1 (by norm_num)
    (fiber_profile_root_quotient_three_quarters ha ha1)
  norm_num

theorem fiber_profile_C_common_increases {df : ℝ} (hd : 13 / 10 ≤ df) :
    StrictMonoOn (fiberProfileC (2601 / 1100) df) (Ico (1 / 2 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberProfileCPrime (2601 / 1100) df)
    (convex_Ico _ _)
  · intro a ha
    exact (fiber_profile_C_hasDerivAt _ _ ha.2).continuousAt.continuousWithinAt
  · intro a ha
    exact (fiber_profile_C_hasDerivAt _ _ (interior_subset ha).2).hasDerivWithinAt
  · intro a ha
    have ha' := interior_subset ha
    exact fiber_profile_CPrime_common hd ha'.1 ha'.2

theorem fiber_profile_C_H_increases :
    StrictMonoOn (fiberProfileC (408321 / 333200) (4 / 5)) (Ico (3 / 4 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberProfileCPrime (408321 / 333200) (4 / 5))
    (convex_Ico _ _)
  · intro a ha
    exact (fiber_profile_C_hasDerivAt _ _ ha.2).continuousAt.continuousWithinAt
  · intro a ha
    exact (fiber_profile_C_hasDerivAt _ _ (interior_subset ha).2).hasDerivWithinAt
  · intro a ha
    have ha' := interior_subset ha
    exact fiber_profile_CPrime_H ha'.1 ha'.2

theorem fiber_profile_D_root_increases {cf df rho kappa m s delta b beta t u a a' : ℝ}
    (hr : 0 < rho) (hk : 0 ≤ kappa) (hm : 0 < m) (hs : 0 < s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hah : a < 1) (ha'h : a' < 1) (haa' : a ≤ a')
    (hC : fiberProfileC cf df a ≤ fiberProfileC cf df a') :
    fiberProfileD cf df rho kappa m s delta b beta t u a ≤
      fiberProfileD cf df rho kappa m s delta b beta t u a' := by
  have hg := fiber_profile_G0_increases ⟨ha,hah⟩ ⟨ha.trans haa',ha'h⟩ haa'
  have hbs := fiber_profile_B_lower hr hk hm hs hu
  have hcoef : 0 ≤ fiberProfileB1 rho kappa s u * t + fiberProfileB0 rho kappa m s u := by
    have hb1 : 0 ≤ fiberProfileB1 rho kappa s u := by linarith only [hbs.1]
    exact add_nonneg (mul_nonneg hb1 ht) hbs.2
  have hg' := mul_le_mul_of_nonneg_right hg hcoef
  have hc' := div_le_div_of_nonneg_right hC hm.le
  rw [fiber_profile_D_normal hr.ne' hm.ne' hs.ne',fiber_profile_D_normal hr.ne' hm.ne' hs.ne']
  linarith only [hg',hc']

theorem fiber_profile_E_root_increases {t u a a' : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (ha : 0 ≤ a) (hah : a < 1) (ha'h : a' < 1) (haa' : a ≤ a') :
    fiberProfileE t u a ≤ fiberProfileE t u a' := by
  have hg := fiber_profile_G0_increases ⟨ha,hah⟩ ⟨ha.trans haa',ha'h⟩ haa'
  have hb : 0 ≤ fiberProfileEB0 u := by linarith only [fiber_profile_EB_lower hu]
  have h := mul_le_mul_of_nonneg_left hg (mul_nonneg ht hb)
  rw [fiber_profile_E_normal,fiber_profile_E_normal]
  linarith only [h]

end Erdos993Lean.Analytic.V213
