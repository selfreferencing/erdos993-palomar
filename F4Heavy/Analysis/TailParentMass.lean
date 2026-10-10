module

public import F4Heavy.Analysis.TailDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_probability_antitone (lam X Y : ℝ) (hl : 0 < lam) (hXY : X ≤ Y) :
    p lam Y ≤ p lam X := by
  have he := Real.exp_le_exp.mpr (neg_le_neg hXY)
  unfold p
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + lam * Real.exp (-Y))
    (by positivity : 0 < 1 + lam * Real.exp (-X))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left he hl.le]

theorem tail_probability_mass_derivative (lam Y : ℝ) (hl : 0 < lam) :
    HasDerivAt (fun x => p lam x * x) (p lam Y * (1 - Y * (1 - p lam Y))) Y := by
  convert (tail_parent_probability_derivative lam Y hl).mul (hasDerivAt_id Y) using 1
  · rfl
  · dsimp
    ring

theorem tail_probability_mass_antitone (lam tau : ℝ) (hl : 0 < lam)
    (ht : 3 / 2 ≤ tau) (hp : p lam tau ≤ 1 / 6) :
    AntitoneOn (fun Y => p lam Y * Y) (Set.Ici tau) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici tau)
  · intro Y hY
    exact (tail_probability_mass_derivative lam Y hl).continuousAt.continuousWithinAt
  · intro Y hY
    exact (tail_probability_mass_derivative lam Y hl).differentiableAt.differentiableWithinAt
  · intro Y hY
    have htY : tau ≤ Y := interior_subset hY
    have hY0 : 0 ≤ Y := by linarith only [ht, htY]
    have hpY := (tail_probability_antitone lam tau Y hl htY).trans hp
    have hmult := mul_le_mul_of_nonneg_left hpY hY0
    have hsign : 1 - Y * (1 - p lam Y) ≤ 0 := by nlinarith only [ht, htY, hmult]
    rw [(tail_probability_mass_derivative lam Y hl).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (p_pos lam Y hl).le hsign

theorem tail_probability_mass_bound (r : Row) (lam Y : ℝ) (hl : 0 < lam)
    (htlo : 3 / 2 ≤ tailTau r lam) (hthi : tailTau r lam ≤ tailTauHi r lam)
    (hps : tailPStar r lam ≤ 1 / 6) (hY : tailTau r lam ≤ Y) :
    p lam Y * Y ≤ tailPStar r lam * tailTauHi r lam := by
  have hpstar : p lam (tailTau r lam) ≤ 1 / 6 := by
    rw [tail_probability_at_threshold r lam hl]
    exact hps
  have h := tail_probability_mass_antitone lam (tailTau r lam) hl htlo hpstar
    (show tailTau r lam ∈ Set.Ici (tailTau r lam) from le_rfl) hY hY
  dsimp only at h
  rw [tail_probability_at_threshold r lam hl] at h
  exact h.trans (mul_le_mul_of_nonneg_left hthi
    (by rw [← tail_probability_at_threshold r lam hl]; exact (p_pos lam _ hl).le))

theorem tail_p1_order (r : Row) (lam x z : ℝ) (hg : 0 ≤ gamma r lam)
    (hx : 0 ≤ x) (hxz : x ≤ z) : tailP1 r lam z ≤ tailP1 r lam x := by
  have hz : 0 ≤ z := hx.trans hxz
  have hsq : x ^ 2 ≤ z ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hxz) (add_nonneg hx hz)]
  have hv : tailV z ≤ tailV x := by unfold tailV; linarith only [hxz, hsq]
  have hm := mul_le_mul_of_nonneg_left hv hg
  unfold tailP1
  linarith only [hm, hxz]

theorem tail_p1_derivative (r : Row) (lam Y : ℝ) (hl : 0 < lam) :
    HasDerivAt (fun x => tailP1 r lam (p lam x))
      (p lam Y * (1 - p lam Y) * (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6)) Y := by
  have hp := tail_parent_probability_derivative lam Y hl
  have h := (hp.const_sub 1).add
    ((((hp.div_const 2).const_sub 1).sub ((hp.pow 2).div_const 12)).const_mul (gamma r lam))
  convert h using 1
  · rfl
  · ring

end F4Heavy.Analysis
