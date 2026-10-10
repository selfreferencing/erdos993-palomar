module

public import Erdos993Lean.Analytic.V213.FiberRootCalculus
public import Erdos993Lean.Analytic.V213.FiberTaylor
public import Erdos993Lean.Analytic.V213.FiberUniformConsequences

/-!
Actual negative template interval, Eq72 endpoint transport and
the literal root/f(t) identities used in the ray proof. All logarithms
refer to the actual t=M/mu and U_N template shift.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberRayAroot (t : ℝ) : ℝ := -V22.rootMap (5 / 2 * Real.log t)

noncomputable def fiberRayF (t : ℝ) : ℝ :=
  2 * t * G (5 / 2 * Real.log t) - 9 / 2 * (1 - t) ^ 2

noncomputable def fiberRayCF (mf : ℝ) : ℝ := (77 / 20 + 10 / mf) ^ 2 / (mf + 3)

theorem fiber_ray_template_negative {M : ℕ} {mu : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (ht : (M : ℝ) / mu ≤ 3 / 5) :
    5 / 2 * Real.log ((M : ℝ) / mu) ≤
      fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2)) ∧
      fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2)) < 0 := by
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : 0 < (M : ℝ) := by linarith only [hM8]
  have ht0 := div_pos hMp hmu
  have hk := fiber_upper_shift_bounds hM
  change 71 / 20 ≤ fiberUpperK M ∧ fiberUpperK M ≤ 77 / 20 + 10 / (M : ℝ) at hk
  have hshift := fiber_template_omega_shift (X := fiberUpperPrefactor (M + 2)) hmu
    (by omega : 0 < M) (symmetricUpperPrefactor_pos (M + 2))
  change fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2)) =
    5 / 2 * Real.log ((M : ℝ) / mu) + fiberUpperK M / ((M : ℝ) + 3) at hshift
  have hlog := Real.log_le_sub_one_of_pos ht0
  have hω : 5 / 2 * Real.log ((M : ℝ) / mu) ≤ (-1 : ℝ) := by linarith only [hlog,ht]
  have hrec : 10 / (M : ℝ) ≤ (5 / 4 : ℝ) := by
    apply (div_le_iff₀ hMp).2
    linarith only [hM8]
  have hkp : 0 ≤ fiberUpperK M := by linarith only [hk.1]
  have hm3 : 0 < (M : ℝ) + 3 := by positivity
  have hterm : fiberUpperK M / ((M : ℝ) + 3) ≤ (51 / 110 : ℝ) := by
    apply (div_le_iff₀ hm3).2
    linarith only [hk.2,hrec,hM8]
  rw [hshift]
  exact ⟨le_add_of_nonneg_right (div_nonneg hkp hm3.le),by linarith only [hω,hterm]⟩

theorem fiber_ray_root_formulas {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < fiberRayAroot t ∧ fiberRayAroot t < 1 ∧
      G (5 / 2 * Real.log t) = (fiberRayAroot t) ^ 2 / (1 - fiberRayAroot t) ∧
      |G1 (5 / 2 * Real.log t)| = fiberRayAroot t / (1 - fiberRayAroot t) ∧
      G2 (5 / 2 * Real.log t) = 1 / ((1 - fiberRayAroot t) * (2 - fiberRayAroot t)) := by
  have hω : 5 / 2 * Real.log t < (0 : ℝ) := mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg ht ht1)
  have hs0 : V22.rootMap (5 / 2 * Real.log t) < 0 := by
    have h := shared_rootMap_strictMono hω
    simpa only [shared_rootMap_zero] using h
  have hs1 := shared_rootMap_gt_neg_one (5 / 2 * Real.log t)
  have hd : 0 < 1 + V22.rootMap (5 / 2 * Real.log t) := by linarith only [hs1]
  have hG1 : G1 (5 / 2 * Real.log t) ≤ 0 := by
    unfold G1
    exact (div_neg_of_neg_of_pos hs0 hd).le
  refine ⟨by unfold fiberRayAroot; linarith only [hs0],by unfold fiberRayAroot; linarith only [hs1],?_,?_,?_⟩
  · unfold G fiberRayAroot
    ring
  · rw [abs_of_nonpos hG1]
    unfold G1 fiberRayAroot
    ring
  · unfold G2 fiberRayAroot
    ring

theorem fiber_ray_root_identity {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    -6 * G (5 / 2 * Real.log t) + 71 / 10 * |G1 (5 / 2 * Real.log t)| =
      6 * fiberRayAroot t + 11 / 10 * |G1 (5 / 2 * Real.log t)| := by
  have h := fiber_ray_root_formulas ht ht1
  rw [h.2.2.1,h.2.2.2.1]
  have hd : 0 < 1 - fiberRayAroot t := by linarith only [h.2.1]
  field_simp [hd.ne']
  ring

theorem fiber_ray_f_identity {t : ℝ} (ht : 0 < t) : fiberRayF t = -t * fiberTaylorS t := by
  unfold fiberRayF fiberTaylorS
  field_simp [ht.ne']
  ring

theorem fiber_ray_taylor_endpoint_bound {t M mf k : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hmf : 8 ≤ mf) (hM : mf ≤ M)
    (hk0 : 71 / 20 ≤ k) (hk : k ≤ 77 / 20 + 10 / M) :
    M * fiberTaylorS t + 2 - 6 * G (5 / 2 * Real.log t) +
      71 / 10 * |G1 (5 / 2 * Real.log t)| - fiberRayCF mf * G2 (5 / 2 * Real.log t) ≤
      fiberTaylorEndpoint t M k := by
  have h := fiber_ray_root_formulas ht ht1
  have hmf0 : 0 < mf := by linarith only [hmf]
  have hM0 : 0 < M := hmf0.trans_le hM
  have hk0' : 0 ≤ k := by linarith only [hk0]
  have hkk : k ≤ 77 / 20 + 10 / mf := hk.trans
    (add_le_add (le_refl (77 / 20 : ℝ)) (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 10) hmf0 hM))
  have hkmax : 0 ≤ 77 / 20 + 10 / mf := by positivity
  have hsq := (sq_le_sq₀ hk0' hkmax).2 hkk
  have hcoef : k ^ 2 / (M + 3) ≤ fiberRayCF mf := by
    unfold fiberRayCF
    exact (div_le_div_of_nonneg_right hsq (by positivity)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith only [hM]))
  have hG2 := shared_G2_pos (5 / 2 * Real.log t)
  have hquad := mul_le_mul_of_nonneg_right hcoef hG2.le
  have hω : 5 / 2 * Real.log t < (0 : ℝ) := mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg ht ht1)
  have hG1 : G1 (5 / 2 * Real.log t) < 0 := by
    have hm := shared_G1_strictMono hω
    simpa only [shared_G1_zero] using hm
  have hlin := mul_le_mul_of_nonneg_right hk0 (neg_nonneg.mpr hG1.le)
  rw [abs_of_nonpos hG1.le]
  unfold fiberTaylorEndpoint
  have hq : k ^ 2 * G2 (5 / 2 * Real.log t) / (M + 3) ≤ fiberRayCF mf * G2 (5 / 2 * Real.log t) := by
    convert hquad using 1 <;> ring
  linarith only [hlin,hq]

theorem fiber_ray_taylor_bound {t M mf : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hmf : 8 ≤ mf) (hM : mf ≤ M) :
    M * fiberTaylorS t + 2 - 6 * G (5 / 2 * Real.log t) +
      71 / 10 * |G1 (5 / 2 * Real.log t)| - fiberRayCF mf * G2 (5 / 2 * Real.log t) ≤
      fiberTaylorT t M := by
  have hM0 : 0 < M := by linarith only [hmf,hM]
  unfold fiberTaylorT
  apply le_min
  · exact fiber_ray_taylor_endpoint_bound ht ht1 hmf hM (le_refl _)
      (by
        have hp : 0 ≤ 10 / M := by positivity
        linarith only [hp])
  · exact fiber_ray_taylor_endpoint_bound ht ht1 hmf hM
      (by
        have hp : 0 ≤ 10 / M := by positivity
        linarith only [hp]) (le_refl _)

end Erdos993Lean.Analytic.V213
