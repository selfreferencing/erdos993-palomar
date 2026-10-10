module

public import Erdos993Lean.Analytic.V213.FiberUpperConsumer
public import Erdos993Lean.Analytic.V213.FiberRayTemplate

/-!
Actual all-integer upper-offset supporting-line bound in the
negative omega_U case. Both N Delta terms are retained separately,
with the exact actual U_N logarithm and Eq72 template Taylor bound.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_supporting_line {M : ℕ} {q mu : ℝ}
    (hM : 8 ≤ M) (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (hω : fiberUpperOmega mu (fiberSkew q) (M + 2) < 0) :
    let N := (M : ℝ) + 2
    let r := fiberSkew q
    let Tω := fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2))
    let Uω := fiberUpperOmega mu r (M + 2)
    mu * (fiberF q mu M j - fiberPsi ((M : ℝ) / mu)) ≥
      fiberTaylorT ((M : ℝ) / mu) (M : ℝ) -
        2 * N * ((rhoU r N)⁻¹ - (rho N)⁻¹) * G Tω + N * Delta r N -
        |G1 Uω| * (2 * N * eU r N / rhoU r N - N * Delta r N) := by
  dsimp
  let N : ℝ := (M : ℝ) + 2
  let r := fiberSkew q
  let Tω := fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2))
  let Uω := fiberUpperOmega mu r (M + 2)
  have hN : (10 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast (by omega : 10 ≤ M + 2)
  have hNp : 0 < N := by linarith only [hN]
  have hr : 0 ≤ r := by dsimp [r,fiberSkew]; linarith only [hq0]
  have hrh : r ≤ 1 / 2 := by dsimp [r,fiberSkew]; linarith only [hqh]
  have hρ : 0 < rhoU r N := lt_trans (by norm_num) (fiber_uniform_upper_rate hN hr hrh)
  have hB : 0 < N / mu := div_pos hNp hmu
  have hf := fiber_upper_constrained_gain hM hq0 hqh hmu j hw
  rw [min_eq_right hω.le] at hf
  change fiberBonus q M - 2 / rhoU r N * G Uω ≤ fiberF q mu M j / (N / mu) at hf
  have hscaled := mul_le_mul_of_nonneg_left ((le_div_iff₀ hB).mp hf) hmu.le
  have hF : N * (1 + Delta r N) - 2 * N / rhoU r N * G Uω ≤ mu * fiberF q mu M j := by
    rw [← fiber_upper_gamma_identity (by linarith only [hq0] : 0 < q) (by linarith only [hqh] : q < 1) M] at hscaled
    change mu * ((gamma r N - 2 / rhoU r N * G Uω) * (N / mu)) ≤ mu * fiberF q mu M j at hscaled
    unfold gamma at hscaled
    convert hscaled using 1 <;> field_simp [hmu.ne'] <;> ring
  have hOi := fiber_upper_omega_identity (r := r) hmu (by omega : 2 ≤ M + 2)
  push_cast at hOi
  change Uω = Tω + rhoU r N * Delta r N / 2 - eU r N at hOi
  have hGt := fiber_G_taylor_all_real Tω (Uω - Tω)
  rw [show Tω + (Uω - Tω) = Uω by ring] at hGt
  have hshift : Uω - Tω = rhoU r N * Delta r N / 2 - eU r N := by linarith only [hOi]
  rw [hshift] at hGt
  have hgscaled := mul_le_mul_of_nonneg_left hGt (by positivity : 0 ≤ 2 * N / rhoU r N)
  have hsig : G1 Uω < 0 := by
    have h := shared_G1_strictMono hω
    simpa only [shared_G1_zero] using h
  have ht : N - mu * fiberPsi ((M : ℝ) / mu) - 2 * (N + 1) * G Tω ≥
      fiberTaylorT ((M : ℝ) / mu) (M : ℝ) := by
    have h := fiber_upper_taylor_minorant hM hmu
    convert h using 1 <;> dsimp [N,Tω] <;> ring
  have hid : N * (1 + Delta r N) - 2 * N / rhoU r N *
      (G Tω + (rhoU r N * Delta r N / 2 - eU r N) * G1 Uω) -
      mu * fiberPsi ((M : ℝ) / mu) =
      N - mu * fiberPsi ((M : ℝ) / mu) - 2 * (N + 1) * G Tω -
        2 * N * ((rhoU r N)⁻¹ - (rho N)⁻¹) * G Tω + N * Delta r N -
        |G1 Uω| * (2 * N * eU r N / rhoU r N - N * Delta r N) := by
    rw [abs_of_nonpos hsig.le]
    unfold rho
    field_simp [hNp.ne',hρ.ne',ne_of_gt (by linarith only [hNp] : 0 < N + 1)]
    ring
  have hbound : fiberTaylorT ((M : ℝ) / mu) (M : ℝ) -
      2 * N * ((rhoU r N)⁻¹ - (rho N)⁻¹) * G Tω + N * Delta r N -
      |G1 Uω| * (2 * N * eU r N / rhoU r N - N * Delta r N) ≤
      mu * (fiberF q mu M j - fiberPsi ((M : ℝ) / mu)) := by
    linarith only [hF,hgscaled,ht,hid]
  exact hbound

end Erdos993Lean.Analytic.V213
