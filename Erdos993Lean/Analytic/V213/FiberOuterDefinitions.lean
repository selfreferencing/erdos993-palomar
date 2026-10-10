module

public import Erdos993Lean.Analytic.V213.FiberGainMonotonicity
public import Erdos993Lean.Analytic.V213.FiberUpperEnvelope

/-!
Exact outer-envelope definitions.
P is written rationally in y to avoid introducing sqrt(y) into calculus;
its identity with D_*+y*C_sqrt(y) is proved. The chi lower and square-root
bounds hold on the full real-width domain N>=17, with no finite family.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberOuterChi (N : ℝ) : ℝ := 1 - 1 / (2 * N) - 1 / (6 * N ^ 2)

noncomputable def fiberOuterC (m y : ℝ) : ℝ :=
  ((1 - y / (3 * (1 - y))) * m - 4) ^ 2 / (2 * m) -
    (m - 1) / (6 * (1 - y) * (m - 2)) - y * m / (12 * (1 - y) ^ 2)

noncomputable def fiberOuterP (N y : ℝ) : ℝ := fiberGainD (N + 1) + y * fiberOuterC (N + 1) y

noncomputable def fiberOuterR (N y : ℝ) : ℝ :=
  (1 - y) * N / (N + 1) - (2 / (N + 1) + y / (3 * (1 - y))) / fiberOuterChi N

noncomputable def fiberOuterDelta (N y : ℝ) : ℝ := y / (1 - y) * (N - 1 + 1 / N)

noncomputable def fiberOuterU (N y t : ℝ) : ℝ :=
  1 + fiberOuterDelta N y - 2 / fiberOuterR N y *
    V22.G (min 0 ((5 / 2 : ℝ) * Real.log t + fiberOuterP N y))

theorem fiber_outer_C_square (m r : ℝ) : fiberOuterC m (r ^ 2) = fiberGainC r m := rfl

theorem fiber_outer_P_square (N r : ℝ) :
    fiberOuterP N (r ^ 2) = fiberGainD (N + 1) + r ^ 2 * fiberGainC r (N + 1) := rfl

theorem fiber_outer_P_sqrt {y : ℝ} (hy : 0 ≤ y) (N : ℝ) :
    fiberOuterP N y = fiberGainD (N + 1) + y * fiberGainC (Real.sqrt y) (N + 1) := by
  unfold fiberOuterP fiberOuterC fiberGainC
  rw [Real.sq_sqrt hy]

theorem fiber_outer_chi_bounds {N : ℝ} (hN : 17 ≤ N) :
    31 / 32 ≤ fiberOuterChi N ∧ fiberOuterChi N < 1 := by
  have hn : 0 < N := by linarith only [hN]
  have h1 : 1 / (2 * N) ≤ (1 / 34 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hN])
  have h2 : 1 / (6 * N ^ 2) ≤ (1 / 1734 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith only [hN])
  have hpos : 0 < 1 / (2 * N) := by positivity
  have hnon : 0 ≤ 1 / (6 * N ^ 2) := by positivity
  unfold fiberOuterChi
  constructor <;> linarith only [h1,h2,hpos,hnon]

theorem fiber_outer_chi_pos {N : ℝ} (hN : 17 ≤ N) : 0 < fiberOuterChi N := by
  linarith only [(fiber_outer_chi_bounds hN).1]

theorem fiber_outer_chi_square {N : ℝ} (hN : 0 < N) :
    (1 - 1 / N) - fiberOuterChi N ^ 2 = (3 * N ^ 2 - 6 * N - 1) / (36 * N ^ 4) := by
  unfold fiberOuterChi
  field_simp [hN.ne']
  ring

theorem fiber_outer_chi_sqrt {N : ℝ} (hN : 17 ≤ N) :
    fiberOuterChi N ≤ Real.sqrt (1 - 1 / N) := by
  have hn : 0 < N := by linarith only [hN]
  have hinv : 1 / N ≤ 1 := (div_le_one hn).2 (by linarith only [hN])
  have ha : 0 ≤ 1 - 1 / N := by linarith only [hinv]
  have hs := fiber_outer_chi_square hn
  have hp : 0 ≤ (3 * N ^ 2 - 6 * N - 1) / (36 * N ^ 4) := by
    apply div_nonneg _ (by positivity)
    nlinarith only [hN]
  apply (sq_le_sq₀ (fiber_outer_chi_pos hN).le (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt ha]
  linarith only [hs,hp]

theorem fiber_outer_chi_increases : MonotoneOn fiberOuterChi (Ici (17 : ℝ)) := by
  intro N hN M hM hNM
  change 17 ≤ N at hN
  change 17 ≤ M at hM
  have hn : 0 < N := by linarith only [hN]
  have hm : 0 < M := by linarith only [hM]
  have h1 : 1 / (2 * M) ≤ 1 / (2 * N) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hNM])
  have h2 : 1 / (6 * M ^ 2) ≤ 1 / (6 * N ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith only [hNM,hn])
  unfold fiberOuterChi
  linarith only [h1,h2]

theorem fiber_outer_delta_actual {N r : ℝ} (hN : 0 < N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberOuterDelta N (r ^ 2) = V22.Delta r N := by
  have ha : 0 < 1 - r ^ 2 := by nlinarith only [hr0,hrh]
  unfold fiberOuterDelta V22.Delta
  field_simp [hN.ne',ha.ne'] <;> ring

theorem fiber_outer_P_actual {N r : ℝ} (hN : 17 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberOuterP N (r ^ 2) ≤ V22.phiR r N := by
  rw [fiber_outer_P_square]
  exact fiber_uniform_phi_lower (by linarith only [hN]) hr0 le_rfl hrh

theorem fiber_outer_R_actual {N r : ℝ} (hN : 17 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberOuterR N (r ^ 2) ≤ V22.rhoU r N := by
  have hn : 0 < N := by linarith only [hN]
  have ha : 0 < 1 - r ^ 2 := by nlinarith only [hr0,hrh]
  have hchi := fiber_outer_chi_pos hN
  have hcmp := fiber_outer_chi_sqrt hN
  have hs : 0 < Real.sqrt (1 - 1 / N) := hchi.trans_le hcmp
  have hnum : 0 ≤ 2 / (N + 1) + r ^ 2 / (3 * (1 - r ^ 2)) := by positivity
  have hdiv := div_le_div_of_nonneg_left hnum hchi hcmp
  have hl := fiber_upper_rate_lower (r := r) (rm := r) (by linarith only [hN]) hr0 le_rfl hrh
  rw [fiber_rhoStar_formula] at hl
  unfold fiberOuterR V22.rho at *
  have he : (1 - r ^ 2) * (N / (N + 1)) = (1 - r ^ 2) * N / (N + 1) := by ring
  rw [he] at hl
  linarith only [hl,hdiv]

end Erdos993Lean.Analytic.V213
