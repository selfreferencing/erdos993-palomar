module

public import Erdos993Lean.Analytic.V213.FiberOuterGainCalculus
public import Erdos993Lean.Analytic.V213.FiberOuterRates

/-!
Full-domain lower bound for P_y and exact printed mixed derivative.
The edge value is derived from the canonical rational formula. The y
concavity, m monotonicity and source gain monotonicity are discharged;
no derivative/monotonicity lemma is assumed as a paper premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberOuterPMixedEdge (m : ℝ) : ℝ :=
  53801 / 166698 - 8 / m ^ 2 + 1 / (6 * (21 / 25 : ℝ) ^ 2 * (m - 2) ^ 2)

theorem fiber_hasDerivAt_outer_PPrime_edge {m : ℝ} (hm : 2 < m) :
    HasDerivAt (fun x => fiberOuterPPrimeM x (4 / 25)) (fiberOuterPMixedEdge m) m := by
  have hm0 : 0 < m := by linarith only [hm]
  have hm2 : 0 < m - 2 := by linarith only [hm]
  have h1 := (hasDerivAt_id m).const_mul (53801 / 166698 : ℝ)
  have h2 := (hasDerivAt_const m (8 : ℝ)).div (hasDerivAt_id m) hm0.ne'
  have h3 := (hasDerivAt_const m (625 : ℝ)).div (((hasDerivAt_id m).sub_const 2).const_mul 2646) (by dsimp; positivity)
  have h := (((h1.sub_const (1391 / 378 : ℝ)).add h2).sub h3)
  have he : HasDerivAt (fun x => (53801 / 166698 : ℝ) * x - 1391 / 378 +
      8 / x - 625 / (2646 * (x - 2))) (fiberOuterPMixedEdge m) m := by
    convert h using 1
    · funext x
      rfl
    · dsimp [fiberOuterPMixedEdge]
      norm_num
      field_simp [hm0.ne',hm2.ne']
      ring
  apply he.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hm] with x hx
  exact fiber_outer_PPrime_edge hx

theorem fiber_outer_PMixedEdge_positive {m : ℝ} (hm : 18 ≤ m) :
    0 < fiberOuterPMixedEdge m := by
  have hm0 : 0 < m := by linarith only [hm]
  have hm2 : 0 < m - 2 := by linarith only [hm]
  have h8 : 8 / m ^ 2 ≤ (2 / 81 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < m ^ 2)).2
    nlinarith only [hm]
  have hp : 0 < 1 / (6 * (21 / 25 : ℝ) ^ 2 * (m - 2) ^ 2) := by positivity
  unfold fiberOuterPMixedEdge
  linarith only [h8,hp]

theorem fiber_outer_PPrime_edge_increases :
    StrictMonoOn (fun m => fiberOuterPPrimeM m (4 / 25)) (Ici (18 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberOuterPMixedEdge) (convex_Ici _)
  · intro m hm
    change 18 ≤ m at hm
    exact (fiber_hasDerivAt_outer_PPrime_edge (by linarith only [hm])).continuousAt.continuousWithinAt
  · intro m hm
    have hm' : 18 < m := by simpa only [interior_Ici,mem_Ioi] using hm
    exact (fiber_hasDerivAt_outer_PPrime_edge (by linarith only [hm'])).hasDerivWithinAt
  · intro m hm
    have hm' : 18 < m := by simpa only [interior_Ici,mem_Ioi] using hm
    exact fiber_outer_PMixedEdge_positive hm'.le

theorem fiber_outer_PPrime_start : fiberOuterPPrimeM 18 (4 / 25) = (758425 / 296352 : ℝ) := by
  rw [fiber_outer_PPrime_edge (by norm_num : (2 : ℝ) < 18)]
  norm_num

theorem fiber_outer_PPrime_lower {N y : ℝ} (hN : 17 ≤ N) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    758425 / 296352 ≤ fiberOuterPPrimeM (N + 1) y := by
  have hm : 18 ≤ N + 1 := by linarith only [hN]
  have hE := fiber_outer_PPrime_edge_increases.monotoneOn (show (18 : ℝ) ∈ Ici 18 by exact le_rfl) hm hm
  rw [fiber_outer_PPrime_start] at hE
  have hY := fiber_outer_PPrime_antitone hm ⟨hy0,hyh⟩ (by norm_num) hyh
  exact hE.trans hY

theorem fiber_outer_gain_slope_dominates_rate {N y : ℝ} (hN : 17 ≤ N) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    5 / 2 < fiberOuterPPrimeM (N + 1) y ∧
      -fiberOuterRPrime N y / fiberOuterR N y < fiberOuterPPrimeM (N + 1) y := by
  have hP : 5 / 2 < fiberOuterPPrimeM (N + 1) y := by
    linarith only [fiber_outer_PPrime_lower hN hy0 hyh]
  exact ⟨hP,(fiber_outer_rate_slope_ratio hN hy0 hyh).trans hP⟩

theorem fiber_outer_P_increases_y {N : ℝ} (hN : 17 ≤ N) :
    StrictMonoOn (fiberOuterP N) (Icc 0 (4 / 25 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberOuterPPrimeM (N + 1)) (convex_Icc _ _)
  · intro y hy
    exact (fiber_hasDerivAt_outer_P (by linarith only [hN]) (by linarith only [hy.2])).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Icc 0 (4 / 25 : ℝ) := interior_subset hy
    exact (fiber_hasDerivAt_outer_P (by linarith only [hN]) (by linarith only [hy'.2])).hasDerivWithinAt
  · intro y hy
    have hy' : y ∈ Icc 0 (4 / 25 : ℝ) := interior_subset hy
    linarith only [(fiber_outer_gain_slope_dominates_rate hN hy'.1 hy'.2).1]

theorem fiber_outer_P_increases_N {a n : ℝ} (ha : 0 < a) (hah : a ≤ 2 / 5)
    (hn : 17 ≤ n) (hna : 18 / 5 ≤ (n + 1) * a) :
    StrictMonoOn (fun N => fiberOuterP N (a ^ 2)) (Ici n) := by
  have hmono := fiber_gain_frozen_strictMono (b := a) ha le_rfl (by linarith only [hah])
    (by linarith only [hn] : 11 ≤ n + 1) hna
  intro N hN M hM hNM
  change n ≤ N at hN
  change n ≤ M at hM
  simpa only [fiber_outer_P_square] using hmono (show n + 1 ≤ N + 1 by linarith only [hN])
    (show n + 1 ≤ M + 1 by linarith only [hM]) (by linarith only [hNM] : N + 1 < M + 1)

end Erdos993Lean.Analytic.V213
