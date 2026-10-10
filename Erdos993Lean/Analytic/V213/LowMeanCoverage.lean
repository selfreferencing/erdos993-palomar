module

public import Erdos993Lean.Analytic.V213.LowMeanCoverageFacts

/-! The literal eleven-group coverage lemma, with closed mean seams and
left-selected activity seams on the actual accepted N44 intervals. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_input_probability_group (i : ℕ) (hi : i < 55) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ)) :
    FreeCountVariance.q lam ∈ Set.Icc
      (lowMeanFractionReal (lowMeanGroupAt (lowMeanInputRowAt i).group).l)
      (lowMeanFractionReal (lowMeanGroupAt (lowMeanInputRowAt i).group).h) := by
  obtain ⟨ha, _, _, hql, hqh, _⟩ := lowMean_n44_endpoint_facts i hi
  have ha0 : (0 : ℝ) ≤ (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ) := by linarith
  have hlam0 : 0 ≤ lam := le_trans ha0 hlam.1
  exact ⟨le_trans hql (FreeCountVariance.q_le_q ha0 hlam.1),
    le_trans (FreeCountVariance.q_le_q hlam0 hlam.2) hqh⟩

/-- Coverage on each full closed input interval is stronger than the
left-selected convention. Both ends of every certificate mean range are included. -/
theorem lowMean_coverage_activity (i : ℕ) (hi : i < 55) {lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ))
    (hmu : mu ∈ Set.Icc (4 / FreeCountVariance.q lam)
      (lowMeanFractionReal (lowMeanInputRowAt i).mu0)) :
    ∃ c, c < 28 ∧ lowMeanCertificateGroupAt c = (lowMeanInputRowAt i).group ∧
      FreeCountVariance.q lam ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt c).l)
        (lowMeanFractionReal (lowMeanCertificateAt c).h) ∧
      mu ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt c).muA)
        (lowMeanFractionReal (lowMeanCertificateAt c).muB) ∧
      mu ∈ Set.Icc (max (lowMeanFractionReal (lowMeanCertificateAt c).muA)
        (4 / FreeCountVariance.q lam)) (lowMeanFractionReal (lowMeanCertificateAt c).muB) := by
  let k := (lowMeanInputRowAt i).group
  let g := lowMeanGroupAt k
  obtain ⟨hk, _, _, hupper⟩ := lowMean_input_real_caps i hi
  have hq := lowMean_input_probability_group i hi hlam
  have he := lowMean_n44_endpoint_facts i hi
  have hlampos : 0 < lam := by linarith [hlam.1, he.1]
  have hqpos := FreeCountVariance.q_pos hlampos
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hfloor⟩ := lowMean_group_real_facts k hk
  have hb := lowMean_group_bounds k hk
  have first := lowMean_group_certificate_fields k g.certLo hk ⟨le_rfl, hb.2.2.1⟩
  have last := lowMean_group_certificate_fields k g.certHi hk ⟨hb.2.2.1, le_rfl⟩
  have hf : lowMeanFractionReal (lowMeanCertificateAt g.certLo).muA ≤ mu := by
    rw [first.2.2.2.2.2.1 rfl, hfloor]
    exact le_trans (div_le_div_of_nonneg_left (by norm_num) hqpos hq.2) hmu.1
  have hh : mu ≤ lowMeanFractionReal (lowMeanCertificateAt g.certHi).muB := by
    rw [last.2.2.2.2.2.2.1 rfl]
    exact le_trans hmu.2 hupper
  have hend : g.certLo + (g.certHi - g.certLo) = g.certHi := by dsimp only [g] at *; omega
  have hs : ∀ c, g.certLo ≤ c → c < g.certLo + (g.certHi - g.certLo) →
      lowMeanFractionReal (lowMeanCertificateAt c).muB =
        lowMeanFractionReal (lowMeanCertificateAt (c + 1)).muA := by
    intro c hc hc'
    have facts := lowMean_group_certificate_fields k c hk ⟨hc, by dsimp only [g] at *; omega⟩
    exact congrArg lowMeanFractionReal (facts.2.2.2.2.2.2.2 (by dsimp only [g] at *; omega))
  obtain ⟨c, hc, hc', hrange⟩ := lowMean_consecutive_closed_cover
    (fun c => lowMeanFractionReal (lowMeanCertificateAt c).muA)
    (fun c => lowMeanFractionReal (lowMeanCertificateAt c).muB) mu g.certLo
    (g.certHi - g.certLo) hf (by simpa only [hend] using hh) hs
  have facts := lowMean_group_certificate_fields k c hk ⟨hc, by dsimp only [g] at *; omega⟩
  have hqc : FreeCountVariance.q lam ∈ Set.Icc
      (lowMeanFractionReal (lowMeanCertificateAt c).l) (lowMeanFractionReal (lowMeanCertificateAt c).h) := by
    simpa only [facts.2.1, facts.2.2.1] using hq
  exact ⟨c, facts.1, lowMean_group_certificate_member k c hk ⟨hc, by dsimp only [g] at *; omega⟩,
    hqc, hrange, max_le_iff.mpr ⟨hrange.1, hmu.1⟩, hrange.2⟩

/-- Literal Lemma 6.3: q belongs to the image of the actual closed activity input. -/
theorem lowMean_group_coverage (i : ℕ) (hi : i < 55) {q mu : ℝ}
    (hq : q ∈ FreeCountVariance.q '' Set.Icc
      (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ))
    (hmu : mu ∈ Set.Icc (4 / q) (lowMeanFractionReal (lowMeanInputRowAt i).mu0)) :
    ∃ c, c < 28 ∧ lowMeanCertificateGroupAt c = (lowMeanInputRowAt i).group ∧
      q ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt c).l)
        (lowMeanFractionReal (lowMeanCertificateAt c).h) ∧
      mu ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt c).muA)
        (lowMeanFractionReal (lowMeanCertificateAt c).muB) ∧
      mu ∈ Set.Icc (max (lowMeanFractionReal (lowMeanCertificateAt c).muA) (4 / q))
        (lowMeanFractionReal (lowMeanCertificateAt c).muB) := by
  obtain ⟨lam, hlam, rfl⟩ := hq
  exact lowMean_coverage_activity i hi hlam hmu

/-- Every activity in the full closed domain has an input selected with
its left endpoint open except at the first input. -/
theorem lowMean_selected_activity_cover {lam : ℝ}
    (hlam : lam ∈ Set.Icc (1 / 3 : ℝ) (7 / 3)) :
    ∃ i, i < 55 ∧ lowMeanLeftSelected
      (fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ))
      (fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)) i lam := by
  rcases lowMean_cover_dimensions_kernel with ⟨_, _, _, _, _, hfirst, hlast, _⟩
  have hf : (Erdos993Lean.Analytic.N44.Data.pieceLo.getD 0 0 : ℝ) = 1 / 3 := by
    rw [← lowMean_n44Lo_real, hfirst]; norm_num [lowMeanFractionReal]
  have hh : (Erdos993Lean.Analytic.N44.Data.pieceHi.getD 54 0 : ℝ) = 7 / 3 := by
    rw [← lowMean_n44Hi_real, hlast]; norm_num [lowMeanFractionReal]
  obtain ⟨i, _, hi, hs⟩ := lowMean_consecutive_left_cover
    (fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ))
    (fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)) lam 0 54
    (Or.inl ⟨rfl, by simpa only [hf] using hlam.1⟩)
    (by simpa only [zero_add, hh] using hlam.2) (by
      intro k _ hk
      exact (lowMean_n44_endpoint_facts k (by omega)).2.2.2.2.2.2 (by omega))
  exact ⟨i, by omega, hs⟩

theorem lowMean_input_separated (i j : ℕ) (hi : i < 55) (hj : j < 55) (hij : i < j) :
    (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ) ≤
      (Erdos993Lean.Analytic.N44.Data.pieceLo.getD j 0 : ℝ) := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_inputs_separated_kernel i hi
  have h' := of_decide_eq_true (Erdos993Lean.F4Fast.forall_lt_of_range_all h j hj)
  have hvi := (lowMean_input_group_checked i hi).2.2.1
  have hvj := (lowMean_input_group_checked j hj).2.1
  simpa only [lowMean_n44Hi_real, lowMean_n44Lo_real] using
    (lowMean_fraction_le_iff hvi hvj).mp (h' hij)

/-- No activity has two inputs under the paper's left-selected convention. -/
theorem lowMean_selected_activity_unique (i j : ℕ) (hi : i < 55) (hj : j < 55) {lam : ℝ}
    (hsi : lowMeanLeftSelected
      (fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ))
      (fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)) i lam)
    (hsj : lowMeanLeftSelected
      (fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ))
      (fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)) j lam) : i = j := by
  have impossible (a b : ℕ) (ha : a < 55) (hb : b < 55) (hab : a < b)
      (hsa : lowMeanLeftSelected
        (fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ))
        (fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)) a lam)
      (hsb : lowMeanLeftSelected
        (fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ))
        (fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)) b lam) : False := by
    have hsep := lowMean_input_separated a b ha hb hab
    rcases hsb.1 with hzero | hstrict
    · omega
    · linarith [hsa.2]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact impossible i j hi hj hij hsi hsj
  · exact impossible j i hj hi hji hsj hsi

theorem lowMean_activity_closed_and_selected_seam (i : ℕ) (hi : i < 54) :
    let lo := fun k => (Erdos993Lean.Analytic.N44.Data.pieceLo.getD k 0 : ℝ)
    let hi' := fun k => (Erdos993Lean.Analytic.N44.Data.pieceHi.getD k 0 : ℝ)
    hi' i ∈ Set.Icc (lo i) (hi' i) ∧ hi' i ∈ Set.Icc (lo (i + 1)) (hi' (i + 1)) ∧
      lowMeanLeftSelected lo hi' i (hi' i) ∧ ¬lowMeanLeftSelected lo hi' (i + 1) (hi' i) := by
  have h := lowMean_n44_endpoint_facts i (by omega)
  have hn := lowMean_n44_endpoint_facts (i + 1) (by omega)
  have hs := h.2.2.2.2.2.2 hi
  refine ⟨⟨h.2.2.1.le, le_rfl⟩, ⟨hs.symm.le, ?_⟩, ⟨Or.inr h.2.2.1, le_rfl⟩, ?_⟩
  · dsimp only
    rw [hs]; exact hn.2.2.1.le
  · intro hsel
    rcases hsel.1 with hzero | hlt
    · omega
    · dsimp only at hlt
      rw [← hs] at hlt; exact lt_irrefl _ hlt


/-- The eleven printed probability spans cover their full closed domain. -/
theorem lowMean_group_probability_cover {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 4 : ℝ) (7 / 10)) :
    ∃ k, k < 11 ∧ q ∈ Set.Icc (lowMeanFractionReal (lowMeanGroupAt k).l)
      (lowMeanFractionReal (lowMeanGroupAt k).h) := by
  rcases lowMean_cover_dimensions_kernel with ⟨_, _, _, _, _, _, _, hl, hh, _⟩
  have hf : lowMeanFractionReal (lowMeanGroupAt 0).l = 1 / 4 := by
    rw [hl]; norm_num [lowMeanFractionReal]
  have hend : lowMeanFractionReal (lowMeanGroupAt 10).h = 7 / 10 := by
    rw [hh]; norm_num [lowMeanFractionReal]
  obtain ⟨k, _, hk, hs⟩ := lowMean_consecutive_closed_cover
    (fun k => lowMeanFractionReal (lowMeanGroupAt k).l)
    (fun k => lowMeanFractionReal (lowMeanGroupAt k).h) q 0 10
    (by simpa only [hf] using hq.1) (by simpa only [zero_add, hend] using hq.2) (by
      intro k _ hk
      have h := of_decide_eq_true (Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_groups_order_kernel k (by omega))
      exact congrArg lowMeanFractionReal h.2.2)
  exact ⟨k, by omega, hs⟩

/-- Every closed mean seam is included in the literal group tiling. -/
theorem lowMean_group_mean_cover (k : ℕ) (hk : k < 11) {mu : ℝ}
    (hmu : mu ∈ Set.Icc (lowMeanFractionReal (lowMeanGroupAt k).muLo)
      (lowMeanFractionReal (lowMeanGroupAt k).muHi)) :
    ∃ c, c < 28 ∧ lowMeanCertificateGroupAt c = k ∧
      mu ∈ Set.Icc (lowMeanFractionReal (lowMeanCertificateAt c).muA)
        (lowMeanFractionReal (lowMeanCertificateAt c).muB) := by
  let g := lowMeanGroupAt k
  have hb := lowMean_group_bounds k hk
  have hf := lowMean_group_certificate_fields k g.certLo hk ⟨le_rfl, hb.2.2.1⟩
  have hh := lowMean_group_certificate_fields k g.certHi hk ⟨hb.2.2.1, le_rfl⟩
  have hend : g.certLo + (g.certHi - g.certLo) = g.certHi := by dsimp only [g] at *; omega
  obtain ⟨c, hc, hc', hr⟩ := lowMean_consecutive_closed_cover
    (fun c => lowMeanFractionReal (lowMeanCertificateAt c).muA)
    (fun c => lowMeanFractionReal (lowMeanCertificateAt c).muB) mu g.certLo
    (g.certHi - g.certLo)
    (by simpa only [hf.2.2.2.2.2.1 rfl] using hmu.1)
    (by simpa only [hend, hh.2.2.2.2.2.2.1 rfl] using hmu.2) (by
      intro c hc hc'
      have h := lowMean_group_certificate_fields k c hk ⟨hc, by dsimp only [g] at *; omega⟩
      exact congrArg lowMeanFractionReal (h.2.2.2.2.2.2.2 (by dsimp only [g] at *; omega)))
  have h := lowMean_group_certificate_fields k c hk ⟨hc, by dsimp only [g] at *; omega⟩
  exact ⟨c, h.1, lowMean_group_certificate_member k c hk ⟨hc, by dsimp only [g] at *; omega⟩, hr⟩

end Erdos993Lean.Analytic.V213
