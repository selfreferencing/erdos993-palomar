module

public import Erdos993Lean.Analytic.V213.LowMeanCoverageChecker

/-! Semantic interpretations of the complete grouped integer cover checks. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_group_bounds (k : ℕ) (hk : k < 11) :
    let g := lowMeanGroupAt k
    g.iotaLo ≤ g.iotaHi ∧ g.iotaHi < 55 ∧ g.certLo ≤ g.certHi ∧ g.certHi < 28 := by
  have h := (lowMean_group_checked k hk).1
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem lowMean_group_real_facts (k : ℕ) (hk : k < 11) :
    let g := lowMeanGroupAt k
    lowMeanFractionValid g.l ∧ lowMeanFractionValid g.h ∧
    lowMeanFractionValid g.D ∧ lowMeanFractionValid g.theta ∧
    lowMeanFractionValid g.muLo ∧ lowMeanFractionValid g.muHi ∧
    0 < lowMeanFractionReal g.l ∧ lowMeanFractionReal g.h < 1 ∧
    0 < lowMeanFractionReal g.D ∧ 0 < lowMeanFractionReal g.theta ∧
    lowMeanFractionReal g.muLo = 4 / lowMeanFractionReal g.h := by
  have h := (lowMean_group_checked k hk).1
  rcases h with ⟨_, _, _, _, hl, hh, hD, ht, ha, hb, hpl, hph, hpD, hpt, hmul, _⟩
  have hzero : lowMeanFractionValid (0, 1) := by decide
  have hlf := (lowMean_fraction_lt_iff hzero hl).mp hpl
  have hhf := (lowMean_fraction_lt_iff hh (by decide : lowMeanFractionValid (1, 1))).mp hph
  have hDf := (lowMean_fraction_lt_iff hzero hD).mp hpD
  have htf := (lowMean_fraction_lt_iff hzero ht).mp hpt
  simp only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div, Int.cast_one, div_one] at hlf hhf hDf htf
  refine ⟨hl, hh, hD, ht, ha, hb, hlf, hhf, hDf, htf, ?_⟩
  have hp : lowMeanFractionValid (lowMeanFractionMul (lowMeanGroupAt k).muLo (lowMeanGroupAt k).h) := Nat.mul_pos ha hh
  have hm : lowMeanFractionReal (lowMeanGroupAt k).muLo * lowMeanFractionReal (lowMeanGroupAt k).h = 4 := by
    rw [← lowMean_fraction_mul]
    simpa [lowMeanFractionReal] using (lowMean_fraction_eq_iff hp (by decide : lowMeanFractionValid (4, 1))).mp hmul
  have hne : lowMeanFractionReal (lowMeanGroupAt k).h ≠ 0 := by
    intro hz; rw [hz, mul_zero] at hm; norm_num at hm
  exact (eq_div_iff hne).mpr hm

theorem lowMean_group_certificate_fields (k i : ℕ) (hk : k < 11)
    (hi : (lowMeanGroupAt k).certLo ≤ i ∧ i ≤ (lowMeanGroupAt k).certHi) :
    let g := lowMeanGroupAt k
    let c := lowMeanCertificateAt i
    i < 28 ∧ c.l = g.l ∧ c.h = g.h ∧ c.D = g.D ∧ c.theta = g.theta ∧
    (i = g.certLo → c.muA = g.muLo) ∧
    (i = g.certHi → c.muB = g.muHi) ∧
    (i < g.certHi → c.muB = (lowMeanCertificateAt (i + 1)).muA) := by
  have hb := lowMean_group_bounds k hk
  have hi28 : i < 28 := lt_of_le_of_lt hi.2 hb.2.2.2
  have hm := lowMean_group_certificate_member k i hk hi
  have h := lowMean_certificate_group_checked i hi28
  simp only [lowMeanCertificateGroupFacts, hm] at h
  rcases h with ⟨_, _, _, hl, hh, hD, ht, ha, hb, hs⟩
  exact ⟨hi28, hl, hh, hD, ht, ha, hb, hs⟩

theorem lowMean_input_real_caps (i : ℕ) (hi : i < 55) :
    let r := lowMeanInputRowAt i
    let g := lowMeanGroupAt r.group
    r.group < 11 ∧
    lowMeanFractionReal r.D ≤ lowMeanFractionReal g.D ∧
    lowMeanFractionReal r.theta ≤ lowMeanFractionReal g.theta ∧
    lowMeanFractionReal r.mu0 ≤ lowMeanFractionReal g.muHi := by
  have h := (lowMean_input_group_checked i hi).1
  rcases h with ⟨hk, _, _, hD, ht, hm, hDb, htb, hmb⟩
  obtain ⟨_, _, hgD, hgt, _, hgm, _⟩ := lowMean_group_real_facts (lowMeanInputRowAt i).group hk
  exact ⟨hk, (lowMean_fraction_le_iff hD hgD).mp hDb,
    (lowMean_fraction_le_iff ht hgt).mp htb, (lowMean_fraction_le_iff hm hgm).mp hmb⟩

theorem lowMean_n44_endpoint_facts (i : ℕ) (hi : i < 55) :
    let a : ℝ := (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ)
    let b : ℝ := (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ)
    let g := lowMeanGroupAt (lowMeanInputRowAt i).group
    (1 / 3 : ℝ) ≤ a ∧ b ≤ (7 / 3 : ℝ) ∧ a < b ∧
    lowMeanFractionReal g.l ≤ FreeCountVariance.q a ∧
    FreeCountVariance.q b ≤ lowMeanFractionReal g.h ∧
    FreeCountVariance.Dhat b = lowMeanFractionReal (lowMeanInputRowAt i).D ∧
    (i < 54 → b = (Erdos993Lean.Analytic.N44.Data.pieceLo.getD (i + 1) 0 : ℝ)) := by
  have h := (lowMean_input_group_checked i hi).2
  rcases h with ⟨hvl, hvh, hnl, hnh, hdl, hdh, hlohi, hql, hqh, hcap, hs⟩
  have hk := (lowMean_input_real_caps i hi).1
  obtain ⟨hgl, hgh, _⟩ := lowMean_group_real_facts (lowMeanInputRowAt i).group hk
  have hqlv : lowMeanFractionValid (lowMeanActivityQFraction (lowMeanN44LoFraction i)) := by
    dsimp [lowMeanFractionValid, lowMeanActivityQFraction] at *; omega
  have hqhv : lowMeanFractionValid (lowMeanActivityQFraction (lowMeanN44HiFraction i)) := by
    dsimp [lowMeanFractionValid, lowMeanActivityQFraction] at *; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h' := (lowMean_fraction_le_iff (by decide : lowMeanFractionValid (1, 3)) hvl).mp hdl
    rw [lowMean_n44Lo_real] at h'
    simpa [lowMeanFractionReal] using h'
  · have h' := (lowMean_fraction_le_iff hvh (by decide : lowMeanFractionValid (7, 3))).mp hdh
    rw [lowMean_n44Hi_real] at h'
    simpa [lowMeanFractionReal] using h'
  · simpa only [lowMean_n44Lo_real, lowMean_n44Hi_real] using (lowMean_fraction_lt_iff hvl hvh).mp hlohi
  · have h' := (lowMean_fraction_le_iff hgl hqlv).mp hql
    simpa only [lowMean_activityQ_fraction hvl hnl, lowMean_n44Lo_real] using h'
  · have h' := (lowMean_fraction_le_iff hqhv hgh).mp hqh
    simpa only [lowMean_activityQ_fraction hvh hnh, lowMean_n44Hi_real] using h'
  · have h' := lowMean_activityCap_fraction hvh
    rw [hcap] at h'
    simpa only [lowMean_n44Hi_real] using h'.symm
  · intro hi54
    have h' := congrArg lowMeanFractionReal (hs hi54)
    simpa only [lowMean_n44Hi_real, lowMean_n44Lo_real] using h'

end Erdos993Lean.Analytic.V213
